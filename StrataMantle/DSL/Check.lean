/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public import StrataMantle.DSL.Syntax
public import StrataMantle.DSL.Model

/-!
# The `environment` command: checking

The first two passes of the elaborator.  `collect` reads the block into a model, assigning
environment names and rejecting duplicates; `resolve` resolves every type, checks arities,
parameter order and positivity, derives each datatype's case instruction, and splits the
block into stages.  Every mistake is logged
at its syntax node and the passes go on, so all of them are reported; the caller emits
nothing if any was.
-/

public meta section

namespace Strata.Mantle.DSL

open Lean Elab Command

/-! ## Errors -/

/-- The checking monad: command elaboration, and whether an error has been logged. -/
abbrev CheckM := StateT Bool CommandElabM

/-- Log `msg` at `ref`, and remember that checking failed. -/
def err (ref : Syntax) (msg : String) : CheckM Unit := do
  logErrorAt ref msg
  set true

/-- An environment name as the user writes it, unescaped: `py.add`. -/
def showName (n : Name) : String := n.toString (escape := false)

/-- A doc comment with the given text. -/
def mkDoc (s : String) : TSyntax ``Lean.Parser.Command.docComment :=
  ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (" " ++ s ++ " -/")]⟩

/-! ## The model -/

/-- Where a declaration sits: its environment namespace and the namespaces opened there. -/
structure Ctx where
  ns : Name := .anonymous
  /-- Indices into `Collected.opens`. -/
  opens : Array Nat := #[]
  deriving Inhabited

/-- What every declaration has. -/
structure Common where
  /-- The declared identifier. -/
  ref : Syntax
  envName : Name
  /-- The Lean name, relative to the environment's namespace. -/
  lean : Name
  doc? : Option (TSyntax ``Lean.Parser.Command.docComment)
  ctx : Ctx
  deriving Inhabited

/-- A constructor, as written. -/
structure CtorD where
  c : Common
  binders : Array (TSyntax `mantleBinder)
  deriving Inhabited

/-- A `type` or `data` declaration, as written.  `ctors` is `none` for a primitive type. -/
structure TypeD where
  c : Common
  /-- Name, syntax, positivity. -/
  params : Array (String × Syntax × Bool)
  ctors : Option (Array CtorD)
  deriving Inhabited

/-- An `abbrev`, as written. -/
structure AbbrevD where
  c : Common
  params : Array (String × Syntax)
  body : TSyntax `mantleTy
  deriving Inhabited

/-- An `insn`, as written.  `ret` is `none` for a terminal one. -/
structure OpD where
  c : Common
  terminal : Bool
  typeParams : Array (String × Syntax)
  binders : Array (TSyntax `mantleBinder)
  ret : Option (TSyntax `mantleTy)
  deriving Inhabited

/-- A declaration of the block, in source order.  A `group` is one `data` or one `mutual`. -/
inductive Item where
  | type (d : TypeD)
  | group (ds : Array TypeD)
  | abbrev (d : AbbrevD)
  | op (d : OpD)
  deriving Inhabited

/-- Pass 1's result. -/
structure Collected where
  items : Array Item := #[]
  /-- Each `open` argument, with the namespace it was written in. -/
  opens : Array (Ident × Name) := #[]
  /-- Every environment name the block declares, abbreviations included. -/
  declared : Std.HashMap Name Syntax := {}
  /-- Lean name → environment name, for the clash check. -/
  leanNames : Std.HashMap Name Name := {}
  deriving Inhabited

/-! ## Pass 1: collect -/

/-- The scope pass 1 walks through. -/
structure Frame where
  name : Name
  ref : Syntax
  opens : Array Nat

/-- Pass 1's state. -/
structure CollectState where
  out : Collected := {}
  frames : Array Frame := #[]
  topOpens : Array Nat := #[]

/-- Append an item. -/
def CollectState.push (s : CollectState) (i : Item) : CollectState :=
  { s with out := { s.out with items := s.out.items.push i } }

/-- Lean names the elaborator generates for the environment itself. -/
def reservedLean (parentShort : Option Name) : List Name :=
  [`env, `names, `mem_env, `Internal] ++ (parentShort.map (fun p => [p]) |>.getD [])

section
variable (envShort : Name) (ancestorNames : Std.HashSet Name) (reserved : List Name)

/-- The current environment namespace and the opens in scope. -/
def CollectState.ctx (s : CollectState) : Ctx :=
  { ns := s.frames.foldl (fun n f => n ++ f.name) .anonymous
    opens := s.frames.foldl (fun os f => os ++ f.opens) s.topOpens }

/-- Read `as "s"`. -/
def readAs (as? : Option (TSyntax `Strata.Mantle.DSL.mantleAs)) : Option String :=
  as?.map fun a => a.raw[1].isStrLit?.getD ""

/-- Name a declaration: check its identifier, its environment name and its Lean name. -/
def declare (s : CollectState) (id : Ident) (as? : Option String)
    (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (leanPrefix : Name := .anonymous)
    (generated : List Name := []) : StateT CollectState CheckM Common := do
  let ctx := s.ctx
  let short := id.getId
  unless short.isAtomic do
    err id s!"`{showName short}`: a declaration's name has one component; use `namespace`"
  let envName := ctx.ns ++ (match as? with | some a => Name.mkSimple a | none => short)
  let lean := leanPrefix ++ short
  let st ← get
  let dup := ancestorNames.contains envName || st.out.declared.contains envName
  if dup then
    err id s!"`{showName envName}` is already declared"
  else
    modify fun st =>
      { st with out := { st.out with declared := st.out.declared.insert envName id } }
  if dup then pure ()
  else if leanPrefix.isAnonymous && reserved.contains short.getRoot then
    err id s!"`{showName (envShort ++ short)}` is reserved for the environment; \
      rename one with `as`"
  else
    let mut clash := false
    for g in lean :: generated do
      if let some other := st.out.leanNames[g]? then
        unless clash do
          err id s!"`{showName (envShort ++ g)}` is already generated for \
            `{showName other}`; rename one with `as`"
        clash := true
    unless clash do
      modify fun st =>
        let ln := (lean :: generated).foldl (fun m g => m.insert g envName) st.out.leanNames
        { st with out := { st.out with leanNames := ln } }
  return { ref := id, envName, lean, doc?, ctx }

/-- The Lean names a type `T` generates besides its own: `T.ref`, `T.ty`, `T.name`,
`T.name_ref` and `T.decl_ref`, and a datatype's case instruction `T.case`, with its `sig` and
`name`.  A constructor `c` of `T` is `T.c`, so `declare` rejects each of these as a
constructor name. -/
def typeGenerated (lean : Name) (data : Bool := false) : List Name :=
  [lean ++ `ref, lean ++ `ty, lean ++ `name, lean ++ `name_ref, lean ++ `decl_ref] ++
    if data then [lean ++ `case, lean ++ `case ++ `sig, lean ++ `case ++ `name] else []

/-- The environment name of a datatype's case instruction: `case` under the datatype's. -/
def caseName (envName : Name) : Name := Name.mkStr envName "case"

/-- The Lean names an instruction generates besides its own. -/
def opGenerated (lean : Name) : List Name := [lean ++ `sig, lean ++ `name]

/-- Read the type parameters of a `type` or `data`. -/
def readTyParams (ps : Array (TSyntax `Strata.Mantle.DSL.mantleTyParam)) :
    Array (String × Syntax × Bool) :=
  ps.map fun p =>
    let id := p.raw[2]
    (id.getId.toString (escape := false), id, !p.raw[1].getArgs.isEmpty)

/-- Read a `data` declaration's constructors, after the type itself is declared. -/
def readCtors (ty : Common) (cs : Array (TSyntax `Strata.Mantle.DSL.mantleCtor)) :
    StateT CollectState CheckM (Array CtorD) := do
  let mut out := #[]
  for c in cs do
    match c with
    | `(mantleCtor| | $[$doc?:docComment]? $n:ident $[$as?:mantleAs]? $bs:mantleBinder*) =>
      let cm ← declare envShort ancestorNames reserved (← get) n (readAs as?) doc?
        (leanPrefix := ty.lean)
      out := out.push { c := cm, binders := bs }
    | _ => err c "unexpected constructor syntax"
  return out

/-- Pass 1 over one declaration.  Inside `mutual … end`, `group?` collects the datatypes,
which become one item at the `end`. -/
partial def collectDecl (d : TSyntax `mantleDecl) (group? : Option (IO.Ref (Array TypeD))) :
    StateT CollectState CheckM Unit := do
  let s ← get
  if let some _ := group? then
    unless d.raw.isOfKind ``declData do
      err d "only `data` may appear in `mutual`"
      return
  match d with
  | `(mantleDecl| $[$doc?:docComment]? type $n:ident $[$as?:mantleAs]? $ps:mantleTyParam*) =>
    let c ← declare envShort ancestorNames reserved s n (readAs as?) doc?
      (generated := typeGenerated n.getId)
    modify (·.push (.type { c, params := readTyParams ps, ctors := none }))
  | `(mantleDecl| $[$doc?:docComment]? data $n:ident $[$as?:mantleAs]? $ps:mantleTyParam*
        where $cs:mantleCtor*) =>
    let c ← declare envShort ancestorNames reserved s n (readAs as?) doc?
      (generated := typeGenerated n.getId (data := true))
    -- The case instruction's environment name.
    let cn := caseName c.envName
    let st ← get
    if ancestorNames.contains cn || st.out.declared.contains cn then
      err n s!"`{showName cn}`, the case instruction of `{showName c.envName}`, is already \
        declared"
    else
      modify fun st => { st with out := { st.out with declared := st.out.declared.insert cn n } }
    let ctors ← readCtors envShort ancestorNames reserved c cs
    let t : TypeD := { c, params := readTyParams ps, ctors := some ctors }
    match group? with
    | some g => g.modify (·.push t)
    | none => modify (·.push (.group #[t]))
  | `(mantleDecl| $[$doc?:docComment]? abbrev $n:ident $[$as?:mantleAs]? $[( $ps* )]?
        := $body) =>
    let c ← declare envShort ancestorNames reserved s n (readAs as?) doc?
      (generated := [n.getId ++ `ty])
    let params := (ps.getD #[]).map fun p => (p.getId.toString (escape := false), p.raw)
    modify (·.push (.abbrev { c, params, body }))
  | `(mantleDecl| $[$doc?:docComment]? $[$term?:mantleTerminal]? insn $n:ident
        $[$as?:mantleAs]? $[[ $tps* ]]? $bs:mantleBinder* $[: $ret?]?) =>
    let c ← declare envShort ancestorNames reserved s n (readAs as?) doc?
      (generated := opGenerated n.getId)
    let typeParams := (tps.getD #[]).map fun p => (p.getId.toString (escape := false), p.raw)
    match term?, ret? with
    | some _, some r => err r "a terminal instruction has no result type"
    | none, none => err n s!"`{showName n.getId}` needs a result type `: τ`"
    | _, _ => pure ()
    modify (·.push (.op { c, terminal := term?.isSome, typeParams, binders := bs, ret := ret? }))
  | `(mantleDecl| namespace $n:ident) =>
    modify fun st =>
      { st with frames := st.frames.push { name := n.getId, ref := n, opens := #[] } }
  | `(mantleDecl| end $[$n?:ident]?) =>
    match s.frames.back?, n? with
    | none, some n => err n s!"`end {showName n.getId}` has no namespace to close"
    | none, none => err d "`end` has no namespace to close"
    | some f, none => err d s!"`end` needs the namespace's name: `end {showName f.name}`"
    | some f, some n =>
      if f.name != n.getId then
        err n s!"`end {showName n.getId}` closes namespace `{showName f.name}`"
      else
        modify fun st => { st with frames := st.frames.pop }
  | `(mantleDecl| open $ns:ident*) =>
    for o in ns do
      let st ← get
      let i := st.out.opens.size
      modify fun st => { st with out := { st.out with opens := st.out.opens.push (o, st.ctx.ns) } }
      modify fun st =>
        match st.frames.back? with
        | some f => { st with frames := st.frames.pop.push { f with opens := f.opens.push i } }
        | none => { st with topOpens := st.topOpens.push i }
  | _ =>
    if d.raw.isOfKind ``declDef then
      err d.raw[1] "defined instructions are not supported yet"
    else if d.raw.isOfKind ``declMutual then
      if group?.isSome then
        err d "only `data` may appear in `mutual`"
        return
      let g ← IO.mkRef #[]
      for inner in d.raw[1].getArgs do
        -- Each element is the declaration, or a node holding it alone.
        let inner := if inner.getNumArgs == 1 && !inner.isOfKind ``declData then inner[0] else inner
        collectDecl ⟨inner⟩ (some g)
      let members ← g.get
      unless members.isEmpty do
        modify (·.push (.group members))
    else
      err d "unsupported declaration"

end

/-- Pass 1: read the block. -/
def collect (envShort : Name) (ancestorNames : Std.HashSet Name) (reserved : List Name)
    (ds : Array (TSyntax `mantleDecl)) : CheckM Collected := do
  let ((), s) ← (ds.forM fun d => collectDecl envShort ancestorNames reserved d none).run {}
  return s.out

/-! ## Pass 2: resolve -/

/-- What a name in a type can stand for. -/
inductive Known where
  /-- A type; `own` is its stage and position in the stage's batch, if this block declares
  it. -/
  | type (info : TypeInfo) (own : Option (Nat × Nat))
  | abbrev (info : AbbrevInfo)

/-- A constructor, resolved: its arguments' names and types. -/
structure RCtor where
  d : CtorD
  args : Array (String × RTy)
  deriving Inhabited

/-- A region, resolved: its name, entry parameters and the type it leaves with. -/
structure RRegion where
  name : String
  params : Array (String × RTy)
  ret : RTy
  deriving Inhabited

/-- A successor, resolved: its name and the types of the values it receives. -/
structure RSucc where
  name : String
  payload : Array RTy
  deriving Inhabited

/-- An instruction, resolved. -/
structure ROp where
  d : OpD
  args : Array (String × RTy)
  /-- The variadic's name and element type. -/
  variadic : Option (String × RTy)
  regions : Array RRegion
  succs : Array RSucc
  /-- The return type, or `none` for a terminal instruction. -/
  ret : Option RTy
  deriving Inhabited

/-- One `addTypes`, `addData` or `addInsns` of the chain. -/
inductive Stage where
  | types (ds : Array TypeD)
  | data (members : Array (TypeD × Array RCtor × ROp))
  | ops (ds : Array ROp)
  deriving Inhabited

/-- Pass 2's result. -/
structure Resolved where
  stages : Array Stage := #[]
  /-- The abbreviations, with the stage count when each was declared. -/
  abbrevs : Array (AbbrevD × AbbrevInfo) := #[]
  /-- Every type this block declares, by environment name: its stage (from 1) and position. -/
  own : Std.HashMap Name (TypeInfo × Nat × Nat) := {}
  deriving Inhabited

/-- What pass 2 reads. -/
structure ResolveCtx where
  envNs : Name
  /-- Each `open`, resolved to an absolute namespace, or `none` if it did not resolve. -/
  opens : Array (Option Name)

/-- The candidates for `n` written in namespace `ns`: `ns.n`, then each enclosing namespace's,
innermost first, then `n` itself. -/
def scopeCandidates (ns n : Name) : List Name :=
  let rec go : Name → List Name
    | .anonymous => [n]
    | p@(.str q _) => (p ++ n) :: go q
    | p@(.num q _) => (p ++ n) :: go q
  go ns

/-- Resolve `id`, a name in a type, to a known type or abbreviation. -/
def resolveName (rc : ResolveCtx) (ctx : Ctx) (known : Std.HashMap Name Known) (id : Ident) :
    CheckM (Option (Name × Known)) := do
  let n := id.getId
  for c in scopeCandidates ctx.ns n do
    if let some k := known[c]? then return some (c, k)
  let mut hits : Array (Name × Known) := #[]
  for i in ctx.opens do
    if let some (some o) := rc.opens[i]? then
      let c := o ++ n
      if let some k := known[c]? then
        unless hits.any (·.1 == c) do hits := hits.push (c, k)
  match hits.size with
  | 0 => err id s!"unknown type `{showName n}`"; return none
  | 1 => return hits[0]?
  | _ =>
    let shown := ", ".intercalate (hits.toList.map fun (c, _) => s!"`{showName c}`")
    err id s!"`{showName n}` is ambiguous: {shown}"
    return none

/-- `n argument(s)`. -/
def plural (n : Nat) (w : String) : String := if n == 1 then s!"1 {w}" else s!"{n} {w}s"

/-- Resolve a type under the type variables `vars`. -/
partial def resolveTy (rc : ResolveCtx) (ctx : Ctx) (known : Std.HashMap Name Known)
    (vars : Array String) (stx : TSyntax `mantleTy) : CheckM (Option RTy) := do
  match stx with
  | `(mantleTy| ( $t )) => resolveTy rc ctx known vars t
  | `(mantleTy| $f:ident) => app f #[]
  | `(mantleTy| $f:ident $args*) => app f args
  | _ => err stx "unexpected type syntax"; return none
where
  app (f : Ident) (args : Array (TSyntax `mantleTy)) : CheckM (Option RTy) := do
    let n := f.getId
    if n.isAtomic then
      if let some i := vars.idxOf? (n.toString (escape := false)) then
        unless args.isEmpty do
          err f s!"type parameter `{showName n}` takes no arguments"
          return none
        return some (.var i)
    let some (full, k) ← resolveName rc ctx known f | return none
    let arity := match k with
      | .type info _ => info.params.size
      | .abbrev info => info.arity
    if arity != args.size then
      err f s!"type `{showName n}` expects {plural arity "argument"}, got {args.size}"
      return none
    let mut rargs := #[]
    let mut ok := true
    for a in args do
      match ← resolveTy rc ctx known vars a with
      | some r => rargs := rargs.push r
      | none => ok := false
    unless ok do return none
    match k with
    | .type _ _ => return some (.app full rargs)
    | .abbrev info => return some (info.body.subst rargs)

/-- Check names for duplicates against `seen`, reporting each at its second occurrence. -/
def checkDistinct (seen : Array String) (xs : Array (String × Syntax)) :
    CheckM (Array String) := do
  let mut seen := seen
  for (x, ref) in xs do
    if seen.contains x then err ref s!"duplicate parameter `{x}`"
    seen := seen.push x
  return seen

/-- Resolve `(x y : τ)` binders, which are all a constructor takes. -/
def resolveArgBinders (rc : ResolveCtx) (ctx : Ctx) (known : Std.HashMap Name Known)
    (vars : Array String) (seen : Array String) (bs : Array (TSyntax `mantleBinder)) :
    CheckM (Array (String × RTy × Syntax) × Array String) := do
  let mut out := #[]
  let mut seen := seen
  for b in bs do
    match b with
    | `(mantleBinder| ( $xs:ident* : $t )) =>
      seen ← checkDistinct seen (xs.map fun x => (x.getId.toString (escape := false), x.raw))
      if let some r ← resolveTy rc ctx known vars t then
        for x in xs do out := out.push (x.getId.toString (escape := false), r, t.raw)
    | _ => err b "a constructor takes only arguments `(x : τ)`"
  return (out, seen)

/-- The rank of a binder: arguments, then the variadic, then regions, then successors. -/
def binderRank (b : TSyntax `mantleBinder) : Nat :=
  if b.raw.isOfKind ``binderArgs then 0
  else if b.raw.isOfKind ``binderVariadic then 1
  else if b.raw.isOfKind ``binderRegions then 2
  else 3

/-- What a binder of rank `r`, out of order, must precede. -/
def binderOrderMsg : Nat → String
  | 0 => "arguments must come before the variadic, the regions and the successors"
  | 1 => "the variadic must come before the regions and the successors"
  | _ => "regions must come before the successors"

/-- Resolve an instruction's binders and return type. -/
def resolveOp (rc : ResolveCtx) (known : Std.HashMap Name Known) (d : OpD) :
    CheckM (Option ROp) := do
  let ctx := d.c.ctx
  let vars := d.typeParams.map (·.1)
  let errsBefore ← get
  set false
  let mut seen ← checkDistinct #[] d.typeParams
  let mut args := #[]
  let mut variadic : Option (String × RTy) := none
  let mut nPoly := 0
  let mut regions := #[]
  let mut succs := #[]
  let mut maxRank := 0
  for b in d.binders do
    let r := binderRank b
    if r < maxRank then err b (binderOrderMsg r)
    maxRank := max maxRank r
    match b with
    | `(mantleBinder| ( $xs:ident* : $t )) =>
      seen ← checkDistinct seen (xs.map fun x => (x.getId.toString (escape := false), x.raw))
      if let some ty ← resolveTy rc ctx known vars t then
        for x in xs do args := args.push (x.getId.toString (escape := false), ty)
    | `(mantleBinder| ( * $xs:ident* : $t )) =>
      nPoly := nPoly + 1
      if nPoly > 1 then err b "at most one variadic"
      if h : 1 < xs.size then err xs[1] "a variadic binds one name"
      seen ← checkDistinct seen
        ((xs.extract 0 1).map fun x => (x.getId.toString (escape := false), x.raw))
      if let some ty ← resolveTy rc ctx known vars t then
        if variadic.isNone then
          variadic := some ((xs[0]?.map (·.getId.toString (escape := false))).getD "", ty)
    | `(mantleBinder| ( $[& $rs:ident]* $ps:mantleParams* : $t )) =>
      seen ← checkDistinct seen (rs.map fun x => (x.getId.toString (escape := false), x.raw))
      let mut params := #[]
      let mut pseen := #[]
      for p in ps do
        match p with
        | `(mantleParams| ( $xs:ident* : $pt )) =>
          pseen ← checkDistinct pseen
            (xs.map fun x => (x.getId.toString (escape := false), x.raw))
          if let some ty ← resolveTy rc ctx known vars pt then
            for x in xs do params := params.push (x.getId.toString (escape := false), ty)
        | _ => err p "unexpected region parameter syntax"
      if let some ty ← resolveTy rc ctx known vars t then
        for r in rs do
          regions := regions.push { name := r.getId.toString (escape := false), params, ret := ty }
    | `(mantleBinder| ( $[^ $ks:ident]* $ps:mantleParams* )) =>
      seen ← checkDistinct seen (ks.map fun x => (x.getId.toString (escape := false), x.raw))
      let mut payload := #[]
      let mut pseen := #[]
      for p in ps do
        match p with
        | `(mantleParams| ( $xs:ident* : $pt )) =>
          pseen ← checkDistinct pseen
            (xs.map fun x => (x.getId.toString (escape := false), x.raw))
          if let some ty ← resolveTy rc ctx known vars pt then
            for _ in xs do payload := payload.push ty
        | _ => err p "unexpected successor parameter syntax"
      for k in ks do
        succs := succs.push { name := k.getId.toString (escape := false), payload }
    | _ => err b "unexpected binder syntax"
  -- `some none` for a terminal instruction, `none` if the return type does not resolve.
  let ret : Option (Option RTy) ← match d.ret with
    | some t => pure ((← resolveTy rc ctx known vars t).map some)
    | none => pure (some none)
  let failed ← get
  set (errsBefore || failed)
  if failed then return none
  let some ret := ret | return none
  return some { d, args, variadic, regions, succs, ret }

/-- Check a payload type of a group: a member, or a parameter declared positive, may not
occur under a non-positive parameter.  This is what `DataTy.ok` decides. -/
partial def checkPositive (known : Std.HashMap Name Known) (members : Array Name)
    (pol : Array (String × Syntax × Bool)) (ref : Syntax) (t : RTy)
    (under : Option (Name × Nat)) :
    CheckM Unit := do
  match t with
  | .var l =>
    if let (some (h, i), some (x, _, true)) := (under, pol[l]?) then
      err ref s!"positive parameter `{x}` occurs under non-positive parameter {i} of \
        `{showName h}`"
  | .app h args =>
    if let some (g, i) := under then
      if members.contains h then
        err ref s!"`{showName h}` recurses through non-positive parameter {i} of `{showName g}`"
        return
    let ps := match known[h]? with
      | some (.type info _) => info.params.map (fun (p : String × Bool) => p.2)
      | _ => #[]
    for h' : j in [0:args.size] do
      let a := args[j]
      let under' := match under with
        | some u => some u
        | none => if ps[j]?.getD true then none else some (h, j + 1)
      checkPositive known members pol ref a under'

/-- The case instruction of the datatype `d`, whose constructors are `rcs`:
`terminal insn T.case [a …] (scrutinee : T a …) (^c₁ (x : τ)) …`, one successor per
constructor, in declaration order, receiving its fields.  A successor is named by its
constructor, so no constructor may be named as a parameter of `T` or as `scrutinee`. -/
def caseOp (d : TypeD) (rcs : Array RCtor) :
    CheckM (Option ROp) := do
  let params := d.params.map (·.1)
  let mut ok := true
  for c in rcs do
    let sname := c.d.c.envName.getString!
    if params.contains sname || sname == "scrutinee" then
      let what := if sname == "scrutinee" then "the scrutinee" else "a parameter"
      err c.d.c.ref s!"constructor `{sname}` clashes with {what} of \
        `{showName (caseName d.c.envName)}`; rename one with `as`"
      ok := false
  unless ok do return none
  let en := showName d.c.envName
  let opd : OpD :=
    { c := { ref := d.c.ref, envName := caseName d.c.envName, lean := d.c.lean ++ `case,
             doc? := some (mkDoc s!"Eliminate a `{en}`: one successor per constructor, in \
               declaration order, each receiving its constructor's fields."),
             ctx := d.c.ctx }
      terminal := true, typeParams := d.params.map (fun (x, r, _) => (x, r)), binders := #[],
      ret := none }
  let self : RTy := .app d.c.envName ((Array.range params.size).map RTy.var)
  let succs : Array RSucc := rcs.map fun c =>
    { name := c.d.c.envName.getString!, payload := c.args.map (·.2) }
  let r : ROp :=
    { d := opd
      args := #[("scrutinee", self)]
      variadic := none
      regions := #[]
      succs := succs
      ret := none }
  return some r

/-- Pass 2: resolve the block and split it into stages. -/
def resolve (rc : ResolveCtx) (ancestors : Array EnvEntry) (items : Array Item) :
    CheckM Resolved := do
  let mut known : Std.HashMap Name Known := {}
  -- The ancestors' types and abbreviations, farthest first.
  for e in ancestors.reverse do
    for t in e.types do known := known.insert t.envName (.type t none)
    for a in e.abbrevs do known := known.insert a.envName (.abbrev a)
  let mut stages : Array Stage := #[]
  let mut own : Std.HashMap Name (TypeInfo × Nat × Nat) := {}
  let mut abbrevs : Array (AbbrevD × AbbrevInfo) := #[]
  -- `run`: 1 inside a run of types, 2 inside a run of instructions.
  let mut run := 0
  for item in items do
    match item with
    | .type d =>
      if run != 1 then
        stages := stages.push (.types #[])
        run := 1
      let k := stages.size
      let some (.types ds) := stages.back? | unreachable!
      discard <| checkDistinct #[] (d.params.map fun (x, r, _) => (x, r))
      let info : TypeInfo :=
        { envName := d.c.envName, owner := rc.envNs, lean := d.c.lean,
          params := d.params.map fun (x, _, b) => (x, b) }
      stages := stages.pop.push (.types (ds.push d))
      own := own.insert d.c.envName (info, k, ds.size)
      known := known.insert d.c.envName (.type info (some (k, ds.size)))
    | .group ds =>
      run := 0
      let k := stages.size + 1
      for h : j in [0:ds.size] do
        let d := ds[j]
        discard <| checkDistinct #[] (d.params.map fun (x, r, _) => (x, r))
        let ctors := (d.ctors.getD #[]).map (·.c.envName)
        let info : TypeInfo :=
          { envName := d.c.envName, owner := rc.envNs, lean := d.c.lean,
            params := d.params.map (fun (x, _, b) => (x, b)), ctors }
        own := own.insert d.c.envName (info, k, j)
        known := known.insert d.c.envName (.type info (some (k, j)))
      let members := ds.map (·.c.envName)
      let mut out := #[]
      for d in ds do
        let vars := d.params.map (·.1)
        let mut rcs := #[]
        for c in d.ctors.getD #[] do
          -- A constructor's instruction binds the datatype's parameters and then its fields,
          -- so a field may not reuse a parameter's name.
          let (args, _) ← resolveArgBinders rc c.c.ctx known vars vars c.binders
          -- Positivity, at each payload's type syntax.
          for (_, r, ref) in args do
            checkPositive known members d.params ref r none
          rcs := rcs.push { d := c, args := args.map fun (x, r, _) => (x, r) }
        -- The member's case instruction, which the group's `addData` declares.
        if let some r ← caseOp d rcs then out := out.push (d, rcs, r)
      stages := stages.push (.data out)
    | .abbrev d =>
      let vars := d.params.map (·.1)
      discard <| checkDistinct #[] d.params
      if let some body ← resolveTy rc d.c.ctx known vars d.body then
        let info : AbbrevInfo :=
          { envName := d.c.envName, owner := rc.envNs, lean := d.c.lean,
            arity := d.params.size, body }
        abbrevs := abbrevs.push (d, info)
        known := known.insert d.c.envName (.abbrev info)
    | .op d =>
      if run != 2 then
        stages := stages.push (.ops #[])
        run := 2
      if let some r ← resolveOp rc known d then
        let some (.ops rs) := stages.back? | unreachable!
        stages := stages.pop.push (.ops (rs.push r))
  return { stages, abbrevs, own }

/-- Every prefix of every name: the namespaces that exist. -/
def namespacesOf (names : Array Name) : Std.HashSet Name := Id.run do
  let mut s : Std.HashSet Name := {}
  for n in names do
    let mut p := n.getPrefix
    while !p.isAnonymous do
      s := s.insert p
      p := p.getPrefix
  return s

/-- Resolve each `open` argument to an absolute namespace. -/
def resolveOpens (namespaces : Std.HashSet Name) (opens : Array (Ident × Name)) :
    CheckM (Array (Option Name)) :=
  opens.mapM fun (o, ns) => do
    match (scopeCandidates ns o.getId).find? namespaces.contains with
    | some n => return some n
    | none => err o s!"unknown namespace `{showName o.getId}`"; return none

end Strata.Mantle.DSL

end
