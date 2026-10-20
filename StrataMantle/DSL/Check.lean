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
kinds, parameter order and positivity, derives each datatype's case instruction, and splits
the block into stages.  A type expression is resolved first, and its kind is then
`TypeExpr.Raw.kind`'s.  Every mistake is logged at its syntax node and the passes go on, so all of them are reported; the caller emits
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
  /-- Name, syntax, positivity, kind. -/
  params : Array (String × Syntax × Bool × Kind)
  ctors : Option (Array CtorD)
  deriving Inhabited

/-- An `abbrev`, as written. -/
structure AbbrevD where
  c : Common
  /-- Name, syntax, kind. -/
  params : Array (String × Syntax × Kind)
  body : TSyntax `mantleTy
  deriving Inhabited

/-- An `insn`, as written.  `ret` is `none` for a terminal one. -/
structure OpD where
  c : Common
  terminal : Bool
  /-- Name, syntax, kind. -/
  typeParams : Array (String × Syntax × Kind)
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
  [`env, `names, `mem_env, `nameSet, `nameSet_ordered, `mem_nameSet, `Internal] ++
    (parentShort.map (fun p => [p]) |>.getD [])

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
`T.name_ref`, `T.decl_ref` and `T.toRaw_ty`, and a datatype's case instruction `T.case`, with
its `sig` and `name`.  A constructor `c` of `T` is `T.c`, so `declare` rejects each of these as
a constructor name. -/
def typeGenerated (lean : Name) (data : Bool := false) : List Name :=
  [lean ++ `ref, lean ++ `ty, lean ++ `name, lean ++ `name_ref, lean ++ `decl_ref,
    lean ++ `toRaw_ty] ++
    if data then [lean ++ `case, lean ++ `case ++ `sig, lean ++ `case ++ `name] else []

/-- The environment name of a datatype's case instruction: `case` under the datatype's. -/
def caseName (envName : Name) : Name := Name.mkStr envName "case"

/-- The Lean names an instruction generates besides its own. -/
def opGenerated (lean : Name) : List Name := [lean ++ `sig, lean ++ `name]

/-- Read the type parameters of a `type` or `data`. -/
def readTyParams (ps : Array (TSyntax `Strata.Mantle.DSL.mantleTyParam)) :
    Array (String × Syntax × Bool × Kind) :=
  ps.map fun p =>
    let id := p.raw[2]
    (id.getId.toString (escape := false), id, !p.raw[1].getArgs.isEmpty,
      if p.raw[3].getArgs.isEmpty then .type else .list)

/-- Read type parameters written as for an `insn` or `abbrev`: a bare name is a type, and each
name of `(cs ds : list)` a list. -/
def readKindedParams (ps : Array Syntax) : Array (String × Syntax × Kind) :=
  let read (p : Syntax) (k : Kind) := (p.getId.toString (escape := false), p, k)
  ps.flatMap fun p => if p.isIdent then #[read p .type] else p[1].getArgs.map (read · .list)

/-- Read an `insn`'s type parameters. -/
def readInsnParams (tps? : Option (TSyntax `Strata.Mantle.DSL.mantleInsnParams)) :
    Array (String × Syntax × Kind) :=
  readKindedParams ((tps?.map (·.raw[1].getArgs)).getD #[])

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
    let params := readKindedParams ((ps.getD #[]).map (·.raw))
    modify (·.push (.abbrev { c, params, body }))
  | `(mantleDecl| $[$doc?:docComment]? $[$term?:mantleTerminal]? insn $n:ident
        $[$as?:mantleAs]? $[$tps?:mantleInsnParams]? $bs:mantleBinder* $[: $ret?]?) =>
    let c ← declare envShort ancestorNames reserved s n (readAs as?) doc?
      (generated := opGenerated n.getId)
    let typeParams := readInsnParams tps?
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
  args : Array (String × Ty)
  deriving Inhabited

/-- A region, resolved: its name, entry parameters and the type it leaves with. -/
structure RRegion where
  name : String
  params : Array (String × Ty)
  ret : Ty
  deriving Inhabited

/-- A successor, resolved: its name and the types of the values it receives, a list for a
spread, which receives one value per element. -/
structure RSucc where
  name : String
  payload : Array Ty
  deriving Inhabited

/-- An instruction, resolved. -/
structure ROp where
  d : OpD
  args : Array (String × Ty)
  /-- The variadic's name and type: a type, or a list for a spread. -/
  variadic : Option (String × Ty)
  regions : Array RRegion
  succs : Array RSucc
  /-- The return type, or `none` for a terminal instruction. -/
  ret : Option Ty
  deriving Inhabited

/-- The most types or instructions one stage holds.  A reference to the `j`th declaration of a
stage, and each proof about the stage's literal, reduces the literal in the elaborator, so a
bound keeps each of them small whatever the block's size.  A datatype group is one stage,
however many constructors it has. -/
def stageMax : Nat := 64

/-- One `addTypes`, `addData` or `addInsns` of the chain.  A run of types, or of
instructions, is split into stages of at most `stageMax`, which the interface does not show. -/
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

/-- Whether `stx` is a name, perhaps in parentheses. -/
partial def isName (stx : TSyntax `mantleTy) : Bool :=
  match stx with
  | `(mantleTy| ( $t )) => isName t
  | `(mantleTy| $_:ident) => true
  | _ => false

/-- Report `r`, a list written `stx`, where a type belongs: a list parameter named alone with a
hint to splice it, and anything else, `[*as]` included, with `msg`.  `vars` names the
variables. -/
def notType (vars : Array (String × Kind)) (stx : TSyntax `mantleTy) (r : Ty) (msg : String) :
    CheckM Unit :=
  match r with
  | .list #[.var i] =>
    match vars[i]? with
    | some (x, .list) =>
      if isName stx then
        err stx s!"list parameter `{x}` where a type is expected; splice it into a list with \
          `*{x}`"
      else err stx msg
    | some (_, .type) | none => err stx msg
  | _ => err stx msg

/-- Resolve a type expression under the variables `vars`, each a name and a kind, whatever its
kind: a type or a list.  `TypeExpr.Raw.kind` gives the kind.  Every list is a literal: a list
parameter `cs` is `[*cs]`.  A literal holds types and at most one splice `*x`, anywhere,
of a list. -/
partial def resolveExpr (rc : ResolveCtx) (ctx : Ctx) (known : Std.HashMap Name Known)
    (vars : Array (String × Kind)) (stx : TSyntax `mantleTy) : CheckM (Option Ty) := do
  match stx with
  | `(mantleTy| ( $t )) => resolveExpr rc ctx known vars t
  | `(mantleTy| [ $es,* ]) => literal es.getElems
  | `(mantleTy| * $x:ident) =>
    err stx s!"a splice `*{showName x.getId}` is allowed only inside `[…]`"; return none
  | `(mantleTy| $f:ident) => app f #[]
  | `(mantleTy| $f:ident $args*) => app f args
  | _ => err stx "unexpected type syntax"; return none
where
  /-- The variable `x` names, with its level. -/
  var? (x : Name) : Option Nat :=
    if x.isAtomic then
      let s := x.toString (escape := false)
      vars.findIdx? (·.1 == s)
    else none
  app (f : Ident) (args : Array (TSyntax `mantleTy)) : CheckM (Option Ty) := do
    let n := f.getId
    if let some i := var? n then
      unless args.isEmpty do
        err f s!"type parameter `{showName n}` takes no arguments"
        return none
      -- A list parameter is the literal that splices it.
      match (vars[i]?.map (·.2) : Option Kind) with
      | some .list => return some (.list #[.var i])
      | some .type | none => return some (.var i)
    let some (full, k) ← resolveName rc ctx known f | return none
    let kinds : Array Kind := match k with
      | .type info _ => info.params.map (·.2.2)
      | .abbrev info => info.params
    if kinds.size != args.size then
      err f s!"type `{showName n}` expects {plural kinds.size "argument"}, got {args.size}"
      return none
    let mut rargs := #[]
    let mut ok := true
    for h : j in [0:args.size] do
      let a := args[j]
      let some r ← resolveExpr rc ctx known vars a
        | ok := false
      match kinds[j]?.getD .type, r.kind (vars.map (·.2)) with
      | .list, .type =>
        err a s!"argument {j + 1} of `{showName n}` is a type, but its parameter takes a list \
          of types"
        ok := false
      | .type, .list =>
        notType vars a r s!"argument {j + 1} of `{showName n}` is a list of types, but its \
          parameter takes a type"
        ok := false
      | _, _ => rargs := rargs.push r
    unless ok do return none
    match k with
    | .type _ _ => return some (.app (mantleName full) rargs)
    -- Instantiation splices a list argument where the body splices its parameter.  Each
    -- literal keeps at most one splice: the body's splices the parameter at most once, and the
    -- argument, itself a literal, splices at most one list in its place.
    | .abbrev info => return some (info.body.instantiate rargs)
  /-- A list literal's elements: types, and at most one splice, anywhere, of a list. -/
  literal (es : Array (TSyntax `mantleTy)) : CheckM (Option Ty) := do
    let mut out := #[]
    let mut ok := true
    let mut splices := 0
    for h : i in [0:es.size] do
      let e := es[i]
      match e with
      | `(mantleTy| * $x:ident) =>
        splices := splices + 1
        if splices > 1 then
          err e "a list may splice at most one list parameter"; ok := false
        match ← app x #[] with
        | some (.list #[r@(.var _)]) => out := out.push r
        | some _ =>
          err x s!"`{showName x.getId}` is not a list parameter: only a list parameter may \
            be spliced"
          ok := false
        | none => ok := false
      | _ =>
        match ← resolveExpr rc ctx known vars e with
        | some r =>
          if r.kind (vars.map (·.2)) == .list then
            notType vars e r "a list of types may not hold a list"; ok := false
          else out := out.push r
        | none => ok := false
    unless ok do return none
    return some (.list out)

/-- Resolve a type, an expression of kind `.type`, under the variables `vars`. -/
def resolveTy (rc : ResolveCtx) (ctx : Ctx) (known : Std.HashMap Name Known)
    (vars : Array (String × Kind)) (stx : TSyntax `mantleTy) : CheckM (Option Ty) := do
  let some r ← resolveExpr rc ctx known vars stx | return none
  if r.kind (vars.map (·.2)) == .list then
    notType vars stx r "a list of types where a type is expected"
    return none
  return some r

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
    (vars : Array (String × Kind)) (seen : Array String) (bs : Array (TSyntax `mantleBinder)) :
    CheckM (Array (String × Ty × Syntax) × Array String) := do
  let mut out := #[]
  let mut seen := seen
  for b in bs do
    match b with
    | `(mantleBinder| ( $xs:ident* : $t )) =>
      seen ← checkDistinct seen (xs.map fun x => (x.getId.toString (escape := false), x.raw))
      if let some r ← resolveTy rc ctx known vars t then
        for x in xs do out := out.push (x.getId.toString (escape := false), r, t.raw)
    | `(mantleBinder| ( * $_:ident* : $_ )) =>
      err b "a constructor takes no spread `(*xs : τ)`: each field is one value"
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

/-- Whether region or successor parameters are written as a spread, `(*xs : τ)`. -/
def isSpread (p : TSyntax `Strata.Mantle.DSL.mantleParams) : Bool := !p.raw[1].getArgs.isEmpty

/-- Resolve an instruction's binders and return type. -/
def resolveOp (rc : ResolveCtx) (known : Std.HashMap Name Known) (d : OpD) :
    CheckM (Option ROp) := do
  let ctx := d.c.ctx
  let vars := d.typeParams.map fun (x, _, k) => (x, k)
  let errsBefore ← get
  set false
  let mut seen ← checkDistinct #[] (d.typeParams.map fun (x, r, _) => (x, r))
  let mut args := #[]
  let mut variadic : Option (String × Ty) := none
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
      -- Its kind, by `TypeExpr.Raw.kind`, makes the variadic a spread of a list or `each` of a type.
      let ty? ← resolveExpr rc ctx known vars t
      if let some ty := ty? then
        if variadic.isNone then
          variadic := some ((xs[0]?.map (·.getId.toString (escape := false))).getD "", ty)
    | `(mantleBinder| ( $[& $rs:ident]* $ps:mantleParams* : $t )) =>
      seen ← checkDistinct seen (rs.map fun x => (x.getId.toString (escape := false), x.raw))
      let mut params := #[]
      let mut pseen := #[]
      for p in ps do
        if isSpread p then
          err p "a region parameter cannot be a spread `(*xs : τ)`: each is one value"
          continue
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
        | `(mantleParams| ( * $xs:ident* : $pt )) =>
          -- A spread passes one value per element of its list.
          if h : 1 < xs.size then err xs[1] "a spread binds one name"
          pseen ← checkDistinct pseen
            ((xs.extract 0 1).map fun x => (x.getId.toString (escape := false), x.raw))
          if let some ty ← resolveExpr rc ctx known vars pt then
            if ty.kind (vars.map (·.2)) == .list then payload := payload.push ty
            else err pt "a spread `(*xs : τ)` in a successor's payload takes a list of types: \
              one value per element"
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
  let ret : Option (Option Ty) ← match d.ret with
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
    (pol : Array (String × Syntax × Bool × Kind)) (ref : Syntax) (t : Ty)
    (under : Option (Name × Nat)) :
    CheckM Unit := do
  match t with
  | .var l =>
    if let (some (h, i), some (x, _, true, _)) := (under, pol[l]?) then
      err ref s!"positive parameter `{x}` occurs under non-positive parameter {i} of \
        `{showName h}`"
  | .app h args =>
    let h := leanName h
    if let some (g, i) := under then
      if members.contains h then
        err ref s!"`{showName h}` recurses through non-positive parameter {i} of `{showName g}`"
        return
    let ps := match known[h]? with
      | some (.type info _) => info.params.map fun (p : String × Bool × Kind) => p.2.1
      | _ => #[]
    for h' : j in [0:args.size] do
      let a := args[j]
      let under' := match under with
        | some u => some u
        | none => if ps[j]?.getD true then none else some (h, j + 1)
      checkPositive known members pol ref a under'
  -- A literal is in its position's polarity, and so is each element.
  | .list es =>
    for e in es do checkPositive known members pol ref e under

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
      terminal := true, typeParams := d.params.map (fun (x, r, _, k) => (x, r, k)),
      binders := #[],
      ret := none }
  let self : Ty := .app (mantleName d.c.envName) (TypeExpr.Raw.vars (d.params.map (·.2.2.2)))
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
      let full := match stages.back? with
        | some (.types ds) => ds.size ≥ stageMax
        | _ => true
      if run != 1 || full then
        stages := stages.push (.types #[])
        run := 1
      let k := stages.size
      let some (.types ds) := stages.back? | unreachable!
      discard <| checkDistinct #[] (d.params.map fun (x, r, _) => (x, r))
      let info : TypeInfo :=
        { envName := d.c.envName, owner := rc.envNs, lean := d.c.lean,
          params := d.params.map fun (x, _, b, k) => (x, b, k) }
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
            params := d.params.map (fun (x, _, b, k) => (x, b, k)), ctors }
        own := own.insert d.c.envName (info, k, j)
        known := known.insert d.c.envName (.type info (some (k, j)))
      let members := ds.map (·.c.envName)
      let mut out := #[]
      for d in ds do
        let vars := d.params.map fun (x, _, _, k) => (x, k)
        let mut rcs := #[]
        for c in d.ctors.getD #[] do
          -- A constructor's instruction binds the datatype's parameters and then its fields,
          -- so a field may not reuse a parameter's name.
          let (args, _) ← resolveArgBinders rc c.c.ctx known vars (vars.map (·.1)) c.binders
          -- Positivity, at each payload's type syntax.
          for (_, r, ref) in args do
            checkPositive known members d.params ref r none
          rcs := rcs.push { d := c, args := args.map fun (x, r, _) => (x, r) }
        -- The member's case instruction, which the group's `addData` declares.
        if let some r ← caseOp d rcs then out := out.push (d, rcs, r)
      stages := stages.push (.data out)
    | .abbrev d =>
      let vars := d.params.map fun (x, _, k) => (x, k)
      discard <| checkDistinct #[] (d.params.map fun (x, r, _) => (x, r))
      if let some body ← resolveTy rc d.c.ctx known vars d.body then
        let info : AbbrevInfo :=
          { envName := d.c.envName, owner := rc.envNs, lean := d.c.lean,
            params := d.params.map (·.2.2), body }
        abbrevs := abbrevs.push (d, info)
        known := known.insert d.c.envName (.abbrev info)
    | .op d =>
      let full := match stages.back? with
        | some (.ops rs) => rs.size ≥ stageMax
        | _ => true
      if run != 2 || full then
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
