/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public import StrataMantle.DSL.Check

/-!
# The `environment` command: emitting

The third pass.  Once checking has passed, the elaborator writes ordinary commands with
syntax quotations and elaborates them: the stages that build `E.env`, `E.env` itself, the
parent rule, and the references.  The generated code calls `Mantle/Env.lean`'s public API as
hand-written code does, so the kernel checks everything the elaborator emits.

The stages are `private`, in `E.Internal`.  The interface is written against a generic
refinement `e` from public pieces only, so nothing downstream reduces through a stage: `o.sig`
from the types' `ty`, and `o` as the stage's reference cast to it by `InsnRef.cast`.  A
constructor `T.c` is an instruction the same way: `T.c.sig` is written out, and `T.c` is the
reference `InsnRef.ofAddData` gives, cast to it.  A datatype's case instruction `T.case` is one
too: `addData` declares it with the group, and `T.case` is the reference
`InsnRef.ofAddDataCase` gives, cast to `T.case.sig`.

Quotations are unhygienic, because the generated names are the user's interface.  References
to the API, to an ancestor and to the environment's own declarations are written from
`_root_`, so no name in the user's scope can capture them.  The one hygienic binder is the
interface's `RefinedBy` instance, which no caller names (see `EmitCtx.hId`).
-/

public meta section

namespace Strata.Mantle.DSL

open Lean Elab Command

set_option hygiene false

/-! ## Terms -/

/-- An identifier for the global constant `n`, immune to the user's namespaces. -/
def rootId (n : Name) : Ident := mkIdent (`_root_ ++ n)

/-- The fixed lemmas of an instruction's `InsnRef.cast` proof. -/
def insnCastLemmas : Array Ident := #[
  `Strata.Mantle.InsnSig.ofSubset, `Strata.Mantle.InsnSig.mk.injEq,
  `Strata.Mantle.TypeExpr.ofSubset_app, `Strata.Mantle.TypeExpr.ofSubset_var,
  `Strata.Mantle.TypeExpr.app_eq_app_iff, `Strata.Mantle.TypeRef.ofSubset_ofSubset,
  `Strata.Mantle.name_TypeRef_ofSubset, `Strata.Mantle.RegionSig.ofSubset_of,
  `Strata.Mantle.RegionSig.of_eq_of_iff, `Strata.Mantle.Param.mk.injEq, `Vector.map_mk,
  `Vector.mk.injEq, `List.map_toArray, `List.map_cons, `List.map_nil, `Array.mk.injEq,
  `List.cons.injEq, `Option.map_none, `Option.map_some, `Option.some.injEq, `heq_eq_eq,
  `and_self, `and_true, `true_and].map rootId

/-- A `Strata.Mantle.Name` literal for an environment name. -/
partial def nameLit : Name → Term
  | .anonymous => Unhygienic.run `(Strata.Mantle.Name.base)
  | .str p s => Unhygienic.run `(Strata.Mantle.Name.str $(nameLit p) $(quote s))
  | .num p i => Unhygienic.run `(Strata.Mantle.Name.num $(nameLit p) $(quote i))

/-- `name.str s`. -/
def sfx (n : Name) (s : String) : Name := Name.mkStr n s

/-- What emitting reads. -/
structure EmitCtx where
  /-- `Strata.Mantle.Base`. -/
  envNs : Name
  /-- `Base`, as written after `environment`. -/
  envShort : Name
  parent : Option EnvEntry
  vis? : Option (TSyntax ``Lean.Parser.Command.visibility)
  /-- Whether interface definitions are `@[expose]`. -/
  expose : Bool
  /-- How many stages; stage `m` is `env`. -/
  m : Nat
  /-- Every type this block declares: its stage and position. -/
  ownTypes : Std.HashMap Name (TypeInfo × Nat × Nat)
  /-- Every type an ancestor declares. -/
  inherited : Std.HashMap Name TypeInfo
  /-- Every name the ancestors declare, nearest first: the parent's `names`. -/
  parentNames : Array Name
  /-- Every name `env` declares, in `names` order. -/
  allNames : Array Name
  /-- The interface's instance binder, `[h : RefinedBy env e]`.  Instance search fills it and
  no caller names it, so it is hygienic: no user name captures it. -/
  hId : Ident

namespace EmitCtx

variable (cx : EmitCtx)

/-- One of this environment's constants, by its name relative to `E`. -/
def own (rel : Name) : Ident := rootId (cx.envNs ++ rel)

/-- One of the stages' constants, in `E.Internal`. -/
def internal (s : String) : Ident := cx.own (sfx `Internal s)

/-- The visibility of the stages: `private`, whatever the environment's. -/
def stageVis? : Option (TSyntax ``Lean.Parser.Command.visibility) :=
  some (Lean.Parser.Command.visibility.ofBool false)

/-- The environment at the end of stage `k`: the parent's (or the empty one) at `0`,
`env` at `m`. -/
def stage (k : Nat) : Term :=
  if k == 0 then
    match cx.parent with
    | some p => rootId (p.leanNs ++ `env)
    | none => Unhygienic.run `((Strata.Mantle.Env.empty : Strata.Mantle.Env _root_.Unit))
  else if k == cx.m then cx.own `env
  else cx.internal s!"s{k}"

/-- A list of `Strata.Mantle.Name` literals. -/
def litList (ns : Array Name) : Term :=
  Unhygienic.run `(([$(ns.map nameLit),*] : List Strata.Mantle.Name))

/-- Every name stage `k` declares, as a list: the parent's and `env`'s as literals, which
`mem_env` states. -/
def stageList (k : Nat) : Term :=
  if k == 0 then
    match cx.parent with
    | some _ => litList cx.parentNames
    | none => cx.internal "list0"
  else if k == cx.m then litList cx.allNames
  else cx.internal s!"list{k}"

/-- `n ∈ stage k ↔ n ∈ stageList k`. -/
def stageMem (k : Nat) : Ident :=
  if k == 0 then
    match cx.parent with
    | some p => rootId (p.leanNs ++ `mem_env)
    | none => cx.internal "mem0"
  else if k == cx.m then cx.own `mem_env
  else cx.internal s!"mem{k}"

/-- A proof of `stage j ⊆ stage i`, for `j < i`. -/
def chain (j i : Nat) : Term := Id.run do
  let mut t : Term := cx.internal s!"hst{i}"
  for k' in [0:i - j - 1] do
    let k := i - 1 - k'
    t := Unhygienic.run `(Strata.Mantle.Env.Prefix.trans $(cx.internal s!"hst{k}") $t)
  return t

/-- A reference to type `h` in stage `j`. -/
def refAt (h : Name) (j : Nat) : Term :=
  match cx.ownTypes[h]? with
  | some (info, t, _) =>
    let r : Term := cx.own (`Internal ++ info.lean ++ `ref₀)
    if t == j then r
    else Unhygienic.run `(Strata.Mantle.TypeRef.ofSubset $(cx.chain t j) $r)
  | none =>
    match cx.inherited[h]? with
    | some info =>
      Unhygienic.run `(($(rootId (info.owner ++ info.lean ++ `ref)) (e := $(cx.stage j))))
    | none => Unhygienic.run `(sorry)

/-- A type, in stage `j`. -/
partial def tyAt (j : Nat) : RTy → Term
  | .var i => Unhygienic.run `(Strata.Mantle.TypeExpr.var $(quote i) (by decide))
  | .app h args =>
    let as : Array Term := args.map (tyAt j)
    -- At `stage j` itself, not the `addTypes` expression an own `ref₀` is typed against,
    -- so that `simp` matches `TypeExpr.ofSubset_app` on it.
    Unhygienic.run
      `(Strata.Mantle.TypeExpr.app (env := $(cx.stage j)) $(cx.refAt h j) #v[$as,*])

/-- A type, over a generic `e`, with the variables named `vars`. -/
partial def tyGen (vars : Array Term) : RTy → Term
  | .var i => vars[i]?.getD (Unhygienic.run `(sorry))
  | .app h args =>
    let as : Array Term := args.map (tyGen vars)
    let info := match cx.ownTypes[h]? with
      | some (info, _, _) => info
      | none => cx.inherited[h]?.getD default
    Unhygienic.run `($(rootId (info.owner ++ info.lean ++ `ty)) $as*)

/-- A payload of the group added at stage `k`, whose members are `members`.  Every other type
is read through `refs`, the stage's literal references (`payRefs`). -/
partial def dataTy (k : Nat) (members : Array Name) (refs : Std.HashMap Name Term) :
    RTy → Term
  | .var l => Unhygienic.run `(Strata.Mantle.DataTy.var $(quote l))
  | .app h args =>
    let as : Array Term := args.map (dataTy k members refs)
    match members.idxOf? h with
    | some j =>
      Unhygienic.run `(Strata.Mantle.DataTy.ref
        (Strata.Mantle.TypeRef.ofAddTypes $(cx.stage (k - 1)) $(cx.internal s!"hdr{k}")
          $(cx.internal s!"fresh{k}") $(quote j)) #[$as,*])
    | none =>
      Unhygienic.run `(Strata.Mantle.DataTy.ext $(refs[h]?.getD (cx.refAt h (k - 1))) #[$as,*])

/-- The `TypeInfo` of a type this block or an ancestor declares. -/
def info (h : Name) : TypeInfo :=
  match cx.ownTypes[h]? with
  | some (i, _, _) => i
  | none => cx.inherited[h]?.getD default

/-- A constant of the environment declaring `h`, by its name relative to that
environment. -/
def ownOrInherited (h : Name) (rel : Name) : Ident :=
  if cx.ownTypes.contains h then cx.own rel else rootId ((cx.info h).owner ++ rel)

/-- A proof of `stage t ⊆ e`, under `[h : env ⊑ e]`. -/
def liftTo (t : Nat) : Term :=
  if t == cx.m then Unhygienic.run `(Strata.Mantle.RefinedBy.subset (self := $(cx.hId)))
  else Unhygienic.run `(Strata.Mantle.Env.Prefix.trans $(cx.internal s!"hsub{t}")
    (Strata.Mantle.RefinedBy.subset (self := $(cx.hId))))

end EmitCtx

/-! ## Commands -/

/-- The heads of `t` that are not in `members`, added to `acc` in order. -/
partial def collectHeads (members : Array Name) (t : RTy) (acc : Array Name) : Array Name :=
  match t with
  | .var _ => acc
  | .app h args =>
    let acc := if members.contains h || acc.contains h then acc else acc.push h
    args.foldl (fun acc a => collectHeads members a acc) acc

/-- A return type as a term: `some τ`, or `none` for a terminal instruction. -/
def retTerm (ty : RTy → Term) : Option RTy → CommandElabM Term
  | some t => `(some $(ty t))
  | none => `(none)

/-- `def`, with the given modifiers. -/
def defCmd (doc : TSyntax ``Lean.Parser.Command.docComment)
    (vis? : Option (TSyntax ``Lean.Parser.Command.visibility)) (expose : Bool) (id : Ident)
    (bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty val : Term) :
    CommandElabM Command :=
  if expose then
    `($doc:docComment @[expose] $[$vis?:visibility]? def $id:ident $bs* : $ty := $val)
  else
    `($doc:docComment $[$vis?:visibility]? def $id:ident $bs* : $ty := $val)

/-- `abbrev`, for a name constant: reducible, so a lemma about it keys as its value does. -/
def abbrevCmd (doc : TSyntax ``Lean.Parser.Command.docComment)
    (vis? : Option (TSyntax ``Lean.Parser.Command.visibility)) (id : Ident) (ty val : Term) :
    CommandElabM Command :=
  `($doc:docComment $[$vis?:visibility]? abbrev $id:ident : $ty := $val)

/-- `theorem`, with the given modifiers. -/
def thmCmd (doc : TSyntax ``Lean.Parser.Command.docComment)
    (vis? : Option (TSyntax ``Lean.Parser.Command.visibility)) (simp : Bool) (id : Ident)
    (bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) (ty val : Term) :
    CommandElabM Command :=
  if simp then
    `($doc:docComment @[simp] $[$vis?:visibility]? theorem $id:ident $bs* : $ty := $val)
  else
    `($doc:docComment $[$vis?:visibility]? theorem $id:ident $bs* : $ty := $val)

/-- The docstring of a declaration: the user's, or a fixed one. -/
def docOr (doc? : Option (TSyntax ``Lean.Parser.Command.docComment)) (s : String) :
    TSyntax ``Lean.Parser.Command.docComment :=
  doc?.getD (mkDoc s)

/-- The names a stage declares, in order. -/
def stageNames : Stage → Array Name
  | .types ds => ds.map (·.c.envName)
  | .data ms =>
    ms.map (·.1.c.envName) ++ ms.flatMap (fun (_, cs, _) => cs.map (·.d.c.envName)) ++
      ms.map (·.2.2.d.c.envName)
  | .ops ds => ds.map (·.d.c.envName)

/-- The Lean name, relative to `E`, of the `Name` constant for each environment name. -/
def nameConsts (stages : Array Stage) : Std.HashMap Name Name := Id.run do
  let mut m := {}
  for s in stages do
    match s with
    | .types ds => for d in ds do m := m.insert d.c.envName (d.c.lean ++ `name)
    | .data ms =>
      for (d, cs, o) in ms do
        m := m.insert d.c.envName (d.c.lean ++ `name)
        for c in cs do m := m.insert c.d.c.envName (c.d.c.lean ++ `name)
        m := m.insert o.d.c.envName (o.d.c.lean ++ `name)
    | .ops ds => for d in ds do m := m.insert d.d.c.envName (d.d.c.lean ++ `name)
  return m

/-- Positivity, as a term. -/
def polTerm (b : Bool) : Term :=
  if b then Unhygienic.run `(Strata.Mantle.Positivity.pos)
  else Unhygienic.run `(Strata.Mantle.Positivity.non)

/-- A `TypeDecl` literal, from each parameter's name and whether it is positive. -/
def typeDeclTerm (nameId : Ident) (params : Array (String × Bool)) : CommandElabM Term := do
  let ps ← params.mapM fun (x, b) => `(⟨$(quote x), $(polTerm b)⟩)
  `(({ ann := (), name := $nameId, params := #[$ps,*] } :
      Strata.Mantle.TypeDecl _root_.Unit))

/-- `n` primed with `Name.appendAfter` until it is not in `avoid`, as `GuessLex` freshens a
measure's names: `n'`, then `n''`, and so on.  Core's `LocalContext.getUnusedName` suffixes
`_1` and searches a local context, and `mkFreshUserName` adds macro scopes; this keeps the
primes users see.  One of the `avoid.size + 1` candidates is free, so the search stops. -/
def primeAvoiding (avoid : Array Name) (n : Name) : Name := Id.run do
  let mut c := n.appendAfter "'"
  for _ in [0:avoid.size] do
    if !avoid.contains c then return c
    c := c.appendAfter "'"
  return c

/-- Every command the block generates. -/
def emitCommands (cx : EmitCtx) (stages : Array Stage) (abbrevs : Array (AbbrevD × AbbrevInfo))
    (envDoc? : Option (TSyntax ``Lean.Parser.Command.docComment)) :
    CommandElabM (Array Command) := do
  let vis? := cx.vis?
  let svis? := EmitCtx.stageVis?
  let consts := nameConsts stages
  let nameId (n : Name) : Ident := cx.own (consts[n]?.getD `missing)
  let mut cs : Array Command := #[]
  let envStr := showName cx.envShort
  -- Names.
  for s in stages do
    match s with
    | .types ds =>
      for d in ds do
        cs := cs.push (← abbrevCmd (mkDoc s!"The name `{showName d.c.envName}`.") vis?
          (mkIdent (d.c.lean ++ `name)) (← `(Strata.Mantle.Name)) (nameLit d.c.envName))
    | .data ms =>
      for (d, ctors, _) in ms do
        cs := cs.push (← abbrevCmd (mkDoc s!"The name `{showName d.c.envName}`.") vis?
          (mkIdent (d.c.lean ++ `name)) (← `(Strata.Mantle.Name)) (nameLit d.c.envName))
        for c in ctors do
          cs := cs.push (← abbrevCmd (mkDoc s!"The name `{showName c.d.c.envName}`.") vis?
            (mkIdent (c.d.c.lean ++ `name)) (← `(Strata.Mantle.Name)) (nameLit c.d.c.envName))
      for (_, _, d) in ms do
        cs := cs.push (← abbrevCmd (mkDoc s!"The name `{showName d.d.c.envName}`.") vis?
          (mkIdent (d.d.c.lean ++ `name)) (← `(Strata.Mantle.Name)) (nameLit d.d.c.envName))
    | .ops ds =>
      for d in ds do
        cs := cs.push (← abbrevCmd (mkDoc s!"The name `{showName d.d.c.envName}`.") vis?
          (mkIdent (d.d.c.lean ++ `name)) (← `(Strata.Mantle.Name)) (nameLit d.d.c.envName))
  -- `names`: every name, latest stage first, then the parent's.
  let lits : Array Term := (stages.reverse.flatMap stageNames).map fun n => (nameId n : Term)
  let namesVal ← match cx.parent with
    | some p => `([$lits,*] ++ $(rootId (p.leanNs ++ `names)))
    | none => `([$lits,*])
  cs := cs.push (← defCmd (mkDoc s!"Every name `{envStr}.env` declares.") vis? cx.expose
    (mkIdent `names) #[] (← `(List Strata.Mantle.Name)) namesVal)
  if cx.parent.isNone then
    cs := cs.push (← defCmd (mkDoc "The names the empty environment declares.") svis? false
      (mkIdent `Internal.list0) #[] (← `(List Strata.Mantle.Name)) (← `([])))
    cs := cs.push (← thmCmd (mkDoc "The empty environment declares no name.") svis? false
      (mkIdent `Internal.mem0) #[← `(bracketedBinder| {n : Strata.Mantle.Name})]
      (← `(n ∈ (Strata.Mantle.Env.empty : Strata.Mantle.Env _root_.Unit) ↔
        n ∈ $(cx.internal "list0")))
      (← `(by simp [$(cx.internal "list0"):ident])))
  -- The stages.  `payRefIds` keeps each data stage's payload references, which the
  -- constructors' casts unfold.
  let mut payRefIds : Std.HashMap Nat (Array Ident) := {}
  let nBinder ← `(bracketedBinder| {n : Strata.Mantle.Name})
  for h : i in [0:stages.size] do
    let k := i + 1
    let prev := cx.stage (k - 1)
    let prevList := cx.stageList (k - 1)
    let prevMem := cx.stageMem (k - 1)
    let stageId := cx.stage k
    let isLast := k == cx.m
    let I (s : String) : Ident := mkIdent (sfx `Internal s!"{s}{k}")
    let R (s : String) : Ident := cx.internal s!"{s}{k}"
    -- The list `names` or `Internal.list{k}` unfolds to.
    let mut listParts : Array Term := #[]
    match stages[i] with
    | .types ds =>
      let decls ← ds.mapM fun d =>
        typeDeclTerm (nameId d.c.envName) (d.params.map fun (x, _, b) => (x, b))
      let ns : Array Term := ds.map fun d => nameId d.c.envName
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}: types.") svis? false (I "types") #[]
        (← `(Array (Strata.Mantle.TypeDecl _root_.Unit))) (← `(#[$decls,*])))
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}'s names.") svis? false (I "names") #[]
        (← `(Array Strata.Mantle.Name)) (← `(#[$ns,*])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s names, as a literal.") svis? false
        (I "names_eq") #[] (← `(($(R "types")).map (·.name) = $(R "names")))
        (← `(by simp [$(R "types"):ident, $(R "names"):ident])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s types may be added.") svis? false
        (I "fresh") #[] (← `(Strata.Mantle.Env.FreshTypes $prev $(R "types")))
        (← `(⟨Strata.Mantle.Env.FreshNames.of_list $prevList $(prevMem).mp
              (by rw [$(R "names_eq"):ident]; decide), by decide⟩)))
      let val ← `(Strata.Mantle.Env.addTypes $prev $(R "types") $(R "fresh"))
      if isLast then
        cs := cs.push (← defCmd (docOr envDoc? s!"The environment `{envStr}`.") vis? false
          (mkIdent `env) #[] (← `(Strata.Mantle.Env _root_.Unit)) val)
      else
        cs := cs.push (← defCmd (mkDoc s!"Stage {k}.") svis? false (I "s") #[]
          (← `(Strata.Mantle.Env _root_.Unit)) val)
      listParts := #[← `(($(R "names")).toList)]
    | .data ms =>
      let members := ms.map (·.1.c.envName)
      let hdr ← ms.mapM fun (d, _) =>
        typeDeclTerm (nameId d.c.envName) (d.params.map fun (x, _, b) => (x, b))
      let hns : Array Term := ms.map fun (d, _) => nameId d.c.envName
      -- The constructors' names, then the case instructions'.
      let cns : Array Term :=
        ms.flatMap (fun (_, ctors, _) => ctors.map fun c => (nameId c.d.c.envName : Term))
          ++ ms.map fun (_, _, d) => (nameId d.d.c.envName : Term)
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}: the group's members, as types.") svis? false
        (I "hdr") #[] (← `(Array (Strata.Mantle.TypeDecl _root_.Unit))) (← `(#[$hdr,*])))
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}'s member names.") svis? false (I "hdrNames")
        #[] (← `(Array Strata.Mantle.Name)) (← `(#[$hns,*])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s member names, as a literal.") svis? false
        (I "hdrNames_eq") #[] (← `(($(R "hdr")).map (·.name) = $(R "hdrNames")))
        (← `(by simp [$(R "hdr"):ident, $(R "hdrNames"):ident])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s members may be added as types.") svis?
        false (I "fresh") #[] (← `(Strata.Mantle.Env.FreshTypes $prev $(R "hdr")))
        (← `(⟨Strata.Mantle.Env.FreshNames.of_list $prevList $(prevMem).mp
              (by rw [$(R "hdrNames_eq"):ident]; decide), by decide⟩)))
      let t ← `(Strata.Mantle.Env.addTypes $prev $(R "hdr") $(R "fresh"))
      -- The payloads' other types, as references built from literals.  `admissible`'s
      -- `decide` reads each one's parameters, and cannot unfold `TypeRef.ofSubset` or an
      -- ancestor's unexposed `T.ref`.
      let mut heads : Array Name := #[]
      for (_, ctors, _) in ms do
        for c in ctors do
          for (_, ty) in c.args do heads := collectHeads members ty heads
      let mut refs : Std.HashMap Name Term := {}
      let mut rids : Array Ident := #[]
      for h : hi in [0:heads.size] do
        let hd := heads[hi]
        let inf := cx.info hd
        let rid := mkIdent (sfx `Internal s!"payRef{k}_{hi}")
        let nm := cx.ownOrInherited hd (inf.lean ++ `name)
        let decl ← typeDeclTerm nm inf.params
        let lemmas : Array Ident :=
          if cx.ownTypes.contains hd then #[]
          else #[cx.ownOrInherited hd (inf.lean ++ `name_ref),
            cx.ownOrInherited hd (inf.lean ++ `decl_ref)]
        cs := cs.push (← defCmd (mkDoc s!"`{showName hd}` in stage {k - 1}, from literals.")
          svis? false rid #[] (← `(Strata.Mantle.TypeRef $prev $(quote inf.params.size)))
          (← `(⟨$nm, $decl, rfl, by
                have r := ($(cx.refAt hd (k - 1))).resolves
                try simp only [Strata.Mantle.name_TypeRef_ofSubset,
                  Strata.Mantle.decl_TypeRef_ofSubset, $[$lemmas:ident],*] at r
                exact r⟩)))
        refs := refs.insert hd (cx.own rid.getId)
        rids := rids.push (cx.own rid.getId)
      payRefIds := payRefIds.insert k rids
      let mut groups : Array Term := #[]
      for (_, ctors, _) in ms do
        let mut cts : Array Term := #[]
        for c in ctors do
          let args ← c.args.mapM fun (x, ty) =>
            `(⟨$(quote x), $(cx.dataTy k members refs ty)⟩)
          cts := cts.push
            (← `({ ann := (), name := $(nameId c.d.c.envName), args := #[$args,*] }))
        groups := groups.push (← `(#[$cts,*]))
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}: the constructors.") svis? false (I "ctors")
        #[] (← `(Array (Array (Strata.Mantle.Ctor _root_.Unit (Strata.Mantle.DataTy $prev $t)))))
        (← `(#[$groups,*])))
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}'s constructor names.") svis? false
        (I "cnames") #[] (← `(Array Strata.Mantle.Name)) (← `(#[$cns,*])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s constructor and case names, as a literal.")
        svis? false (I "cnames_eq") #[]
        (← `(Strata.Mantle.Env.ctorNames $(R "ctors") ++ Strata.Mantle.Env.caseNames $(R "hdr") =
              $(R "cnames")))
        (← `(by simp [$(R "ctors"):ident, $(R "hdr"):ident, $(R "cnames"):ident,
              Strata.Mantle.Env.caseNames, Strata.Mantle.Name.caseName])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s constructor and case names are fresh.")
        svis? false (I "cfresh") #[]
        (← `(Strata.Mantle.Env.FreshNames $t (Strata.Mantle.Env.ctorNames $(R "ctors") ++
              Strata.Mantle.Env.caseNames $(R "hdr"))))
        (← `(Strata.Mantle.Env.FreshNames.of_list (($(R "hdrNames")).toList ++ $prevList)
              (fun hn => by
                rw [Strata.Mantle.Env.mem_addTypes, $(R "hdrNames_eq"):ident,
                  $prevMem:ident] at hn
                exact List.mem_append.mpr (hn.imp Array.mem_toList_iff.mpr id))
              (by rw [$(R "cnames_eq"):ident]; decide))))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s constructors make a datatype group.") svis?
        false (I "adm") #[]
        (← `(Strata.Mantle.Env.admissible $(R "hdr") $(R "ctors") = true)) (← `(by decide)))
      let val ← `(Strata.Mantle.Env.addData $prev $(R "hdr") $(R "fresh") $(R "ctors")
        $(R "cfresh") $(R "adm"))
      if isLast then
        cs := cs.push (← defCmd (docOr envDoc? s!"The environment `{envStr}`.") vis? false
          (mkIdent `env) #[] (← `(Strata.Mantle.Env _root_.Unit)) val)
      else
        cs := cs.push (← defCmd (mkDoc s!"Stage {k}.") svis? false (I "s") #[]
          (← `(Strata.Mantle.Env _root_.Unit)) val)
      listParts := #[← `(($(R "hdrNames")).toList), ← `(($(R "cnames")).toList)]
    | .ops ds =>
      let mut pairs : Array Term := #[]
      for d in ds do
        let sig0 := mkIdent (`Internal ++ d.d.c.lean ++ `sig₀)
        let tps : Array Term := d.d.typeParams.map fun (x, _) => quote x
        let args ← d.args.mapM fun (x, ty) => `(⟨$(quote x), $(cx.tyAt (k - 1) ty)⟩)
        let variadic ← match d.variadic with
          | some (x, ty) => `(some ⟨$(quote x), $(cx.tyAt (k - 1) ty)⟩)
          | none => `(none)
        let regs ← d.regions.mapM fun r => do
          let ps ← r.params.mapM fun (x, ty) => `(⟨$(quote x), $(cx.tyAt (k - 1) ty)⟩)
          `(⟨$(quote r.name), Strata.Mantle.RegionSig.of #[$ps,*] $(cx.tyAt (k - 1) r.ret)⟩)
        let succs ← d.succs.mapM fun sc => do
          let ts := sc.payload.map (cx.tyAt (k - 1))
          `(⟨$(quote sc.name), #[$ts,*]⟩)
        cs := cs.push (← defCmd (mkDoc s!"The signature of `{showName d.d.c.envName}`, in \
            stage {k - 1}.") svis? false sig0 #[]
          (← `(Strata.Mantle.InsnSig $prev))
          (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
                 variadic := $variadic, returnType := $(← retTerm (cx.tyAt (k - 1)) d.ret),
                 regions := #[$regs,*], succs := #[$succs,*] })))
        pairs := pairs.push (← `(($(nameId d.d.c.envName), $(cx.own sig0.getId))))
      let ns : Array Term := ds.map fun d => nameId d.d.c.envName
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}: instructions.") svis? false (I "ops") #[]
        (← `(Array (Strata.Mantle.Name × Strata.Mantle.InsnSig $prev))) (← `(#[$pairs,*])))
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}'s names.") svis? false (I "names") #[]
        (← `(Array Strata.Mantle.Name)) (← `(#[$ns,*])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s names, as a literal.") svis? false
        (I "names_eq") #[] (← `(($(R "ops")).map (·.1) = $(R "names")))
        -- By the kernel, over lists: `simp` recurses once per element, and the kernel cannot
        -- reduce `Array.map`.
        (← `(by apply Array.toList_inj.mp; rw [Array.toList_map]; decide +kernel)))
      -- Each reference's bound `j < ops.size` follows from this one.  `decide` on `ops.size`
      -- itself unfolds the array, recursing once per element, for every reference.
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s size.") svis? false (I "ops_size") #[]
        (← `(($(R "ops")).size = $(quote ds.size))) (← `(by decide +kernel)))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s names are fresh.") svis? false
        (I "fresh") #[] (← `(Strata.Mantle.Env.FreshNames $prev (($(R "ops")).map (·.1))))
        -- `+kernel`: the check is quadratic in the batch, and elaborator evaluation is slow.
        (← `(Strata.Mantle.Env.FreshNames.of_list $prevList $(prevMem).mp
              (by rw [$(R "names_eq"):ident]; decide +kernel))))
      let val ← `(Strata.Mantle.Env.addInsns $prev $(R "ops") $(R "fresh"))
      if isLast then
        cs := cs.push (← defCmd (docOr envDoc? s!"The environment `{envStr}`.") vis? false
          (mkIdent `env) #[] (← `(Strata.Mantle.Env _root_.Unit)) val)
      else
        cs := cs.push (← defCmd (mkDoc s!"Stage {k}.") svis? false (I "s") #[]
          (← `(Strata.Mantle.Env _root_.Unit)) val)
      listParts := #[← `(($(R "names")).toList)]
    -- Membership: `n ∈ stage k ↔ n ∈ stageList k`.
    let listVal ← listParts.foldrM (fun p acc => `($p ++ $acc)) prevList
    let memLemma ← match stages[i] with
      | .types _ => `(Strata.Mantle.Env.mem_addTypes)
      | .ops _ => `(Strata.Mantle.Env.mem_addInsns)
      | .data .. => `(Strata.Mantle.Env.mem_addData)
    let eqs : Array Ident := match stages[i] with
      | .data .. => #[R "hdrNames_eq", R "cnames_eq"]
      | _ => #[R "names_eq"]
    let memProof ← if isLast then
        -- Neither `simp` nor the unifier may meet the literal: each recurses once per element.
        -- `simp` proves membership in `listVal`, whose parts are constants, and `decide +kernel`
        -- that `listVal` is the literal, which unifies with the statement's syntactically.
        `(Iff.trans
            (by simp only [$stageId:term, $memLemma:term, $[$eqs:ident],*, $prevMem:ident,
              List.mem_append, Array.mem_toList_iff, or_assoc])
            (Iff.of_eq (congrArg (fun l => $(mkIdent `n) ∈ l)
              (by decide +kernel : $listVal = $(cx.stageList k)))))
      else do
        cs := cs.push (← defCmd (mkDoc s!"Every name stage {k} declares.") svis? false
          (I "list") #[] (← `(List Strata.Mantle.Name)) listVal)
        `(by
          simp only [$stageId:term, $memLemma:term, $[$eqs:ident],*, $prevMem:ident,
            $(R "list"):ident, List.mem_append, Array.mem_toList_iff, or_assoc])
    let memStmt ← `($(mkIdent `n) ∈ $stageId ↔ $(mkIdent `n) ∈ $(cx.stageList k))
    if isLast then
      cs := cs.push (← thmCmd (mkDoc s!"The names `{envStr}.env` declares, as literals, in \
          `names` order.") vis? true (mkIdent `mem_env) #[nBinder] memStmt memProof)
    else
      cs := cs.push (← thmCmd (mkDoc s!"Every name stage {k} declares.") svis? false (I "mem")
        #[nBinder] memStmt memProof)
    -- Order.
    let sub ← match stages[i] with
      | .types _ => `(Strata.Mantle.Env.subset_addTypes)
      | .data .. => `(Strata.Mantle.Env.subset_addData)
      | .ops _ => `(Strata.Mantle.Env.subset_addInsns)
    cs := cs.push (← thmCmd (mkDoc s!"Stage {k} extends stage {k - 1}.") svis? false (I "hst") #[]
      (← `($prev ⊆ $stageId)) sub)
    if let some p := cx.parent then
      if !isLast then
        let hp ← if k == 1 then pure (R "hst" : Term)
          else `(Strata.Mantle.Env.Prefix.trans $(cx.internal s!"hp{k - 1}") $(R "hst"))
        cs := cs.push (← thmCmd (mkDoc s!"Stage {k} extends the parent.") svis? false (I "hp")
          #[] (← `($(rootId (p.leanNs ++ `env)) ⊆ $stageId)) hp)
        cs := cs.push (← `(command| $[$svis?:visibility]? local instance :
          Strata.Mantle.RefinedBy $(rootId (p.leanNs ++ `env)) $stageId := ⟨$(R "hp")⟩))
    -- The types this stage declares, in this stage.
    match stages[i] with
    | .types ds =>
      for h : j in [0:ds.size] do
        let d := ds[j]
        cs := cs.push (← defCmd (mkDoc s!"`{showName d.c.envName}`, in stage {k}.") svis? false
          (mkIdent (`Internal ++ d.c.lean ++ `ref₀)) #[]
          (← `(Strata.Mantle.TypeRef $stageId $(quote d.params.size)))
          (← `(Strata.Mantle.TypeRef.ofAddTypes $prev $(R "types") $(R "fresh") $(quote j))))
    | .data ms =>
      for h : j in [0:ms.size] do
        let (d, ctors, _) := ms[j]
        cs := cs.push (← defCmd (mkDoc s!"`{showName d.c.envName}`, in stage {k}.") svis? false
          (mkIdent (`Internal ++ d.c.lean ++ `ref₀)) #[]
          (← `(Strata.Mantle.TypeRef $stageId $(quote d.params.size)))
          (← `(Strata.Mantle.TypeRef.ofAddData
                (Strata.Mantle.TypeRef.ofAddTypes $prev $(R "hdr") $(R "fresh") $(quote j)))))
        -- Each constructor's instruction, as `addData` declared it.
        for h : jc in [0:ctors.size] do
          let c := ctors[jc]
          cs := cs.push (← defCmd (mkDoc s!"`{showName c.d.c.envName}`, in stage {k}.") svis?
            false (mkIdent (`Internal ++ c.d.c.lean ++ `ref₀)) #[]
            (← `(Strata.Mantle.InsnRef $stageId
                  (Strata.Mantle.Env.ctorSig $(quote j) $(quote jc))))
            (← `(Strata.Mantle.InsnRef.ofAddData $(quote j) $(quote jc))))
      -- Each member's case instruction, as `addData` declared it.
      for h : j in [0:ms.size] do
        let (_, _, d) := ms[j]
        cs := cs.push (← defCmd (mkDoc s!"`{showName d.d.c.envName}`, in stage {k}.") svis?
          false (mkIdent (`Internal ++ d.d.c.lean ++ `ref₀)) #[]
          (← `(Strata.Mantle.InsnRef $stageId (Strata.Mantle.Env.caseSig $(quote j))))
          (← `(Strata.Mantle.InsnRef.ofAddDataCase $(quote j))))
    | .ops _ => pure ()
  -- Each stage, in `env`.
  let first := if cx.parent.isSome then 0 else 1
  for k' in [0:cx.m - first] do
    let k := cx.m - 1 - k'
    let pf ← if k + 1 == cx.m then pure (cx.internal s!"hst{cx.m}" : Term)
      else `(Strata.Mantle.Env.Prefix.trans $(cx.internal s!"hst{k + 1}") $(cx.internal s!"hsub{k + 1}"))
    cs := cs.push (← thmCmd (mkDoc s!"Stage {k} is a prefix of `env`.") svis? false
      (mkIdent (sfx `Internal s!"hsub{k}")) #[] (← `($(cx.stage k) ⊆ $(cx.own `env))) pf)
  -- The parent rule.
  if let some p := cx.parent then
    let pShort := p.leanNs.componentsRev.head?.getD `P
    let pEnv := rootId (p.leanNs ++ `env)
    let pf := cx.liftTo 0
    let doc := mkDoc s!"Whatever refines `{envStr}` refines its parent, `{showName pShort}`."
    let ruleId := mkIdent (Name.mkSimple ("to" ++ pShort.toString (escape := false)))
    cs := cs.push (← `(command| $doc:docComment $[$vis?:visibility]? instance $ruleId:ident
      {e : Strata.Mantle.Env _root_.Unit}
      [$(cx.hId) : Strata.Mantle.RefinedBy $(cx.own `env) e] :
      Strata.Mantle.RefinedBy $pEnv e := ⟨$pf⟩))
  -- References, in every refinement of `env`.  The interface binds three names of its own:
  -- the refinement `{e : Env Unit}` and, in `T.ty` and `n.ty`, the scope `{s : Nat}`, which
  -- are implicit and keep these stable names so callers can pin them (`(e := Demo.env)`); and
  -- the instance `[h : RefinedBy env e]`, which instance search fills, so it is hygienic
  -- (`cx.hId`).  `T.ty` and `n.ty` bind the type's parameters beside `e` and `s` under the
  -- user's names, so a parameter named `e` or `s` would capture one of them: it is renamed
  -- by `primeAvoiding`, away from `e`, `s`, every parameter and every earlier renaming
  -- (`type T (e) (e')` binds `e''` and `e'`).  Every other parameter keeps its name.
  cs := cs.push (← `(command| section))
  cs := cs.push (← `(command| variable {e : Strata.Mantle.Env _root_.Unit}
    [$(cx.hId) : Strata.Mantle.RefinedBy $(cx.own `env) e]))
  let sBinder ← `(bracketedBinder| {s : Nat})
  let paramBinders (xs : Array Ident) : CommandElabM (Array (TSyntax
      ``Lean.Parser.Term.bracketedBinder)) :=
    xs.mapM fun x => `(bracketedBinder| ($x : Strata.Mantle.TypeExpr e s))
  let varIdents (xs : Array String) : Array Ident := Id.run do
    let stable : Array Name := #[`e, `s]
    let mut avoid : Array Name := stable ++ xs.map Name.mkSimple
    let mut out := #[]
    for x in xs do
      let n := Name.mkSimple x
      let n' := if stable.contains n then primeAvoiding avoid n else n
      avoid := avoid.push n'
      out := out.push (mkIdent n')
    return out
  for h : i in [0:stages.size] do
    let k := i + 1
    let tys : Array TypeD := match stages[i] with
      | .types ds => ds
      | .data ms => ms.map (·.1)
      | .ops _ => #[]
    for d in tys do
      let en := showName d.c.envName
      let refId := mkIdent (d.c.lean ++ `ref)
      cs := cs.push (← defCmd (docOr d.c.doc? s!"The type `{en}`.") vis? false refId #[]
        (← `(Strata.Mantle.TypeRef e $(quote d.params.size)))
        (← `(Strata.Mantle.TypeRef.ofSubset $(cx.liftTo k)
              $(cx.own (`Internal ++ d.c.lean ++ `ref₀)))))
      cs := cs.push (← thmCmd (mkDoc s!"`{d.c.lean.toString (escape := false)}.ref` refers to \
          `{en}`.") vis? true (mkIdent (d.c.lean ++ `name_ref)) #[]
        (← `(($(cx.own (d.c.lean ++ `ref)) (e := e)).name = $(cx.own (d.c.lean ++ `name))))
        (← `(by rw [$(cx.own (d.c.lean ++ `ref)):ident, Strata.Mantle.name_TypeRef_ofSubset]
              <;> rfl)))
      cs := cs.push (← thmCmd (mkDoc s!"`{d.c.lean.toString (escape := false)}.ref`'s \
          declaration.") vis? true (mkIdent (d.c.lean ++ `decl_ref)) #[]
        (← `(($(cx.own (d.c.lean ++ `ref)) (e := e)).decl =
              $(← typeDeclTerm (cx.own (d.c.lean ++ `name))
                  (d.params.map fun (x, _, b) => (x, b)))))
        (← `(by rw [$(cx.own (d.c.lean ++ `ref)):ident, Strata.Mantle.decl_TypeRef_ofSubset]
              <;> rfl)))
      let xs := varIdents (d.params.map (·.1))
      let xts : Array Term := xs.map (fun x => (x : Term))
      cs := cs.push (← defCmd (mkDoc s!"`{en}`, as a type expression.") vis? cx.expose
        (mkIdent (d.c.lean ++ `ty)) (#[sBinder] ++ (← paramBinders xs))
        (← `(Strata.Mantle.TypeExpr e s))
        (← `(Strata.Mantle.TypeExpr.app $(cx.own (d.c.lean ++ `ref)) #v[$xts,*])))
  for (d, info) in abbrevs do
    let xs := varIdents (d.params.map (·.1))
    cs := cs.push (← defCmd (docOr d.c.doc? s!"The abbreviation `{showName d.c.envName}`.") vis?
      cx.expose (mkIdent (d.c.lean ++ `ty)) (#[sBinder] ++ (← paramBinders xs))
      (← `(Strata.Mantle.TypeExpr e s)) (cx.tyGen (xs.map fun x => (x : Term)) info.body))
  -- Constructors and case instructions, as instructions: the signature written out against
  -- `e`, and the stage's reference cast to it by `simp` over `InsnSig.ext_toRaw`.
  for h : i in [0:stages.size] do
    let k := i + 1
    let .data ms := stages[i] | continue
    -- The `addData` expression, not the stage constant, so that the derived signatures'
    -- lemmas match the types they are lifted through.
    let addDataTerm ← `(Strata.Mantle.Env.addData $(cx.stage (k - 1)) $(cx.internal s!"hdr{k}")
      $(cx.internal s!"fresh{k}") $(cx.internal s!"ctors{k}") $(cx.internal s!"cfresh{k}")
      $(cx.internal s!"adm{k}"))
    for (d, ctors, _) in ms do
      let n := d.params.size
      let vars ← (Array.range n).mapM fun l =>
        `(Strata.Mantle.TypeExpr.var $(quote l) (by decide))
      let ty := cx.tyGen vars
      let tps : Array Term := d.params.map fun (x, _, _) => quote x
      let retR : RTy := .app d.c.envName ((Array.range n).map RTy.var)
      for c in ctors do
        let en := showName c.d.c.envName
        let sigId := mkIdent (c.d.c.lean ++ `sig)
        let args ← c.args.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
        cs := cs.push (← defCmd (mkDoc s!"The signature of `{en}`, a constructor of \
            `{showName d.c.envName}`.") vis? cx.expose sigId #[]
          (← `(Strata.Mantle.InsnSig e))
          (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
                 returnType := some $(ty retR), distinct := by simp })))
        let mut heads : Array Name := #[]
        for (_, t) in c.args do heads := collectHeads #[] t heads
        heads := collectHeads #[] retR heads
        let lemmas : Array Ident := heads.flatMap fun hd =>
          let inf := cx.info hd
          #[cx.ownOrInherited hd (inf.lean ++ `ty), cx.ownOrInherited hd (inf.lean ++ `name_ref)]
        -- One splice, as for instructions below.
        let unfolds : Array Ident := #[cx.own sigId.getId, cx.internal s!"ctors{k}",
          cx.internal s!"hdr{k}"] ++ (payRefIds[k]?.getD #[]) ++ lemmas
        cs := cs.push (← defCmd (docOr c.d.c.doc? s!"The constructor `{en}` of \
            `{showName d.c.envName}`.") vis? false (mkIdent c.d.c.lean) #[]
          (← `(Strata.Mantle.InsnRef e $(cx.own sigId.getId)))
          (← `(Strata.Mantle.InsnRef.cast
                -- Two passes: the derived signature's lemmas first, before the group's
                -- literals are unfolded inside its arguments.
                (by apply Strata.Mantle.InsnSig.ext_toRaw <;>
                  (try simp only [Strata.Mantle.InsnSig.ofSubset, Array.map_map,
                    Function.comp_def, Strata.Mantle.TypeExpr.toRaw_ofSubset,
                    Strata.Mantle.Env.argTypes_ctorSig, Strata.Mantle.Env.returnType_ctorSig,
                    Option.map_map])
                  <;> simp [$[$unfolds:ident],*,
                    Strata.Mantle.InsnSig.ofSubset, Strata.Mantle.TypeExpr.Raw.vars,
                    Strata.Mantle.TypeDecl.arity, Function.comp_def])
                (Strata.Mantle.InsnRef.ofSubset (s := $addDataTerm)
                  $(cx.liftTo k) $(cx.own (`Internal ++ c.d.c.lean ++ `ref₀))))))
    for (md, _, d) in ms do
      let en := showName d.d.c.envName
      let sigId := mkIdent (d.d.c.lean ++ `sig)
      let vars ← (Array.range d.d.typeParams.size).mapM fun l =>
        `(Strata.Mantle.TypeExpr.var $(quote l) (by decide))
      let ty := cx.tyGen vars
      let tps : Array Term := d.d.typeParams.map fun (x, _) => quote x
      let args ← d.args.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
      let succs ← d.succs.mapM fun sc => do
        let ts := sc.payload.map ty
        `(⟨$(quote sc.name), #[$ts,*]⟩)
      cs := cs.push (← defCmd (mkDoc s!"The signature of `{en}`.") vis? cx.expose sigId #[]
        (← `(Strata.Mantle.InsnSig e))
        (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
               returnType := none, succs := #[$succs,*], distinct := by simp })))
      let mut heads : Array Name := #[]
      for (_, t) in d.args do heads := collectHeads #[] t heads
      for sc in d.succs do
        for t in sc.payload do heads := collectHeads #[] t heads
      let lemmas : Array Ident := heads.flatMap fun hd =>
        let inf := cx.info hd
        #[cx.ownOrInherited hd (inf.lean ++ `ty), cx.ownOrInherited hd (inf.lean ++ `name_ref)]
      let unfolds : Array Ident := #[cx.own sigId.getId, cx.internal s!"ctors{k}",
        cx.internal s!"hdr{k}"] ++ (payRefIds[k]?.getD #[]) ++ lemmas
      cs := cs.push (← defCmd (docOr d.d.c.doc? s!"Eliminate a `{showName md.c.envName}`: one \
          successor per constructor, in declaration order, each receiving its constructor's \
          fields.") vis? false (mkIdent d.d.c.lean) #[]
        (← `(Strata.Mantle.InsnRef e $(cx.own sigId.getId)))
        (← `(Strata.Mantle.InsnRef.cast
              (by apply Strata.Mantle.InsnSig.ext_toRaw <;>
                (try simp only [Strata.Mantle.InsnSig.ofSubset, Array.map_map,
                  Function.comp_def, Strata.Mantle.TypeExpr.toRaw_ofSubset,
                  Strata.Mantle.Env.argTypes_caseSig, Strata.Mantle.Env.returnType_caseSig,
                  Strata.Mantle.Env.succs_caseSig])
                <;> simp [$[$unfolds:ident],*,
                  Strata.Mantle.InsnSig.ofSubset, Strata.Mantle.TypeExpr.Raw.vars,
                  Strata.Mantle.TypeDecl.arity, Strata.Mantle.Name.lastString,
                  Function.comp_def])
              (Strata.Mantle.InsnRef.ofSubset (s := $addDataTerm)
                $(cx.liftTo k) $(cx.own (`Internal ++ d.d.c.lean ++ `ref₀))))))
  for h : i in [0:stages.size] do
    let k := i + 1
    let .ops ds := stages[i] | continue
    for h : j in [0:ds.size] do
      let d := ds[j]
      let en := showName d.d.c.envName
      let sigId := mkIdent (d.d.c.lean ++ `sig)
      -- The signature, written against `e` from public pieces: the types' `ty`, `var` and
      -- `RegionSig.of`.  `decide` refuses goals over the free `e`, so `simp` proves the
      -- distinctness obligations.
      let vars ← (Array.range d.d.typeParams.size).mapM fun l =>
        `(Strata.Mantle.TypeExpr.var $(quote l) (by decide))
      let ty := cx.tyGen vars
      let tps : Array Term := d.d.typeParams.map fun (x, _) => quote x
      let args ← d.args.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
      let variadic ← match d.variadic with
        | some (x, t) => `(some ⟨$(quote x), $(ty t)⟩)
        | none => `(none)
      let regs ← d.regions.mapM fun r => do
        let ps ← r.params.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
        `(⟨$(quote r.name), Strata.Mantle.RegionSig.of #[$ps,*] $(ty r.ret) (by simp)⟩)
      let succs ← d.succs.mapM fun sc => do
        let ts := sc.payload.map ty
        `(⟨$(quote sc.name), #[$ts,*]⟩)
      cs := cs.push (← defCmd (mkDoc s!"The signature of `{en}`.") vis? cx.expose sigId #[]
        (← `(Strata.Mantle.InsnSig e))
        (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
               variadic := $variadic, returnType := $(← retTerm ty d.ret), regions := #[$regs,*],
               succs := #[$succs,*], distinct := by simp })))
      -- `o` casts the stage's reference to `o.sig`.  `simp` unfolds both signatures to
      -- applications and compares them by name: an own type's `ref` unfolds, an ancestor's
      -- `name_ref` rewrites.
      let mut heads : Array Name := #[]
      for (_, t) in d.args do heads := collectHeads #[] t heads
      if let some (_, t) := d.variadic then heads := collectHeads #[] t heads
      if let some t := d.ret then heads := collectHeads #[] t heads
      for r in d.regions do
        for (_, t) in r.params do heads := collectHeads #[] t heads
        heads := collectHeads #[] r.ret heads
      for sc in d.succs do
        for t in sc.payload do heads := collectHeads #[] t heads
      -- One splice: an empty one between fixed entries, when the signature names no type,
      -- would leave an empty entry.
      let lemmas : Array Ident :=
        #[cx.own (`Internal ++ d.d.c.lean ++ `sig₀), cx.own sigId.getId] ++
        heads.flatMap (fun hd =>
          let inf := cx.info hd
          #[cx.ownOrInherited hd (inf.lean ++ `ty), cx.ownOrInherited hd
            (inf.lean ++ (if cx.ownTypes.contains hd then `ref else `name_ref))]) ++
        insnCastLemmas
      cs := cs.push (← defCmd (mkDoc s!"`{en}`, in stage {k}.") svis? false
        (mkIdent (`Internal ++ d.d.c.lean ++ `ref₀)) #[]
        (← `(Strata.Mantle.InsnRef $(cx.stage k)
              (Strata.Mantle.InsnSig.ofSubset $(cx.internal s!"hst{k}")
                $(cx.own (`Internal ++ d.d.c.lean ++ `sig₀)))))
        (← `(Strata.Mantle.InsnRef.ofAddInsns $(cx.internal s!"ops{k}")
              $(cx.internal s!"fresh{k}") $(quote j)
              (Nat.lt_of_lt_of_eq (by decide : ($(quote j) : Nat) < $(quote ds.size))
                $(cx.internal s!"ops_size{k}").symm))))
      cs := cs.push (← defCmd (docOr d.d.c.doc? s!"The instruction `{en}`.") vis? false
        (mkIdent d.d.c.lean) #[] (← `(Strata.Mantle.InsnRef e $(cx.own sigId.getId)))
        (← `(Strata.Mantle.InsnRef.cast
              (by simp only [$[$lemmas:ident],*])
              (Strata.Mantle.InsnRef.ofSubset $(cx.liftTo k)
                $(cx.own (`Internal ++ d.d.c.lean ++ `ref₀))))))
  cs := cs.push (← `(command| end))
  return cs

/-! ## The command -/

/-- Resolve `extends P` to the parent's record, and check that `P` is visible enough. -/
def resolveParent (envShort : Name) (p : Ident) (isPublic isModule : Bool) :
    CheckM (Option EnvEntry) := do
  let env ← getEnv
  let full? ← try
      some <$> resolveGlobalConstNoOverload (mkIdentFrom p (p.getId ++ `env))
    catch _ => pure none
  let pStr := showName p.getId
  let some full := full? | err p s!"unknown environment `{pStr}`"; return none
  let full := privateToUserName full
  let some e := findEntry? env full.getPrefix |
    err p s!"`{pStr}` is not declared with `environment`"; return none
  if isPublic && !e.isPublic then
    err p s!"public environment `{showName envShort}` cannot extend private environment \
      `{pStr}`"
    return none
  if isPublic && isModule && !(env.setExporting true).contains full then
    let mod := (env.getModuleIdxFor? full).bind (env.header.moduleNames[·]?)
    err p s!"`{pStr}` is imported privately; use `public import {mod.getD `_}`"
    return none
  return some e

/-- Elaborate `environment`: check everything, then emit. -/
def elabEnvironment (doc? : Option (TSyntax ``Lean.Parser.Command.docComment))
    (vis? : Option (TSyntax ``Lean.Parser.Command.visibility)) (kw : Syntax) (e : Ident)
    (p? : Option Ident) (ds : Array (TSyntax `mantleDecl)) : CommandElabM Unit := do
  let isModule := (← getEnv).header.isModule
  let explicit := vis?.map fun v => v.raw.isOfKind ``Lean.Parser.Command.public
  let isPublic := explicit.getD ((← getScope).isPublic || !isModule)
  let vis? := explicit.map Lean.Parser.Command.visibility.ofBool
  let envShort := e.getId
  let envNs := (← getCurrNamespace) ++ envShort
  let (res?, failed) ← (do
      let env ← getEnv
      unless env.contains `Strata.Mantle.Env.addInsns do
        err kw "an environment needs `public import StrataMantle.Env`"
      if (env.getModuleIdx? `StrataMantle.Env.WF).isNone then
        err kw "building an environment needs `import StrataMantle.Env.WF`"
      let parent ← match p? with
        | some p => resolveParent envShort p isPublic isModule
        | none => pure none
      let ancestors := (parent.map fun pe => ancestry env pe.leanNs).getD #[]
      let mut ancestorNames : Std.HashSet Name := {}
      for a in ancestors do
        for n in a.names do ancestorNames := ancestorNames.insert n
        for ab in a.abbrevs do ancestorNames := ancestorNames.insert ab.envName
      let parentShort := parent.map fun pe =>
        Name.mkSimple ("to" ++ (pe.leanNs.componentsRev.head?.getD `P).toString (escape := false))
      let col ← collect envShort ancestorNames (reservedLean parentShort) ds
      let namespaces := namespacesOf (ancestorNames.toArray ++ col.declared.keys.toArray)
      let opens ← resolveOpens namespaces col.opens
      let res ← resolve { envNs, opens } ancestors col.items
      if res.stages.isEmpty then
        err kw "an environment declares at least one type, datatype or instruction"
      return some (parent, ancestors, res) : CheckM _).run false
  if failed then return
  let some (parent, ancestors, res) := res? | return
  let mut inherited : Std.HashMap Name TypeInfo := {}
  for a in ancestors do
    for t in a.types do inherited := inherited.insert t.envName t
  let names := res.stages.reverse.flatMap stageNames
  let parentNames := ancestors.flatMap (·.names)
  -- The instance binder, hygienic: one fresh macro scope, shared by every command.
  let hId := mkIdent (← withFreshMacroScope (MonadQuotation.addMacroScope `h))
  let cx : EmitCtx :=
    { envNs, envShort, parent, vis?, expose := isPublic && isModule, m := res.stages.size,
      ownTypes := res.own, inherited, parentNames, allNames := names ++ parentNames, hId }
  let cmds ← emitCommands cx res.stages res.abbrevs doc?
  let errorsBefore := (← get).messages.toList.filter (·.severity == .error) |>.length
  withRef kw do
    elabCommand (← `(command| namespace $(mkIdent envShort)))
    for c in cmds do elabCommand c
    elabCommand (← `(command| end $(mkIdent envShort)))
  let errorsAfter := (← get).messages.toList.filter (·.severity == .error) |>.length
  if errorsAfter > errorsBefore then
    logErrorAt kw "internal error: the declarations `environment` generated do not \
      elaborate; this is a bug in the elaborator, not in the block"
    return
  -- Record the environment for its children.
  let mut types : Array TypeInfo := #[]
  let mut ops : Array OpInfo := #[]
  for s in res.stages do
    match s with
    | .types ds => for d in ds do types := types.push (res.own[d.c.envName]?.getD default).1
    | .data ms =>
      for (d, _) in ms do types := types.push (res.own[d.c.envName]?.getD default).1
      for (_, _, d) in ms do
        ops := ops.push { envName := d.d.c.envName, owner := envNs, lean := d.d.c.lean,
                          typeArgc := d.d.typeParams.size }
    | .ops ds =>
      for d in ds do
        let info : OpInfo :=
          { envName := d.d.c.envName, owner := envNs, lean := d.d.c.lean,
            typeArgc := d.d.typeParams.size }
        ops := ops.push info
  let entry : EnvEntry :=
    { leanNs := envNs, isPublic, parent := parent.map (·.leanNs), types,
      abbrevs := res.abbrevs.map (·.2), ops, names }
  modifyEnv (envEntries.addEntry · entry)

elab_rules : command
  | `($[$doc?:docComment]? $[$vis?:visibility]? environment%$kw $e:ident $[extends $p?:ident]?
      where $ds:mantleDecl*) =>
    elabEnvironment doc? vis? kw e p? ds

end Strata.Mantle.DSL

end
