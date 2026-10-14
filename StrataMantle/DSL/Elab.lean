/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.AuxLemma
public meta import StrataMantle.Util.NameMap
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

A stage's names are fresh against a `NameSet` of every name before it, from the parent's
`nameSet`.  The sets are literal trees, `Internal.set{k}` after stage `k` and `nameSet` after
the last, which the elaborator computes and writes itself (`mantle_name_set%`).  The kernel
checks that adding a stage's names to the set before gives the set after
(`mantle_kernel_rfl`), so it adds each name once, in its own stage.

Quotations are unhygienic, because the generated names are the user's interface.  References
to the API, to an ancestor and to the environment's own declarations are written from
`_root_`, so no name in the user's scope can capture them.  The one hygienic binder is the
interface's `RefinedBy` instance, which no caller names (see `EmitCtx.hId`).
-/

namespace Strata.Mantle.DSL

/-- `mantle_internal_error% "msg"`: what the elaborator writes where its own invariant fails,
in place of a term it cannot build.  It does not elaborate, so the block reports an internal
error rather than accepting a `sorry`. -/
syntax (name := internalError) "mantle_internal_error% " str : term

/-- `mantle_kernel_rfl`: close `a = b` by `Eq.refl a`, which only the kernel checks.  The
elaborator's unifier would reduce both sides itself, far more slowly. -/
syntax (name := kernelRfl) "mantle_kernel_rfl" : tactic

/-- `mantle_name_set% k₁ k₂ …`: the `NameSet` that adding the names with keys `k₁`, `k₂`, …
to the empty set in order builds, as a literal tree whose keys are raw `Nat` literals.  The
elaborator writes the tree itself, rather than elaborating a term of it. -/
syntax (name := nameSetLit) "mantle_name_set% " num* : term

end Strata.Mantle.DSL

public meta section

namespace Strata.Mantle.DSL

open Lean Elab Command

set_option hygiene false

@[term_elab internalError] def elabInternalError : Term.TermElab := fun stx _ => do
  let `(mantle_internal_error% $msg:str) := stx | throwUnsupportedSyntax
  throwError "internal error: {msg.getString}"

@[tactic kernelRfl] def evalKernelRfl : Tactic.Tactic := fun _ =>
  Tactic.closeMainGoalUsing `mantle_kernel_rfl fun ty _ => do
    let ty ← instantiateMVars ty
    if ty.hasMVar || ty.hasFVar || ty.hasLevelParam then
      throwError "mantle_kernel_rfl: the goal is not closed:{indentExpr ty}"
    let .app (.app (.app (.const ``Eq us) α) a) _ := ty
      | throwError "mantle_kernel_rfl: the goal is not an equation:{indentExpr ty}"
    return mkConst (← Meta.mkAuxLemma [] ty (mkApp2 (mkConst ``Eq.refl us) α a))

/-- A tree, as an expression. -/
def treeExpr : Strata.Mantle.NatTree23 Unit → Expr
  | .leaf => mkApp (mkConst ``Strata.Mantle.NatTree23.leaf) (mkConst ``Unit)
  | .two l k _ r => mkAppN (mkConst ``Strata.Mantle.NatTree23.two)
      #[mkConst ``Unit, treeExpr l, mkRawNatLit k, mkConst ``Unit.unit, treeExpr r]
  | .three l k₁ _ m k₂ _ r => mkAppN (mkConst ``Strata.Mantle.NatTree23.three)
      #[mkConst ``Unit, treeExpr l, mkRawNatLit k₁, mkConst ``Unit.unit, treeExpr m,
        mkRawNatLit k₂, mkConst ``Unit.unit, treeExpr r]

@[term_elab nameSetLit] def elabNameSetLit : Term.TermElab := fun stx _ => do
  let `(mantle_name_set% $ks:num*) := stx | throwUnsupportedSyntax
  let t ← ks.foldlM (init := Strata.Mantle.NatTree23.leaf) fun t k =>
    match t.insert? k.getNat () with
    | some t => pure t
    | none => throwError "internal error: the key {k.getNat} occurs twice"
  return mkApp2 (mkConst ``Strata.Mantle.NameMap.mk) (mkConst ``Unit) (treeExpr t)

/-- The term for a broken invariant, which fails to elaborate with `msg`. -/
def internalErrorTerm (msg : String) : Term :=
  Unhygienic.run `(mantle_internal_error% $(quote msg))

/-! ## Terms -/

/-- An identifier for the global constant `n`, immune to the user's namespaces. -/
def rootId (n : Name) : Ident := mkIdent (`_root_ ++ n)

/-! ## Raw-form proofs

A cast between two spellings of a signature is proved by `InsnSig.carry_eq_of_toRaw`: each side
stands for the same raw data.  Each side's raw data is proved one node at a time, by the lemmas
of `Env.lean`'s "Raw forms, node by node", so the proof grows with the signature and nothing
rewrites a nested term.  The two sides meet where their raw forms are compared, by unification:
names there are an own type's name constant, which a reference unfolds to, or an inherited
type's, which its `name_ref` gives. -/

/-- `l.map f = m`, from each element's equation. -/
def mapChain (pfs : Array Term) : Term :=
  pfs.foldr (fun p acc => Unhygienic.run `(Strata.Mantle.map_cons_eq_of $p $acc))
    (Unhygienic.run `(rfl))

/-- `[a₁, …] = [b₁, …]`, from each `aᵢ = bᵢ`. -/
def consChain (pfs : Array Term) : Term :=
  pfs.foldr (fun p acc => Unhygienic.run `(Strata.Mantle.cons_eq_of $p $acc))
    (Unhygienic.run `(rfl))

/-- `DataTy.toRawList as = bs`, from each element's equation. -/
def dataChain (pfs : Array Term) : Term :=
  pfs.foldr (fun p acc => Unhygienic.run `(Strata.Mantle.DataTy.toRawList_cons_eq_of $p $acc))
    (Unhygienic.run `(rfl))

/-- A list's raw form, its types' by `rec`: a list variable is the literal `[*j]`. -/
def listRaw (kinds : Array Kind) (rec : Ty → Term) : Ty → Term
  | .var j => Unhygienic.run `(Strata.Mantle.TypeList.toRaw_lit_of
      (Strata.Mantle.map_cons_eq_of
        (Strata.Mantle.TypeList.Elem.toRaw_splice $(quote j) rfl) rfl))
  | .list es => Unhygienic.run `(Strata.Mantle.TypeList.toRaw_lit_of $(mapChain (es.map fun e =>
      match e with
      | .var j =>
        if e.kind kinds == .list then
          Unhygienic.run `(Strata.Mantle.TypeList.Elem.toRaw_splice $(quote j) rfl)
        else Unhygienic.run `(Strata.Mantle.TypeList.Elem.toRaw_ty_of $(rec e))
      | _ => Unhygienic.run `(Strata.Mantle.TypeList.Elem.toRaw_ty_of $(rec e)))))
  | e => rec e

/-- An argument's raw form: a list's or a type's. -/
def argRaw (kinds : Array Kind) (rec : Ty → Term) (a : Ty) : Term :=
  if a.kind kinds == .list then
    Unhygienic.run `(Strata.Mantle.TypeArg.toRaw_list_of $(listRaw kinds rec a))
  else Unhygienic.run `(Strata.Mantle.TypeArg.toRaw_ty_of $(rec a))

/-- A named entry's: `(name, raw)`. -/
def pairRaw (pf : Term) : Term := Unhygienic.run `(Strata.Mantle.pair_eq_of $pf)

/-- Two sides that stand for the same raw data: `l : a = x` and `r : b = x`. -/
def bothRaw (l r : Term) : Term := Unhygienic.run `(Eq.trans $l (Eq.symm $r))

/-- A `Strata.Mantle.Name` literal for an environment name. -/
partial def nameLit : Name → Term
  | .anonymous => Unhygienic.run `(Strata.Mantle.Name.base)
  | .str p s => Unhygienic.run `(Strata.Mantle.Name.str $(nameLit p) $(quote s))
  | .num p i => Unhygienic.run `(Strata.Mantle.Name.num $(nameLit p) $(quote i))

/-- The key of an environment name, as the kernel computes it from the name's literal. -/
def nameKey (n : Name) : Nat := (mantleName n).key

/-- The literal `mantle_name_set%` elaborates to, as `ks` builds it. -/
def setLit (ks : Array Nat) : Term :=
  Unhygienic.run `(mantle_name_set% $(ks.map fun k => Syntax.mkNumLit (toString k))*)

/-- `name.str s`. -/
def sfx (n : Name) (s : String) : Name := Name.mkStr n s

/-- A list, as a `TypeList`, in a scope whose variables have kinds `kinds`, its types written by
`ty`: list variable `j` is `TypeList.var j`, and a literal's splice `*j` is `Elem.splice j`. -/
def listTerm (kinds : Array Kind) (ty : Ty → Term) : Ty → Term
  | .var j => Unhygienic.run `(Strata.Mantle.TypeList.var $(quote j) (by decide))
  | .list es => Unhygienic.run `(Strata.Mantle.TypeList.lit #[$(es.map fun e =>
      if e.kind kinds == .list then Unhygienic.run
        `(Strata.Mantle.TypeList.Elem.splice $(quote (match e with | .var j => j | _ => 0))
          (by decide))
      else Unhygienic.run `(Strata.Mantle.TypeList.Elem.ty $(ty e))),*])
  -- Checking puts only lists in a list position.  Anywhere else this is a `TypeExpr`, which
  -- fails to elaborate as a `TypeList`.
  | e => ty e

/-- An argument of a type constructor, as a `TypeArg`: a list or a type. -/
def argTerm (kinds : Array Kind) (ty : Ty → Term) (a : Ty) : Term :=
  if a.kind kinds == .list then Unhygienic.run `(Strata.Mantle.TypeArg.list $(listTerm kinds ty a))
  else Unhygienic.run `(Strata.Mantle.TypeArg.ty $(ty a))

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
  /-- The keys of the names the parent's `nameSet` holds, in the order its stages add them. -/
  parentKeys : Array Nat
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

/-- The set of every name stage `k` declares: the parent's `nameSet`, or `∅`, at `0`. -/
def stageSet (k : Nat) : Term :=
  if k == 0 then
    match cx.parent with
    | some p => rootId (p.leanNs ++ `nameSet)
    | none => Unhygienic.run `((∅ : Strata.Mantle.NameSet))
  else if k == cx.m then cx.own `nameSet
  else cx.internal s!"set{k}"

/-- `(stageSet k).Ordered`. -/
def stageOrd (k : Nat) : Term :=
  if k == 0 then
    match cx.parent with
    | some p => rootId (p.leanNs ++ `nameSet_ordered)
    | none => Unhygienic.run `(Strata.Mantle.NameSet.ordered_empty)
  else if k == cx.m then cx.own `nameSet_ordered
  else cx.internal s!"ord{k}"

/-- `n ∈ stage k ↔ n ∈ stageSet k`. -/
def stageSetMem (k : Nat) : Term :=
  if k == 0 then
    match cx.parent with
    | some p => rootId (p.leanNs ++ `mem_nameSet)
    | none => Unhygienic.run `((iff_of_false (Strata.Mantle.Env.not_mem_empty _)
        (Strata.Mantle.NameSet.not_mem_empty _)))
  else if k == cx.m then cx.own `mem_nameSet
  else cx.internal s!"smem{k}"

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
    else Unhygienic.run
      `(Strata.Mantle.TypeRef.ofLE (Strata.Mantle.Env.le_of_subset $(cx.chain t j)) $r)
  | none =>
    match cx.inherited[h]? with
    | some info =>
      Unhygienic.run `(($(rootId (info.owner ++ info.lean ++ `ref)) (e := $(cx.stage j))))
    | none => internalErrorTerm s!"type `{h}` is neither declared nor inherited"

/-- The kinds proof of an application of the type that `owner` declares as `lean`, in `e`:
`TypeExpr.app`'s when `allTypes`, else `TypeExpr.appK`'s.  It reads the declaration from
`decl_ref` and leaves `rfl` on the declaration.  Nothing rewrites the goal, so the proof does
not look inside the arguments, and a type nested in its own argument, at any depth, elaborates
as a flat one does. -/
def declKinds (owner lean : Name) (e : Term) (allTypes : Bool) : Term :=
  let hd := Unhygienic.run `(($(rootId (owner ++ lean ++ `decl_ref)) (e := $e)))
  if allTypes then Unhygienic.run `(Strata.Mantle.TypeRef.kinds_of_decl $hd rfl)
  else Unhygienic.run `(Strata.Mantle.TypeRef.kinds_toList_of_decl $hd rfl)

/-- The `TypeInfo` of a type this block or an ancestor declares. -/
def info (h : Name) : TypeInfo :=
  match cx.ownTypes[h]? with
  | some (i, _, _) => i
  | none => cx.inherited[h]?.getD default

/-- Whether every parameter of `h` is a type, so that `TypeExpr.app` applies it. -/
def allTypes (h : Name) : Bool := (cx.info h).params.all (·.2.2 == .type)

/-- A proof of `stage t ≤ stage j`, for `t ≤ j`. -/
def leTerm (t j : Nat) : Term :=
  if t == j then Unhygienic.run `(Strata.Mantle.Env.Le.refl _)
  else Unhygienic.run `(Strata.Mantle.Env.le_of_subset $(cx.chain t j))

/-- A type, in stage `j`, in a scope whose variables have kinds `kinds`. -/
partial def tyAt (j : Nat) (kinds : Array Kind) : Ty → Term
  | .var i => Unhygienic.run `(Strata.Mantle.TypeExpr.var $(quote i) (by decide))
  | .app h args =>
    let h := leanName h
    let as : Array Term := args.map fun a =>
      if a.kind kinds == .list then listTerm kinds (tyAt j kinds) a else tyAt j kinds a
    -- As the interface writes types, one application per node: an own type's `tyAt` at the
    -- inclusion of its stage in stage `j`, an inherited type's `ty` at stage `j`.
    match cx.ownTypes[h]? with
    | some (info, t, _) =>
      Unhygienic.run `($(cx.own (`Internal ++ info.lean ++ `tyAt)) $(cx.leTerm t j) $as*)
    | none =>
      let info := cx.info h
      Unhygienic.run `(($(rootId (info.owner ++ info.lean ++ `ty)) (e := $(cx.stage j))) $as*)
  -- Checking puts a list only in a list position, which the `app` case and `listTerm` read.
  -- Anywhere else it is a `TypeList`, which fails to elaborate as a `TypeExpr`.
  | l@(.list _) => listTerm kinds (tyAt j kinds) l

/-- A type, over a generic `e`, with the variables named `vars`, of kinds `kinds`: a list
variable's is a `TypeList`.  A list is a `TypeList`, the argument a list parameter's `T.ty`
takes. -/
partial def tyGen (vars : Array Term) (kinds : Array Kind) : Ty → Term
  | .var i => vars[i]?.getD (internalErrorTerm s!"type variable #{i} is out of scope")
  | .app h args =>
    let h := leanName h
    let as : Array Term := args.map fun a =>
      if a.kind kinds == .list then listTerm kinds (tyGen vars kinds) a else tyGen vars kinds a
    let info := cx.info h
    Unhygienic.run `($(rootId (info.owner ++ info.lean ++ `ty)) $as*)
  | l@(.list _) => listTerm kinds (tyGen vars kinds) l

/-- Whether `t` is the list variable `j`, spliced: its level. -/
def spliceOf? (kinds : Array Kind) : Ty → Option Nat
  | .var j =>
    match kinds[j]? with
    | some .list => some j
    | some .type | none => none
  | _ => none

/-- A type of an abbreviation's body, over a generic `e`, with the parameters named `vars`, of
kinds `kinds`.  A list is a `TypeList`: its types in literals, each list parameter spliced in by
`++`, and a list parameter alone its own `TypeList`.  Appending is how `instantiate` splices
a list argument (`TypeExpr.instantiate_append`), and on literals it is the literal of both
(`TypeExpr.lit_append_lit`), so `n.ty` builds what checking expands the
abbreviation to with `Raw.instantiate`. -/
partial def abbrevTy (vars : Array Term) (kinds : Array Kind) : Ty → Term
  | .var i => vars[i]?.getD (internalErrorTerm s!"type variable #{i} is out of scope")
  | .app h args =>
    let h := leanName h
    let as : Array Term := args.map fun a =>
      if a.kind kinds == .list then abbrevList vars kinds a else abbrevTy vars kinds a
    let info := cx.info h
    Unhygienic.run `($(rootId (info.owner ++ info.lean ++ `ty)) $as*)
  | l@(.list _) => abbrevList vars kinds l
where
  /-- A list of the body: runs of types as literals, appended to the list parameters spliced
  between them. -/
  abbrevList (vars : Array Term) (kinds : Array Kind) : Ty → Term
    | .list es => Id.run do
      let mut parts : Array Term := #[]
      let mut run : Array Term := #[]
      for e in es do
        match spliceOf? kinds e with
        | some j =>
          unless run.isEmpty do
            parts := parts.push (Unhygienic.run `(Strata.Mantle.TypeList.lit #[$run,*]))
            run := #[]
          parts := parts.push (vars[j]?.getD
            (internalErrorTerm s!"list variable #{j} is out of scope"))
        | none =>
          run := run.push (Unhygienic.run `(Strata.Mantle.TypeList.Elem.ty
            $(abbrevTy vars kinds e)))
      if !run.isEmpty || parts.isEmpty then
        parts := parts.push (Unhygienic.run `(Strata.Mantle.TypeList.lit #[$run,*]))
      match parts.toList with
      | [] => Unhygienic.run `(Strata.Mantle.TypeList.lit #[])
      | p :: ps => ps.foldl (fun acc q => Unhygienic.run `($acc ++ $q)) p
    | e => abbrevTy vars kinds e

/-- A payload of the group added at stage `k`, whose members are `members`.  Every other type
is read through `refs`, the stage's literal references (`payRefs`). -/
partial def dataTy (k : Nat) (members : Array Name) (refs : Std.HashMap Name Term) :
    Ty → Term
  | .var l => Unhygienic.run `(Strata.Mantle.DataTy.var $(quote l))
  | .app h args =>
    let h := leanName h
    let as : Array Term := args.map (dataTy k members refs)
    match members.idxOf? h with
    | some j =>
      Unhygienic.run `(Strata.Mantle.DataTy.ref
        (Strata.Mantle.TypeRef.ofAddTypes $(cx.stage (k - 1)) $(cx.internal s!"hdr{k}")
          $(cx.internal s!"fresh{k}") $(quote j)) #[$as,*])
    | none =>
      Unhygienic.run `(Strata.Mantle.DataTy.ext $(refs[h]?.getD (cx.refAt h (k - 1))) #[$as,*])
  | .list es =>
    let es : Array Term := es.map (dataTy k members refs)
    Unhygienic.run `(Strata.Mantle.DataTy.list #[$es,*])

/-- A constant of the environment declaring `h`, by its name relative to that
environment. -/
def ownOrInherited (h : Name) (rel : Name) : Ident :=
  if cx.ownTypes.contains h then cx.own rel else rootId ((cx.info h).owner ++ rel)

/-- The raw form of `tyAt j kinds t`. -/
partial def rawAt (j : Nat) (kinds : Array Kind) : Ty → Term
  | .var i => Unhygienic.run `(Strata.Mantle.TypeExpr.toRaw_var $(quote i) rfl)
  | .app h args =>
    let h := leanName h
    let holes : Array Term := args.map fun _ => Unhygienic.run `(_)
    let pfs := args.map fun a =>
      if a.kind kinds == .list then listRaw kinds (rawAt j kinds) a else rawAt j kinds a
    let lem := match cx.ownTypes[h]? with
      | some (info, t, _) => Unhygienic.run
          `($(cx.own (`Internal ++ info.lean ++ `toRaw_tyAt)) $(cx.leTerm t j) $holes*)
      | none =>
        let info := cx.info h
        Unhygienic.run `(($(rootId (info.owner ++ info.lean ++ `toRaw_ty)) (e := $(cx.stage j)))
          $holes*)
    Unhygienic.run `(Eq.trans $lem (Strata.Mantle.TypeExpr.Raw.app_eq_of $(consChain pfs)))
  | l@(.list _) => listRaw kinds (rawAt j kinds) l

/-- The raw form of `tyGen vars kinds t`, by each type's `toRaw_ty`. -/
partial def rawGen (kinds : Array Kind) : Ty → Term
  | .var i => Unhygienic.run `(Strata.Mantle.TypeExpr.toRaw_var $(quote i) rfl)
  | .app h args =>
    let info := cx.info (leanName h)
    let holes : Array Term := args.map fun _ => Unhygienic.run `(_)
    let pfs := args.map fun a =>
      if a.kind kinds == .list then listRaw kinds (rawGen kinds) a else rawGen kinds a
    Unhygienic.run `(Eq.trans ($(rootId (info.owner ++ info.lean ++ `toRaw_ty)) $holes*)
      (Strata.Mantle.TypeExpr.Raw.app_eq_of $(consChain pfs)))
  | l@(.list _) => listRaw kinds (rawGen kinds) l

/-- The raw form of a payload `dataTy k members refs t`. -/
partial def rawData (members : Array Name) : Ty → Term
  | .var _ => Unhygienic.run `(Strata.Mantle.DataTy.toRaw_var _)
  | .app h args =>
    let pfs := args.map (rawData members)
    if members.contains (leanName h) then
      Unhygienic.run `(Strata.Mantle.DataTy.toRaw_ref_of rfl $(dataChain pfs))
    else Unhygienic.run `(Strata.Mantle.DataTy.toRaw_ext_of rfl $(dataChain pfs))
  | .list es =>
    Unhygienic.run `(Strata.Mantle.DataTy.toRaw_list_of $(dataChain (es.map (rawData members))))

/-- A proof of `stage t ≤ e`, under `[h : env ⊑ e]`. -/
def liftTo (t : Nat) : Term :=
  if t == cx.m then Unhygienic.run `(Strata.Mantle.RefinedBy.le (self := $(cx.hId)))
  else Unhygienic.run `(Strata.Mantle.Env.Le.trans
    (Strata.Mantle.Env.le_of_subset $(cx.internal s!"hsub{t}"))
    (Strata.Mantle.RefinedBy.le (self := $(cx.hId))))

end EmitCtx

/-! ## Commands -/

/-- The heads of `t` that are not in `members`, added to `acc` in order. -/
partial def collectHeads (members : Array Name) (t : Ty) (acc : Array Name) : Array Name :=
  match t with
  | .var _ => acc
  | .app h args =>
    let h := leanName h
    let acc := if members.contains h || acc.contains h then acc else acc.push h
    args.foldl (fun acc a => collectHeads members a acc) acc
  | .list es => es.foldl (fun acc a => collectHeads members a acc) acc

/-- A return type as a term: `some τ`, or `none` for a terminal instruction. -/
def retTerm (ty : Ty → Term) : Option Ty → CommandElabM Term
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

/-- A kind, as a term. -/
def kindTerm : Kind → Term
  | .type => Unhygienic.run `(Strata.Mantle.Kind.type)
  | .list => Unhygienic.run `(Strata.Mantle.Kind.list)

/-- A `TypeDecl` literal, from each parameter's name, whether it is positive, and its kind. -/
def typeDeclTerm (nameId : Ident) (params : Array (String × Bool × Kind)) :
    CommandElabM Term := do
  let ps ← params.mapM fun (x, b, k) => `(⟨$(quote x), ⟨$(polTerm b), $(kindTerm k)⟩⟩)
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

/-- The private `Internal.T.tyAt`, an own type `T` applied in any environment its stage, the
term `stage`, is included in, and its raw-form lemma `Internal.T.toRaw_tyAt`.  The stage's
signatures write `T` with it, one application per node, as the interface writes `T.ty`. -/
def tyAtCmds (cx : EmitCtx) (stage : Term) (lean : Name) (params : Array (String × Kind)) :
    CommandElabM (Array Command) := do
  let svis? := EmitCtx.stageVis?
  let avoid : Array Name := #[`e, `s, `hle] ++ params.map (Name.mkSimple ·.1)
  let xs : Array Ident := params.map fun (x, _) =>
    let n := Name.mkSimple x
    mkIdent (if n == `e || n == `s || n == `hle then primeAvoiding avoid n else n)
  let ks := params.map (·.2)
  let binders ← (xs.zip ks).mapM fun
    | (x, .list) => `(bracketedBinder| ($x : Strata.Mantle.TypeList e s))
    | (x, .type) => `(bracketedBinder| ($x : Strata.Mantle.TypeExpr e s))
  let pre : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[
    ← `(bracketedBinder| {e : Strata.Mantle.Env _root_.Unit}),
    ← `(bracketedBinder| (hle : $stage ≤ e)),
    ← `(bracketedBinder| {s : _root_.Array Strata.Mantle.Kind})]
  let ref ← `(Strata.Mantle.TypeRef.ofLE hle $(cx.own (`Internal ++ lean ++ `ref₀)))
  let allTypes := ks.all (· == .type)
  let body ← if allTypes then
      `(Strata.Mantle.TypeExpr.app $ref #v[$(xs.map fun x => (x : Term)),*] rfl)
    else
      let as ← (xs.zip ks).mapM fun
        | (x, .list) => `(Strata.Mantle.TypeArg.list $x)
        | (x, .type) => `(Strata.Mantle.TypeArg.ty $x)
      `(Strata.Mantle.TypeExpr.appK $ref #v[$as,*] rfl)
  let tyAtId := cx.own (`Internal ++ lean ++ `tyAt)
  let raws ← xs.mapM fun x => `(Strata.Mantle.TypeExpr.toRaw $x)
  let rawPf ← if allTypes then
      `(Strata.Mantle.TypeExpr.toRaw_app_of (hk := rfl) rfl
          $(mapChain (xs.map fun _ => Unhygienic.run `(rfl))))
    else
      `(Strata.Mantle.TypeExpr.toRaw_appK_of (hk := rfl) rfl
          $(mapChain (ks.map fun
            | .list => Unhygienic.run `(Strata.Mantle.TypeArg.toRaw_list_of rfl)
            | .type => Unhygienic.run `(Strata.Mantle.TypeArg.toRaw_ty_of rfl))))
  return #[
    ← defCmd (mkDoc s!"`{lean}`, applied in an environment its stage is included in.") svis?
      false (mkIdent (`Internal ++ lean ++ `tyAt)) (pre ++ binders)
      (← `(Strata.Mantle.TypeExpr e s)) body,
    ← thmCmd (mkDoc s!"The raw form of `{lean}` applied.") svis? false
      (mkIdent (`Internal ++ lean ++ `toRaw_tyAt)) (pre ++ binders)
      (← `(Strata.Mantle.TypeExpr.toRaw ($tyAtId (s := s) hle $(xs.map fun x => (x : Term))*) =
            Strata.Mantle.TypeExpr.Raw.app $(cx.own (lean ++ `name)) ⟨[$raws,*]⟩))
      rawPf]

/-- The keys each stage's sets are built from, in order from the empty set, after `pre`, the
parent's: after a datatype's members, then after the whole stage.  For a stage of types or
instructions the first is the set before. -/
def stageKeys (pre : Array Nat) (stages : Array Stage) : Array (Array Nat × Array Nat) :=
  (stages.foldl (init := (pre, #[])) fun (ks, out) st =>
    let mid := match st with
      | .data ms => ks ++ ms.map (nameKey ·.1.c.envName)
      | _ => ks
    let all := ks ++ (stageNames st).map nameKey
    (all, out.push (mid, all))).2

/-- The set after a batch: its literal, the kernel's check that adding the batch's names to the
set before gives it, and its order.  `rel`, `eqRel` and `ordRel` name them relative to `E`;
`isPub` makes the set and its order the environment's, else they are a stage's. -/
def EmitCtx.setCmds (cx : EmitCtx) (what : String) (rel eqRel ordRel : Name) (isPub : Bool)
    (before beforeOrd names : Term) (lit : Array Nat) :
    CommandElabM (Array Command) := do
  let svis? := EmitCtx.stageVis?
  let (sv?, ex) := if isPub then (cx.vis?, cx.expose) else (svis?, false)
  return #[
    ← defCmd (mkDoc s!"Every name {what} declares, as a set.") sv? ex (mkIdent rel) #[]
      (← `(Strata.Mantle.NameSet)) (setLit lit),
    ← thmCmd (mkDoc s!"The set after {what}: the set before, with its names added.") svis?
      false (mkIdent eqRel) #[]
      (← `(Strata.Mantle.NameSet.insertAll? $before $names = some $(cx.own rel)))
      -- By the kernel alone, which adds only these names and compares the result with the
      -- literal.
      (← `(by mantle_kernel_rfl)),
    ← thmCmd (mkDoc s!"The set after {what} is ordered.") sv? false (mkIdent ordRel) #[]
      (← `(Strata.Mantle.NameSet.Ordered $(cx.own rel)))
      (← `((Strata.Mantle.NameSet.insertAll?_spec $beforeOrd $(cx.own eqRel)).1))]

/-- A batch's freshness, by `of_insertAll?`: the set before is ordered (`ord`) and holds the
environment's names (`mem`), and adding the batch, spelled as `namesEq` says, gives the set
`rel` (`eqRel`). -/
def EmitCtx.freshTerm (cx : EmitCtx) (rel eqRel : Name) (ord mem namesEq : Term) : Term :=
  Unhygienic.run `(Strata.Mantle.Env.FreshNames.of_insertAll? (T := $(cx.own rel)) $ord
    ($mem).mp (by rw [$namesEq:term]; exact $(cx.own eqRel)))

/-- `hmem{k}`: every name of `t`, stage `k`'s members added as types, is in `hset{k}`. -/
def EmitCtx.hmemCmd (cx : EmitCtx) (k : Nat) (t prevOrd prevSMem : Term) :
    CommandElabM Command := do
  let R (s : String) : Ident := cx.internal s!"{s}{k}"
  thmCmd (mkDoc s!"Every name stage {k}'s members declare, with the names before.")
    EmitCtx.stageVis? false (mkIdent (sfx `Internal s!"hmem{k}"))
    #[← `(bracketedBinder| {n : Strata.Mantle.Name})]
    (← `($(mkIdent `n) ∈ $t ↔ $(mkIdent `n) ∈ $(R "hset")))
    (← `(Iff.trans Strata.Mantle.Env.mem_addTypes
          (Strata.Mantle.NameSet.mem_of_insertAll? $prevOrd $(R "hset_eq")
            $(R "hdrNames_eq") $prevSMem)))

/-- The proof of stage `k`'s membership in its set: the stage's lemma, then the set's. -/
def EmitCtx.smemProof (cx : EmitCtx) (st : Stage) (prevOrd prevSMem : Term) (eqRel : Name)
    (k : Nat) : Term :=
  let R (s : String) : Ident := cx.internal s!"{s}{k}"
  let eq := cx.own eqRel
  match st with
  | .types _ => Unhygienic.run `(Iff.trans Strata.Mantle.Env.mem_addTypes
      (Strata.Mantle.NameSet.mem_of_insertAll? $prevOrd $eq $(R "names_eq") $prevSMem))
  | .ops _ => Unhygienic.run `(Iff.trans Strata.Mantle.Env.mem_addInsns
      (Strata.Mantle.NameSet.mem_of_insertAll? $prevOrd $eq $(R "names_eq") $prevSMem))
  | .data .. => Unhygienic.run `(Iff.trans Strata.Mantle.Env.mem_addData (Iff.trans or_left_comm
      (Strata.Mantle.NameSet.mem_of_insertAll? $(R "hord") $eq $(R "cnames_eq")
        (Iff.trans (Iff.symm Strata.Mantle.Env.mem_addTypes) $(R "hmem")))))

/-- Stage `k`'s membership lemmas, `n ∈ stage k ↔ n ∈ stageList k` and its set's, and the list
that the first's statement unfolds to.  `listParts` are the stage's names, as lists. -/
def EmitCtx.memCmds (cx : EmitCtx) (st : Stage) (k : Nat) (listParts : Array Term) :
    CommandElabM (Array Command) := do
  let vis? := cx.vis?
  let svis? := EmitCtx.stageVis?
  let envStr := showName cx.envShort
  let prevList := cx.stageList (k - 1)
  let prevMem := cx.stageMem (k - 1)
  let stageId := cx.stage k
  let isLast := k == cx.m
  let setRel : Name := if isLast then `nameSet else sfx `Internal s!"set{k}"
  let eqRel : Name := sfx `Internal s!"set_eq{k}"
  let I (s : String) : Ident := mkIdent (sfx `Internal s!"{s}{k}")
  let R (s : String) : Ident := cx.internal s!"{s}{k}"
  let nBinder ← `(bracketedBinder| {n : Strata.Mantle.Name})
  let mut cs : Array Command := #[]
  -- Membership: `n ∈ stage k ↔ n ∈ stageList k`.
  let listVal ← listParts.foldrM (fun p acc => `($p ++ $acc)) prevList
  let memLemma ← match st with
    | .types _ => `(Strata.Mantle.Env.mem_addTypes)
    | .ops _ => `(Strata.Mantle.Env.mem_addInsns)
    | .data .. => `(Strata.Mantle.Env.mem_addData)
  let eqs : Array Ident := match st with
    | .data .. => #[R "hdrNames_eq", R "cnames_eq"]
    | _ => #[R "names_eq"]
  -- A term of one step per part, whatever the stage's size and position: the stage's
  -- lemma, then each part by its names lemma, then the stage before by its own.
  let step (eq rest : Term) : CommandElabM Term :=
    `(Iff.trans (or_congr (Strata.Mantle.Env.mem_toList_of_eq $eq) $rest)
        List.mem_append.symm)
  let parts ← (eqs.map fun (x : Ident) => (x : Term)).foldrM step (prevMem : Term)
  let memTerm ← `(Iff.trans $memLemma $parts)
  let memProof ← if isLast then
      -- The unifier may not meet the literal: it recurses once per element.  The term proves
      -- membership in `listVal`, whose parts are constants, and `decide +kernel` that
      -- `listVal` is the literal, which unifies with the statement's syntactically.
      `(Iff.trans $memTerm
          (Iff.of_eq (congrArg (fun l => $(mkIdent `n) ∈ l)
            (by decide +kernel : $listVal = $(cx.stageList k)))))
    else do
      cs := cs.push (← defCmd (mkDoc s!"Every name stage {k} declares.") svis? false
        (I "list") #[] (← `(List Strata.Mantle.Name)) listVal)
      pure memTerm
  let memStmt ← `($(mkIdent `n) ∈ $stageId ↔ $(mkIdent `n) ∈ $(cx.stageList k))
  if isLast then
    cs := cs.push (← thmCmd (mkDoc s!"The names `{envStr}.env` declares, as literals, in \
        `names` order.") vis? true (mkIdent `mem_env) #[nBinder] memStmt memProof)
  else
    cs := cs.push (← thmCmd (mkDoc s!"Every name stage {k} declares.") svis? false (I "mem")
      #[nBinder] memStmt memProof)
  let smemProof := cx.smemProof st (cx.stageOrd (k - 1)) (cx.stageSetMem (k - 1)) eqRel k
  let smemStmt ← `($(mkIdent `n) ∈ $stageId ↔ $(mkIdent `n) ∈ $(cx.own setRel))
  if isLast then
    cs := cs.push (← thmCmd (mkDoc s!"The names `{envStr}.env` declares, as a set.") vis?
      false (mkIdent `mem_nameSet) #[nBinder] smemStmt smemProof)
  else
    cs := cs.push (← thmCmd (mkDoc s!"Every name stage {k} declares, as a set.") svis? false
      (I "smem") #[nBinder] smemStmt smemProof)
  return cs

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
  let sets := stageKeys cx.parentKeys stages
  for h : i in [0:stages.size] do
    let k := i + 1
    let prev := cx.stage (k - 1)
    let prevList := cx.stageList (k - 1)
    let prevMem := cx.stageMem (k - 1)
    let prevSet := cx.stageSet (k - 1)
    let prevOrd := cx.stageOrd (k - 1)
    let prevSMem := cx.stageSetMem (k - 1)
    let stageId := cx.stage k
    let isLast := k == cx.m
    let setRel : Name := if isLast then `nameSet else sfx `Internal s!"set{k}"
    let ordRel : Name := if isLast then `nameSet_ordered else sfx `Internal s!"ord{k}"
    let eqRel : Name := sfx `Internal s!"set_eq{k}"
    let I (s : String) : Ident := mkIdent (sfx `Internal s!"{s}{k}")
    let R (s : String) : Ident := cx.internal s!"{s}{k}"
    -- The list `names` or `Internal.list{k}` unfolds to.
    let mut listParts : Array Term := #[]
    match stages[i] with
    | .types ds =>
      let decls ← ds.mapM fun d =>
        typeDeclTerm (nameId d.c.envName) (d.params.map fun (x, _, b, k) => (x, b, k))
      let ns : Array Term := ds.map fun d => nameId d.c.envName
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}: types.") svis? false (I "types") #[]
        (← `(Array (Strata.Mantle.TypeDecl _root_.Unit))) (← `(#[$decls,*])))
      cs := cs.push (← defCmd (mkDoc s!"Stage {k}'s names.") svis? false (I "names") #[]
        (← `(Array Strata.Mantle.Name)) (← `(#[$ns,*])))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s names, as a literal.") svis? false
        (I "names_eq") #[] (← `(($(R "types")).map (·.name) = $(R "names")))
        (← `(by simp [$(R "types"):ident, $(R "names"):ident])))
      cs := cs ++ (← cx.setCmds s!"stage {k}" setRel eqRel ordRel isLast prevSet prevOrd
        (R "names") (sets[i]?.getD (#[], #[])).2)
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s types may be added.") svis? false
        (I "fresh") #[] (← `(Strata.Mantle.Env.FreshTypes $prev $(R "types")))
        (← `(⟨$(cx.freshTerm setRel eqRel prevOrd prevSMem (R "names_eq")), by decide⟩)))
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
        typeDeclTerm (nameId d.c.envName) (d.params.map fun (x, _, b, k) => (x, b, k))
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
      cs := cs ++ (← cx.setCmds s!"stage {k}'s members" (sfx `Internal s!"hset{k}")
        (sfx `Internal s!"hset_eq{k}") (sfx `Internal s!"hord{k}") false prevSet prevOrd
        (R "hdrNames") (sets[i]?.getD (#[], #[])).1)
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s members may be added as types.") svis?
        false (I "fresh") #[] (← `(Strata.Mantle.Env.FreshTypes $prev $(R "hdr")))
        (← `(⟨$(cx.freshTerm (sfx `Internal s!"hset{k}") (sfx `Internal s!"hset_eq{k}")
              prevOrd prevSMem (R "hdrNames_eq")), by decide⟩)))
      let t ← `(Strata.Mantle.Env.addTypes $prev $(R "hdr") $(R "fresh"))
      cs := cs.push (← cx.hmemCmd k t prevOrd prevSMem)
      -- The payloads' other types, as references built from literals.  `admissible`'s
      -- `decide` reads each one's parameters, and cannot unfold `TypeRef.ofLE` or an
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
                try simp only [Strata.Mantle.name_TypeRef_ofLE,
                  Strata.Mantle.decl_TypeRef_ofLE, $[$lemmas:ident],*] at r
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
        -- By the kernel, over lists: `simp` would unfold the constructors' payloads, recursing
        -- once per level of their types.
        (← `(by
              apply Array.toList_inj.mp
              rw [Strata.Mantle.Env.toList_ctorNames_append_caseNames]
              decide +kernel)))
      cs := cs ++ (← cx.setCmds s!"stage {k}" setRel eqRel ordRel isLast (R "hset") (R "hord")
        (R "cnames") (sets[i]?.getD (#[], #[])).2)
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s constructor and case names are fresh.")
        svis? false (I "cfresh") #[]
        (← `(Strata.Mantle.Env.FreshNames $t (Strata.Mantle.Env.ctorNames $(R "ctors") ++
              Strata.Mantle.Env.caseNames $(R "hdr"))))
        (cx.freshTerm setRel eqRel (R "hord") (R "hmem") (R "cnames_eq")))
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s constructors make a datatype group.") svis?
        false (I "adm") #[]
        -- `+kernel`: the check reads every payload, and the elaborator's evaluation recurses
        -- once per level of their types.  `addData` consumes it.
        (← `(Strata.Mantle.Env.admissible $(R "hdr") $(R "ctors") = true))
        (← `(by decide +kernel)))
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
        let ks := d.d.typeParams.map (·.2.2)
        let tyK := cx.tyAt (k - 1) ks
        let tps ← d.d.typeParams.mapM fun (x, _, kd) => `(⟨$(quote x), $(kindTerm kd)⟩)
        let args ← d.args.mapM fun (x, ty) => `(⟨$(quote x), $(tyK ty)⟩)
        let variadic ← match d.variadic with
          | some (x, ty) =>
            if ty.kind ks == .list then
              `(some ⟨$(quote x), Strata.Mantle.Variadic.spread $(listTerm ks tyK ty)⟩)
            else `(some ⟨$(quote x), Strata.Mantle.Variadic.each $(tyK ty)⟩)
          | none => `(none)
        let regs ← d.regions.mapM fun r => do
          let ps ← r.params.mapM fun (x, ty) => `(⟨$(quote x), $(tyK ty)⟩)
          `(⟨$(quote r.name), Strata.Mantle.RegionSig.of #[$ps,*] $(tyK r.ret)⟩)
        let succs ← d.succs.mapM fun sc => do
          let ts := sc.payload.map (argTerm ks tyK)
          `(⟨$(quote sc.name), #[$ts,*]⟩)
        cs := cs.push (← defCmd (mkDoc s!"The signature of `{showName d.d.c.envName}`, in \
            stage {k - 1}.") svis? false sig0 #[]
          (← `(Strata.Mantle.InsnSig $prev))
          (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
                 variadic := $variadic, returnType := $(← retTerm tyK d.ret),
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
      cs := cs ++ (← cx.setCmds s!"stage {k}" setRel eqRel ordRel isLast prevSet prevOrd
        (R "names") (sets[i]?.getD (#[], #[])).2)
      cs := cs.push (← thmCmd (mkDoc s!"Stage {k}'s names are fresh.") svis? false
        (I "fresh") #[] (← `(Strata.Mantle.Env.FreshNames $prev (($(R "ops")).map (·.1))))
        (cx.freshTerm setRel eqRel prevOrd prevSMem (R "names_eq")))
      let val ← `(Strata.Mantle.Env.addInsns $prev $(R "ops") $(R "fresh"))
      if isLast then
        cs := cs.push (← defCmd (docOr envDoc? s!"The environment `{envStr}`.") vis? false
          (mkIdent `env) #[] (← `(Strata.Mantle.Env _root_.Unit)) val)
      else
        cs := cs.push (← defCmd (mkDoc s!"Stage {k}.") svis? false (I "s") #[]
          (← `(Strata.Mantle.Env _root_.Unit)) val)
      listParts := #[← `(($(R "names")).toList)]
    cs := cs ++ (← cx.memCmds stages[i] k listParts)
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
          Strata.Mantle.RefinedBy $(rootId (p.leanNs ++ `env)) $stageId :=
            ⟨Strata.Mantle.Env.le_of_subset $(R "hp")⟩))
    -- The types this stage declares, in this stage.
    match stages[i] with
    | .types ds =>
      for h : j in [0:ds.size] do
        let d := ds[j]
        cs := cs.push (← defCmd (mkDoc s!"`{showName d.c.envName}`, in stage {k}.") svis? false
          (mkIdent (`Internal ++ d.c.lean ++ `ref₀)) #[]
          (← `(Strata.Mantle.TypeRef $stageId $(quote d.params.size)))
          (← `(Strata.Mantle.TypeRef.ofAddTypes $prev $(R "types") $(R "fresh") $(quote j))))
        cs := cs ++ (← tyAtCmds cx stageId d.c.lean (d.params.map fun (x, _, _, k) => (x, k)))
    | .data ms =>
      for h : j in [0:ms.size] do
        let (d, ctors, _) := ms[j]
        cs := cs.push (← defCmd (mkDoc s!"`{showName d.c.envName}`, in stage {k}.") svis? false
          (mkIdent (`Internal ++ d.c.lean ++ `ref₀)) #[]
          (← `(Strata.Mantle.TypeRef $stageId $(quote d.params.size)))
          (← `(Strata.Mantle.TypeRef.ofAddData
                (Strata.Mantle.TypeRef.ofAddTypes $prev $(R "hdr") $(R "fresh") $(quote j)))))
        cs := cs ++ (← tyAtCmds cx stageId d.c.lean (d.params.map fun (x, _, _, k) => (x, k)))
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
  -- the refinement `{e : Env Unit}` and, in `T.ty` and `n.ty`, the scope `{s : Array Kind}`,
  -- which are implicit and keep these stable names so callers can pin them
  -- (`(e := Demo.env)`); and
  -- the instance `[h : RefinedBy env e]`, which instance search fills, so it is hygienic
  -- (`cx.hId`).  `T.ty` and `n.ty` bind the type's parameters beside `e` and `s` under the
  -- user's names, so a parameter named `e` or `s` would capture one of them: it is renamed
  -- by `primeAvoiding`, away from `e`, `s`, every parameter and every earlier renaming
  -- (`type T (e) (e')` binds `e''` and `e'`).  Every other parameter keeps its name.
  cs := cs.push (← `(command| section))
  cs := cs.push (← `(command| variable {e : Strata.Mantle.Env _root_.Unit}
    [$(cx.hId) : Strata.Mantle.RefinedBy $(cx.own `env) e]))
  let sBinders ← #[`s].mapM fun n =>
    `(bracketedBinder| {$(mkIdent n) : _root_.Array Strata.Mantle.Kind})
  -- A list parameter binds a list, any other a type.
  let paramBinders (xs : Array Ident) (ks : Array Kind) : CommandElabM (Array (TSyntax
      ``Lean.Parser.Term.bracketedBinder)) :=
    (xs.zip ks).mapM fun
      | (x, .list) => `(bracketedBinder| ($x : Strata.Mantle.TypeList e s))
      | (x, .type) => `(bracketedBinder| ($x : Strata.Mantle.TypeExpr e s))
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
        (← `(Strata.Mantle.TypeRef.ofLE $(cx.liftTo k)
              $(cx.own (`Internal ++ d.c.lean ++ `ref₀)))))
      cs := cs.push (← thmCmd (mkDoc s!"`{d.c.lean.toString (escape := false)}.ref` refers to \
          `{en}`.") vis? true (mkIdent (d.c.lean ++ `name_ref)) #[]
        (← `(($(cx.own (d.c.lean ++ `ref)) (e := e)).name = $(cx.own (d.c.lean ++ `name))))
        (← `(by rw [$(cx.own (d.c.lean ++ `ref)):ident,
                Strata.Mantle.name_TypeRef_ofLE $(cx.liftTo k)] <;> rfl)))
      cs := cs.push (← thmCmd (mkDoc s!"`{d.c.lean.toString (escape := false)}.ref`'s \
          declaration.") vis? true (mkIdent (d.c.lean ++ `decl_ref)) #[]
        (← `(($(cx.own (d.c.lean ++ `ref)) (e := e)).decl =
              $(← typeDeclTerm (cx.own (d.c.lean ++ `name))
                  (d.params.map fun (x, _, b, k) => (x, b, k)))))
        (← `(by rw [$(cx.own (d.c.lean ++ `ref)):ident,
                Strata.Mantle.decl_TypeRef_ofLE $(cx.liftTo k)] <;> rfl)))
      let xs := varIdents (d.params.map (·.1))
      let ks := d.params.map (·.2.2.2)
      let refT := cx.own (d.c.lean ++ `ref)
      -- `decl_ref` exposes the declaration, whose kinds `rfl` computes.
      let kindsPf := EmitCtx.declKinds cx.envNs d.c.lean (mkIdent `e) (ks.all (· == .type))
      let body ← if ks.all (· == .type) then
          `(Strata.Mantle.TypeExpr.app $refT #v[$(xs.map fun x => (x : Term)),*] $kindsPf)
        else
          let as ← (xs.zip ks).mapM fun
            | (x, .list) => `(Strata.Mantle.TypeArg.list $x)
            | (x, .type) => `(Strata.Mantle.TypeArg.ty $x)
          `(Strata.Mantle.TypeExpr.appK $refT #v[$as,*] $kindsPf)
      cs := cs.push (← defCmd (mkDoc s!"`{en}`, as a type expression.") vis? cx.expose
        (mkIdent (d.c.lean ++ `ty)) (sBinders ++ (← paramBinders xs ks))
        (← `(Strata.Mantle.TypeExpr e s)) body)
      -- Its raw form, for the casts' proofs: one application of `toRaw_app_of`.
      let tyApp ← `($(cx.own (d.c.lean ++ `ty)) (e := e) (s := s) $(xs.map fun x => (x : Term))*)
      let raws ← xs.mapM fun x => `(Strata.Mantle.TypeExpr.toRaw $x)
      let rawPf ← if ks.all (· == .type) then
          `(Strata.Mantle.TypeExpr.toRaw_app_of (hk := $kindsPf)
              ($(cx.own (d.c.lean ++ `name_ref)) (e := e))
              $(mapChain (xs.map fun _ => Unhygienic.run `(rfl))))
        else
          `(Strata.Mantle.TypeExpr.toRaw_appK_of (hk := $kindsPf)
              ($(cx.own (d.c.lean ++ `name_ref)) (e := e))
              $(mapChain (ks.map fun
                | .list => Unhygienic.run `(Strata.Mantle.TypeArg.toRaw_list_of rfl)
                | .type => Unhygienic.run `(Strata.Mantle.TypeArg.toRaw_ty_of rfl))))
      cs := cs.push (← thmCmd (mkDoc s!"The raw form of `{en}` applied.") vis? false
        (mkIdent (d.c.lean ++ `toRaw_ty)) (sBinders ++ (← paramBinders xs ks))
        (← `(Strata.Mantle.TypeExpr.toRaw $tyApp =
              Strata.Mantle.TypeExpr.Raw.app $(cx.own (d.c.lean ++ `name)) ⟨[$raws,*]⟩))
        rawPf)
  for (d, info) in abbrevs do
    let xs := varIdents (d.params.map (·.1))
    cs := cs.push (← defCmd (docOr d.c.doc? s!"The abbreviation `{showName d.c.envName}`.") vis?
      cx.expose (mkIdent (d.c.lean ++ `ty))
      (sBinders ++ (← paramBinders xs info.params))
      (← `(Strata.Mantle.TypeExpr e s))
      (cx.abbrevTy (xs.map fun x => (x : Term)) info.params info.body))
  -- Constructors and case instructions, as instructions: the signature written out against
  -- `e`, and the stage's reference cast to it by `InsnSig.carry_eq_of_toRaw`, node by node.
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
      let ks := d.params.map (·.2.2.2)
      let vars ← ks.zipIdx.mapM fun
        | (.type, l) => `(Strata.Mantle.TypeExpr.var $(quote l) (by decide))
        | (.list, l) => `(Strata.Mantle.TypeList.var $(quote l) (by decide))
      let ty := cx.tyGen vars ks
      let tps ← d.params.mapM fun (x, _, _, kd) => `(⟨$(quote x), $(kindTerm kd)⟩)
      -- A list parameter is the literal that splices it.
      let retR : Ty := .app (mantleName d.c.envName) (TypeExpr.Raw.vars ks)
      for c in ctors do
        let en := showName c.d.c.envName
        let sigId := mkIdent (c.d.c.lean ++ `sig)
        let args ← c.args.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
        cs := cs.push (← defCmd (mkDoc s!"The signature of `{en}`, a constructor of \
            `{showName d.c.envName}`.") vis? cx.expose sigId #[]
          (← `(Strata.Mantle.InsnSig e))
          (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
                 returnType := some $(ty retR), distinct := by simp })))
        -- `T.c` casts the stage's reference to `T.c.sig`: the derived signature's raw data, read
        -- from the group's literal, is `T.c.sig`'s.  The proof is under `exact`, so that the
        -- reference, elaborated first, fixes the signature it starts from.
        let members := ms.map (·.1.c.envName)
        let gen := cx.rawGen ks
        let hargs := bothRaw
          (Unhygienic.run `(Eq.trans Strata.Mantle.Env.argTypes_toList_ctorSig
            $(mapChain (c.args.map fun (_, t) => pairRaw (EmitCtx.rawData members t)))))
          (mapChain (c.args.map fun (_, t) => pairRaw (gen t)))
        let hret := bothRaw (Unhygienic.run `(Strata.Mantle.Env.returnType_ctorSig))
          (Unhygienic.run `(Strata.Mantle.map_some_eq_of $(gen retR)))
        cs := cs.push (← defCmd (docOr c.d.c.doc? s!"The constructor `{en}` of \
            `{showName d.c.envName}`.") vis? false (mkIdent c.d.c.lean) #[]
          (← `(Strata.Mantle.InsnRef e $(cx.own sigId.getId)))
          (← `(Strata.Mantle.InsnRef.cast
                (by exact (Strata.Mantle.InsnSig.carry_eq_of_toRaw _ rfl
                  (Eq.trans Strata.Mantle.Env.typeParams_toList_ctorSig rfl) $hargs
                  (congrArg (Option.map _) Strata.Mantle.Env.variadic_ctorSig) $hret
                  (congrArg (fun a => List.map _ (Array.toList a))
                    Strata.Mantle.Env.regions_ctorSig)
                  (congrArg (fun a => List.map _ (Array.toList a))
                    Strata.Mantle.Env.succs_ctorSig)))
                (Strata.Mantle.InsnRef.ofLE (s := $addDataTerm)
                  $(cx.liftTo k) $(cx.own (`Internal ++ c.d.c.lean ++ `ref₀))))))
    for (md, _, d) in ms do
      let en := showName d.d.c.envName
      let sigId := mkIdent (d.d.c.lean ++ `sig)
      let ks := d.d.typeParams.map (·.2.2)
      let vars ← ks.zipIdx.mapM fun
        | (.type, l) => `(Strata.Mantle.TypeExpr.var $(quote l) (by decide))
        | (.list, l) => `(Strata.Mantle.TypeList.var $(quote l) (by decide))
      let ty := cx.tyGen vars ks
      let tps ← d.d.typeParams.mapM fun (x, _, kd) => `(⟨$(quote x), $(kindTerm kd)⟩)
      let args ← d.args.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
      let succs ← d.succs.mapM fun sc => do
        let ts := sc.payload.map (argTerm ks ty)
        `(⟨$(quote sc.name), #[$ts,*]⟩)
      cs := cs.push (← defCmd (mkDoc s!"The signature of `{en}`.") vis? cx.expose sigId #[]
        (← `(Strata.Mantle.InsnSig e))
        (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
               returnType := none, succs := #[$succs,*], distinct := by simp })))
      -- `T.case` casts the stage's reference to `T.case.sig`, as a constructor does.
      let members := ms.map (·.1.c.envName)
      let gen := cx.rawGen ks
      let hargs := bothRaw (Unhygienic.run `(Strata.Mantle.Env.argTypes_toList_caseSig))
        (mapChain (d.args.map fun (_, t) => pairRaw (gen t)))
      let ctorsOf : Array RSucc := (ms.find? fun (m, _) => m.c.envName == md.c.envName).elim
        #[] fun (_, cs, _) => cs.map fun c => { name := "", payload := c.args.map (·.2) }
      let fields := mapChain (ctorsOf.map fun sc =>
        pairRaw (mapChain (sc.payload.map (EmitCtx.rawData members))))
      let hsuccs := bothRaw
        (Unhygienic.run `(Eq.trans Strata.Mantle.Env.succs_toList_caseSig $fields))
        (mapChain (d.succs.map fun sc => pairRaw (mapChain (sc.payload.map (argRaw ks gen)))))
      cs := cs.push (← defCmd (docOr d.d.c.doc? s!"Eliminate a `{showName md.c.envName}`: one \
          successor per constructor, in declaration order, each receiving its constructor's \
          fields.") vis? false (mkIdent d.d.c.lean) #[]
        (← `(Strata.Mantle.InsnRef e $(cx.own sigId.getId)))
        (← `(Strata.Mantle.InsnRef.cast
              (by exact (Strata.Mantle.InsnSig.carry_eq_of_toRaw _ rfl
                (Eq.trans Strata.Mantle.Env.typeParams_toList_caseSig rfl) $hargs
                (congrArg (Option.map _) Strata.Mantle.Env.variadic_caseSig)
                (congrArg (Option.map _) Strata.Mantle.Env.returnType_caseSig)
                (congrArg (fun a => List.map _ (Array.toList a))
                  Strata.Mantle.Env.regions_caseSig) $hsuccs))
              (Strata.Mantle.InsnRef.ofLE (s := $addDataTerm)
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
      let ks := d.d.typeParams.map (·.2.2)
      let vars ← ks.zipIdx.mapM fun
        | (.type, l) => `(Strata.Mantle.TypeExpr.var $(quote l) (by decide))
        | (.list, l) => `(Strata.Mantle.TypeList.var $(quote l) (by decide))
      let ty := cx.tyGen vars ks
      let tps ← d.d.typeParams.mapM fun (x, _, kd) => `(⟨$(quote x), $(kindTerm kd)⟩)
      let args ← d.args.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
      let variadic ← match d.variadic with
        | some (x, t) =>
          if t.kind ks == .list then `(some ⟨$(quote x), Strata.Mantle.Variadic.spread $(ty t)⟩)
          else `(some ⟨$(quote x), Strata.Mantle.Variadic.each $(ty t)⟩)
        | none => `(none)
      let regs ← d.regions.mapM fun r => do
        let ps ← r.params.mapM fun (x, t) => `(⟨$(quote x), $(ty t)⟩)
        `(⟨$(quote r.name), Strata.Mantle.RegionSig.of #[$ps,*] $(ty r.ret) (by simp)⟩)
      let succs ← d.succs.mapM fun sc => do
        let ts := sc.payload.map (argTerm ks ty)
        `(⟨$(quote sc.name), #[$ts,*]⟩)
      cs := cs.push (← defCmd (mkDoc s!"The signature of `{en}`.") vis? cx.expose sigId #[]
        (← `(Strata.Mantle.InsnSig e))
        (← `({ ann := (), typeParams := #[$tps,*], argTypes := #[$args,*],
               variadic := $variadic, returnType := $(← retTerm ty d.ret), regions := #[$regs,*],
               succs := #[$succs,*], distinct := by simp })))
      -- `o` casts the stage's reference to `o.sig`: `sig₀`, carried twice, stands for the
      -- same raw data as `o.sig`, node by node.
      let at₀ := cx.rawAt (k - 1) ks
      let gen := cx.rawGen ks
      let side (raw : Ty → Term) : Term × Term × Term × Term × Term :=
        let hargs := mapChain (d.args.map fun (_, t) => pairRaw (raw t))
        let hvar := match d.variadic with
          | some (_, t) => Unhygienic.run
              `(Strata.Mantle.map_some_eq_of $(pairRaw (argRaw ks raw t)))
          | none => Unhygienic.run `(rfl)
        let hret := match d.ret with
          | some t => Unhygienic.run `(Strata.Mantle.map_some_eq_of $(raw t))
          | none => Unhygienic.run `(rfl)
        let hregs := mapChain (d.regions.map fun r => pairRaw (Unhygienic.run
          `(Strata.Mantle.RegionSig.fields_of
              (by exact (by decide : List.Nodup
                ([$(r.params.map fun (x, _) => Syntax.mkStrLit x),*] : List String)))
              $(mapChain (r.params.map fun (_, t) => pairRaw (raw t))) $(raw r.ret))))
        let hsuccs := mapChain (d.succs.map fun sc =>
          pairRaw (mapChain (sc.payload.map (argRaw ks raw))))
        (hargs, hvar, hret, hregs, hsuccs)
      let (a₀, v₀, r₀, g₀, s₀) := side at₀
      let (a₁, v₁, r₁, g₁, s₁) := side gen
      cs := cs.push (← defCmd (mkDoc s!"`{en}`, in stage {k}.") svis? false
        (mkIdent (`Internal ++ d.d.c.lean ++ `ref₀)) #[]
        (← `(Strata.Mantle.InsnRef $(cx.stage k)
              (Strata.Mantle.InsnSig.ofLE
                (Strata.Mantle.Env.le_of_subset $(cx.internal s!"hst{k}"))
                $(cx.own (`Internal ++ d.d.c.lean ++ `sig₀)))))
        (← `(Strata.Mantle.InsnRef.ofAddInsns $(cx.internal s!"ops{k}")
              $(cx.internal s!"fresh{k}") $(quote j)
              (Nat.lt_of_lt_of_eq (by decide : ($(quote j) : Nat) < $(quote ds.size))
                $(cx.internal s!"ops_size{k}").symm))))
      cs := cs.push (← defCmd (docOr d.d.c.doc? s!"The instruction `{en}`.") vis? false
        (mkIdent d.d.c.lean) #[] (← `(Strata.Mantle.InsnRef e $(cx.own sigId.getId)))
        (← `(Strata.Mantle.InsnRef.cast
              (by exact (Eq.trans (Strata.Mantle.InsnSig.carry_carry _ _ _)
                (Strata.Mantle.InsnSig.carry_eq_of_toRaw _ rfl rfl $(bothRaw a₀ a₁)
                  $(bothRaw v₀ v₁) $(bothRaw r₀ r₁) $(bothRaw g₀ g₁) $(bothRaw s₀ s₁))))
              (Strata.Mantle.InsnRef.ofLE $(cx.liftTo k)
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
      unless env.contains `Strata.Mantle.RefinedBy do
        err kw "an environment needs `public import StrataMantle.Env.Refine`"
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
  -- The parent's `nameSet` is built as its stages built it: each ancestor's names, farthest
  -- first, in the order its stages add them.
  let parentKeys := (ancestors.reverse.flatMap (·.order)).map nameKey
  -- The instance binder, hygienic: one fresh macro scope, shared by every command.
  let hId := mkIdent (← withFreshMacroScope (MonadQuotation.addMacroScope `h))
  let cx : EmitCtx :=
    { envNs, envShort, parent, vis?, expose := isPublic && isModule, m := res.stages.size,
      ownTypes := res.own, inherited, parentNames, allNames := names ++ parentNames,
      parentKeys, hId }
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
      abbrevs := res.abbrevs.map (·.2), ops, names, order := res.stages.flatMap stageNames }
  modifyEnv (envEntries.addEntry · entry)

elab_rules : command
  | `($[$doc?:docComment]? $[$vis?:visibility]? environment%$kw $e:ident $[extends $p?:ident]?
      where $ds:mantleDecl*) =>
    elabEnvironment doc? vis? kw e p? ds

end Strata.Mantle.DSL

end
