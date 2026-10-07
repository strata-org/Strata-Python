/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.Raw
import StrataMantle.Env.DataProps
import StrataMantle.Env.TypeExprRawProps

set_option autoImplicit false

/-!
# Well-formedness of declarations and environments

An environment is well formed when every type reference in every declaration
resolves to a type declaration that appears *strictly earlier* in the environment,
so the reference graph is acyclic by construction.

`checkDecl` decides the obligations of one declaration and `checkFrom` those of a
batch, left to right.  Their soundness lemmas are `WF.appendChecked`, `WF.appendList` and
`wf_ofAscArray`.  The checks consult the environment's hash map, so they run in compiled
code (`native_decide`) but not in the kernel.
-/

open Strata (IndexMap)

namespace Strata.Mantle

public section

variable {α : Type}

/-! ## Well-formedness of an environment

An `Env.Raw α` is an *ordered* map: a declaration may only mention type declarations that
precede it.  The specification (`Env.Raw.WF`) is indexed by a position in `env.decls.keys`,
and the checker (`Env.Raw.checkFrom`) runs over the declaration list, checking each
declaration at the position it takes.  `Env.Raw.wf_ofAscArray` joins the two.  A checked
`TypeExpr` carries `TypeExpr.WFRel` against `RefBefore`.
-/

namespace TypeExpr

/-- Well-formedness of a `TypeExpr.Raw` relative to an abstract *resolver*:
`R name n` reads "`name` is a type declaration of arity `n` that this expression
is allowed to mention".  Growing the environment or the scope is `WFRel.mono`. -/
inductive WFRel (R : Name → Nat → Prop) (scope : Nat) : Raw → Prop
  | var {i : Nat} (lt : i < scope) : WFRel R scope (.var i)
  | app {name : Name} {args : Array Raw}
      (ref : R name args.size)
      (argsWF : ∀ a ∈ args, WFRel R scope a) : WFRel R scope (.app name args)

theorem WFRel.mono {R R' : Name → Nat → Prop} {scope scope' : Nat} {e : Raw}
    (hR : ∀ n a, R n a → R' n a) (hs : scope ≤ scope') (h : WFRel R scope e) :
    WFRel R' scope' e := by
  induction h with
  | var lt => exact .var (Nat.lt_of_lt_of_le lt hs)
  | app ref _ ih => exact .app (hR _ _ ref) ih

/-- What an application's well-formedness says about its head. -/
theorem WFRel.refBefore {R : Name → Nat → Prop} {scope : Nat} {n : Name} {as : Array Raw}
    (h : WFRel R scope (.app n as)) : R n as.size := by
  cases h with | app ref _ => exact ref

/-- What an application's well-formedness says about its arguments. -/
theorem WFRel.args {R : Name → Nat → Prop} {scope : Nat} {n : Name} {as : Array Raw}
    (h : WFRel R scope (.app n as)) : ∀ a ∈ as, WFRel R scope a := by
  cases h with | app _ hargs => exact hargs

/-- Instantiating every variable in scope by a closed type gives a closed type. -/
theorem WFRel.instantiate {R : Name → Nat → Prop} {scope : Nat} {args : Array Raw}
    (hargs : ∀ a ∈ args, WFRel R 0 a) (hn : scope ≤ args.size) {e : Raw}
    (h : WFRel R scope e) : WFRel R 0 (e.instantiate args) := by
  induction h with
  | @var i lt =>
    have hi : i < args.size := Nat.lt_of_lt_of_le lt hn
    simpa [Raw.instantiate, Array.getElem?_eq_getElem hi] using hargs _ (Array.getElem_mem hi)
  | app ref _ ih =>
    rw [Raw.instantiate_app]
    refine .app (by simpa using ref) (fun a ha => ?_)
    obtain ⟨b, hb, rfl⟩ := Array.mem_map.mp ha
    exact ih b hb

end TypeExpr

namespace Decl.Raw

end Decl.Raw

namespace RegionSig.Raw

/-- A region signature is well formed under `scope` type variables when its parameter types
and its return type are, and its parameters are named distinctly.  `scope` is the enclosing
instruction's `typeArgc`: a region binds no type variables of its own. -/
def WF (R : Name → Nat → Prop) (scope : Nat) (r : RegionSig.Raw) : Prop :=
  (∀ p ∈ r.params, TypeExpr.WFRel R scope p.type)
    ∧ TypeExpr.WFRel R scope r.returnType
    ∧ r.paramNames.Nodup

/-- Build well-formedness from the three component obligations. -/
theorem wf_mk {R : Name → Nat → Prop} {scope : Nat} {r : RegionSig.Raw}
    (hparams : ∀ p ∈ r.params, TypeExpr.WFRel R scope p.type)
    (hret : TypeExpr.WFRel R scope r.returnType)
    (hnames : r.paramNames.Nodup) : WF R scope r :=
  ⟨hparams, hret, hnames⟩

/-- The parameter types of a well-formed region signature are well formed. -/
theorem wf_params {R : Name → Nat → Prop} {scope : Nat} {r : RegionSig.Raw}
    (h : WF R scope r) : ∀ p ∈ r.params, TypeExpr.WFRel R scope p.type := h.1

/-- The return type of a well-formed region signature is well formed. -/
theorem wf_returnType {R : Name → Nat → Prop} {scope : Nat} {r : RegionSig.Raw}
    (h : WF R scope r) : TypeExpr.WFRel R scope r.returnType := h.2.1

/-- The parameters of a well-formed region signature are named distinctly. -/
theorem wf_paramNames {R : Name → Nat → Prop} {scope : Nat} {r : RegionSig.Raw}
    (h : WF R scope r) : r.paramNames.Nodup := h.2.2

/-- A region signature stays well formed when the resolver accepts more. -/
theorem WF.mono {R R' : Name → Nat → Prop} {scope : Nat} {r : RegionSig.Raw}
    (hR : ∀ n a, R n a → R' n a) (h : r.WF R scope) : r.WF R' scope :=
  ⟨fun p hp => (h.1 p hp).mono hR (Nat.le_refl _), h.2.1.mono hR (Nat.le_refl _), h.2.2⟩

end RegionSig.Raw

namespace InsnDecl.Raw

/-- An instruction is well formed when its parameter types, its variadic's element type,
its return type if it has one, the signature of each region it takes and the payload types of each
successor are, each under the `typeArgc` de Bruijn variables the instruction binds; and when
the names it binds (type parameters, arguments, the variadic, regions and successors) are
pairwise distinct. -/
def WF (R : Name → Nat → Prop) (d : InsnDecl.Raw α) : Prop :=
  (∀ p ∈ d.argTypes, TypeExpr.WFRel R d.typeArgc p.type)
    ∧ (∀ v ∈ d.variadic, TypeExpr.WFRel R d.typeArgc v.type)
    ∧ (∀ t ∈ d.returnType, TypeExpr.WFRel R d.typeArgc t)
    ∧ (∀ r ∈ d.regions, r.type.WF R d.typeArgc)
    ∧ (∀ s ∈ d.succs, ∀ t ∈ s.type, TypeExpr.WFRel R d.typeArgc t)
    ∧ d.paramNames.Nodup

/-- Build well-formedness from the six component obligations. -/
theorem wf_mk {R : Name → Nat → Prop} {d : InsnDecl.Raw α}
    (hargs : ∀ p ∈ d.argTypes, TypeExpr.WFRel R d.typeArgc p.type)
    (hvar : ∀ v ∈ d.variadic, TypeExpr.WFRel R d.typeArgc v.type)
    (hret : ∀ t ∈ d.returnType, TypeExpr.WFRel R d.typeArgc t)
    (hregions : ∀ r ∈ d.regions, r.type.WF R d.typeArgc)
    (hsuccs : ∀ s ∈ d.succs, ∀ t ∈ s.type, TypeExpr.WFRel R d.typeArgc t)
    (hnames : d.paramNames.Nodup) : WF R d :=
  ⟨hargs, hvar, hret, hregions, hsuccs, hnames⟩

/-- The argument types of a well-formed instruction are well formed. -/
theorem wf_argTypes {R : Name → Nat → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ p ∈ d.argTypes, TypeExpr.WFRel R d.typeArgc p.type := h.1

/-- The variadic element type of a well-formed instruction, if any, is well formed. -/
theorem wf_variadic {R : Name → Nat → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ v ∈ d.variadic, TypeExpr.WFRel R d.typeArgc v.type := h.2.1

/-- The return type of a well-formed instruction, if any, is well formed. -/
theorem wf_returnType {R : Name → Nat → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ t ∈ d.returnType, TypeExpr.WFRel R d.typeArgc t := h.2.2.1

/-- Every region signature of a well-formed instruction is well formed, under the
instruction's type variables. -/
theorem wf_regions {R : Name → Nat → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ r ∈ d.regions, r.type.WF R d.typeArgc := h.2.2.2.1

/-- Every payload type of every successor of a well-formed instruction is well formed, under
the instruction's type variables. -/
theorem wf_succs {R : Name → Nat → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ s ∈ d.succs, ∀ t ∈ s.type, TypeExpr.WFRel R d.typeArgc t := h.2.2.2.2.1

/-- No two of the type parameters, arguments, variadic, regions and successors of a
well-formed instruction share a name. -/
theorem wf_paramNames {R : Name → Nat → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    d.paramNames.Nodup := h.2.2.2.2.2

/-- An instruction stays well formed when the resolver accepts more. -/
theorem WF.mono {R R' : Name → Nat → Prop} {d : InsnDecl.Raw α}
    (hR : ∀ n a, R n a → R' n a) (h : d.WF R) : d.WF R' :=
  ⟨fun p hp => (h.1 p hp).mono hR (Nat.le_refl _),
   fun t ht => (h.2.1 t ht).mono hR (Nat.le_refl _),
   fun t ht => (h.2.2.1 t ht).mono hR (Nat.le_refl _),
   fun r hr => (h.2.2.2.1 r hr).mono hR,
   fun s hs t ht => (h.2.2.2.2.1 s hs t ht).mono hR (Nat.le_refl _),
   h.2.2.2.2.2⟩

end InsnDecl.Raw

namespace Decl.Raw

/-- A declaration is well formed when the declaration it wraps is: a primitive type names
its parameters distinctly, and an instruction, a constructor included, is well formed. -/
def WF (R : Name → Nat → Prop) : Decl.Raw α → Prop
  | .type d => d.paramNames.Nodup
  -- `R` does not know a group's own members: `Env.Raw.checkGroup` checks the group, and a
  -- member alias checks nothing.
  | .dataHead _ => True
  | .dataRest .. => True
  | .insn d => InsnDecl.Raw.WF R d

theorem WF.mono {R R' : Name → Nat → Prop} {d : Decl.Raw α}
    (hR : ∀ n a, R n a → R' n a) (h : d.WF R) : d.WF R' := by
  cases d with
  | type t => exact h
  | dataHead g => trivial
  | dataRest _ _ _ => trivial
  | insn i => exact InsnDecl.Raw.WF.mono hR h

/-- A type declaration has no body, so it is well formed under any relation once its
parameters are named distinctly. -/
@[simp] theorem wf_type_iff {R : Name → Nat → Prop} {d : TypeDecl α} :
    WF R (.type d) ↔ d.paramNames.Nodup := Iff.rfl

@[simp] theorem wf_dataHead {R : Name → Nat → Prop} (g : DataGroup α TypeExpr.Raw) :
    WF R (.dataHead g) := trivial

@[simp] theorem wf_dataRest {R : Name → Nat → Prop} (n h : Name) (i : Nat) :
    WF R (.dataRest (α := α) n h i) := trivial

/-- Well-formedness of a wrapped instruction declaration is the instruction's own. -/
@[simp] theorem wf_insn_iff {R : Name → Nat → Prop} {d : InsnDecl.Raw α} :
    WF R (.insn d) ↔ InsnDecl.Raw.WF R d := Iff.rfl

end Decl.Raw

namespace Env.Raw

/-- `name` resolves to a type declaration of arity `arity` that occurs *strictly
before* position `i` of the environment. -/
def RefBefore (env : Env.Raw α) (i : Nat) (name : Name) (arity : Nat) : Prop :=
  match (env.types.before i)[name]? with
  | some t => t.arity = arity
  | none => False

/-- The `types.before` lookup in positional terms. -/
theorem getElem?_types_before {env : Env.Raw α} {i : Nat} {name : Name} :
    (env.types.before i)[name]? =
      (IndexMap.idxOf? env.decls name).bind
        (fun j => if j < i then (env.decls[name]?).bind env.typeOfDecl? else none) := by
  show (env.types.before i).get? name = _
  unfold SubEnv.get? SubEnv.before
  simp only [decls_types, pred_types]
  cases IndexMap.idxOf? env.decls name with
  | none => simp
  | some j => simp only [Option.bind_some]; split <;> simp [*]

/-- `RefBefore` holds exactly when the `before` view yields a type of that arity. -/
theorem refBefore_iff_getElem? {env : Env.Raw α} {i : Nat} {name : Name} {arity : Nat} :
    env.RefBefore i name arity ↔
      ∃ t, (env.types.before i)[name]? = some t ∧ t.arity = arity := by
  unfold RefBefore
  cases hv : (env.types.before i)[name]? <;> simp

/-- `RefBefore` spelled out positionally: the name has a position before `i`, and what is
declared there denotes a type of the right arity, a group member or a group head. -/
theorem refBefore_iff {env : Env.Raw α} {i : Nat} {name : Name} {arity : Nat} :
    env.RefBefore i name arity ↔
      ∃ j t, IndexMap.idxOf? env.decls name = some j ∧ j < i ∧
        env.typeOf? name = some t ∧ t.arity = arity := by
  rw [refBefore_iff_getElem?]
  simp only [getElem?_types_before]
  constructor
  · intro ⟨t, hv, ha⟩
    cases hj : IndexMap.idxOf? env.decls name with
    | none => rw [hj] at hv; simp at hv
    | some j =>
      rw [hj] at hv
      simp only [Option.bind_some] at hv
      split at hv
      · exact ⟨j, t, rfl, by assumption, hv, ha⟩
      · simp at hv
  · intro ⟨j, t, hj, hji, hget, ha⟩
    refine ⟨t, ?_, ha⟩
    rw [hj]
    simp only [Option.bind_some, if_pos hji]
    exact hget

/-- Everything declared is declared before the end, so a type it denotes is in the
`before` view of any position at or past the end. -/
theorem typesBefore_of_typeOf? {env : Env.Raw α} {n : Name} {d : TypeDecl α} {i : Nat}
    (h : env.typeOf? n = some d) (hi : env.decls.keys.size ≤ i) :
    (env.types.before i)[n]? = some d := by
  have hm : n ∈ env.decls := by
    unfold typeOf? at h
    cases hx : env.decls[n]? with
    | none => rw [hx] at h; simp at h
    | some e => exact IndexMap.mem_of_getElem?_eq_some hx
  have hs : (IndexMap.idxOf? env.decls n).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]
    simpa using hm
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
  have hplt : p < env.decls.keys.size :=
    (Array.getElem?_eq_some_iff.mp (IndexMap.getElem?_keys_of_idxOf?_eq_some hp)).1
  rw [getElem?_types_before, hp, Option.bind_some, if_pos (by omega)]
  exact h

/-- What the `before` view yields is what the name denotes. -/
theorem typeOf?_of_typesBefore {env : Env.Raw α} {n : Name} {d : TypeDecl α} {i : Nat}
    (h : (env.types.before i)[n]? = some d) : env.typeOf? n = some d := by
  rw [getElem?_types_before] at h
  cases hp : IndexMap.idxOf? env.decls n with
  | none => rw [hp] at h; simp at h
  | some p =>
    rw [hp, Option.bind_some] at h
    split at h
    · exact h
    · simp at h

theorem RefBefore.mono {env : Env.Raw α} {i j : Nat} (h : i ≤ j) {name : Name} {arity : Nat}
    (hr : env.RefBefore i name arity) : env.RefBefore j name arity := by
  obtain ⟨k, t, hk, hki, hget, ha⟩ := refBefore_iff.mp hr
  exact refBefore_iff.mpr ⟨k, t, hk, Nat.lt_of_lt_of_le hki h, hget, ha⟩

end Env.Raw

/-! ### Checking an environment

A declaration is checked against the environment itself: `RefBefore` is a hash-map lookup
plus a position comparison.  None of this reduces in the kernel, because `String.hash` is
`opaque`; obligations are discharged by `native_decide` or by a tactic. -/

namespace Env.Raw

/-- Decision procedure for `RefBefore`: one lookup in `types.before i`. -/
@[expose]
def RefBefore.check (env : Env.Raw α) (i : Nat) (name : Name) (arity : Nat) : Bool :=
  match (env.types.before i)[name]? with
  | some t => t.arity == arity
  | none => false

@[simp] theorem refBefore_check_eq_true {env : Env.Raw α} {i : Nat} {name : Name} {arity : Nat} :
    RefBefore.check env i name arity = true ↔ env.RefBefore i name arity := by
  unfold RefBefore.check RefBefore
  cases (env.types.before i)[name]? <;> simp

end Env.Raw

namespace TypeExpr.Raw

mutual
/-- Decision procedure for `WFRel`, abstracted over the resolver as `WFRel` is: `R name n`
decides "this expression may mention `name` as a type of arity `n`".  Arguments are matched
through `Array.mk`, which keeps both functions structurally recursive. -/
@[expose]
def check (R : Name → Nat → Bool) (scope : Nat) : Raw → Bool
  | .var k => k < scope
  | .app name ⟨args⟩ => R name args.length && checkList R scope args

@[expose]
def checkList (R : Name → Nat → Bool) (scope : Nat) : List Raw → Bool
  | [] => true
  | e :: es => check R scope e && checkList R scope es
end

mutual
theorem wfRel_of_check {R : Name → Nat → Bool} {Rel : Name → Nat → Prop}
    (hR : ∀ n a, R n a = true → Rel n a) {scope : Nat} :
    ∀ (e : Raw), check R scope e = true → WFRel Rel scope e
  | .var _, h => .var (by simpa [check] using h)
  | .app _ ⟨args⟩, h => by
    simp only [check, Bool.and_eq_true] at h
    exact .app (hR _ _ (by simpa using h.1))
      (fun a ha => wfRel_of_checkList hR args h.2 a (by simpa using ha))
termination_by e _ => sizeOf e
decreasing_by all_goals (simp_wf; omega)

theorem wfRel_of_checkList {R : Name → Nat → Bool} {Rel : Name → Nat → Prop}
    (hR : ∀ n a, R n a = true → Rel n a) {scope : Nat} :
    ∀ (es : List Raw), checkList R scope es = true → ∀ a ∈ es, WFRel Rel scope a
  | [], _ => by simp
  | e :: es, h => by
    simp only [checkList, Bool.and_eq_true] at h
    -- both recursive calls are made here, on syntactic `e` and `es`, so that the decreasing
    -- goals mention those rather than a variable a later `rcases` substituted
    have he : WFRel Rel scope e := wfRel_of_check hR e h.1
    have hes : ∀ a ∈ es, WFRel Rel scope a := wfRel_of_checkList hR es h.2
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact hes a ha
-- The `+ 1` is what makes the step out of `app` decrease: `sizeOf (.app n ⟨args⟩)` counts the
-- `Array.mk` wrapper, which 4.31's automatic measure does not see through.
termination_by es _ => sizeOf es + 1
decreasing_by all_goals (simp_wf; omega)
end

/-! ### Datatype payloads

A constructor's payload is checked against three things, none of which is an environment: a
resolver `R` for the positions where recursion is allowed, a resolver `Rneg` for the
positions where it is not, and a lookup `paramsOf` giving each type constructor's parameter
polarity. -/

mutual
/-- Whether de Bruijn level `l` occurs in the expression at all.  Inspects only `var`
nodes. -/
@[expose]
def varOccurs (l : Nat) : Raw → Bool
  | .var k => k == l
  | .app _ ⟨args⟩ => varOccursList l args

@[expose]
def varOccursList (l : Nat) : List Raw → Bool
  | [] => false
  | e :: es => varOccurs l e || varOccursList l es
end

mutual
/-- Whether every occurrence of level `l` sits in a parameter declared `.pos`. -/
@[expose]
def varPositive (paramsOf : Name → Option (Array (Param Positivity))) (l : Nat) : Raw → Bool
  | .var _ => true
  | .app n ⟨args⟩ =>
    match paramsOf n with
    | none => false
    | some ⟨ps⟩ => ps.length == args.length && varPositiveArgs paramsOf l ps args

@[expose]
def varPositiveArgs (paramsOf : Name → Option (Array (Param Positivity))) (l : Nat) :
    List (Param Positivity) → List Raw → Bool
  | [], [] => true
  | ⟨_, .pos⟩ :: ps, e :: es => varPositive paramsOf l e && varPositiveArgs paramsOf l ps es
  | ⟨_, .non⟩ :: ps, e :: es => !varOccurs l e && varPositiveArgs paramsOf l ps es
  | _, _ => false
end

mutual
/-- Whether a payload is well formed *and* keeps its recursion positive.

`R` applies where recursion is allowed.  Passing through a parameter declared `.non`
switches to `Rneg`, `R` with the group's own types withheld, for the rest of the subterm. -/
@[expose]
def checkPayload (paramsOf : Name → Option (Array (Param Positivity)))
    (R Rneg : Name → Nat → Bool) (scope : Nat) : Raw → Bool
  | .var k => k < scope
  | .app n ⟨args⟩ =>
    R n args.length &&
      (match paramsOf n with
       | none => false
       | some ⟨ps⟩ =>
         ps.length == args.length && checkPayloadArgs paramsOf R Rneg scope ps args)

@[expose]
def checkPayloadArgs (paramsOf : Name → Option (Array (Param Positivity)))
    (R Rneg : Name → Nat → Bool) (scope : Nat) : List (Param Positivity) → List Raw → Bool
  | [], [] => true
  | ⟨_, .pos⟩ :: ps, e :: es =>
    checkPayload paramsOf R Rneg scope e && checkPayloadArgs paramsOf R Rneg scope ps es
  | ⟨_, .non⟩ :: ps, e :: es =>
    check Rneg scope e && checkPayloadArgs paramsOf R Rneg scope ps es
  | _, _ => false
end

/-! ### Monotonicity

Each traversal accepts more when its resolvers accept more and its parameter lookup keeps
answering what it answered. -/

mutual
theorem check_mono {R R' : Name → Nat → Bool} (hR : ∀ n a, R n a = true → R' n a = true)
    {scope : Nat} : ∀ e : Raw, check R scope e = true → check R' scope e = true
  | .var _, h => by simpa [check] using h
  | .app _ ⟨args⟩, h => by
    simp only [check, Bool.and_eq_true] at h ⊢
    exact ⟨hR _ _ h.1, checkList_mono hR args h.2⟩

theorem checkList_mono {R R' : Name → Nat → Bool} (hR : ∀ n a, R n a = true → R' n a = true)
    {scope : Nat} : ∀ es : List Raw, checkList R scope es = true →
      checkList R' scope es = true
  | [], _ => by simp [checkList]
  | e :: es, h => by
    simp only [checkList, Bool.and_eq_true] at h ⊢
    exact ⟨check_mono hR e h.1, checkList_mono hR es h.2⟩
end

mutual
/-- `varPositive` accepts more when the parameter lookup keeps its answers. -/
theorem varPositive_mono {P P' : Name → Option (Array (Param Positivity))}
    (hp : ∀ n ps, P n = some ps → P' n = some ps) {l : Nat} :
    ∀ e : Raw, varPositive P l e = true → varPositive P' l e = true
  | .var _, _ => by simp [varPositive]
  | .app n ⟨args⟩, h => by
    simp only [varPositive] at h ⊢
    cases hn : P n with
    | none => rw [hn] at h; simp at h
    | some ps =>
      obtain ⟨ps⟩ := ps
      rw [hn] at h
      rw [hp n _ hn]
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨h.1, varPositiveArgs_mono hp ps args h.2⟩

/-- The list form of `varPositive_mono`. -/
theorem varPositiveArgs_mono {P P' : Name → Option (Array (Param Positivity))}
    (hp : ∀ n ps, P n = some ps → P' n = some ps) {l : Nat} :
    ∀ (ps : List (Param Positivity)) (es : List Raw), varPositiveArgs P l ps es = true →
      varPositiveArgs P' l ps es = true
  | [], [], _ => by simp [varPositiveArgs]
  | ⟨_, .pos⟩ :: ps, e :: es, h => by
    simp only [varPositiveArgs, Bool.and_eq_true] at h ⊢
    exact ⟨varPositive_mono hp e h.1, varPositiveArgs_mono hp ps es h.2⟩
  | ⟨_, .non⟩ :: ps, e :: es, h => by
    simp only [varPositiveArgs, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, varPositiveArgs_mono hp ps es h.2⟩
  | [], _ :: _, h => by simp [varPositiveArgs] at h
  | _ :: _, [], h => by simp [varPositiveArgs] at h
end

mutual
/-- `checkPayload` accepts more when its resolvers do and its lookup keeps its answers. -/
theorem checkPayload_mono {P P' : Name → Option (Array (Param Positivity))}
    {R R' N N' : Name → Nat → Bool}
    (hp : ∀ n ps, P n = some ps → P' n = some ps)
    (hR : ∀ n a, R n a = true → R' n a = true)
    (hN : ∀ n a, N n a = true → N' n a = true) {scope : Nat} :
    ∀ e : Raw, checkPayload P R N scope e = true → checkPayload P' R' N' scope e = true
  | .var _, h => by simpa [checkPayload] using h
  | .app n ⟨args⟩, h => by
    simp only [checkPayload, Bool.and_eq_true] at h ⊢
    obtain ⟨hr, hrest⟩ := h
    refine ⟨hR _ _ hr, ?_⟩
    cases hn : P n with
    | none => rw [hn] at hrest; simp at hrest
    | some ps =>
      obtain ⟨ps⟩ := ps
      rw [hn] at hrest
      rw [hp n _ hn]
      simp only [Bool.and_eq_true] at hrest ⊢
      exact ⟨hrest.1, checkPayloadArgs_mono hp hR hN ps args hrest.2⟩

/-- The list form of `checkPayload_mono`. -/
theorem checkPayloadArgs_mono {P P' : Name → Option (Array (Param Positivity))}
    {R R' N N' : Name → Nat → Bool}
    (hp : ∀ n ps, P n = some ps → P' n = some ps)
    (hR : ∀ n a, R n a = true → R' n a = true)
    (hN : ∀ n a, N n a = true → N' n a = true) {scope : Nat} :
    ∀ (ps : List (Param Positivity)) (es : List Raw), checkPayloadArgs P R N scope ps es = true →
      checkPayloadArgs P' R' N' scope ps es = true
  | [], [], _ => by simp [checkPayloadArgs]
  | ⟨_, .pos⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h ⊢
    exact ⟨checkPayload_mono hp hR hN e h.1, checkPayloadArgs_mono hp hR hN ps es h.2⟩
  | ⟨_, .non⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h ⊢
    exact ⟨check_mono hN e h.1, checkPayloadArgs_mono hp hR hN ps es h.2⟩
  | [], _ :: _, h => by simp [checkPayloadArgs] at h
  | _ :: _, [], h => by simp [checkPayloadArgs] at h
end

mutual
/-- A payload that keeps its recursion positive is well formed against `R`, when what a
`.non` position may refer to `R` accepts too.  So a constructor's payload is an argument type
its instruction may declare. -/
theorem check_of_checkPayload {P : Name → Option (Array (Param Positivity))}
    {R N : Name → Nat → Bool} (hN : ∀ n a, N n a = true → R n a = true) {scope : Nat} :
    ∀ e : Raw, checkPayload P R N scope e = true → check R scope e = true
  | .var _, h => by simpa [checkPayload, check] using h
  | .app n ⟨args⟩, h => by
    simp only [checkPayload, Bool.and_eq_true] at h
    obtain ⟨hr, hrest⟩ := h
    simp only [check, Bool.and_eq_true]
    refine ⟨hr, ?_⟩
    cases hn : P n with
    | none => rw [hn] at hrest; simp at hrest
    | some ps =>
      obtain ⟨ps⟩ := ps
      rw [hn] at hrest
      simp only [Bool.and_eq_true] at hrest
      exact checkList_of_checkPayloadArgs hN ps args hrest.2

/-- The list form of `check_of_checkPayload`. -/
theorem checkList_of_checkPayloadArgs {P : Name → Option (Array (Param Positivity))}
    {R N : Name → Nat → Bool} (hN : ∀ n a, N n a = true → R n a = true) {scope : Nat} :
    ∀ (ps : List (Param Positivity)) (es : List Raw), checkPayloadArgs P R N scope ps es = true →
      checkList R scope es = true
  | [], [], _ => rfl
  | ⟨_, .pos⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h
    simp only [checkList, Bool.and_eq_true]
    exact ⟨check_of_checkPayload hN e h.1, checkList_of_checkPayloadArgs hN ps es h.2⟩
  | ⟨_, .non⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h
    simp only [checkList, Bool.and_eq_true]
    exact ⟨check_mono hN e h.1, checkList_of_checkPayloadArgs hN ps es h.2⟩
  | [], _ :: _, h => by simp [checkPayloadArgs] at h
  | _ :: _, [], h => by simp [checkPayloadArgs] at h
end

/-- An application is well formed when its head is accepted at its argument count and every
argument is well formed. -/
theorem check_app {R : Name → Nat → Bool} {scope : Nat} {n : Name} {as : Array Raw} :
    check R scope (.app n as) = true ↔ R n as.size = true ∧ ∀ a ∈ as, check R scope a = true := by
  obtain ⟨as⟩ := as
  have hl : ∀ l : List Raw, checkList R scope l = true ↔ ∀ a ∈ l, check R scope a = true := by
    intro l; induction l <;> simp_all [checkList]
  simp [check, hl]

/-- The converse of `wfRel_of_check`: a well-formed expression passes the check of any
resolver that accepts what the relation does. -/
theorem check_of_wfRel {R : Name → Nat → Bool} {Rel : Name → Nat → Prop}
    (hR : ∀ n a, Rel n a → R n a = true) {scope : Nat} {e : Raw}
    (h : TypeExpr.WFRel Rel scope e) : check R scope e = true := by
  induction h with
  | var lt => simpa [check] using lt
  | app ref _ ih => exact check_app.mpr ⟨hR _ _ ref, ih⟩

/-- The declared-before-use resolver, against which a declaration outside a mutual group is
checked. -/
@[expose]
def checkAt (env : Env.Raw α) (i : Nat) (scope : Nat) : Raw → Bool :=
  check (Env.Raw.RefBefore.check env i) scope

theorem wfRel_of_checkAt {env : Env.Raw α} {i scope : Nat} (e : Raw)
    (h : checkAt env i scope e = true) : WFRel (env.RefBefore i) scope e :=
  wfRel_of_check (fun _ _ hb => Env.Raw.refBefore_check_eq_true.mp hb) e h

end TypeExpr.Raw

namespace DataGroup

/-! ### What a mutual group owes, abstractly

A group is checked against three resolvers and nothing else: what a name's parameters are,
what a payload position may refer to, and what a `.non` position may refer to. -/

/-- Every payload of every constructor of every member resolves, keeps its recursion in
parameters declared `.pos`, and respects what its own member declared about its parameters. -/
@[expose]
def checkWith (g : DataGroup α TypeExpr.Raw)
    (paramsOf : Name → Option (Array (Param Positivity)))
    (inGroup outside : Name → Nat → Bool) : Bool :=
  g.members.all fun m =>
    m.ctors.all fun c =>
      c.args.all fun p =>
        TypeExpr.Raw.checkPayload paramsOf inGroup outside m.arity p.type
          && m.params.zipIdx.all fun (pol, k) =>
              match pol.type with
              | .pos => TypeExpr.Raw.varPositive paramsOf k p.type
              | .non => true

/-- Every name a group binds is bound once where it is bound: each member's parameters are
named distinctly, and so is everything each constructor's instruction binds, the member's
parameters then the payload's fields, and everything its case instruction binds, the member's
parameters, `scrutinee` and one successor per constructor. -/
@[expose]
def checkNames (g : DataGroup α TypeExpr.Raw) : Bool :=
  g.members.all fun m =>
    decide m.paramNames.Nodup &&
      (m.ctors.all fun c => decide (m.paramNames ++ c.args.toList.map (·.name)).Nodup) &&
      decide (m.paramNames ++ ["scrutinee"] ++ m.ctors.toList.map (·.name.lastString)).Nodup

theorem checkWith_mono {g : DataGroup α TypeExpr.Raw}
    {P P' : Name → Option (Array (Param Positivity))} {R R' N N' : Name → Nat → Bool}
    (hp : ∀ n ps, P n = some ps → P' n = some ps)
    (hR : ∀ n a, R n a = true → R' n a = true)
    (hN : ∀ n a, N n a = true → N' n a = true)
    (h : g.checkWith P R N = true) : g.checkWith P' R' N' = true := by
  simp only [checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true] at h ⊢
  intro m hm c hc p hpm
  obtain ⟨hpay, hpol⟩ := h m hm c hc p hpm
  refine ⟨TypeExpr.Raw.checkPayload_mono hp hR hN _ hpay, ?_⟩
  intro x hx
  have := hpol x hx
  match x with
  | (⟨_, .pos⟩, _) => exact TypeExpr.Raw.varPositive_mono hp _ this
  | (⟨_, .non⟩, _) => rfl

end DataGroup

namespace Env.Raw

/-! ### What a mutual group owes, and what an alias owes -/

/-- What the type constructor `n` says about its parameters, among the types declared before
position `j`. -/
@[expose]
def paramsBefore (env : Env.Raw α) (j : Nat) (n : Name) :
    Option (Array (Param Positivity)) :=
  ((env.types.before j)[n]?).map (·.params)

/-- Whether the positions after a group head at `i` hold the group's other members, in order,
each as an alias of this head.  Then "declared before `i + k`", for a group of `k` members,
means "declared before the group, or one of its members". -/
@[expose]
def groupLayout (env : Env.Raw α) (i : Nat) (g : DataGroup α TypeExpr.Raw) : Bool :=
  g.members.zipIdx.all fun (m, j) =>
    j == 0 || (env.decls.keys[i + j]? == some m.name &&
      match env.decls[m.name]? with
      | some (.dataRest n h j') => n == m.name && h == g.first.name && j' == j
      | _ => false)

/-- Whether each member of a group has its case instruction: `T.case`, for the member `T`, is
declared as an instruction marked as the case instruction of that member of this group.
`checkAlias` checks that instruction against the one the group derives. -/
@[expose]
def groupCases (env : Env.Raw α) (g : DataGroup α TypeExpr.Raw) : Bool :=
  g.members.zipIdx.all fun p =>
    match env.decls[p.1.name.caseName]? with
    | some (.insn d) => d.kind == .case ⟨g.first.name, p.2⟩
    | _ => false

/-- Whether a mutual group headed at position `i` is an admissible definition.

A payload may refer to anything declared before `i + k`, except that under a parameter
declared `.non` it may only refer to what is declared before `i`.  Each member's own `.pos`
parameters must occur only in `.pos` positions, and the names the group binds are distinct.
A group is checked exactly as its members would be if they had been added as plain types
first; `Env.addData` is built on that.  Each member's case instruction is declared too. -/
@[expose]
def checkGroup (env : Env.Raw α) (i : Nat) (g : DataGroup α TypeExpr.Raw) : Bool :=
  env.groupLayout i g && env.groupCases g && g.checkNames &&
    g.checkWith (env.paramsBefore (i + g.members.size))
      (RefBefore.check env (i + g.members.size)) (RefBefore.check env i)

/-- Whether an alias addresses something that is there: its head is a group declared
strictly earlier, and that group has a member at the address, under the alias's own name.  A
constructor's instruction is checked the same way, and must be the instruction the group
gives that constructor: the same name and signature, its annotation aside.  So must a case
instruction. -/
@[expose]
def checkAlias (env : Env.Raw α) (i : Nat) (n : Name) : Decl.Raw α → Bool
  | .dataRest _ h idx =>
    (match IndexMap.idxOf? env.decls h with | some j => j < i | none => false)
      && (match (env.decls[h]?).bind Decl.Raw.asGroup with
          | some g => (match g.member? idx with | some m => m.name == n | none => false)
          | none => false)
  | .insn d =>
    match d.kind with
    | .decl => true
    | .ctor a =>
      (match IndexMap.idxOf? env.decls a.head with | some j => j < i | none => false)
        && (match (env.decls[a.head]?).bind Decl.Raw.asGroup with
            | some g => (g.ctorInsn? a.dataIdx a.idx).map (·.erase) == some d.erase
            | none => false)
    | .case a =>
      (match IndexMap.idxOf? env.decls a.head with | some j => j < i | none => false)
        && (match (env.decls[a.head]?).bind Decl.Raw.asGroup with
            | some g => (g.caseInsn? a.dataIdx).map (·.erase) == some d.erase
            | none => false)
  | _ => true

/-- The environment is well formed:

* every type expression resolves to something declared earlier, which forbids forward
  references and cycles outside a mutual group;
* every mutual group is an admissible definition: its recursion stays in parameters declared
  `.pos`, and each member is honest about its own;
* every alias addresses a member that the group it names has, and every constructor's
  instruction and every case instruction is the one its group gives it.

The last two are stated as decided checks, `b = true`. -/
structure WF (env : Env.Raw α) : Prop where
  declWF : ∀ (i : Nat) (n : Name) (d : Decl.Raw α),
    env.decls.keys[i]? = some n → env[n]? = some d → d.WF (env.RefBefore i)
  groupWF : ∀ (i : Nat) (n : Name) (g : DataGroup α TypeExpr.Raw),
    env.decls.keys[i]? = some n → env[n]? = some (.dataHead g) →
      env.checkGroup i g = true
  aliasWF : ∀ (i : Nat) (n : Name) (d : Decl.Raw α),
    env.decls.keys[i]? = some n → env[n]? = some d → env.checkAlias i n d = true

/-! ### Extending a well-formed environment

`WF.append` is the preservation lemma for `append`: the new declaration is admitted exactly
when it refers only to declarations already present.  `keys_append` puts it at position
`env.decls.keys.size`. -/

/-- The base case for building an environment by repeated `append`. -/
theorem wf_empty : (empty : Env.Raw α).WF where
  declWF := by intro i n d hkey; simp at hkey
  groupWF := by intro i n g hkey; simp at hkey
  aliasWF := by intro i n d hkey; simp at hkey

theorem not_mem_keys_of_not_mem {env : Env.Raw α} {n : Name} (h : n ∉ env) :
    n ∉ env.decls.keys.toList :=
  fun hm => h (IndexMap.mem_iff_keys_contains.mpr (by simpa using hm))

/-- A name that was already declared still resolves to the same declaration. -/
theorem stable_append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env} {k : Name}
    {e : Decl.Raw α} (hk : env.decls[k]? = some e) : (env.append d fresh).decls[k]? = some e := by
  have hmem : k ∈ env := IndexMap.mem_of_getElem?_eq_some hk
  have hne : ¬ (d.name == k) = true := fun hb => fresh (by rw [eq_of_beq hb]; exact hmem)
  show ((env.append d fresh)[k]?) = some e
  rw [get?_append, if_neg hne]
  exact hk

/-- Appending preserves what a name resolves to, an alias included. -/
theorem typeOf?_append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env} {m : Name}
    {t : TypeDecl α} (ht : env.typeOf? m = some t) :
    (env.append d fresh).typeOf? m = some t := by
  have stable : ∀ {k : Name} {e : Decl.Raw α}, env.decls[k]? = some e →
      (env.append d fresh).decls[k]? = some e := stable_append
  unfold Env.Raw.typeOf? at ht ⊢
  cases hx : env.decls[m]? with
  | none => rw [hx] at ht; simp at ht
  | some e =>
    rw [hx] at ht
    rw [stable hx]
    cases e with
    | type tt => exact ht
    | dataHead g => exact ht
    | dataRest n h i =>
      simp only [Option.bind_some, Env.Raw.typeOfDecl?] at ht ⊢
      cases hh : env.decls[h]? with
      | none => rw [hh] at ht; simp at ht
      | some eh => rw [hh] at ht; rw [stable hh]; exact ht
    | insn _ =>
      simp only [Option.bind_some, Env.Raw.typeOfDecl?] at ht
      exact absurd ht (by simp)

/-- `append` only adds resolutions, so every reference stays valid.  `hi` keeps
the new declaration's own position out of reach. -/
theorem RefBefore.append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env} {i : Nat}
    {m : Name} {a : Nat}
    (h : env.RefBefore i m a) : (env.append d fresh).RefBefore i m a := by
  obtain ⟨j, t, hj, hji, ht, ha⟩ := refBefore_iff.mp h
  have hm : m ∈ env := by
    unfold Env.Raw.typeOf? at ht
    cases hx : env.decls[m]? with
    | none => rw [hx] at ht; simp at ht
    | some d' => exact IndexMap.mem_of_getElem?_eq_some hx
  have hne : ¬ (d.name == m) = true := fun hb => fresh (by rw [eq_of_beq hb]; exact hm)
  exact refBefore_iff.mpr
    ⟨j, t, by rw [idxOf?_append, if_neg hne]; exact hj, hji, typeOf?_append ht, ha⟩

theorem refBefore_check_append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env}
    {i : Nat} {m : Name} {a : Nat} (h : RefBefore.check env i m a = true) :
    RefBefore.check (env.append d fresh) i m a = true :=
  refBefore_check_eq_true.mpr (RefBefore.append (fresh := fresh) (refBefore_check_eq_true.mp h))

/-- What the `before j` view yields survives an append: the name keeps its position, and
`typeOf?_append` keeps what it denotes. -/
theorem typesBefore_append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env} {j : Nat}
    {m : Name} {t : TypeDecl α} (h : (env.types.before j)[m]? = some t) :
    ((env.append d fresh).types.before j)[m]? = some t := by
  rw [getElem?_types_before] at h ⊢
  cases hp : IndexMap.idxOf? env.decls m with
  | none => rw [hp] at h; simp at h
  | some p =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · rename_i hpj
      have hm : m ∈ env := by
        show m ∈ env.decls
        rw [IndexMap.mem_iff_contains, ← IndexMap.isSome_idxOf?_eq_contains, hp]
        rfl
      have hne : ¬ (d.name == m) = true := fun hb => fresh (by rw [eq_of_beq hb]; exact hm)
      rw [idxOf?_append, if_neg hne, hp, Option.bind_some, if_pos hpj]
      exact typeOf?_append (m := m) h
    · simp at h

/-- A group's own check survives an extension. -/
theorem checkGroup_append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env} {i : Nat}
    {g : DataGroup α TypeExpr.Raw} (h : env.checkGroup i g = true) :
    (env.append d fresh).checkGroup i g = true := by
  simp only [checkGroup, Bool.and_eq_true] at h ⊢
  refine ⟨⟨⟨?_, ?_⟩, h.1.2⟩, DataGroup.checkWith_mono ?_ (fun _ _ => refBefore_check_append)
    (fun _ _ => refBefore_check_append) h.2⟩
  · have hl := h.1.1.1
    simp only [groupLayout, Array.all_eq_true_iff_forall_mem, Bool.or_eq_true, beq_iff_eq,
      Bool.and_eq_true] at hl ⊢
    intro x hx
    rcases hl x hx with h0 | ⟨hk, hd⟩
    · exact .inl h0
    · refine .inr ⟨?_, ?_⟩
      · rw [keys_append, Array.getElem?_push]
        have hlt : i + x.2 < env.decls.keys.size := (Array.getElem?_eq_some_iff.mp hk).1
        rw [if_neg (by omega)]
        exact hk
      · cases hx' : env.decls[x.1.name]? with
        | none => rw [hx'] at hd; simp at hd
        | some e => rw [hx'] at hd; rw [stable_append hx']; exact hd
  · have hc := h.1.1.2
    simp only [groupCases, Array.all_eq_true_iff_forall_mem] at hc ⊢
    intro x hx
    have hcx := hc x hx
    cases hx' : env.decls[x.1.name.caseName]? with
    | none => rw [hx'] at hcx; simp at hcx
    | some e => rw [hx'] at hcx; rw [stable_append hx']; exact hcx
  · intro n ps hn
    unfold paramsBefore at hn ⊢
    cases ht : (env.types.before (i + g.members.size))[n]? with
    | none => rw [ht] at hn; simp at hn
    | some t => rw [ht] at hn; rw [typesBefore_append ht]; exact hn

/-- An alias still addresses what it addressed. -/
theorem checkAlias_append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env} {i : Nat}
    {n : Name} {e : Decl.Raw α} (h : env.checkAlias i n e = true) :
    (env.append d fresh).checkAlias i n e = true := by
  -- both alias forms consult the head's position and the head's declaration, and only those
  have pos : ∀ {h' : Name} {j : Nat}, IndexMap.idxOf? env.decls h' = some j →
      IndexMap.idxOf? (env.append d fresh).decls h' = some j := by
    intro h' j hj
    have hmem : h' ∈ env := by
      show h' ∈ env.decls
      rw [IndexMap.mem_iff_contains, ← IndexMap.isSome_idxOf?_eq_contains, hj]
      rfl
    have hne : ¬ (d.name == h') = true := fun hb => fresh (by rw [eq_of_beq hb]; exact hmem)
    rw [idxOf?_append, if_neg hne]; exact hj
  cases e with
  | dataRest _ hd idx =>
    simp only [checkAlias, Bool.and_eq_true] at h ⊢
    obtain ⟨hj, hg⟩ := h
    refine ⟨?_, ?_⟩
    · cases hx : IndexMap.idxOf? env.decls hd with
      | none => rw [hx] at hj; simp at hj
      | some j => rw [hx] at hj; rw [pos hx]; exact hj
    · cases hx : env.decls[hd]? with
      | none => rw [hx] at hg; simp at hg
      | some eh => rw [hx] at hg; rw [stable_append hx]; exact hg
  | insn di =>
    -- a constructor and a case instruction consult their head in the same way
    have addr : ∀ {h' : Name} {f : DataGroup α TypeExpr.Raw → Bool},
        ((match IndexMap.idxOf? env.decls h' with | some j => j < i | none => false) &&
          (match (env.decls[h']?).bind Decl.Raw.asGroup with
           | some g => f g | none => false)) = true →
        ((match IndexMap.idxOf? (env.append d fresh).decls h' with
            | some j => j < i | none => false) &&
          (match ((env.append d fresh).decls[h']?).bind Decl.Raw.asGroup with
           | some g => f g | none => false)) = true := by
      intro h' f h
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨hj, hg⟩ := h
      refine ⟨?_, ?_⟩
      · cases hx : IndexMap.idxOf? env.decls h' with
        | none => rw [hx] at hj; simp at hj
        | some j => rw [hx] at hj; rw [pos hx]; exact hj
      · cases hx : env.decls[h']? with
        | none => rw [hx] at hg; simp at hg
        | some eh => rw [hx] at hg; rw [stable_append hx]; exact hg
    cases hk : di.kind <;> simp only [checkAlias, hk] at h ⊢
    all_goals first | rfl | exact addr h
  | type _ => rfl
  | dataHead _ => rfl

end Env.Raw

namespace RegionSig.Raw

/-- Decision procedure for `RegionSig.Raw.WF (env.RefBefore i) scope`. -/
@[expose]
def checkAt (env : Env.Raw α) (i : Nat) (scope : Nat) (r : RegionSig.Raw) : Bool :=
  r.params.all (fun p => TypeExpr.Raw.checkAt env i scope p.type)
    && TypeExpr.Raw.checkAt env i scope r.returnType
    && decide r.paramNames.Nodup

/-- Soundness of `RegionSig.Raw.checkAt`: a region signature it accepts is well formed at
position `i`. -/
theorem wf_of_checkAt {env : Env.Raw α} {i scope : Nat} {r : RegionSig.Raw}
    (h : r.checkAt env i scope = true) : r.WF (env.RefBefore i) scope := by
  simp only [checkAt, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨hparams, hret⟩, hnames⟩ := h
  exact ⟨fun p hp => TypeExpr.Raw.wfRel_of_checkAt _ (hparams p hp),
    TypeExpr.Raw.wfRel_of_checkAt _ hret, of_decide_eq_true hnames⟩

end RegionSig.Raw

namespace Decl.Raw

/-- Decision procedure for `Decl.Raw.WF (env.RefBefore i)`. -/
@[expose]
def checkAt (env : Env.Raw α) (i : Nat) : Decl.Raw α → Bool
  | .type d => decide d.paramNames.Nodup
  | .dataHead _ => true
  | .dataRest .. => true
  | .insn d =>
    d.argTypes.all (fun p => TypeExpr.Raw.checkAt env i d.typeArgc p.type)
      && d.variadic.all (fun v => TypeExpr.Raw.checkAt env i d.typeArgc v.type)
      && d.returnType.all (TypeExpr.Raw.checkAt env i d.typeArgc)
      && d.regions.all (fun r => r.type.checkAt env i d.typeArgc)
      && d.succs.all (fun s => s.type.all (TypeExpr.Raw.checkAt env i d.typeArgc))
      && decide d.paramNames.Nodup

/-- Soundness of `Decl.Raw.checkAt`: a declaration it accepts is well formed at
position `i`. -/
theorem wf_of_checkAt {env : Env.Raw α} {i : Nat} {d : Decl.Raw α} (h : d.checkAt env i = true) :
    d.WF (env.RefBefore i) := by
  cases d with
  | type t => exact (of_decide_eq_true h : t.paramNames.Nodup)
  | dataHead g => trivial
  | dataRest _ _ _ => trivial
  | insn ins =>
    simp only [checkAt, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem,
      Option.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨hargs, hvar⟩, hret⟩, hregions⟩, hsuccs⟩, hnames⟩ := h
    exact ⟨fun q hq => TypeExpr.Raw.wfRel_of_checkAt _ (hargs q hq),
      fun v hv => TypeExpr.Raw.wfRel_of_checkAt _ (hvar v (by simpa using hv)),
      fun t ht => TypeExpr.Raw.wfRel_of_checkAt _ (hret t (by simpa using ht)),
      fun r hr => RegionSig.Raw.wf_of_checkAt (hregions r hr),
      fun s hs t ht => TypeExpr.Raw.wfRel_of_checkAt _ (hsuccs s hs t ht),
      of_decide_eq_true hnames⟩

end Decl.Raw

namespace Env.Raw

/-- What a declaration owes as a definition: a group head must be admissible, and no other
form owes anything. -/
@[expose]
def checkGroupOf (env : Env.Raw α) (i : Nat) : Decl.Raw α → Bool
  | .dataHead g => env.checkGroup i g
  | _ => true

/-- Everything the declaration stored at position `i` under name `n` owes: its type
expressions resolve, an alias addresses something real, and a group is admissible. -/
@[expose]
def checkDecl (env : Env.Raw α) (i : Nat) (n : Name) (d : Decl.Raw α) : Bool :=
  d.checkAt env i && env.checkAlias i n d && env.checkGroupOf i d

/-- Appending a declaration that owes only what is already declared preserves
well-formedness.  The two side conditions default to `rfl`, which discharges them for a
primitive type and for an instruction that is not a constructor. -/
theorem WF.append {env : Env.Raw α} (h : env.WF) {d : Decl.Raw α} (fresh : d.name ∉ env)
    (hat : d.WF (env.RefBefore env.decls.keys.size))
    (halias : env.checkAlias env.decls.keys.size d.name d = true := by rfl)
    (hgroup : env.checkGroupOf env.decls.keys.size d = true := by rfl) :
    (env.append d fresh).WF := by
  -- one case split serves all three fields: the new declaration, or an old one
  have split : ∀ (i : Nat) (n : Name) (e : Decl.Raw α),
      (env.append d fresh).decls.keys[i]? = some n → (env.append d fresh)[n]? = some e →
      (i = env.decls.keys.size ∧ n = d.name ∧ e = d) ∨
        (env.decls.keys[i]? = some n ∧ env[n]? = some e) := by
    intro i n e hkey he
    rw [keys_append, Array.getElem?_push] at hkey
    split at hkey
    · rename_i hi
      obtain rfl : d.name = n := Option.some.inj hkey
      rw [get?_append, if_pos (by simp)] at he
      exact .inl ⟨hi, rfl, (Option.some.inj he).symm⟩
    · have hnk : n ∈ env.decls.keys.toList := List.mem_of_getElem? (by simpa using hkey)
      have hne : ¬ (d.name == n) = true :=
        fun hb => not_mem_keys_of_not_mem fresh (eq_of_beq hb ▸ hnk)
      rw [get?_append, if_neg hne] at he
      exact .inr ⟨hkey, he⟩
  refine ⟨fun i n e hkey he => ?_, fun i n g hkey he => ?_, fun i n e hkey he => ?_⟩
  · rcases split i n e hkey he with ⟨rfl, rfl, rfl⟩ | ⟨hkey', he'⟩
    · exact hat.mono fun _ _ => RefBefore.append
    · exact (h.declWF i n e hkey' he').mono fun _ _ => RefBefore.append
  · rcases split i n _ hkey he with ⟨rfl, rfl, hde⟩ | ⟨hkey', he'⟩
    · subst hde; exact checkGroup_append (by simpa [checkGroupOf] using hgroup)
    · exact checkGroup_append (h.groupWF i n g hkey' he')
  · rcases split i n e hkey he with ⟨rfl, rfl, rfl⟩ | ⟨hkey', he'⟩
    · exact checkAlias_append halias
    · exact checkAlias_append (h.aliasWF i n e hkey' he')

/-- `WF.append` from the decided form of the same three obligations. -/
theorem WF.appendChecked {env : Env.Raw α} (h : env.WF) {d : Decl.Raw α} (fresh : d.name ∉ env)
    (hd : checkDecl env env.decls.keys.size d.name d = true) : (env.append d fresh).WF := by
  simp only [checkDecl, Bool.and_eq_true] at hd
  exact h.append fresh (Decl.Raw.wf_of_checkAt hd.1.1) hd.1.2 hd.2

/-- Check declarations left to right, each against its own position: the
declaration at position `i` may only refer to type declarations before `i`. -/
def checkFrom (env : Env.Raw α) (i : Nat) : List (Decl.Raw α) → Bool
  | [] => true
  | d :: ds => checkDecl env i d.name d && checkFrom env (i + 1) ds

/-- Unfolding of `checkFrom`: the declaration `j` places along was checked at
position `i + j`. -/
theorem checkDecl_of_checkFrom (env : Env.Raw α) :
    ∀ (i : Nat) (ds : List (Decl.Raw α)), checkFrom env i ds = true →
      ∀ (j : Nat) (d : Decl.Raw α), ds[j]? = some d → checkDecl env (i + j) d.name d = true
  | _, [], _, _, _, h => by simp at h
  | i, e :: ds, hc, 0, d, h => by
    simp only [checkFrom, Bool.and_eq_true] at hc
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    simpa [← h] using hc.1
  | i, e :: ds, hc, j + 1, d, h => by
    simp only [checkFrom, Bool.and_eq_true] at hc
    simp only [List.getElem?_cons_succ] at h
    have := checkDecl_of_checkFrom env (i + 1) ds hc.2 j d h
    simpa [Nat.add_right_comm, Nat.add_assoc] using this

/-- In a list of distinctly-named declarations, searching by the name stored at
index `i` finds the declaration at index `i`. -/
theorem find?_eq_of_getElem? : ∀ {ds : List (Decl.Raw α)},
    List.Pairwise (fun x y => x.name ≠ y.name) ds → ∀ {i : Nat} {d : Decl.Raw α},
      ds[i]? = some d → ds.find? (fun e => e.name == d.name) = some d
  | [], _, _, _, h => by simp at h
  | _ :: _, _, 0, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; simp
  | e :: ds, hp, i + 1, d, h => by
    simp only [List.getElem?_cons_succ] at h
    have hne : (e.name == d.name) = false :=
      beq_eq_false_iff_ne.mpr ((List.pairwise_cons.mp hp).1 d (List.mem_of_getElem? h))
    simpa [hne] using find?_eq_of_getElem? (List.pairwise_cons.mp hp).2 h

/-- **Soundness of the checker.**  `checkFrom` establishes the positional
specification for an environment built by `ofAscArray`. -/
theorem wf_ofAscArray (ds : Array (Decl.Raw α)) (p : DistinctDecls ds)
    (h : checkFrom (ofAscArray ds p) 0 ds.toList = true) : (ofAscArray ds p).WF := by
  have hkeys : (ofAscArray ds p).decls.keys = ds.map Decl.Raw.name := keys_ofAscArray ds p
  have hget : ∀ (j : Nat) (e : Decl.Raw α), ds.toList[j]? = some e →
      (ofAscArray ds p)[e.name]? = some e := by
    intro j e hj
    rw [ofAscArrayMem?, ← Array.find?_toList]
    exact find?_eq_of_getElem? p hj
  -- every field comes from the one per-declaration check, at the declaration's position
  have key : ∀ (i : Nat) (n : Name) (d : Decl.Raw α),
      (ofAscArray ds p).decls.keys[i]? = some n →
      (ofAscArray ds p)[n]? = some d → checkDecl (ofAscArray ds p) i n d = true := by
    intro i n d hkey hd
    rw [hkeys] at hkey
    simp only [Array.getElem?_map, Option.map_eq_some_iff] at hkey
    obtain ⟨d', hd', rfl⟩ := hkey
    have hd'l : ds.toList[i]? = some d' := by simpa using hd'
    obtain rfl : d = d' := Option.some.inj (hd.symm.trans (hget i d' hd'l))
    simpa using checkDecl_of_checkFrom _ 0 ds.toList h i d hd'l
  refine ⟨fun i n d hkey hd => ?_, fun i n g hkey hd => ?_, fun i n d hkey hd => ?_⟩
  · have := key i n d hkey hd
    simp only [checkDecl, Bool.and_eq_true] at this
    exact Decl.Raw.wf_of_checkAt this.1.1
  · have := key i n (.dataHead g) hkey hd
    simp only [checkDecl, Bool.and_eq_true] at this
    exact this.2
  · have := key i n d hkey hd
    simp only [checkDecl, Bool.and_eq_true] at this
    exact this.1.2

/-! ### Appending a batch

A mutual group goes in by `appendList`, and every new declaration is checked in the *final*
environment, as `wf_ofAscArray` does for a whole environment. -/

theorem RefBefore.appendList {env : Env.Raw α} {ds : List (Decl.Raw α)} {fresh : env.FreshList ds}
    {i : Nat} {m : Name} {a : Nat} (h : env.RefBefore i m a) :
    (env.appendList ds fresh).RefBefore i m a :=
  appendList_induct (P := fun s => s.RefBefore i m a) (fun _ _ _ => RefBefore.append) ds fresh h

theorem checkGroup_appendList {env : Env.Raw α} {ds : List (Decl.Raw α)}
    {fresh : env.FreshList ds} {i : Nat} {g : DataGroup α TypeExpr.Raw}
    (h : env.checkGroup i g = true) : (env.appendList ds fresh).checkGroup i g = true :=
  appendList_induct (P := fun s => s.checkGroup i g = true) (fun _ _ _ => checkGroup_append)
    ds fresh h

theorem checkAlias_appendList {env : Env.Raw α} {ds : List (Decl.Raw α)}
    {fresh : env.FreshList ds} {i : Nat} {n : Name} {e : Decl.Raw α}
    (h : env.checkAlias i n e = true) : (env.appendList ds fresh).checkAlias i n e = true :=
  appendList_induct (P := fun s => s.checkAlias i n e = true) (fun _ _ _ => checkAlias_append)
    ds fresh h

theorem typeOf?_appendList {env : Env.Raw α} {ds : List (Decl.Raw α)}
    {fresh : env.FreshList ds} {m : Name} {t : TypeDecl α} (h : env.typeOf? m = some t) :
    (env.appendList ds fresh).typeOf? m = some t :=
  appendList_induct (P := fun s => s.typeOf? m = some t) (fun _ _ _ => typeOf?_append) ds fresh h

theorem typesBefore_appendList {env : Env.Raw α} {ds : List (Decl.Raw α)}
    {fresh : env.FreshList ds} {j : Nat} {m : Name} {t : TypeDecl α}
    (h : (env.types.before j)[m]? = some t) :
    ((env.appendList ds fresh).types.before j)[m]? = some t :=
  appendList_induct (P := fun s => (s.types.before j)[m]? = some t)
    (fun _ _ _ => typesBefore_append) ds fresh h

/-- Appending a batch whose every declaration passes its check in the extended environment,
at the position it lands in, preserves well-formedness. -/
theorem WF.appendList {env : Env.Raw α} (h : env.WF) (ds : List (Decl.Raw α))
    (fresh : env.FreshList ds)
    (hds : checkFrom (env.appendList ds fresh) env.decls.keys.size ds = true) :
    (env.appendList ds fresh).WF := by
  -- one case split serves all three fields: an old declaration, or the batch's `j`th
  have split : ∀ (i : Nat) (n : Name) (e : Decl.Raw α),
      (env.appendList ds fresh).decls.keys[i]? = some n → (env.appendList ds fresh)[n]? = some e →
      (env.decls.keys[i]? = some n ∧ env[n]? = some e) ∨
        (∃ j, i = env.decls.keys.size + j ∧ ds[j]? = some e ∧ e.name = n) := by
    intro i n e hkey he
    rw [keys_appendList, Array.getElem?_append] at hkey
    rw [get?_appendList] at he
    split at hkey
    · rename_i hi
      have hn : n ∈ env :=
        IndexMap.mem_iff_keys_contains.mpr
          (Array.contains_iff_mem.mpr (Array.mem_of_getElem? hkey))
      cases hs : env[n]? with
      | some e' =>
        rw [hs, Option.some_or] at he
        exact .inl ⟨hkey, he⟩
      | none =>
        rw [hs, Option.none_or] at he
        obtain ⟨hp, -⟩ := List.find?_eq_some_iff_append.mp he
        exact absurd (by simpa using hp) (fun hne : e.name = n =>
          fresh.2 e (List.mem_of_find?_eq_some he) (hne ▸ hn))
    · rename_i hi
      simp only [List.getElem?_toArray, List.getElem?_map, Option.map_eq_some_iff] at hkey
      obtain ⟨e', he', rfl⟩ := hkey
      have hs : env[e'.name]? = none := not_getElem?_of_not_mem (fresh.2 e' (List.mem_of_getElem? he'))
      rw [hs, Option.none_or, find?_eq_of_getElem? fresh.1 he'] at he
      obtain rfl := Option.some.inj he
      exact .inr ⟨i - env.decls.keys.size, by omega, he', rfl⟩
  have key : ∀ (j : Nat) (e : Decl.Raw α), ds[j]? = some e →
      checkDecl (env.appendList ds fresh) (env.decls.keys.size + j) e.name e = true :=
    checkDecl_of_checkFrom _ _ ds hds
  refine ⟨fun i n e hkey he => ?_, fun i n g hkey he => ?_, fun i n e hkey he => ?_⟩
  · rcases split i n e hkey he with ⟨hkey', he'⟩ | ⟨j, rfl, hj, rfl⟩
    · exact (h.declWF i n e hkey' he').mono fun _ _ => RefBefore.appendList
    · have := key j e hj
      simp only [checkDecl, Bool.and_eq_true] at this
      exact Decl.Raw.wf_of_checkAt this.1.1
  · rcases split i n _ hkey he with ⟨hkey', he'⟩ | ⟨j, rfl, hj, rfl⟩
    · exact checkGroup_appendList (h.groupWF i n g hkey' he')
    · have := key j _ hj
      simp only [checkDecl, Bool.and_eq_true] at this
      exact this.2
  · rcases split i n e hkey he with ⟨hkey', he'⟩ | ⟨j, rfl, hj, rfl⟩
    · exact checkAlias_appendList (h.aliasWF i n e hkey' he')
    · have := key j e hj
      simp only [checkDecl, Bool.and_eq_true] at this
      exact this.1.2

/-- A batch of operations each well formed in `env`, none of them a constructor, may be
appended without being checked again. -/
theorem WF.appendList_insnsList : ∀ {env : Env.Raw α} (_ : env.WF) (is : List (InsnDecl.Raw α))
    (fresh : env.FreshList (is.map .insn)),
    (∀ d ∈ is, d.WF (env.RefBefore env.decls.keys.size) ∧ d.kind = .decl) →
    (env.appendList (is.map .insn) fresh).WF
  | _, h, [], _, _ => h
  | _, h, d :: is, fresh, hwf =>
    WF.appendList_insnsList
      (h.append fresh.head (Decl.Raw.wf_insn_iff.mpr (hwf d List.mem_cons_self).1)
        (by simp [checkAlias, (hwf d List.mem_cons_self).2]))
      is fresh.tail fun e he =>
        ⟨(hwf e (List.mem_cons_of_mem _ he)).1.mono fun _ _ hr =>
          (RefBefore.append hr).mono (by rw [keys_append]; simp),
         (hwf e (List.mem_cons_of_mem _ he)).2⟩

theorem WF.appendList_insns {env : Env.Raw α} (h : env.WF) (is : Array (InsnDecl.Raw α))
    (fresh : env.FreshList (is.map .insn).toList)
    (hwf : ∀ d ∈ is,
      d.WF (env.RefBefore env.decls.keys.size) ∧ d.kind = .decl) :
    (env.appendList (is.map .insn).toList fresh).WF := by
  generalize hl : (is.map Decl.Raw.insn).toList = l at fresh
  rw [Array.toList_map] at hl
  subst hl
  exact WF.appendList_insnsList h is.toList fresh fun d hd => hwf d (Array.mem_toList_iff.mp hd)

/-- The converse of `checkDecl_of_checkFrom`. -/
theorem checkFrom_of_checkDecl (env : Env.Raw α) :
    ∀ (i : Nat) (ds : List (Decl.Raw α)),
      (∀ (j : Nat) (d : Decl.Raw α), ds[j]? = some d → checkDecl env (i + j) d.name d = true) →
      checkFrom env i ds = true
  | _, [], _ => rfl
  | i, e :: ds, h => by
    simp only [checkFrom, Bool.and_eq_true]
    refine ⟨by simpa using h 0 e rfl, checkFrom_of_checkDecl env (i + 1) ds fun j d hd => ?_⟩
    have := h (j + 1) d (by simpa using hd)
    simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

/-- Type declarations owe only distinct parameter names. -/
theorem checkFrom_typesList (env : Env.Raw α) :
    ∀ (i : Nat) (ts : List (TypeDecl α)), (∀ t ∈ ts, t.paramNames.Nodup) →
      checkFrom env i (ts.map .type) = true
  | _, [], _ => rfl
  | i, t :: ts, h => by
    simp only [List.map_cons, checkFrom, Bool.and_eq_true]
    refine ⟨?_, checkFrom_typesList env (i + 1) ts fun u hu => h u (List.mem_cons_of_mem _ hu)⟩
    simp [checkDecl, Decl.Raw.checkAt, checkAlias, checkGroupOf, h t List.mem_cons_self]

/-- The array form of `checkFrom_typesList`. -/
theorem checkFrom_types (env : Env.Raw α) (i : Nat) (ts : Array (TypeDecl α))
    (h : ∀ t ∈ ts.toList, t.paramNames.Nodup) :
    checkFrom env i (ts.map .type).toList = true := by
  rw [Array.toList_map]
  exact checkFrom_typesList env i ts.toList h

/-! #### Where a batch's declarations land -/

section
variable {env : Env.Raw α} {ds : List (Decl.Raw α)} {fresh : env.FreshList ds} {j : Nat}
  {d : Decl.Raw α}

theorem getElem?_keys_appendList (hd : ds[j]? = some d) :
    (env.appendList ds fresh).decls.keys[env.decls.keys.size + j]? = some d.name := by
  rw [keys_appendList, Array.getElem?_append_right (by omega)]
  simp [hd]

theorem get?_appendList_of_getElem? (hd : ds[j]? = some d) :
    (env.appendList ds fresh).decls[d.name]? = some d := by
  show (env.appendList ds fresh)[d.name]? = some d
  rw [get?_appendList, not_getElem?_of_not_mem (fresh.2 d (List.mem_of_getElem? hd)),
    Option.none_or]
  exact find?_eq_of_getElem? fresh.1 hd

theorem idxOf?_appendList_of_getElem? (hd : ds[j]? = some d) :
    IndexMap.idxOf? (env.appendList ds fresh).decls d.name = some (env.decls.keys.size + j) :=
  (IndexMap.idxOf?_eq_some_iff_getElem?_keys (IndexMap.keys_nodup _)).mpr
    (getElem?_keys_appendList hd)

end

/-- A constructor's instruction is well formed at any position past its group's members. -/
theorem checkAt_ctorDecl {env : Env.Raw α} {g : DataGroup α TypeExpr.Raw} {n p i j : Nat}
    {m : DatatypeDecl α TypeExpr.Raw} {c : Ctor α TypeExpr.Raw}
    (hm : g.members[i]? = some m) (hc : m.ctors[j]? = some c) (hp : n + g.members.size ≤ p)
    (hmem : ∀ {k : Nat} {m' : DatatypeDecl α TypeExpr.Raw}, g.members[k]? = some m' →
      env.RefBefore p m'.name m'.arity)
    (hn : g.checkNames = true)
    (h : g.checkWith (env.paramsBefore (n + g.members.size))
      (RefBefore.check env (n + g.members.size)) (RefBefore.check env n) = true) :
    Decl.Raw.checkAt env p (.insn (g.ctorDecl i m j c)) = true := by
  have hmm : m ∈ g.members := Array.mem_of_getElem? hm
  have hcm : c ∈ m.ctors := Array.mem_of_getElem? hc
  have hsize : (m.params.map (·.name)).size = m.arity := by simp [DatatypeDecl.arity]
  have hRR : ∀ x a, RefBefore.check env (n + g.members.size) x a = true →
      RefBefore.check env p x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono hp)
  have hNR : ∀ x a, RefBefore.check env n x a = true →
      RefBefore.check env (n + g.members.size) x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono (by omega))
  simp only [DataGroup.checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true] at h
  simp only [DataGroup.checkNames, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true,
    decide_eq_true_eq] at hn
  simp only [Decl.Raw.checkAt, DataGroup.ctorDecl, InsnDecl.Raw.typeArgc, hsize,
    Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Option.all_none, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨fun q hq => ?_, ?_⟩, ?_⟩, by simp⟩, by simp⟩, ?_⟩
  · exact TypeExpr.Raw.check_mono hRR _
      (TypeExpr.Raw.check_of_checkPayload hNR _ (h m hmm c hcm q hq).1)
  · simp
  · rw [Option.all_some, TypeExpr.Raw.checkAt, TypeExpr.Raw.check_app]
    refine ⟨refBefore_check_eq_true.mpr (by simpa using hmem hm), fun a ha => ?_⟩
    obtain ⟨k, hk, rfl⟩ := TypeExpr.Raw.mem_vars.mp ha
    simpa [TypeExpr.Raw.check] using hk
  · simpa [InsnDecl.Raw.paramNames, DatatypeDecl.paramNames] using (hn m hmm).1.2 c hcm

/-- A case instruction is well formed at any position past its group's members. -/
theorem checkAt_caseDecl {env : Env.Raw α} {g : DataGroup α TypeExpr.Raw} {n p i : Nat}
    {m : DatatypeDecl α TypeExpr.Raw}
    (hm : g.members[i]? = some m) (hp : n + g.members.size ≤ p)
    (hmem : ∀ {k : Nat} {m' : DatatypeDecl α TypeExpr.Raw}, g.members[k]? = some m' →
      env.RefBefore p m'.name m'.arity)
    (hn : g.checkNames = true)
    (h : g.checkWith (env.paramsBefore (n + g.members.size))
      (RefBefore.check env (n + g.members.size)) (RefBefore.check env n) = true) :
    Decl.Raw.checkAt env p (.insn (g.caseDecl i m)) = true := by
  have hmm : m ∈ g.members := Array.mem_of_getElem? hm
  have hsize : (m.params.map (·.name)).size = m.arity := by simp [DatatypeDecl.arity]
  have hRR : ∀ x a, RefBefore.check env (n + g.members.size) x a = true →
      RefBefore.check env p x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono hp)
  have hNR : ∀ x a, RefBefore.check env n x a = true →
      RefBefore.check env (n + g.members.size) x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono (by omega))
  simp only [DataGroup.checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true] at h
  simp only [DataGroup.checkNames, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true,
    decide_eq_true_eq] at hn
  simp only [Decl.Raw.checkAt, DataGroup.caseDecl, InsnDecl.Raw.typeArgc, hsize,
    Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Option.all_none, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨fun q hq => ?_, ?_⟩, by simp⟩, by simp⟩, fun s hs t ht => ?_⟩, ?_⟩
  · obtain rfl : q = ⟨"scrutinee", .app m.name (TypeExpr.Raw.vars m.arity)⟩ := by simpa using hq
    rw [TypeExpr.Raw.checkAt, TypeExpr.Raw.check_app]
    refine ⟨refBefore_check_eq_true.mpr (by simpa using hmem hm), fun a ha => ?_⟩
    obtain ⟨k, hk, rfl⟩ := TypeExpr.Raw.mem_vars.mp ha
    simpa [TypeExpr.Raw.check] using hk
  · simp
  · obtain ⟨c, hc, rfl⟩ := Array.mem_map.mp hs
    obtain ⟨q, hq, rfl⟩ := Array.mem_map.mp ht
    exact TypeExpr.Raw.check_mono hRR _
      (TypeExpr.Raw.check_of_checkPayload hNR _ (h m hmm c hc q hq).1)
  · simpa [InsnDecl.Raw.paramNames, DatatypeDecl.paramNames, Function.comp_def]
      using (hn m hmm).2

/-- A group appended as one batch owes only its definition: that it binds no name twice,
and `checkWith` against the extended environment at the positions the group occupies. -/
theorem checkFrom_group {env : Env.Raw α} {g : DataGroup α TypeExpr.Raw}
    (fresh : env.FreshList g.decls.toList) (hn : g.checkNames = true)
    (h : g.checkWith
      ((env.appendList _ fresh).paramsBefore (env.decls.keys.size + g.members.size))
      (RefBefore.check (env.appendList _ fresh) (env.decls.keys.size + g.members.size))
      (RefBefore.check (env.appendList _ fresh) env.decls.keys.size)) :
    checkFrom (env.appendList _ fresh) env.decls.keys.size g.decls.toList = true := by
  have h0 := DataGroup.decls_getElem?_zero g
  have hhead : (env.appendList _ fresh).decls[g.first.name]? = some (.dataHead g) :=
    get?_appendList_of_getElem? h0
  have hidx : IndexMap.idxOf? (env.appendList _ fresh).decls g.first.name =
      some env.decls.keys.size := by
    simpa using idxOf?_appendList_of_getElem? (fresh := fresh) h0
  -- every member is a type declared at its own position in the group
  have hmem : ∀ {p k : Nat} {m : DatatypeDecl α TypeExpr.Raw},
      env.decls.keys.size + g.members.size ≤ p → g.members[k]? = some m →
      (env.appendList _ fresh).RefBefore p m.name m.arity := by
    intro p k m hp hm
    have hk : k < g.members.size := (Array.getElem?_eq_some_iff.mp hm).1
    obtain ⟨D, hD, hDname, hDty⟩ : ∃ D, g.decls.toList[k]? = some D ∧ D.name = m.name ∧
        (env.appendList _ fresh).typeOfDecl? D = some m.toTypeDecl := by
      by_cases hk0 : k = 0
      · subst hk0
        have hfm : g.first = m := by
          simpa [DataGroup.first, Array.getElem?_eq_getElem g.nonEmpty] using hm
        refine ⟨_, h0, by simp [hfm], by simp [typeOfDecl?, hfm]⟩
      · refine ⟨_, g.decls_getElem?_of_member hm hk0, rfl, ?_⟩
        simp [typeOfDecl?, hhead, DataGroup.member?, hm]
    refine refBefore_iff.mpr ⟨env.decls.keys.size + k, m.toTypeDecl, ?_, by omega, ?_, rfl⟩
    · rw [← hDname]; exact idxOf?_appendList_of_getElem? hD
    · rw [typeOf?, ← hDname, get?_appendList_of_getElem? hD, Option.bind_some]; exact hDty
  obtain ⟨rest, hds, hrest⟩ := g.decls_toList_eq_cons
  apply checkFrom_of_checkDecl
  intro j d hd
  match j, hd with
  | 0, hd =>
    rw [h0] at hd
    obtain rfl := Option.some.inj hd.symm
    simp only [checkDecl, Decl.Raw.checkAt, checkAlias, checkGroupOf, checkGroup, h, hn,
      Bool.and_true, Bool.true_and, Nat.add_zero, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · simp only [groupLayout, Array.all_eq_true_iff_forall_mem, Bool.or_eq_true, beq_iff_eq,
        Bool.and_eq_true]
      intro ⟨m, k⟩ hmk
      by_cases hk : k = 0
      · exact .inl hk
      · have hm : g.members[k]? = some m := Array.mk_mem_zipIdx_iff_getElem?.mp hmk
        have hr := g.decls_getElem?_of_member hm hk
        have hk' := getElem?_keys_appendList (fresh := fresh) hr
        have hg := get?_appendList_of_getElem? (fresh := fresh) hr
        simp only [Decl.Raw.name_dataRest] at hk' hg
        refine .inr ⟨hk', ?_⟩
        simp [hg]
    -- each member's case instruction is in the batch, marked as that member's
    · simp only [groupCases, Array.all_eq_true_iff_forall_mem]
      intro ⟨m, k⟩ hmk
      have hm : g.members[k]? = some m := Array.mk_mem_zipIdx_iff_getElem?.mp hmk
      have hc : g.caseInsn? k = some (g.caseDecl k m) := by
        simp [DataGroup.caseInsn?, DataGroup.member?, hm]
      obtain ⟨l, hl⟩ := List.mem_iff_getElem?.mp
        (Array.mem_toList_iff.mpr (DataGroup.mem_decls_of_caseInsn? hc))
      have hg := get?_appendList_of_getElem? (fresh := fresh) hl
      simp only [Decl.Raw.name_insn, DataGroup.name_caseDecl] at hg
      simp [hg, DataGroup.caseDecl]
  | j + 1, hd =>
    have hpos : env.decls.keys.size < env.decls.keys.size + (j + 1) := by omega
    have hd0 := hd
    rw [hds] at hd
    have hal := hrest d (List.mem_of_getElem? (by simpa using hd))
    cases d with
    | dataRest n hh i =>
      obtain ⟨rfl, hn⟩ := hal
      simp only [checkDecl, Decl.Raw.checkAt, checkAlias, checkGroupOf, hidx, hhead,
        Option.bind_some, Decl.Raw.asGroup_dataHead, Bool.and_true, Bool.true_and,
        Decl.Raw.name_dataRest, decide_eq_true hpos]
      cases hm : g.member? i with
      | none => rw [hm] at hn; simp at hn
      | some m => rw [hm] at hn; simpa using hn
    | insn d =>
      have hle := DataGroup.size_le_of_decls_getElem? hd0
      rcases hal with ⟨i, k, hik⟩ | ⟨i, hik⟩
      · simp only [DataGroup.ctorInsn?, DataGroup.member?, Option.bind_eq_bind,
          Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hik
        obtain ⟨m, hm, c, hc, rfl⟩ := hik
        have hat := checkAt_ctorDecl (env := env.appendList _ fresh)
          (p := env.decls.keys.size + (j + 1)) hm hc (by omega)
          (fun hm' => hmem (by omega) hm') hn h
        show (_ && _ && _) = true
        rw [hat, Bool.true_and]
        simp [checkAlias, checkGroupOf, DataGroup.ctorDecl, hidx, hhead, DataGroup.ctorInsn?,
          DataGroup.member?, hm, hc]
      · simp only [DataGroup.caseInsn?, DataGroup.member?, Option.map_eq_some_iff] at hik
        obtain ⟨m, hm, rfl⟩ := hik
        have hat := checkAt_caseDecl (env := env.appendList _ fresh)
          (p := env.decls.keys.size + (j + 1)) hm (by omega)
          (fun hm' => hmem (by omega) hm') hn h
        show (_ && _ && _) = true
        rw [hat, Bool.true_and]
        simp [checkAlias, checkGroupOf, DataGroup.caseDecl, hidx, hhead, DataGroup.caseInsn?,
          DataGroup.member?, hm]
    | type _ => exact absurd hal id
    | dataHead _ => exact absurd hal id

/-! ### What the obligations buy

`aliasWF` is what makes a member name usable: the group it addresses has the member it
claims, so the name denotes a type. -/

/-- A well-formed `dataRest` names a type. -/
theorem isSome_typeOf?_of_checkAlias {env : Env.Raw α} {i : Nat} {n mn hd : Name} {idx : Nat}
    (hn : env.decls[n]? = some (.dataRest mn hd idx))
    (h : env.checkAlias i n (.dataRest mn hd idx) = true) : (env.typeOf? n).isSome := by
  simp only [checkAlias, Bool.and_eq_true] at h
  obtain ⟨-, hg⟩ := h
  unfold typeOf?
  rw [hn]
  simp only [Option.bind_some, typeOfDecl?]
  split at hg
  · rename_i g hx
    split at hg
    · rename_i m hm
      rw [hx]
      simp [hm]
    · simp at hg
  · simp at hg

/-- What a well-formed constructor's instruction is: the head it names is a group, and the
instruction is, its annotation aside, the one `DataGroup.ctorInsn?` gives that constructor of
that group.  The group's case instruction gives each constructor's successor exactly these
arguments as its payload (`caseInsn?_of_checkAlias`). -/
theorem ctorInsn?_of_checkAlias {env : Env.Raw α} {i : Nat} {n : Name} {d : InsnDecl.Raw α}
    {a : CtorAddr} (hc : d.kind = .ctor a) (h : env.checkAlias i n (.insn d) = true) :
    ∃ g, env.decls[a.head]? = some (.dataHead g) ∧
      (g.ctorInsn? a.dataIdx a.idx).map (·.erase) = some d.erase := by
  simp only [checkAlias, hc, Bool.and_eq_true] at h
  obtain ⟨-, hg⟩ := h
  cases hx : env.decls[a.head]? with
  | none => rw [hx] at hg; simp at hg
  | some e =>
    rw [hx] at hg
    cases e with
    | dataHead g => exact ⟨g, rfl, by simpa using hg⟩
    | _ => simp [Decl.Raw.asGroup] at hg

/-- What a well-formed case instruction is: the head it names is a group, and the
instruction is, its annotation aside, the one `DataGroup.caseInsn?` gives that member of that
group.  So its successors are the member's constructors, in order, each receiving its
payload. -/
theorem caseInsn?_of_checkAlias {env : Env.Raw α} {i : Nat} {n : Name} {d : InsnDecl.Raw α}
    {a : CaseAddr} (hk : d.kind = .case a) (h : env.checkAlias i n (.insn d) = true) :
    ∃ g, env.decls[a.head]? = some (.dataHead g) ∧
      (g.caseInsn? a.dataIdx).map (·.erase) = some d.erase := by
  simp only [checkAlias, hk, Bool.and_eq_true] at h
  obtain ⟨-, hg⟩ := h
  cases hx : env.decls[a.head]? with
  | none => rw [hx] at hg; simp at hg
  | some e =>
    rw [hx] at hg
    cases e with
    | dataHead g => exact ⟨g, rfl, by simpa using hg⟩
    | _ => simp [Decl.Raw.asGroup] at hg

/-- **What a well-formed environment says about case instructions.**  Every member `m` of a
group the environment declares has its case instruction `m.name.caseName`, and it is, its
annotation aside, the instruction `DataGroup.caseInsn?` derives for that member: terminal, with
no return type; the member's type parameters; the one argument `scrutinee` of the
member applied to them; and one successor per constructor, in declaration order, named by the
constructor and receiving its payload. -/
theorem WF.caseInsn {env : Env.Raw α} (h : env.WF) {i : Nat} {n : Name}
    {g : DataGroup α TypeExpr.Raw} (hk : env.decls.keys[i]? = some n)
    (hg : env[n]? = some (.dataHead g)) {j : Nat} {m : DatatypeDecl α TypeExpr.Raw}
    (hm : g.member? j = some m) :
    ∃ d, env.decls[m.name.caseName]? = some (.insn d) ∧
      (g.caseInsn? j).map (·.erase) = some d.erase := by
  have hgr := h.groupWF i n g hk hg
  simp only [checkGroup, groupCases, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hgr
  have hcase := hgr.1.1.2 (m, j) (Array.mk_mem_zipIdx_iff_getElem?.mpr hm)
  -- the group is the head's, so the case's address names it
  have hn : g.first.name = n := by
    have := name_getElem env (IndexMap.mem_of_getElem?_eq_some hg)
    rw [show env.decls[n]'(IndexMap.mem_of_getElem?_eq_some hg) = .dataHead g from
      Option.some.inj ((IndexMap.getElem?_eq_some_getElem _).symm.trans hg)] at this
    simpa using this
  cases hx : env.decls[m.name.caseName]? with
  | none => simp [hx] at hcase
  | some e =>
    cases e with
    | insn d =>
      simp only [hx, beq_iff_eq] at hcase
      refine ⟨d, rfl, ?_⟩
      -- its position, for `aliasWF`
      have hmem : m.name.caseName ∈ env.decls := IndexMap.mem_of_getElem?_eq_some hx
      have hs : (IndexMap.idxOf? env.decls m.name.caseName).isSome := by
        rw [IndexMap.isSome_idxOf?_eq_contains]; exact IndexMap.mem_iff_contains.mp hmem
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hs
      have hal := h.aliasWF p _ (.insn d) (IndexMap.getElem?_keys_of_idxOf?_eq_some hp) hx
      obtain ⟨g', hg', heq⟩ := caseInsn?_of_checkAlias hcase hal
      have hgg : g' = g := by
        rw [hn] at hg'
        have : env.decls[n]? = some (.dataHead g) := hg
        rw [this] at hg'
        cases hg'; rfl
      subst hgg
      exact heq
    | _ => simp [hx] at hcase

/-! ### Worked examples

The examples need `native_decide`, so they live in `StrataMantleTest/EnvWFTest.lean`. -/

end Env.Raw

end

end Strata.Mantle
