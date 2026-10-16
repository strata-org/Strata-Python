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

`checkDecl` decides the obligations of one declaration, `Env.Raw.check` those of every
declaration in an environment, and `Env.Raw.checkAppend` those of a batch `appendList` adds.
Their soundness lemmas are `WF.appendChecked`, `wf_ofAscArray` and `WF.appendList`.  The
checks consult the environment's hash map, so they run in compiled code (`#guard`) but not in
the kernel.

Key theorems about type expressions: `WF.instantiate`, `WF.weaken`, `WF.mono`, `WF.kind_eq`,
`wfType_var_iff` and `WF.eq_list`, that every well-formed list is a literal.
-/

open Strata (IndexMap)

namespace Strata.Mantle

public section

variable {α : Type}

/-! ## Well-formedness of an environment

An `Env.Raw α` is an *ordered* map: a declaration may only mention type declarations that
precede it.  The specification (`Env.Raw.WF`) is indexed by a position in `env.decls.keys`,
and the checker (`Env.Raw.check`) checks each declaration at its position.
`Env.Raw.wf_ofAscArray` joins the two.  A checked `TypeExpr` carries `TypeExpr.WFRel` against
`RefBefore`.
-/

namespace TypeExpr

mutual
/-- Well-formedness of a `TypeExpr.Raw` at the kind `k`, relative to an abstract *resolver*:
`R name ks` reads "`name` is a type declaration whose arguments have kinds `ks`, which this
expression is allowed to mention", and each argument is checked at its kind.  `scope` gives the
kind of each variable in scope, by de Bruijn level.  A variable is a type; a list is a literal,
whose elements `WFElem` judges.  So a list variable occurs only spliced into a literal: `as` is
written `[*as]`, and one list has one spelling.  `WF.kind_eq` relates the judgment to
`Raw.kind`.  Growing the resolver is `WF.mono`, and growing the scope `WF.weaken`. -/
inductive WF (R : Name → Array Kind → Prop) (scope : Array Kind) : Kind → Raw → Prop
  | var {i : Nat} (h : scope[i]? = some .type) : WF R scope .type (.var i)
  | app {name : Name} {args : Array Raw} {ks : Array Kind} (ref : R name ks)
      (size : args.size = ks.size)
      (argsWF : ∀ (i : Nat) (h : i < args.size), WF R scope (ks[i]'(size ▸ h)) args[i]) :
      WF R scope .type (.app name args)
  | list {elems : Array Raw} (elemsWF : ∀ a ∈ elems, WFElem R scope a) :
      WF R scope .list (.list elems)

/-- An element of a well-formed list literal: a type, or a list variable spliced in. -/
inductive WFElem (R : Name → Array Kind → Prop) (scope : Array Kind) : Raw → Prop
  | ty {e : Raw} (h : WF R scope .type e) : WFElem R scope e
  | splice {j : Nat} (h : scope[j]? = some .list) : WFElem R scope (.var j)
end

/-- Well formed at its own kind, as `Raw.kind` reads it: a type or a list. -/
abbrev WFRel (R : Name → Array Kind → Prop) (scope : Array Kind) (e : Raw) : Prop :=
  WF R scope (e.kind scope) e

/-- A well-formed type. -/
abbrev WFType (R : Name → Array Kind → Prop) (scope : Array Kind) (e : Raw) : Prop :=
  WF R scope .type e

/-- A well-formed list of types: a list literal. -/
abbrev WFList (R : Name → Array Kind → Prop) (scope : Array Kind) (e : Raw) : Prop :=
  WF R scope .list e

/-- The kind the judgment checks is the kind `Raw.kind` reads. -/
theorem WF.kind_eq {R : Name → Array Kind → Prop} {scope : Array Kind} :
    ∀ {k : Kind} {e : Raw}, WF R scope k e → e.kind scope = k
  | _, _, .var h => by simp [Raw.kind, h]
  | _, _, .app .. => rfl
  | _, _, .list _ => rfl

/-- Well formed at a kind is well formed at its own kind. -/
theorem WF.wfRel {R : Name → Array Kind → Prop} {scope : Array Kind} {k : Kind} {e : Raw}
    (h : WF R scope k e) : WFRel R scope e := by
  rwa [WFRel, h.kind_eq]

/-- Well formed at its own kind, and of kind `k`, is well formed at `k`. -/
theorem WF.of_wfRel {R : Name → Array Kind → Prop} {scope : Array Kind} {k : Kind} {e : Raw}
    (h : WFRel R scope e) (hk : e.kind scope = k) : WF R scope k e :=
  hk ▸ h

/-- A variable is well formed as a type exactly when it is a type variable. -/
theorem wfType_var_iff {R : Name → Array Kind → Prop} {scope : Array Kind} {i : Nat} :
    WFType R scope (.var i) ↔ scope[i]? = some .type :=
  ⟨fun | .var h => h, .var⟩

/-- A well-formed list is a literal. -/
theorem WF.eq_list {R : Name → Array Kind → Prop} {scope : Array Kind} {e : Raw}
    (h : WFList R scope e) : ∃ es, e = .list es := by
  cases h with
  | list _ => exact ⟨_, rfl⟩

mutual
/-- A well-formed expression stays well formed when the resolver accepts more. -/
theorem WF.mono {R₁ R₂ : Name → Array Kind → Prop} {scope : Array Kind}
    (hR : ∀ n ks, R₁ n ks → R₂ n ks) : ∀ {k : Kind} {e : Raw}, WF R₁ scope k e → WF R₂ scope k e
  | _, _, .var h => .var h
  | _, _, .app ref size argsWF => .app (hR _ _ ref) size fun i h => WF.mono hR (argsWF i h)
  | _, _, .list elemsWF => .list fun a ha => WFElem.mono hR (elemsWF a ha)

/-- The element form of `WF.mono`. -/
theorem WFElem.mono {R₁ R₂ : Name → Array Kind → Prop} {scope : Array Kind}
    (hR : ∀ n ks, R₁ n ks → R₂ n ks) : ∀ {e : Raw}, WFElem R₁ scope e → WFElem R₂ scope e
  | _, .ty h => .ty (WF.mono hR h)
  | _, .splice h => .splice h
end

mutual
/-- Extending the scope keeps a well-formed expression well formed. -/
theorem WF.weaken {R : Name → Array Kind → Prop} {scope : Array Kind} (ks : Array Kind) :
    ∀ {k : Kind} {e : Raw}, WF R scope k e → WF R (scope ++ ks) k e
  | _, _, .var h =>
    .var (by rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp h).1]; exact h)
  | _, _, .app ref size argsWF => .app ref size fun i h => WF.weaken ks (argsWF i h)
  | _, _, .list elemsWF => .list fun a ha => WFElem.weaken ks (elemsWF a ha)

/-- The element form of `WF.weaken`. -/
theorem WFElem.weaken {R : Name → Array Kind → Prop} {scope : Array Kind} (ks : Array Kind) :
    ∀ {e : Raw}, WFElem R scope e → WFElem R (scope ++ ks) e
  | _, .ty h => .ty (WF.weaken ks h)
  | _, .splice h =>
    .splice (by rw [Array.getElem?_append_left (Array.getElem?_eq_some_iff.mp h).1]; exact h)
end

/-- What an application's well-formedness says about its head: it takes its arguments'
kinds. -/
theorem WF.refBefore {R : Name → Array Kind → Prop} {scope : Array Kind} {k : Kind} {n : Name}
    {as : Array Raw} (h : WF R scope k (.app n as)) : R n (as.map (Raw.kind scope)) := by
  cases h with
  | @app _ _ ks ref size argsWF =>
    have : as.map (Raw.kind scope) = ks :=
      Array.ext (by simp [size]) fun i h₁ _ => by simpa using (argsWF i (by simpa using h₁)).kind_eq
    exact this ▸ ref

/-- What an application's well-formedness says about its arguments. -/
theorem WF.args {R : Name → Array Kind → Prop} {scope : Array Kind} {k : Kind} {n : Name}
    {as : Array Raw} (h : WF R scope k (.app n as)) : ∀ a ∈ as, WFRel R scope a := by
  cases h with
  | app _ _ argsWF =>
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ha
    exact (argsWF i hi).wfRel

/-- What a list literal's well-formedness says about its elements. -/
theorem WF.elems {R : Name → Array Kind → Prop} {scope : Array Kind} {k : Kind} {es : Array Raw}
    (h : WF R scope k (.list es)) : ∀ a ∈ es, WFElem R scope a := by
  cases h with | list hes => exact hes

/-- An element of type kind is a type: a list variable is the one other element. -/
theorem WFElem.wfType {R : Name → Array Kind → Prop} {scope : Array Kind} {a : Raw}
    (h : WFElem R scope a) (hk : a.kind scope = .type) : WFType R scope a := by
  cases h with
  | ty h => exact h
  | splice hj => simp [Raw.kind, hj] at hk

/-- An element is not a literal. -/
theorem WFElem.isElem {R : Name → Array Kind → Prop} {scope : Array Kind} {a : Raw} :
    WFElem R scope a → a.isElem = true
  | .ty h => by cases h <;> rfl
  | .splice _ => rfl

/-- In the empty scope, a literal's elements are types: there is no list variable to splice. -/
theorem WF.elems_closed {R : Name → Array Kind → Prop} {k : Kind} {es : Array Raw}
    (h : WF R #[] k (.list es)) : ∀ a ∈ es, WFType R #[] a := by
  intro a ha
  cases h.elems a ha with
  | ty h => exact h
  | splice h => simp at h

/-- What an argument of kind `k` contributes to a literal it is spliced into: itself, for a
type, and its elements, for a list. -/
private theorem WF.spliced {R : Name → Array Kind → Prop} {scope : Array Kind} {k : Kind}
    {a : Raw} (h : WF R scope k a) : ∀ x ∈ a.spliced, WFElem R scope x := by
  cases h with
  | var hi => simpa [Raw.spliced] using WFElem.ty (.var hi)
  | app ref size argsWF => simpa [Raw.spliced] using WFElem.ty (.app ref size argsWF)
  | @list es hes =>
    obtain ⟨es⟩ := es
    intro x hx
    exact hes x (by simpa [Raw.spliced] using hx)

mutual
/-- Instantiating the variables of `scope` by expressions of `scope₁`, each well formed at its
variable's kind, keeps an expression well formed at its kind. -/
theorem WF.instantiate {R : Name → Array Kind → Prop} {scope scope₁ : Array Kind}
    {args : Array Raw}
    (hargs : ∀ (i : Nat) (hi : i < scope.size), ∃ a, args[i]? = some a ∧ WF R scope₁ scope[i] a) :
    ∀ {k : Kind} {e : Raw}, WF R scope k e → WF R scope₁ k (e.instantiate args)
  | _, _, @WF.var _ _ i hi => by
    have lt : i < scope.size := (Array.getElem?_eq_some_iff.mp hi).1
    obtain ⟨a, ha, hw⟩ := hargs i lt
    have hk : scope[i] = .type := by simpa [Array.getElem?_eq_getElem lt] using hi
    simpa [Raw.instantiate, ha, hk] using hw
  | _, _, @WF.app _ _ n as ks ref size argsWF => by
    rw [Raw.instantiate_app]
    exact .app ref (by simpa using size) fun i h =>
      by simpa using WF.instantiate hargs (argsWF i (by simpa using h))
  | _, _, @WF.list _ _ es hes => by
    rw [Raw.instantiate_list]
    refine .list fun x hx => ?_
    obtain ⟨b, hb, hx⟩ : ∃ b ∈ es, x ∈ Raw.instantiateElem args b := by simpa using hx
    exact WFElem.instantiate hargs (hes b hb) x hx

/-- The element form of `WF.instantiate`: what an element instantiates to, spliced in. -/
theorem WFElem.instantiate {R : Name → Array Kind → Prop} {scope scope₁ : Array Kind}
    {args : Array Raw}
    (hargs : ∀ (i : Nat) (hi : i < scope.size), ∃ a, args[i]? = some a ∧ WF R scope₁ scope[i] a) :
    ∀ {e : Raw}, WFElem R scope e → ∀ x ∈ Raw.instantiateElem args e, WFElem R scope₁ x
  | _, @WFElem.ty _ _ e h => by
    have he := WF.instantiate hargs h
    cases h with
    | @var i hi =>
      have lt : i < scope.size := (Array.getElem?_eq_some_iff.mp hi).1
      obtain ⟨a, ha, hw⟩ := hargs i lt
      simpa [Raw.instantiateElem, ha] using hw.spliced
    | app _ _ _ => simpa [Raw.instantiateElem] using WFElem.ty he
  | _, @WFElem.splice _ _ j hj => by
    have lt : j < scope.size := (Array.getElem?_eq_some_iff.mp hj).1
    obtain ⟨a, ha, hw⟩ := hargs j lt
    simpa [Raw.instantiateElem, ha] using hw.spliced
end

end TypeExpr

namespace Decl.Raw

end Decl.Raw

namespace RegionSig.Raw

/-- A region signature is well formed in `scope` when its parameter types and its return type
are well-formed types, and its parameters are named distinctly.  `scope` is the enclosing
instruction's: a region binds no variables of its own. -/
def WF (R : Name → Array Kind → Prop) (scope : Array Kind) (r : RegionSig.Raw) : Prop :=
  (∀ p ∈ r.params, TypeExpr.WFType R scope p.type)
    ∧ TypeExpr.WFType R scope r.returnType
    ∧ r.paramNames.Nodup

/-- Build well-formedness from the three component obligations. -/
theorem wf_mk {R : Name → Array Kind → Prop} {scope : Array Kind} {r : RegionSig.Raw}
    (hparams : ∀ p ∈ r.params, TypeExpr.WFType R scope p.type)
    (hret : TypeExpr.WFType R scope r.returnType)
    (hnames : r.paramNames.Nodup) : WF R scope r :=
  ⟨hparams, hret, hnames⟩

/-- The parameter types of a well-formed region signature are well formed. -/
theorem wf_params {R : Name → Array Kind → Prop} {scope : Array Kind} {r : RegionSig.Raw}
    (h : WF R scope r) : ∀ p ∈ r.params, TypeExpr.WFType R scope p.type := h.1

/-- The return type of a well-formed region signature is well formed. -/
theorem wf_returnType {R : Name → Array Kind → Prop} {scope : Array Kind} {r : RegionSig.Raw}
    (h : WF R scope r) : TypeExpr.WFType R scope r.returnType := h.2.1

/-- The parameters of a well-formed region signature are named distinctly. -/
theorem wf_paramNames {R : Name → Array Kind → Prop} {scope : Array Kind} {r : RegionSig.Raw}
    (h : WF R scope r) : r.paramNames.Nodup := h.2.2

/-- A region signature stays well formed when the resolver accepts more. -/
theorem WF.mono {R R' : Name → Array Kind → Prop} {scope : Array Kind} {r : RegionSig.Raw}
    (hR : ∀ n ks, R n ks → R' n ks) (h : r.WF R scope) : r.WF R' scope :=
  ⟨fun p hp => (h.1 p hp).mono hR,
    h.2.1.mono hR, h.2.2⟩

end RegionSig.Raw

namespace InsnDecl.Raw

/-- An instruction is well formed when its parameter types, its return type if it has one, the
signature of each region it takes and the payload types of each successor are well-formed types,
and its variadic's type is a well-formed type or list, each in the scope of the variables the
instruction binds; and when the names it binds (type parameters, arguments, the variadic,
regions and successors) are pairwise distinct. -/
def WF (R : Name → Array Kind → Prop) (d : InsnDecl.Raw α) : Prop :=
  (∀ p ∈ d.argTypes, TypeExpr.WFType R d.scope p.type)
    ∧ (∀ v ∈ d.variadic, TypeExpr.WFRel R d.scope v.type)
    ∧ (∀ t ∈ d.returnType, TypeExpr.WFType R d.scope t)
    ∧ (∀ r ∈ d.regions, r.type.WF R d.scope)
    ∧ (∀ s ∈ d.succs, ∀ t ∈ s.type, TypeExpr.WFType R d.scope t)
    ∧ d.paramNames.Nodup

/-- Build well-formedness from the six component obligations. -/
theorem wf_mk {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α}
    (hargs : ∀ p ∈ d.argTypes, TypeExpr.WFType R d.scope p.type)
    (hvar : ∀ v ∈ d.variadic, TypeExpr.WFRel R d.scope v.type)
    (hret : ∀ t ∈ d.returnType, TypeExpr.WFType R d.scope t)
    (hregions : ∀ r ∈ d.regions, r.type.WF R d.scope)
    (hsuccs : ∀ s ∈ d.succs, ∀ t ∈ s.type, TypeExpr.WFType R d.scope t)
    (hnames : d.paramNames.Nodup) : WF R d :=
  ⟨hargs, hvar, hret, hregions, hsuccs, hnames⟩

/-- The argument types of a well-formed instruction are well formed. -/
theorem wf_argTypes {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ p ∈ d.argTypes, TypeExpr.WFType R d.scope p.type := h.1

/-- The variadic type of a well-formed instruction, if any, is well formed: a type or a list. -/
theorem wf_variadic {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ v ∈ d.variadic, TypeExpr.WFRel R d.scope v.type := h.2.1

/-- The return type of a well-formed instruction, if any, is well formed. -/
theorem wf_returnType {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ t ∈ d.returnType, TypeExpr.WFType R d.scope t := h.2.2.1

/-- Every region signature of a well-formed instruction is well formed, under the
instruction's type variables. -/
theorem wf_regions {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ r ∈ d.regions, r.type.WF R d.scope := h.2.2.2.1

/-- Every payload type of every successor of a well-formed instruction is well formed, under
the instruction's type variables. -/
theorem wf_succs {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    ∀ s ∈ d.succs, ∀ t ∈ s.type, TypeExpr.WFType R d.scope t := h.2.2.2.2.1

/-- No two of the type parameters, arguments, variadic, regions and successors of a
well-formed instruction share a name. -/
theorem wf_paramNames {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α} (h : WF R d) :
    d.paramNames.Nodup := h.2.2.2.2.2

/-- An instruction stays well formed when the resolver accepts more. -/
theorem WF.mono {R R' : Name → Array Kind → Prop} {d : InsnDecl.Raw α}
    (hR : ∀ n ks, R n ks → R' n ks) (h : d.WF R) : d.WF R' :=
  ⟨fun p hp => (h.1 p hp).mono hR,
   fun t ht => (h.2.1 t ht).mono hR,
   fun t ht => (h.2.2.1 t ht).mono hR,
   fun r hr => (h.2.2.2.1 r hr).mono hR,
   fun s hs t ht => (h.2.2.2.2.1 s hs t ht).mono hR,
   h.2.2.2.2.2⟩

end InsnDecl.Raw

namespace Decl.Raw

/-- A declaration is well formed when the declaration it wraps is: a primitive type names
its parameters distinctly, and an instruction, a constructor included, is well formed. -/
def WF (R : Name → Array Kind → Prop) : Decl.Raw α → Prop
  | .type d => d.paramNames.Nodup
  -- `R` does not know a group's own members: `Env.Raw.checkGroup` checks the group, and a
  -- member alias checks nothing.
  | .dataHead _ => True
  | .dataRest .. => True
  | .insn d => InsnDecl.Raw.WF R d

/-- A well-formed declaration stays well formed when the resolver accepts more. -/
theorem WF.mono {R R' : Name → Array Kind → Prop} {d : Decl.Raw α}
    (hR : ∀ n ks, R n ks → R' n ks) (h : d.WF R) : d.WF R' := by
  cases d with
  | type t => exact h
  | dataHead g => trivial
  | dataRest _ _ _ => trivial
  | insn i => exact InsnDecl.Raw.WF.mono hR h

/-- A type declaration has no body, so it is well formed under any relation once its
parameters are named distinctly. -/
@[simp] theorem wf_type_iff {R : Name → Array Kind → Prop} {d : TypeDecl α} :
    WF R (.type d) ↔ d.paramNames.Nodup := Iff.rfl

/-- A group head is always well formed. -/
@[simp] theorem wf_dataHead {R : Name → Array Kind → Prop} (g : DataGroup α TypeExpr.Raw) :
    WF R (.dataHead g) := trivial

/-- A group member alias is always well formed. -/
@[simp] theorem wf_dataRest {R : Name → Array Kind → Prop} (n h : Name) (i : Nat) :
    WF R (.dataRest (α := α) n h i) := trivial

/-- Well-formedness of a wrapped instruction declaration is the instruction's own. -/
@[simp] theorem wf_insn_iff {R : Name → Array Kind → Prop} {d : InsnDecl.Raw α} :
    WF R (.insn d) ↔ InsnDecl.Raw.WF R d := Iff.rfl

end Decl.Raw

namespace Env.Raw

/-- `name` resolves to a type declaration whose arguments have kinds `kinds` that occurs
*strictly before* position `i` of the environment.  A wrong number of arguments and a
mis-kinded one fail alike. -/
def RefBefore (env : Env.Raw α) (i : Nat) (name : Name) (kinds : Array Kind) : Prop :=
  match (env.types.before i)[name]? with
  | some t => t.kinds = kinds
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

/-- `RefBefore` holds exactly when the `before` view yields a type of those kinds. -/
theorem refBefore_iff_getElem? {env : Env.Raw α} {i : Nat} {name : Name} {kinds : Array Kind} :
    env.RefBefore i name kinds ↔
      ∃ t, (env.types.before i)[name]? = some t ∧ t.kinds = kinds := by
  unfold RefBefore
  cases hv : (env.types.before i)[name]? <;> simp

/-- `RefBefore` spelled out positionally: the name has a position before `i`, and what is
declared there denotes a type of the right kinds, a group member or a group head. -/
theorem refBefore_iff {env : Env.Raw α} {i : Nat} {name : Name} {kinds : Array Kind} :
    env.RefBefore i name kinds ↔
      ∃ j t, IndexMap.idxOf? env.decls name = some j ∧ j < i ∧
        env.typeOf? name = some t ∧ t.kinds = kinds := by
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

/-- Raising the position bound keeps a reference valid. -/
theorem RefBefore.mono {env : Env.Raw α} {i j : Nat} (h : i ≤ j) {name : Name}
    {kinds : Array Kind} (hr : env.RefBefore i name kinds) : env.RefBefore j name kinds := by
  obtain ⟨k, t, hk, hki, hget, ha⟩ := refBefore_iff.mp hr
  exact refBefore_iff.mpr ⟨k, t, hk, Nat.lt_of_lt_of_le hki h, hget, ha⟩

end Env.Raw

/-! ### Checking an environment

A declaration is checked against the environment itself: `RefBefore` is a hash-map lookup
plus a position comparison.  None of this reduces in the kernel, because `String.hash` is
`opaque`; obligations are checked by `#guard` or proved by a tactic. -/

namespace Env.Raw

/-- Decision procedure for `RefBefore`: one lookup in `types.before i`. -/
@[expose]
def RefBefore.check (env : Env.Raw α) (i : Nat) (name : Name) (kinds : Array Kind) : Bool :=
  match (env.types.before i)[name]? with
  | some t => t.kinds == kinds
  | none => false

/-- Rewrites a passing `RefBefore.check` to `RefBefore`. -/
@[simp] theorem refBefore_check_eq_true {env : Env.Raw α} {i : Nat} {name : Name}
    {kinds : Array Kind} :
    RefBefore.check env i name kinds = true ↔ env.RefBefore i name kinds := by
  unfold RefBefore.check RefBefore
  cases (env.types.before i)[name]? <;> simp

end Env.Raw

namespace TypeExpr.Raw

mutual
/-- Decision procedure for `WFRel`, abstracted over the resolver as `WFRel` is: `R name ks`
decides "this expression may mention `name` as a type whose arguments have kinds `ks`".
Arguments are matched through `Array.mk`, which keeps both functions structurally
recursive. -/
@[expose]
def check (R : Name → Array Kind → Bool) (scope : Array Kind) : Raw → Bool
  | .var k => scope[k]? == some .type
  | .app name ⟨args⟩ => R name ⟨args.map (kind scope)⟩ && checkList R scope args
  | .list ⟨es⟩ => checkElems R scope es && es.all isElem

@[expose]
def checkList (R : Name → Array Kind → Bool) (scope : Array Kind) : List Raw → Bool
  | [] => true
  | e :: es => check R scope e && checkList R scope es

/-- The elements of a literal: a variable in scope, of either kind, or an expression that
passes `check`. -/
@[expose]
def checkElems (R : Name → Array Kind → Bool) (scope : Array Kind) : List Raw → Bool
  | [] => true
  | e :: es =>
    (match e with
     | .var j => decide (j < scope.size)
     | _ => check R scope e) && checkElems R scope es
end

/-- `checkElems` passes the variables in scope and checks everything else. -/
theorem checkElems_iff {R : Name → Array Kind → Bool} {scope : Array Kind} :
    ∀ l : List Raw, checkElems R scope l = true ↔
      ∀ a ∈ l, (a.isVar = false → check R scope a = true) ∧ (∀ j, a = .var j → j < scope.size)
  | [] => by simp [checkElems]
  | .var j :: l => by simp [checkElems, isVar, checkElems_iff l]
  | .app n as :: l => by simp [checkElems, isVar, checkElems_iff l]
  | .list es :: l => by simp [checkElems, isVar, checkElems_iff l]

/-- An element of a literal is well formed when it is a variable in scope, of either kind, or
well formed and not a literal. -/
theorem wfElem_of {Rel : Name → Array Kind → Prop} {scope : Array Kind} {a : Raw}
    (hw : a.isVar = false → WFRel Rel scope a) (hv : ∀ j, a = .var j → j < scope.size)
    (hel : a.isElem = true) : WFElem Rel scope a := by
  cases a with
  | var j =>
    obtain ⟨k, hk⟩ : ∃ k, scope[j]? = some k := ⟨_, Array.getElem?_eq_getElem (hv j rfl)⟩
    cases k with
    | type => exact .ty (.var hk)
    | list => exact .splice hk
  | app _ _ => exact .ty (hw rfl)
  | list _ => simp [isElem] at hel

mutual
/-- Soundness of `check`: what it accepts is well formed, at its kind, under any relation its
resolver implies. -/
theorem wfRel_of_check {R : Name → Array Kind → Bool} {Rel : Name → Array Kind → Prop}
    (hR : ∀ n ks, R n ks = true → Rel n ks) {scope : Array Kind} :
    ∀ (e : Raw), check R scope e = true → WFRel Rel scope e
  | .var i, h => by
    have h : scope[i]? = some .type := by simpa [check] using h
    simpa [WFRel, kind, h] using WF.var (R := Rel) h
  | .app _ ⟨args⟩, h => by
    simp only [check, Bool.and_eq_true] at h
    have hargs := wfRel_of_checkList hR args h.2
    exact .app (hR _ _ (by simpa using h.1)) (by simp) fun i hi => by
      simpa using hargs _ (by simp)
  | .list ⟨es⟩, h => by
    simp only [check, Bool.and_eq_true, List.all_eq_true] at h
    have hvars := (checkElems_iff es).mp h.1
    have hw := wfRel_of_checkElems hR es h.1
    exact .list fun a ha => wfElem_of (hw a (by simpa using ha))
      (fun j hj => (hvars _ (by simpa using ha)).2 j hj) (h.2 a (by simpa using ha))
termination_by e _ => sizeOf e
decreasing_by all_goals (simp_wf; omega)

/-- The list form of `wfRel_of_check`. -/
theorem wfRel_of_checkList {R : Name → Array Kind → Bool} {Rel : Name → Array Kind → Prop}
    (hR : ∀ n ks, R n ks = true → Rel n ks) {scope : Array Kind} :
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

/-- The literal form of `wfRel_of_check`: what `checkElems` accepts that is not a variable is
well formed. -/
theorem wfRel_of_checkElems {R : Name → Array Kind → Bool} {Rel : Name → Array Kind → Prop}
    (hR : ∀ n ks, R n ks = true → Rel n ks) {scope : Array Kind} :
    ∀ (es : List Raw), checkElems R scope es = true → ∀ a ∈ es, a.isVar = false →
      WFRel Rel scope a
  | [], _ => by simp
  | e :: es, h => by
    have hes : ∀ a ∈ es, a.isVar = false → WFRel Rel scope a :=
      wfRel_of_checkElems hR es (by cases e <;> simp_all [checkElems])
    have he : e.isVar = false → WFRel Rel scope e := fun hv =>
      wfRel_of_check hR e (((checkElems_iff (e :: es)).mp h e List.mem_cons_self).1 hv)
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact he
    · exact hes a ha
termination_by es _ => sizeOf es + 1
decreasing_by all_goals (simp_wf; omega)
end

/-! ### Datatype payloads

A constructor's payload is checked against three things, none of which is an environment: a
resolver `R` for the positions where recursion is allowed, a resolver `Rneg` for the
positions where it is not, and a lookup `paramsOf` giving each type constructor's parameters.
A list literal takes the polarity of its position, and each element is checked there.  A
payload's scope is its member's parameters, so a list parameter is a list variable, spliced into a
literal; `[*as]` is the whole list. -/

mutual
/-- Whether de Bruijn level `l` occurs in the expression at all.  Inspects only `var`
nodes. -/
@[expose]
def varOccurs (l : Nat) : Raw → Bool
  | .var k => k == l
  | .app _ ⟨args⟩ => varOccursList l args
  | .list ⟨es⟩ => varOccursList l es

@[expose]
def varOccursList (l : Nat) : List Raw → Bool
  | [] => false
  | e :: es => varOccurs l e || varOccursList l es
end

mutual
/-- Whether every occurrence of level `l` sits in a parameter declared `.pos`. -/
@[expose]
def varPositive (paramsOf : Name → Option (Array (Param TyParam))) (l : Nat) : Raw → Bool
  | .var _ => true
  | .app n ⟨args⟩ =>
    match paramsOf n with
    | none => false
    | some ⟨ps⟩ => ps.length == args.length && varPositiveArgs paramsOf l ps args
  | .list ⟨es⟩ => varPositiveList paramsOf l es

@[expose]
def varPositiveArgs (paramsOf : Name → Option (Array (Param TyParam))) (l : Nat) :
    List (Param TyParam) → List Raw → Bool
  | [], [] => true
  | ⟨_, ⟨.pos, _⟩⟩ :: ps, e :: es => varPositive paramsOf l e && varPositiveArgs paramsOf l ps es
  | ⟨_, ⟨.non, _⟩⟩ :: ps, e :: es => !varOccurs l e && varPositiveArgs paramsOf l ps es
  | _, _ => false

@[expose]
def varPositiveList (paramsOf : Name → Option (Array (Param TyParam))) (l : Nat) :
    List Raw → Bool
  | [] => true
  | e :: es => varPositive paramsOf l e && varPositiveList paramsOf l es
end

mutual
/-- Whether a payload is well formed *and* keeps its recursion positive.

`R` applies where recursion is allowed.  Passing through a parameter declared `.non`
switches to `Rneg`, `R` with the group's own types withheld, for the rest of the subterm. -/
@[expose]
def checkPayload (paramsOf : Name → Option (Array (Param TyParam)))
    (R Rneg : Name → Array Kind → Bool) (scope : Array Kind) : Raw → Bool
  | .var k => scope[k]? == some .type
  | .app n ⟨args⟩ =>
    R n ⟨args.map (kind scope)⟩ &&
      (match paramsOf n with
       | none => false
       | some ⟨ps⟩ =>
         ps.length == args.length && checkPayloadArgs paramsOf R Rneg scope ps args)
  | .list ⟨es⟩ => checkPayloadList paramsOf R Rneg scope es && es.all isElem

@[expose]
def checkPayloadArgs (paramsOf : Name → Option (Array (Param TyParam)))
    (R Rneg : Name → Array Kind → Bool) (scope : Array Kind) :
    List (Param TyParam) → List Raw → Bool
  | [], [] => true
  | ⟨_, ⟨.pos, _⟩⟩ :: ps, e :: es =>
    checkPayload paramsOf R Rneg scope e && checkPayloadArgs paramsOf R Rneg scope ps es
  | ⟨_, ⟨.non, _⟩⟩ :: ps, e :: es =>
    check Rneg scope e && checkPayloadArgs paramsOf R Rneg scope ps es
  | _, _ => false

/-- The elements of a literal: a variable in scope, of either kind, or a payload. -/
@[expose]
def checkPayloadList (paramsOf : Name → Option (Array (Param TyParam)))
    (R Rneg : Name → Array Kind → Bool) (scope : Array Kind) : List Raw → Bool
  | [] => true
  | e :: es =>
    (match e with
     | .var j => decide (j < scope.size)
     | _ => checkPayload paramsOf R Rneg scope e) && checkPayloadList paramsOf R Rneg scope es
end

/-! ### Monotonicity

Each traversal accepts more when its resolvers accept more and its parameter lookup keeps
answering what it answered. -/

mutual
/-- `check` accepts more when its resolver accepts more. -/
theorem check_mono {R R' : Name → Array Kind → Bool}
    (hR : ∀ n ks, R n ks = true → R' n ks = true) {scope : Array Kind} :
    ∀ e : Raw, check R scope e = true → check R' scope e = true
  | .var _, h => h
  | .app _ ⟨args⟩, h => by
    simp only [check, Bool.and_eq_true] at h ⊢
    exact ⟨hR _ _ h.1, checkList_mono hR args h.2⟩
  | .list ⟨es⟩, h => by
    simp only [check, Bool.and_eq_true] at h ⊢
    exact ⟨checkElems_mono hR es h.1, h.2⟩

/-- The list form of `check_mono`. -/
theorem checkList_mono {R R' : Name → Array Kind → Bool}
    (hR : ∀ n ks, R n ks = true → R' n ks = true) {scope : Array Kind} :
    ∀ es : List Raw, checkList R scope es = true → checkList R' scope es = true
  | [], _ => by simp [checkList]
  | e :: es, h => by
    simp only [checkList, Bool.and_eq_true] at h ⊢
    exact ⟨check_mono hR e h.1, checkList_mono hR es h.2⟩

/-- The literal form of `check_mono`. -/
theorem checkElems_mono {R₁ R₂ : Name → Array Kind → Bool}
    (hR : ∀ n ks, R₁ n ks = true → R₂ n ks = true) {scope : Array Kind} :
    ∀ es : List Raw, checkElems R₁ scope es = true → checkElems R₂ scope es = true
  | [], _ => by simp [checkElems]
  | e :: es, h => by
    have he := check_mono hR (scope := scope) e
    simp only [checkElems, Bool.and_eq_true] at h ⊢
    refine ⟨?_, checkElems_mono hR es h.2⟩
    cases e with
    | var => exact h.1
    | app => exact he h.1
    | list => exact he h.1
end

mutual
/-- `varPositive` accepts more when the parameter lookup keeps its answers. -/
theorem varPositive_mono {P P' : Name → Option (Array (Param TyParam))}
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
  | .list ⟨es⟩, h => by
    simp only [varPositive] at h ⊢
    exact varPositiveList_mono hp es h

/-- The argument form of `varPositive_mono`. -/
theorem varPositiveArgs_mono {P P' : Name → Option (Array (Param TyParam))}
    (hp : ∀ n ps, P n = some ps → P' n = some ps) {l : Nat} :
    ∀ (ps : List (Param TyParam)) (es : List Raw), varPositiveArgs P l ps es = true →
      varPositiveArgs P' l ps es = true
  | [], [], _ => by simp [varPositiveArgs]
  | ⟨_, ⟨.pos, _⟩⟩ :: ps, e :: es, h => by
    simp only [varPositiveArgs, Bool.and_eq_true] at h ⊢
    exact ⟨varPositive_mono hp e h.1, varPositiveArgs_mono hp ps es h.2⟩
  | ⟨_, ⟨.non, _⟩⟩ :: ps, e :: es, h => by
    simp only [varPositiveArgs, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, varPositiveArgs_mono hp ps es h.2⟩
  | [], _ :: _, h => by simp [varPositiveArgs] at h
  | _ :: _, [], h => by simp [varPositiveArgs] at h

/-- The list-literal form of `varPositive_mono`. -/
theorem varPositiveList_mono {P P' : Name → Option (Array (Param TyParam))}
    (hp : ∀ n ps, P n = some ps → P' n = some ps) {l : Nat} :
    ∀ es : List Raw, varPositiveList P l es = true → varPositiveList P' l es = true
  | [], _ => rfl
  | e :: es, h => by
    simp only [varPositiveList, Bool.and_eq_true] at h ⊢
    exact ⟨varPositive_mono hp e h.1, varPositiveList_mono hp es h.2⟩
end

mutual
/-- `checkPayload` accepts more when its resolvers do and its lookup keeps its answers. -/
theorem checkPayload_mono {P P' : Name → Option (Array (Param TyParam))}
    {R R' N N' : Name → Array Kind → Bool}
    (hp : ∀ n ps, P n = some ps → P' n = some ps)
    (hR : ∀ n ks, R n ks = true → R' n ks = true)
    (hN : ∀ n ks, N n ks = true → N' n ks = true) {scope : Array Kind} :
    ∀ e : Raw, checkPayload P R N scope e = true → checkPayload P' R' N' scope e = true
  | .var _, h => h
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
  | .list ⟨es⟩, h => by
    simp only [checkPayload, Bool.and_eq_true] at h ⊢
    exact ⟨checkPayloadList_mono hp hR hN es h.1, h.2⟩

/-- The argument form of `checkPayload_mono`. -/
theorem checkPayloadArgs_mono {P P' : Name → Option (Array (Param TyParam))}
    {R R' N N' : Name → Array Kind → Bool}
    (hp : ∀ n ps, P n = some ps → P' n = some ps)
    (hR : ∀ n ks, R n ks = true → R' n ks = true)
    (hN : ∀ n ks, N n ks = true → N' n ks = true) {scope : Array Kind} :
    ∀ (ps : List (Param TyParam)) (es : List Raw), checkPayloadArgs P R N scope ps es = true →
      checkPayloadArgs P' R' N' scope ps es = true
  | [], [], _ => by simp [checkPayloadArgs]
  | ⟨_, ⟨.pos, _⟩⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h ⊢
    exact ⟨checkPayload_mono hp hR hN e h.1, checkPayloadArgs_mono hp hR hN ps es h.2⟩
  | ⟨_, ⟨.non, _⟩⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h ⊢
    exact ⟨check_mono hN e h.1, checkPayloadArgs_mono hp hR hN ps es h.2⟩
  | [], _ :: _, h => by simp [checkPayloadArgs] at h
  | _ :: _, [], h => by simp [checkPayloadArgs] at h

/-- The list-literal form of `checkPayload_mono`. -/
theorem checkPayloadList_mono {P P' : Name → Option (Array (Param TyParam))}
    {R R' N N' : Name → Array Kind → Bool}
    (hp : ∀ n ps, P n = some ps → P' n = some ps)
    (hR : ∀ n ks, R n ks = true → R' n ks = true)
    (hN : ∀ n ks, N n ks = true → N' n ks = true) {scope : Array Kind} :
    ∀ es : List Raw, checkPayloadList P R N scope es = true →
      checkPayloadList P' R' N' scope es = true
  | [], _ => by simp [checkPayloadList]
  | e :: es, h => by
    have he := checkPayload_mono hp hR hN (scope := scope) e
    simp only [checkPayloadList, Bool.and_eq_true] at h ⊢
    refine ⟨?_, checkPayloadList_mono hp hR hN es h.2⟩
    cases e with
    | var => exact h.1
    | app => exact he h.1
    | list => exact he h.1
end

mutual
/-- A payload that keeps its recursion positive is well formed against `R`, when what a
`.non` position may refer to `R` accepts too.  So a constructor's payload is an argument type
its instruction may declare. -/
theorem check_of_checkPayload {P : Name → Option (Array (Param TyParam))}
    {R N : Name → Array Kind → Bool} (hN : ∀ n ks, N n ks = true → R n ks = true)
    {scope : Array Kind} : ∀ e : Raw, checkPayload P R N scope e = true → check R scope e = true
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
  | .list ⟨es⟩, h => by
    simp only [checkPayload, Bool.and_eq_true] at h
    simp only [check, Bool.and_eq_true]
    exact ⟨checkElems_of_checkPayloadList hN es h.1, h.2⟩

/-- The argument form of `check_of_checkPayload`. -/
theorem checkList_of_checkPayloadArgs {P : Name → Option (Array (Param TyParam))}
    {R N : Name → Array Kind → Bool} (hN : ∀ n ks, N n ks = true → R n ks = true)
    {scope : Array Kind} :
    ∀ (ps : List (Param TyParam)) (es : List Raw), checkPayloadArgs P R N scope ps es = true →
      checkList R scope es = true
  | [], [], _ => rfl
  | ⟨_, ⟨.pos, _⟩⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h
    simp only [checkList, Bool.and_eq_true]
    exact ⟨check_of_checkPayload hN e h.1, checkList_of_checkPayloadArgs hN ps es h.2⟩
  | ⟨_, ⟨.non, _⟩⟩ :: ps, e :: es, h => by
    simp only [checkPayloadArgs, Bool.and_eq_true] at h
    simp only [checkList, Bool.and_eq_true]
    exact ⟨check_mono hN e h.1, checkList_of_checkPayloadArgs hN ps es h.2⟩
  | [], _ :: _, h => by simp [checkPayloadArgs] at h
  | _ :: _, [], h => by simp [checkPayloadArgs] at h

/-- The list-literal form of `check_of_checkPayload`. -/
theorem checkElems_of_checkPayloadList {P : Name → Option (Array (Param TyParam))}
    {R N : Name → Array Kind → Bool} (hN : ∀ n ks, N n ks = true → R n ks = true)
    {scope : Array Kind} :
    ∀ es : List Raw, checkPayloadList P R N scope es = true → checkElems R scope es = true
  | [], _ => by simp [checkElems]
  | e :: es, h => by
    have he := check_of_checkPayload (P := P) hN (scope := scope) e
    simp only [checkPayloadList, Bool.and_eq_true] at h
    simp only [checkElems, Bool.and_eq_true]
    refine ⟨?_, checkElems_of_checkPayloadList hN es h.2⟩
    cases e with
    | var => exact h.1
    | app => exact he h.1
    | list => exact he h.1
end

/-- `checkList` is `check` of every element. -/
private theorem checkList_iff {R : Name → Array Kind → Bool} {scope : Array Kind} :
    ∀ l : List Raw, checkList R scope l = true ↔ ∀ a ∈ l, check R scope a = true
  | [] => by simp [checkList]
  | a :: l => by simp [checkList, checkList_iff l]

/-- An application is well formed when its head is accepted at its arguments' kinds and
every argument is well formed. -/
theorem check_app {R : Name → Array Kind → Bool} {scope : Array Kind} {n : Name}
    {as : Array Raw} :
    check R scope (.app n as) = true ↔
      R n (as.map (kind scope)) = true ∧ ∀ a ∈ as, check R scope a = true := by
  obtain ⟨as⟩ := as
  simp [check, checkList_iff]

/-- A list literal is well formed when its elements are types or splices: every element that
is not a variable is well formed, and every variable is in scope. -/
theorem check_list {R : Name → Array Kind → Bool} {scope : Array Kind} {es : Array Raw} :
    check R scope (.list es) = true ↔
      (∀ a ∈ es, a.isVar = false → check R scope a = true) ∧
        (∀ j, Raw.var j ∈ es → j < scope.size) ∧ ∀ a ∈ es, a.isElem = true := by
  obtain ⟨es⟩ := es
  simp only [check, Bool.and_eq_true, checkElems_iff, List.all_eq_true]
  constructor
  · rintro ⟨h, hel⟩
    exact ⟨fun a ha => (h a (by simpa using ha)).1, fun j hj => (h _ (by simpa using hj)).2 j rfl,
      fun a ha => hel a (by simpa using ha)⟩
  · rintro ⟨h, hv, hel⟩
    exact ⟨fun a ha => ⟨h a (by simpa using ha), fun j hj => hv j (hj ▸ by simpa using ha)⟩,
      fun a ha => hel a (by simpa using ha)⟩

mutual
/-- The converse of `wfRel_of_check`: a well-formed expression passes the check of any
resolver that accepts what the relation does. -/
theorem check_of_wf {R : Name → Array Kind → Bool} {Rel : Name → Array Kind → Prop}
    (hR : ∀ n ks, Rel n ks → R n ks = true) {scope : Array Kind} :
    ∀ {k : Kind} {e : Raw}, TypeExpr.WF Rel scope k e → check R scope e = true
  | _, _, .var h => by simp [check, h]
  | _, _, h@(.app ref size argsWF) => check_app.mpr ⟨hR _ _ h.refBefore, fun a ha => by
      obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp ha
      exact check_of_wf hR (argsWF i hi)⟩
  | _, _, .list elemsWF => check_list.mpr
      ⟨fun a ha => (checkElem_of_wfElem hR (elemsWF a ha)).1,
       fun j hj => (checkElem_of_wfElem hR (elemsWF _ hj)).2 j rfl,
       fun a ha => (elemsWF a ha).isElem⟩

/-- The element form of `check_of_wf`. -/
theorem checkElem_of_wfElem {R : Name → Array Kind → Bool} {Rel : Name → Array Kind → Prop}
    (hR : ∀ n ks, Rel n ks → R n ks = true) {scope : Array Kind} :
    ∀ {a : Raw}, TypeExpr.WFElem Rel scope a →
      (a.isVar = false → check R scope a = true) ∧ (∀ j, a = .var j → j < scope.size)
  | _, .ty h => ⟨fun _ => check_of_wf hR h, fun j hj => by
      subst hj
      exact (Array.getElem?_eq_some_iff.mp (TypeExpr.wfType_var_iff.mp h)).1⟩
  | _, .splice h => ⟨fun hv => by simp [isVar] at hv, fun j hj => by
      cases hj
      exact (Array.getElem?_eq_some_iff.mp h).1⟩
end

/-- `check_of_wf`, at the expression's own kind. -/
theorem check_of_wfRel {R : Name → Array Kind → Bool} {Rel : Name → Array Kind → Prop}
    (hR : ∀ n ks, Rel n ks → R n ks = true) {scope : Array Kind} {e : Raw}
    (h : TypeExpr.WFRel Rel scope e) : check R scope e = true :=
  check_of_wf hR h

/-- The declared-before-use resolver, against which a declaration outside a mutual group is
checked. -/
@[expose]
def checkAt (env : Env.Raw α) (i : Nat) (scope : Array Kind) : Raw → Bool :=
  check (Env.Raw.RefBefore.check env i) scope

/-- `checkAt`, for a type: the expression is well formed, and a type rather than a list. -/
@[expose]
def checkTypeAt (env : Env.Raw α) (i : Nat) (scope : Array Kind) (e : Raw) : Bool :=
  e.kind scope == .type && checkAt env i scope e

/-- Soundness of `checkAt`. -/
theorem wfRel_of_checkAt {env : Env.Raw α} {i : Nat} {scope : Array Kind} (e : Raw)
    (h : checkAt env i scope e = true) : WFRel (env.RefBefore i) scope e :=
  wfRel_of_check (fun _ _ hb => Env.Raw.refBefore_check_eq_true.mp hb) e h

/-- Soundness of `checkTypeAt`. -/
theorem wfType_of_checkTypeAt {env : Env.Raw α} {i : Nat} {scope : Array Kind} (e : Raw)
    (h : checkTypeAt env i scope e = true) : WFType (env.RefBefore i) scope e := by
  simp only [checkTypeAt, Bool.and_eq_true, beq_iff_eq] at h
  exact WF.of_wfRel (wfRel_of_checkAt e h.2) h.1

end TypeExpr.Raw

namespace DataGroup

/-! ### What a mutual group owes, abstractly

A group is checked against three resolvers and nothing else: what a name's parameters are,
what a payload position may refer to, and what a `.non` position may refer to. -/

/-- Every payload of every constructor of every member is a type that resolves, keeps its
recursion in parameters declared `.pos`, and respects what its own member declared about its
parameters.  A payload's scope is its member's parameters: `TyParam.kinds m.params`. -/
@[expose]
def checkWith (g : DataGroup α TypeExpr.Raw)
    (paramsOf : Name → Option (Array (Param TyParam)))
    (inGroup outside : Name → Array Kind → Bool) : Bool :=
  g.members.all fun m =>
    m.ctors.all fun c =>
      c.args.all fun p =>
        p.type.kind (TyParam.kinds m.params) == .type
          && TypeExpr.Raw.checkPayload paramsOf inGroup outside (TyParam.kinds m.params) p.type
          && m.params.zipIdx.all fun (pol, k) =>
              match pol.type.polarity with
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

/-- `checkWith` accepts more when its resolvers accept more and its lookup keeps its answers. -/
theorem checkWith_mono {g : DataGroup α TypeExpr.Raw}
    {P P' : Name → Option (Array (Param TyParam))} {R R' N N' : Name → Array Kind → Bool}
    (hp : ∀ n ps, P n = some ps → P' n = some ps)
    (hR : ∀ n ks, R n ks = true → R' n ks = true)
    (hN : ∀ n ks, N n ks = true → N' n ks = true)
    (h : g.checkWith P R N = true) : g.checkWith P' R' N' = true := by
  simp only [checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true] at h ⊢
  intro m hm c hc p hpm
  obtain ⟨⟨hk, hpay⟩, hpol⟩ := h m hm c hc p hpm
  refine ⟨⟨hk, TypeExpr.Raw.checkPayload_mono hp hR hN _ hpay⟩, fun x hx => ?_⟩
  have hpx := hpol x hx
  match x with
  | (⟨_, ⟨.pos, _⟩⟩, _) => exact TypeExpr.Raw.varPositive_mono hp _ hpx
  | (⟨_, ⟨.non, _⟩⟩, _) => rfl

end DataGroup

namespace Env.Raw

/-! ### What a mutual group owes, and what an alias owes -/

/-- What the type constructor `n` says about its parameters, among the types declared before
position `j`. -/
@[expose]
def paramsBefore (env : Env.Raw α) (j : Nat) (n : Name) :
    Option (Array (Param TyParam)) :=
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
    {m : Name} {a : Array Kind}
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

/-- A passing `RefBefore.check` still passes after an append. -/
theorem refBefore_check_append {env : Env.Raw α} {d : Decl.Raw α} {fresh : d.name ∉ env}
    {i : Nat} {m : Name} {a : Array Kind} (h : RefBefore.check env i m a = true) :
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
def checkAt (env : Env.Raw α) (i : Nat) (scope : Array Kind) (r : RegionSig.Raw) : Bool :=
  r.params.all (fun p => TypeExpr.Raw.checkTypeAt env i scope p.type)
    && TypeExpr.Raw.checkTypeAt env i scope r.returnType
    && decide r.paramNames.Nodup

/-- Soundness of `RegionSig.Raw.checkAt`: a region signature it accepts is well formed at
position `i`. -/
theorem wf_of_checkAt {env : Env.Raw α} {i : Nat} {scope : Array Kind} {r : RegionSig.Raw}
    (h : r.checkAt env i scope = true) : r.WF (env.RefBefore i) scope := by
  simp only [checkAt, Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h
  obtain ⟨⟨hparams, hret⟩, hnames⟩ := h
  exact ⟨fun p hp => TypeExpr.Raw.wfType_of_checkTypeAt _ (hparams p hp),
    TypeExpr.Raw.wfType_of_checkTypeAt _ hret, of_decide_eq_true hnames⟩

end RegionSig.Raw

namespace Decl.Raw

/-- Decision procedure for `Decl.Raw.WF (env.RefBefore i)`. -/
@[expose]
def checkAt (env : Env.Raw α) (i : Nat) : Decl.Raw α → Bool
  | .type d => decide d.paramNames.Nodup
  | .dataHead _ => true
  | .dataRest .. => true
  | .insn d =>
    d.argTypes.all (fun p => TypeExpr.Raw.checkTypeAt env i d.scope p.type)
      && d.variadic.all (fun v => TypeExpr.Raw.checkAt env i d.scope v.type)
      && d.returnType.all (TypeExpr.Raw.checkTypeAt env i d.scope)
      && d.regions.all (fun r => r.type.checkAt env i d.scope)
      && d.succs.all (fun s => s.type.all (TypeExpr.Raw.checkTypeAt env i d.scope))
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
    exact ⟨fun q hq => TypeExpr.Raw.wfType_of_checkTypeAt _ (hargs q hq),
      fun v hv => TypeExpr.Raw.wfRel_of_checkAt _ (hvar v (by simpa using hv)),
      fun t ht => TypeExpr.Raw.wfType_of_checkTypeAt _ (hret t (by simpa using ht)),
      fun r hr => RegionSig.Raw.wf_of_checkAt (hregions r hr),
      fun s hs t ht => TypeExpr.Raw.wfType_of_checkTypeAt _ (hsuccs s hs t ht),
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
private def checkFrom (env : Env.Raw α) (i : Nat) : List (Decl.Raw α) → Bool
  | [] => true
  | d :: ds => checkDecl env i d.name d && checkFrom env (i + 1) ds

/-- Unfolding of `checkFrom`: the declaration `j` places along was checked at
position `i + j`. -/
private theorem checkDecl_of_checkFrom (env : Env.Raw α) :
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

/-- Every declaration of `env` is well formed at its position. -/
def check (env : Env.Raw α) : Bool := checkFrom env 0 env.decls.vals.toList

/-- Every declaration `appendList` adds is well formed, at its position, in the result. -/
def checkAppend (env : Env.Raw α) (ds : List (Decl.Raw α)) (fresh : env.FreshList ds) : Bool :=
  checkFrom (env.appendList ds fresh) env.decls.keys.size ds

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

/-- **Soundness of the checker.**  `check` establishes the positional specification for an
environment built by `ofAscArray`. -/
theorem wf_ofAscArray (ds : Array (Decl.Raw α)) (p : DistinctDecls ds)
    (h : (ofAscArray ds p).check = true) : (ofAscArray ds p).WF := by
  rw [check, vals_ofAscArray] at h
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

/-- Appending a batch keeps every reference valid. -/
theorem RefBefore.appendList {env : Env.Raw α} {ds : List (Decl.Raw α)} {fresh : env.FreshList ds}
    {i : Nat} {m : Name} {a : Array Kind} (h : env.RefBefore i m a) :
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
    (hds : env.checkAppend ds fresh = true) : (env.appendList ds fresh).WF := by
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
private theorem checkFrom_of_checkDecl (env : Env.Raw α) :
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
private theorem checkFrom_typesList (env : Env.Raw α) :
    ∀ (i : Nat) (ts : List (TypeDecl α)), (∀ t ∈ ts, t.paramNames.Nodup) →
      checkFrom env i (ts.map .type) = true
  | _, [], _ => rfl
  | i, t :: ts, h => by
    simp only [List.map_cons, checkFrom, Bool.and_eq_true]
    refine ⟨?_, checkFrom_typesList env (i + 1) ts fun u hu => h u (List.mem_cons_of_mem _ hu)⟩
    simp [checkDecl, Decl.Raw.checkAt, checkAlias, checkGroupOf, h t List.mem_cons_self]

/-- A batch of type declarations owes only distinct parameter names. -/
theorem checkAppend_types (env : Env.Raw α) (ts : Array (TypeDecl α))
    (fresh : env.FreshList (ts.map .type).toList) (h : ∀ t ∈ ts.toList, t.paramNames.Nodup) :
    env.checkAppend (ts.map .type).toList fresh = true := by
  rw [checkAppend]
  have := checkFrom_typesList (env.appendList _ fresh) env.decls.keys.size ts.toList h
  rwa [← Array.toList_map] at this

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

/-- A member's constructors and case instruction bind its parameters, each of its kind. -/
private theorem kinds_params (m : DatatypeDecl α TypeExpr.Raw) :
    Param.kinds (m.params.map fun p => (⟨p.name, p.type.kind⟩ : Param Kind)) =
      TyParam.kinds m.params := by
  simp [Function.comp_def]

/-- The variables `i, i + 1, …` of a scope, each as an argument, pass any check. -/
private theorem check_varsFrom {R : Name → Array Kind → Bool} (scope : Array Kind) :
    ∀ (i : Nat) (ks : List Kind), (∀ (j : Nat) (h : j < ks.length), scope[i + j]? = some ks[j]) →
      ∀ a ∈ TypeExpr.Raw.varsFrom i ks, TypeExpr.Raw.check R scope a = true
  | _, [], _ => by simp [TypeExpr.Raw.varsFrom]
  | i, k :: ks, h => by
    have h₀ : scope[i]? = some k := h 0 (by simp)
    have ih := check_varsFrom (R := R) scope (i + 1) ks fun j hj => by
      rw [show i + 1 + j = i + (j + 1) by omega]
      exact h (j + 1) (by simpa using hj)
    have hi : i < scope.size := (Array.getElem?_eq_some_iff.mp h₀).1
    have h₁ : scope[i] = k := by simpa [Array.getElem?_eq_getElem hi] using h₀
    cases k <;> simpa [TypeExpr.Raw.varsFrom, TypeExpr.Raw.check, TypeExpr.Raw.checkElems,
      TypeExpr.Raw.isElem, h₀, h₁, hi] using ih

/-- The variables of a scope, each as an argument, pass any check. -/
private theorem check_vars {R : Name → Array Kind → Bool} (scope : Array Kind) :
    ∀ a ∈ TypeExpr.Raw.vars scope, TypeExpr.Raw.check R scope a = true := fun a ha =>
  check_varsFrom scope 0 scope.toList (fun j hj => by simp) a
    (by simpa [TypeExpr.Raw.vars] using ha)

/-- A member applied to its own parameters is a type, when the member is declared. -/
private theorem checkTypeAt_self {env : Env.Raw α} {p : Nat} {m : DatatypeDecl α TypeExpr.Raw}
    (hm : env.RefBefore p m.name m.toTypeDecl.kinds) :
    TypeExpr.Raw.checkTypeAt env p (TyParam.kinds m.params)
      (.app m.name (TypeExpr.Raw.vars (TyParam.kinds m.params))) = true := by
  rw [TypeExpr.Raw.checkTypeAt, Bool.and_eq_true, TypeExpr.Raw.checkAt, TypeExpr.Raw.check_app,
    TypeExpr.Raw.map_kind_vars]
  exact ⟨rfl, refBefore_check_eq_true.mpr hm, check_vars _⟩

/-- A constructor's instruction is well formed at any position past its group's members. -/
theorem checkAt_ctorDecl {env : Env.Raw α} {g : DataGroup α TypeExpr.Raw} {n p i j : Nat}
    {m : DatatypeDecl α TypeExpr.Raw} {c : Ctor α TypeExpr.Raw}
    (hm : g.members[i]? = some m) (hc : m.ctors[j]? = some c) (hp : n + g.members.size ≤ p)
    (hmem : ∀ {k : Nat} {m' : DatatypeDecl α TypeExpr.Raw}, g.members[k]? = some m' →
      env.RefBefore p m'.name m'.toTypeDecl.kinds)
    (hn : g.checkNames = true)
    (h : g.checkWith (env.paramsBefore (n + g.members.size))
      (RefBefore.check env (n + g.members.size)) (RefBefore.check env n) = true) :
    Decl.Raw.checkAt env p (.insn (g.ctorDecl i m j c)) = true := by
  have hmm : m ∈ g.members := Array.mem_of_getElem? hm
  have hcm : c ∈ m.ctors := Array.mem_of_getElem? hc
  have hRR : ∀ x a, RefBefore.check env (n + g.members.size) x a = true →
      RefBefore.check env p x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono hp)
  have hNR : ∀ x a, RefBefore.check env n x a = true →
      RefBefore.check env (n + g.members.size) x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono (by omega))
  simp only [DataGroup.checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true] at h
  simp only [DataGroup.checkNames, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true,
    decide_eq_true_eq] at hn
  simp only [Decl.Raw.checkAt, DataGroup.ctorDecl, InsnDecl.Raw.scope, kinds_params,
    Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Option.all_none, decide_eq_true_eq]
  have hctors := h m hmm
  refine ⟨⟨⟨⟨⟨fun q hq => ?_, ?_⟩, ?_⟩, by simp⟩, by simp⟩, ?_⟩
  · obtain ⟨⟨hk, hpay⟩, -⟩ := hctors c hcm q hq
    exact (Bool.and_eq_true _ _).mpr
      ⟨hk, TypeExpr.Raw.check_mono hRR _ (TypeExpr.Raw.check_of_checkPayload hNR _ hpay)⟩
  · simp
  · exact checkTypeAt_self (hmem hm)
  · simpa [InsnDecl.Raw.paramNames, DatatypeDecl.paramNames, Function.comp_def]
      using (hn m hmm).1.2 c hcm

/-- A case instruction is well formed at any position past its group's members. -/
theorem checkAt_caseDecl {env : Env.Raw α} {g : DataGroup α TypeExpr.Raw} {n p i : Nat}
    {m : DatatypeDecl α TypeExpr.Raw}
    (hm : g.members[i]? = some m) (hp : n + g.members.size ≤ p)
    (hmem : ∀ {k : Nat} {m' : DatatypeDecl α TypeExpr.Raw}, g.members[k]? = some m' →
      env.RefBefore p m'.name m'.toTypeDecl.kinds)
    (hn : g.checkNames = true)
    (h : g.checkWith (env.paramsBefore (n + g.members.size))
      (RefBefore.check env (n + g.members.size)) (RefBefore.check env n) = true) :
    Decl.Raw.checkAt env p (.insn (g.caseDecl i m)) = true := by
  have hmm : m ∈ g.members := Array.mem_of_getElem? hm
  have hRR : ∀ x a, RefBefore.check env (n + g.members.size) x a = true →
      RefBefore.check env p x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono hp)
  have hNR : ∀ x a, RefBefore.check env n x a = true →
      RefBefore.check env (n + g.members.size) x a = true := fun _ _ hr =>
    refBefore_check_eq_true.mpr ((refBefore_check_eq_true.mp hr).mono (by omega))
  simp only [DataGroup.checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true] at h
  simp only [DataGroup.checkNames, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true,
    decide_eq_true_eq] at hn
  simp only [Decl.Raw.checkAt, DataGroup.caseDecl, InsnDecl.Raw.scope, kinds_params,
    Bool.and_eq_true, Array.all_eq_true_iff_forall_mem, Option.all_none, decide_eq_true_eq]
  have hctors := h m hmm
  refine ⟨⟨⟨⟨⟨fun q hq => ?_, ?_⟩, by simp⟩, by simp⟩, fun s hs t ht => ?_⟩, ?_⟩
  · obtain rfl : q = ⟨"scrutinee", .app m.name (TypeExpr.Raw.vars (TyParam.kinds m.params))⟩ := by
      simpa using hq
    exact checkTypeAt_self (hmem hm)
  · simp
  · obtain ⟨c, hc, rfl⟩ := Array.mem_map.mp hs
    obtain ⟨q, hq, rfl⟩ := Array.mem_map.mp ht
    obtain ⟨⟨hk, hpay⟩, -⟩ := hctors c hc q hq
    exact (Bool.and_eq_true _ _).mpr
      ⟨hk, TypeExpr.Raw.check_mono hRR _ (TypeExpr.Raw.check_of_checkPayload hNR _ hpay)⟩
  · simpa [InsnDecl.Raw.paramNames, DatatypeDecl.paramNames, Function.comp_def]
      using (hn m hmm).2

/-- A group appended as one batch owes only its definition: that it binds no name twice,
and `checkWith` against the extended environment at the positions the group occupies. -/
theorem checkAppend_group {env : Env.Raw α} {g : DataGroup α TypeExpr.Raw}
    (fresh : env.FreshList g.decls.toList) (hn : g.checkNames = true)
    (h : g.checkWith
      ((env.appendList _ fresh).paramsBefore (env.decls.keys.size + g.members.size))
      (RefBefore.check (env.appendList _ fresh) (env.decls.keys.size + g.members.size))
      (RefBefore.check (env.appendList _ fresh) env.decls.keys.size)) :
    env.checkAppend g.decls.toList fresh = true := by
  have h0 := DataGroup.decls_getElem?_zero g
  have hhead : (env.appendList _ fresh).decls[g.first.name]? = some (.dataHead g) :=
    get?_appendList_of_getElem? h0
  have hidx : IndexMap.idxOf? (env.appendList _ fresh).decls g.first.name =
      some env.decls.keys.size := by
    simpa using idxOf?_appendList_of_getElem? (fresh := fresh) h0
  -- every member is a type declared at its own position in the group
  have hmem : ∀ {p k : Nat} {m : DatatypeDecl α TypeExpr.Raw},
      env.decls.keys.size + g.members.size ≤ p → g.members[k]? = some m →
      (env.appendList _ fresh).RefBefore p m.name m.toTypeDecl.kinds := by
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
  rw [checkAppend]
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

end Env.Raw

end

end Strata.Mantle
