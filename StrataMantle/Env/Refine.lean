/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env
-- For compiling the transports, as every module that builds environments does.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Refining environments

`t ≤ s`, read "`s` refines `t`", holds when every name `t` declares, `s` declares compatibly:

* every type of `t` is a type of `s`, with the same parameters;
* every datatype of `t` is a datatype of `s`: the same member of the same group;
* every instruction of `t` is an instruction of `s` with the same signature.  An ordinary
  instruction may become a constructor or a case instruction; any other keeps its kind.

and every annotation of `t` is the annotation of its refinement in `s`.  So `s` may declare
more, and an abstract type of `t` may be a datatype in `s`.

`LeBy R` is the same order with the annotations related by `R` instead: declarations are
compared with their annotations erased, and `R` relates each annotation of `t`, of a type, a
datatype, a constructor or an instruction, to that of its refinement in `s`.  `≤` is
`LeBy Eq`.

The order reads only what names resolve to, never positions: the same declarations in
another order refine each other.

Some key concepts include:

* `TypeDecl.RefinedBy`, `DataGroup.RefinedBy`, `InsnSig.RefinedBy`: when one declaration
  refines another, the last across environments.
* `InsnKind.RefinedBy`: the kinds a refinement may give an instruction.
* `LeBy`, `Le`: the order, with a relation on annotations, and with equal annotations.
* `LeBy.of_le`: equal annotations are related by every reflexive relation.
* `LeBy.of_subset`, `le_of_subset`: an extension refines what it extends.
* `LeBy.annOf?`: how `LeBy R` relates the annotation a name is declared with (`Env.annOf?`).
* `ofLE`: carry a checked form or a reference along a refinement.
* `RefinedBy`, `t ⊑ s`: the order as a class, for instance search.
-/

namespace Strata.Mantle

variable {α : Type}

/-! ### Refining one declaration

Each relation compares the declarations with their annotations erased, and relates each
annotation of the first to the matching one of the second by `R`. -/

/-- `k₁.RefinedBy k₂`: a refinement may give an instruction of kind `k₁` the kind `k₂`.  An
ordinary instruction may take any kind; a constructor or a case instruction keeps its own. -/
@[expose] public def InsnKind.RefinedBy (k₁ k₂ : InsnKind) : Prop := k₁ = .decl ∨ k₂ = k₁

/-- `d₂` refines the type declaration `d₁`. -/
public structure TypeDecl.RefinedBy (R : α → α → Prop) (d₁ d₂ : TypeDecl α) : Prop where
  /-- `d₂` is `d₁`, up to annotations. -/
  erase_eq : d₂.erase = d₁.erase
  /-- `R` relates their annotations. -/
  ann : R d₁.ann d₂.ann

/-- `g₂` refines the datatype group `g₁`. -/
public structure DataGroup.RefinedBy (R : α → α → Prop) (g₁ g₂ : DataGroup α TypeExpr.Raw) :
    Prop where
  /-- `g₂` is `g₁`, up to annotations. -/
  erase_eq : g₂.erase = g₁.erase
  /-- `R` relates each member's annotation to that of the same member of `g₂`. -/
  member : ∀ {i : Nat} {m₁ : DatatypeDecl α TypeExpr.Raw}, g₁.member? i = some m₁ →
    ∃ m₂, g₂.member? i = some m₂ ∧ R m₁.ann m₂.ann
  /-- `R` relates each constructor's annotation to that of the same constructor of `g₂`. -/
  ctor : ∀ {i j : Nat} {c₁ : Ctor α TypeExpr.Raw}, g₁.ctor? i j = some c₁ →
    ∃ c₂, g₂.ctor? i j = some c₂ ∧ R c₁.ann c₂.ann

/-! Each declaration relation is reflexive and transitive when `R` is, and monotone in `R`.
Kinds carry no annotation; their relation is reflexive and transitive. -/

section
variable {R R' : α → α → Prop}

/-- Every kind may stay as it is. -/
public theorem InsnKind.RefinedBy.refl (k : InsnKind) : k.RefinedBy k := .inr rfl

/-- Two changes of kind compose. -/
public theorem InsnKind.RefinedBy.trans {k₁ k₂ k₃ : InsnKind} (h₁ : k₁.RefinedBy k₂)
    (h₂ : k₂.RefinedBy k₃) : k₁.RefinedBy k₃ := by
  rcases h₁ with h₁ | rfl
  · exact .inl h₁
  · exact h₂

/-- A type declaration refines itself. -/
public theorem TypeDecl.RefinedBy.refl (hR : ∀ a, R a a) (d : TypeDecl α) :
    TypeDecl.RefinedBy R d d :=
  ⟨rfl, hR _⟩

/-- Refinement of type declarations composes. -/
public theorem TypeDecl.RefinedBy.trans (hR : ∀ ⦃a b c⦄, R a b → R b c → R a c)
    {d₁ d₂ d₃ : TypeDecl α} (h₁ : TypeDecl.RefinedBy R d₁ d₂) (h₂ : TypeDecl.RefinedBy R d₂ d₃) :
    TypeDecl.RefinedBy R d₁ d₃ :=
  ⟨h₂.erase_eq.trans h₁.erase_eq, hR h₁.ann h₂.ann⟩

/-- A weaker annotation relation keeps a type refinement. -/
public theorem TypeDecl.RefinedBy.mono (hR : ∀ {a b}, R a b → R' a b) {d₁ d₂ : TypeDecl α}
    (h : TypeDecl.RefinedBy R d₁ d₂) : TypeDecl.RefinedBy R' d₁ d₂ :=
  ⟨h.erase_eq, hR h.ann⟩

/-- A datatype group refines itself. -/
public theorem DataGroup.RefinedBy.refl (hR : ∀ a, R a a) (g : DataGroup α TypeExpr.Raw) :
    DataGroup.RefinedBy R g g :=
  ⟨rfl, fun hm => ⟨_, hm, hR _⟩, fun hc => ⟨_, hc, hR _⟩⟩

/-- Refinement of datatype groups composes. -/
public theorem DataGroup.RefinedBy.trans (hR : ∀ ⦃a b c⦄, R a b → R b c → R a c)
    {g₁ g₂ g₃ : DataGroup α TypeExpr.Raw} (h₁ : DataGroup.RefinedBy R g₁ g₂)
    (h₂ : DataGroup.RefinedBy R g₂ g₃) : DataGroup.RefinedBy R g₁ g₃ where
  erase_eq := h₂.erase_eq.trans h₁.erase_eq
  member hm₁ :=
    let ⟨_, hm₂, r₁⟩ := h₁.member hm₁
    let ⟨m₃, hm₃, r₂⟩ := h₂.member hm₂
    ⟨m₃, hm₃, hR r₁ r₂⟩
  ctor hc₁ :=
    let ⟨_, hc₂, r₁⟩ := h₁.ctor hc₁
    let ⟨c₃, hc₃, r₂⟩ := h₂.ctor hc₂
    ⟨c₃, hc₃, hR r₁ r₂⟩

/-- A weaker annotation relation keeps a datatype group refinement. -/
public theorem DataGroup.RefinedBy.mono (hR : ∀ {a b}, R a b → R' a b)
    {g₁ g₂ : DataGroup α TypeExpr.Raw} (h : DataGroup.RefinedBy R g₁ g₂) :
    DataGroup.RefinedBy R' g₁ g₂ where
  erase_eq := h.erase_eq
  member hm := (h.member hm).imp fun _ ⟨hm₂, r⟩ => ⟨hm₂, hR r⟩
  ctor hc := (h.ctor hc).imp fun _ ⟨hc₂, r⟩ => ⟨hc₂, hR r⟩

end

/-! ### Refining an instruction signature -/

/-- `σ₂` refines the instruction signature `σ₁`, of another environment: the same signature,
with `R` relating their annotations.  Whether a refinement may also change the instruction's
kind is `InsnKind.RefinedBy`. -/
public structure InsnSig.RefinedBy (R : α → α → Prop) {t s : Env α} (σ₁ : InsnSig t)
    (σ₂ : InsnSig s) : Prop where
  /-- `σ₂` is `σ₁`, up to annotations. -/
  eq : σ₁.EqUpToAnn σ₂
  /-- `R` relates their annotations. -/
  ann : R σ₁.ann σ₂.ann

namespace InsnSig

section
variable {R R' : α → α → Prop} {t s u : Env α}

/-- A signature refines itself, if `R` is reflexive. -/
public theorem RefinedBy.refl (hR : ∀ a, R a a) (σ : InsnSig t) : σ.RefinedBy R σ :=
  ⟨.refl σ, hR _⟩

/-- Refinement of signatures composes. -/
public theorem RefinedBy.trans (hR : ∀ ⦃a b c⦄, R a b → R b c → R a c) {σ₁ : InsnSig t}
    {σ₂ : InsnSig s} {σ₃ : InsnSig u} (h₁ : σ₁.RefinedBy R σ₂) (h₂ : σ₂.RefinedBy R σ₃) :
    σ₁.RefinedBy R σ₃ :=
  ⟨h₁.eq.trans h₂.eq, hR h₁.ann h₂.ann⟩

/-- A weaker annotation relation keeps a signature refinement. -/
public theorem RefinedBy.mono (hR : ∀ {a b}, R a b → R' a b) {σ₁ : InsnSig t} {σ₂ : InsnSig s}
    (h : σ₁.RefinedBy R σ₂) : σ₁.RefinedBy R' σ₂ :=
  ⟨h.eq, hR h.ann⟩

/-- A signature carried into an extension refines what the original refines. -/
@[simp] public theorem refinedBy_ofSubset_left (hs : s ⊆ t) (σ : InsnSig s) (σ₂ : InsnSig u) :
    (σ.ofSubset hs).RefinedBy R σ₂ ↔ σ.RefinedBy R σ₂ :=
  ⟨fun h => ⟨(eqUpToAnn_carry_left _ σ σ₂).mp h.eq, h.ann⟩,
    fun h => ⟨(eqUpToAnn_carry_left _ σ σ₂).mpr h.eq, h.ann⟩⟩

end

end InsnSig

/-! ### Refining an environment -/

namespace Env

/-- `LeBy R t s`: `s` refines `t`, and `R` relates each annotation of `t` to that of its
refinement in `s`.  For each name, what `s` resolves it to refines what `t` resolves it to. -/
public structure LeBy (R : α → α → Prop) (t s : Env α) : Prop where
  /-- A type of `t` is a type of `s` that refines it. -/
  type : ∀ {n : Name} {d₁ : TypeDecl α}, t.typeOf? n = some d₁ →
    ∃ d₂, s.typeOf? n = some d₂ ∧ TypeDecl.RefinedBy R d₁ d₂
  -- For a datatype's name, `type` follows from `data`: its erase equation and its annotation
  -- are those of the group's member.
  /-- A datatype of `t` is the same member of a group of `s` that refines `t`'s group. -/
  data : ∀ {n : Name} {g₁ : DataGroup α TypeExpr.Raw} {i : Nat},
    t.dataOf? n = some (g₁, i) →
      ∃ g₂, s.dataOf? n = some (g₂, i) ∧ DataGroup.RefinedBy R g₁ g₂
  /-- An instruction of `t` is an instruction of `s` that refines it, at a kind its kind may
  become. -/
  insn : ∀ {n : Name} {σ₁ : InsnSig t} {k₁ : InsnKind}, t.DeclaresInsn n σ₁ k₁ →
    ∃ σ₂ k₂, s.DeclaresInsn n σ₂ k₂ ∧ k₁.RefinedBy k₂ ∧ σ₁.RefinedBy R σ₂

/-- `s` refines `t`, with the same annotations.  It is written `t ≤ s`. -/
@[expose] public def Le (t s : Env α) : Prop := LeBy Eq t s

public instance : LE (Env α) := ⟨Le⟩

section
variable {R : α → α → Prop} {t s u : Env α}

/-- A refinement keeps every type. -/
public theorem LeBy.keepsTypes (h : LeBy R t s) : t.KeepsTypes s :=
  ⟨fun hd => let ⟨d₂, hd₂, r⟩ := h.type hd; ⟨d₂, hd₂, r.erase_eq⟩⟩

/-- A refinement keeps every instruction. -/
public theorem LeBy.keepsInsns (h : LeBy R t s) : t.KeepsInsns s :=
  ⟨fun hσ => let ⟨σ₂, k₂, hσ₂, _, r⟩ := h.insn hσ; ⟨σ₂, k₂, hσ₂, r.eq⟩⟩

/-- Every environment refines itself, if `R` is reflexive. -/
public theorem LeBy.refl (hR : ∀ a, R a a) (t : Env α) : LeBy R t t where
  type hd := ⟨_, hd, .refl hR _⟩
  data hd := ⟨_, hd, .refl hR _⟩
  insn hσ := ⟨_, _, hσ, .refl _, .refl hR _⟩

/-- Refinement is transitive, if `R` is. -/
public theorem LeBy.trans (hR : ∀ ⦃a b c⦄, R a b → R b c → R a c) (h₁ : LeBy R t s)
    (h₂ : LeBy R s u) : LeBy R t u where
  type hd₁ := by
    obtain ⟨d₂, hd₂, r₁⟩ := h₁.type hd₁
    obtain ⟨d₃, hd₃, r₂⟩ := h₂.type hd₂
    exact ⟨d₃, hd₃, r₁.trans hR r₂⟩
  data hg₁ := by
    obtain ⟨g₂, hg₂, r₁⟩ := h₁.data hg₁
    obtain ⟨g₃, hg₃, r₂⟩ := h₂.data hg₂
    exact ⟨g₃, hg₃, r₁.trans hR r₂⟩
  insn hσ₁ := by
    obtain ⟨σ₂, k₂, hσ₂, hk₁, r₁⟩ := h₁.insn hσ₁
    obtain ⟨σ₃, k₃, hσ₃, hk₂, r₂⟩ := h₂.insn hσ₂
    exact ⟨σ₃, k₃, hσ₃, hk₁.trans hk₂, r₁.trans hR r₂⟩

/-- A refinement relating annotations by `R` relates them by any weaker relation. -/
public theorem LeBy.mono {R' : α → α → Prop} (hR : ∀ {a b}, R a b → R' a b)
    (h : LeBy R t s) : LeBy R' t s where
  type hd₁ := (h.type hd₁).imp fun _ ⟨hd₂, r⟩ => ⟨hd₂, r.mono hR⟩
  data hg₁ := (h.data hg₁).imp fun _ ⟨hg₂, r⟩ => ⟨hg₂, r.mono hR⟩
  insn hσ₁ :=
    let ⟨σ₂, k₂, hσ₂, hk, r⟩ := h.insn hσ₁
    ⟨σ₂, k₂, hσ₂, hk, r.mono hR⟩

/-- A refinement with the same annotations relates them by every reflexive relation. -/
public theorem LeBy.of_le (hR : ∀ a, R a a) (h : t ≤ s) : LeBy R t s :=
  LeBy.mono (R := Eq) (fun h => h ▸ hR _) h

/-- Every environment refines itself. -/
@[refl] public theorem Le.refl (t : Env α) : t ≤ t := LeBy.refl (fun _ => rfl) t

/-- Refinement is transitive. -/
public theorem Le.trans (h₁ : t ≤ s) (h₂ : s ≤ u) : t ≤ u :=
  LeBy.trans (fun _ _ _ => Eq.trans) h₁ h₂

/-- Two refinements compose, forgetting how they relate annotations.  Transports read no
annotation, so carrying along both refinements is carrying along this one. -/
public theorem LeBy.trans_true {R₁ R₂ : α → α → Prop} (h₁ : LeBy R₁ t s) (h₂ : LeBy R₂ s u) :
    LeBy (fun _ _ => True) t u :=
  LeBy.trans (fun _ _ _ _ _ => trivial) (h₁.mono fun _ => trivial) (h₂.mono fun _ => trivial)

/-- An extension refines what it extends, relating each annotation to itself by `R`. -/
public theorem LeBy.of_subset (hR : ∀ a, R a a) (h : t ⊆ s) : LeBy R t s where
  type hd := ⟨_, typeOf?_of_subset h hd, .refl hR _⟩
  data hd := ⟨_, dataOf?_of_subset h hd, .refl hR _⟩
  insn {_ σ _} hσ := ⟨_, _, hσ.of_subset h, .refl _, InsnSig.eqUpToAnn_carry _ σ, hR _⟩

/-- An extension refines what it extends. -/
public theorem le_of_subset (h : t ⊆ s) : t ≤ s := LeBy.of_subset (fun _ => rfl) h

/-- A refinement declares every name its original does. -/
public theorem mem_of_le (h : LeBy R t s) {n : Name} (hn : n ∈ t) : n ∈ s := by
  rcases lookup_of_mem hn with ⟨_, hd⟩ | ⟨_, _, hσ⟩
  · obtain ⟨_, hd₂, -⟩ := h.type hd
    exact mem_of_typeOf? hd₂
  · obtain ⟨_, _, hσ₂, -⟩ := h.insn hσ
    exact hσ₂.mem

/-- A name's annotation in `t` is related by `R` to its annotation in a refinement. -/
public theorem LeBy.annOf? (h : LeBy R t s) {n : Name} {a₁ : α} (ha : t.annOf? n = some a₁) :
    ∃ a₂, s.annOf? n = some a₂ ∧ R a₁ a₂ := by
  rcases annOf?_eq_some ha with ⟨_, _, hσ, rfl⟩ | ⟨_, hd, rfl⟩
  · obtain ⟨σ₂, _, hσ₂, -, r⟩ := h.insn hσ
    exact ⟨σ₂.ann, annOf?_of_declaresInsn hσ₂, r.ann⟩
  · obtain ⟨d₂, hd₂, r⟩ := h.type hd
    exact ⟨d₂.ann, annOf?_of_typeOf? hd₂, r.ann⟩

/-- A refinement keeps every constructor where it is: only an ordinary instruction changes
kind. -/
public theorem ctorAddr?_of_le (h : LeBy R t s) {n : Name} {a : CtorAddr}
    (ha : t.ctorAddr? n = some a) : s.ctorAddr? n = some a := by
  obtain ⟨_, k, hσ, hk⟩ := exists_declaresInsn_of_ctorAddr? ha
  obtain ⟨_, k₂, hσ₂, hkk, -⟩ := h.insn hσ
  rw [ctorAddr?_of_declaresInsn hσ₂]
  rcases hkk with rfl | rfl
  · exact absurd hk (by simp [InsnKind.ctor?])
  · exact hk

/-- A name that resolves to a type in `t` resolves to it in every refinement. -/
public theorem ResolvesType.of_le (h : LeBy R t s) {n : Name} {d : TypeDecl α}
    (hd : t.ResolvesType n d) : s.ResolvesType n d :=
  hd.carry h.keepsTypes

end

end Env

/--
`t ⊑ s`: `s` refines `t`, as a class.

Each environment states its parent as an instance, so instance search finds `t ⊑ s` for every
ancestor `t` of `s`.  Code written under `[t ⊑ e]` uses `t`'s references in any refinement `e`.
-/
public class RefinedBy (t s : Env α) : Prop where
  /-- `s` refines `t`. -/
  le : t ≤ s

@[inherit_doc] scoped infix:50 " ⊑ " => RefinedBy

/-- `s ⊒ t`: `s` refines `t`, the same as `t ⊑ s`.  Input only; terms print with `⊑`. -/
scoped syntax:50 term:51 " ⊒ " term:51 : term
macro_rules | `($s ⊒ $t) => `(RefinedBy $t $s)

/-- Every environment refines itself. -/
public instance (priority := high) RefinedBy.refl {t : Env α} : t ⊑ t := ⟨Env.Le.refl _⟩

/-! ## Transport

Everything checked against `t` carries over to a refinement `s`, along any `LeBy R`: `ofLE` is
`carry` at what the refinement keeps, and reads no annotation. -/

namespace TypeExpr

/-- Reinterpret in a refinement. -/
public abbrev ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t) {scope : Nat}
    (e : TypeExpr s scope) : TypeExpr t scope :=
  e.carry h.keepsTypes

/-- Reinterpreting changes nothing an expression stands for. -/
@[simp] public theorem toRaw_ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    {scope : Nat} (e : TypeExpr s scope) : (e.ofLE h).toRaw = e.toRaw :=
  toRaw_carry _ e

end TypeExpr

/-- Carry a type reference into a refinement. -/
public abbrev TypeRef.ofLE {s t : Env α} {arity : Nat} {R : α → α → Prop} (h : Env.LeBy R s t)
    (r : TypeRef s arity) : TypeRef t arity :=
  r.carry h.keepsTypes

/-- Carrying a type reference keeps its name. -/
@[simp] public theorem name_TypeRef_ofLE {s t : Env α} {arity : Nat} {R : α → α → Prop}
    (h : Env.LeBy R s t) (r : TypeRef s arity) : (r.ofLE h).name = r.name :=
  name_TypeRef_carry _ r

/-- Carrying a type reference keeps its declaration. -/
@[simp] public theorem decl_TypeRef_ofLE {s t : Env α} {arity : Nat} {R : α → α → Prop}
    (h : Env.LeBy R s t) (r : TypeRef s arity) : (r.ofLE h).decl = r.decl :=
  decl_TypeRef_carry _ r

/-- Carrying a reference twice is carrying it once. -/
@[simp] public theorem TypeRef.ofLE_ofLE {s t u : Env α} {arity : Nat} {R₁ R₂ : α → α → Prop}
    (h₁ : Env.LeBy R₁ s t) (h₂ : Env.LeBy R₂ t u) (r : TypeRef s arity) :
    (r.ofLE h₁).ofLE h₂ = r.ofLE (h₁.trans_true h₂) :=
  TypeRef.carry_carry _ _ r

namespace TypeExpr

/-- Reinterpreting a type variable gives the variable. -/
@[simp] public theorem ofLE_var {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    {scope : Nat} (i : Nat) (hi : i < scope) : (var (env := s) i hi).ofLE h = var i hi :=
  carry_var _ i hi

/-- Reinterpreting an application reinterprets the reference and the arguments. -/
@[simp] public theorem ofLE_app {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    {scope arity : Nat} (r : TypeRef s arity) (args : Vector (TypeExpr s scope) arity) :
    (app r args).ofLE h = app (r.ofLE h) (args.map (·.ofLE h)) :=
  carry_app _ r args

end TypeExpr

namespace RegionSig

variable {scope : Nat}

/-- Reinterpret in a refinement. -/
public abbrev ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    (r : RegionSig s scope) : RegionSig t scope :=
  r.carry h.keepsTypes

/-- Reinterpreting reinterprets each parameter. -/
@[simp] public theorem params_ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    (r : RegionSig s scope) :
    (r.ofLE h).params = r.params.map (fun p => ⟨p.name, p.type.ofLE h⟩) :=
  params_carry _ r

/-- Reinterpreting reinterprets the return type. -/
@[simp] public theorem returnType_ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    (r : RegionSig s scope) : (r.ofLE h).returnType = r.returnType.ofLE h :=
  returnType_carry _ r

/-- Reinterpreting `of` reinterprets its parameter types and its return type. -/
@[simp] public theorem ofLE_of {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    (params : Array (Param (TypeExpr s scope))) (returnType : TypeExpr s scope)
    (distinct : (params.toList.map (·.name)).Nodup) :
    (of params returnType distinct).ofLE h =
      of (params.map fun p => ⟨p.name, p.type.ofLE h⟩) (returnType.ofLE h)
        (by simpa [Function.comp_def] using distinct) :=
  carry_of _ params returnType distinct

end RegionSig

namespace InsnSig

/-- Reinterpret in a refinement.  It is `carry` at what the refinement keeps, so that a
signature reinterpreted along a refinement and one carried along an extension unify by their
arguments. -/
public abbrev ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t) (i : InsnSig s) :
    InsnSig t :=
  i.carry h.keepsTypes

/-- Reinterpreting is carrying at what the refinement keeps. -/
public theorem ofLE_eq_carry {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    (i : InsnSig s) : i.ofLE h = i.carry h.keepsTypes := rfl

/-- A carried signature refines what the original refines. -/
@[simp] public theorem refinedBy_ofLE_left {s t u : Env α} {R R' : α → α → Prop}
    (h : Env.LeBy R' s t) (σ : InsnSig s) (σ₂ : InsnSig u) :
    (σ.ofLE h).RefinedBy R σ₂ ↔ σ.RefinedBy R σ₂ := by
  rw [ofLE_eq_carry]
  exact ⟨fun r => ⟨(eqUpToAnn_carry_left _ σ σ₂).mp r.eq, r.ann⟩,
    fun r => ⟨(eqUpToAnn_carry_left _ σ σ₂).mpr r.eq, r.ann⟩⟩

end InsnSig

/-- A name that resolves to an instruction in `t` resolves to it in every refinement, possibly
at another kind. -/
public theorem Env.ResolvesInsn.of_le {t s : Env α} {R : α → α → Prop} (h : Env.LeBy R t s)
    {name : Name} {isig : InsnSig t} (hr : t.ResolvesInsn name isig) :
    s.ResolvesInsn name (isig.ofLE h) :=
  hr.carry h.keepsTypes h.keepsInsns

/-- Carry an instruction reference into a refinement. -/
public abbrev InsnRef.ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    {isig : InsnSig s} (r : InsnRef s isig) : InsnRef t (isig.ofLE h) :=
  r.carry h.keepsTypes h.keepsInsns

/-- Carrying an instruction reference keeps its name. -/
@[simp] public theorem name_InsnRef_ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    {isig : InsnSig s} (r : InsnRef s isig) : (r.ofLE h).name = r.name := by
  simp [InsnRef.ofLE]

/-- Carry a declaration into a refinement. -/
public abbrev Decl.ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t) : Decl s → Decl t :=
  Decl.carry h.keepsTypes h.keepsInsns

/-- Carrying a declaration keeps its name. -/
@[simp] public theorem Decl.name_ofLE {s t : Env α} {R : α → α → Prop} (h : Env.LeBy R s t)
    (d : Decl s) : (d.ofLE h).name = d.name := by
  simp [Decl.ofLE]

end Strata.Mantle
