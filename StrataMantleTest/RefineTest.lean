/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.Refine

set_option autoImplicit false

/-!
# Refinement beyond extension

`t ≤ s` without `t ⊆ s`:

Every proof uses only the public lookups and their lemmas: no `import all`.

* *Merging*: an environment refines two extensions of a common base.
* *Annotations*: `LeBy R` relates annotations by `R`.  With `Nat` annotations and `≤`, raising
  one refines and lowering one does not.  `≤` itself, `LeBy Eq`, requires them equal.
  References carry along any `LeBy R`.
* *Specialization*: an abstract type becomes a datatype, and ordinary instructions become its
  constructor and its case instruction.  A reference carried across the refinement is the
  constructor.
-/

namespace Strata.Mantle.RefineTest

open Strata.Mantle

-- The environments are only reasoned about.  Compiling them would need `Env.Raw`'s code, which
-- `StrataMantle.Env` does not export.
noncomputable section

/-! ## Merging

`P` and `J` both extend `b`, and `M` extends `P` by `J`'s declaration.  `J` is not a prefix of
`M`, but `M` refines it. -/

namespace Merge

private def aD : TypeDecl Unit := { ann := (), name := .str .base "A" }
private def xD : TypeDecl Unit := { ann := (), name := .str .base "X" }
private def nD : TypeDecl Unit := { ann := (), name := .str .base "N" }

private def b : Env Unit := Env.empty.addType aD (by simp)
private def P : Env Unit := b.addType xD (by simp [b, aD, xD])
private def J : Env Unit := b.addType nD (by simp [b, aD, nD])
private def M : Env Unit := P.addType nD (by simp [P, b, aD, xD, nD])

/-- `M` names every type `J` names: both extend `b` by `N`, and `M` also declares `X`. -/
private theorem typeOf?_J_M {n : Name} {d : TypeDecl Unit} (h : J.typeOf? n = some d) :
    M.typeOf? n = some d := by
  rw [J, Env.typeOf?_addType] at h
  rw [M, Env.typeOf?_addType, P, Env.typeOf?_addType]
  by_cases hn : nD.name == n
  · simpa [hn] using h
  · by_cases hx : xD.name = n
    · subst hx
      simp [b, Env.typeOf?_addType, aD, xD, nD] at h
    · simpa [hn, hx] using h

/-- `J` declares no datatype. -/
private theorem dataOf?_J (n : Name) : J.dataOf? n = none := by
  rw [J, Env.dataOf?_addType, b, Env.dataOf?_addType, Env.dataOf?_empty]
  simp

/-- `J` declares no instruction. -/
private theorem not_declaresInsn_J {n : Name} {σ : InsnSig J} {k : InsnKind} :
    ¬ J.DeclaresInsn n σ k := fun h => by
  obtain ⟨σ₀, h₀, -⟩ := Env.declaresInsn_addType h
  obtain ⟨σ₁, h₁, -⟩ := Env.declaresInsn_addType h₀
  exact Env.not_declaresInsn_empty h₁

example : J ≤ M := show Env.LeBy _ J M from
  { type := fun hd => ⟨_, typeOf?_J_M hd, rfl, rfl⟩
    data := fun hd => by simp [dataOf?_J] at hd
    insn := fun hd => (not_declaresInsn_J hd).elim }
example : P ≤ M := Env.le_of_subset (Env.subset_addType _ _ _)

end Merge

/-! ## Annotations

`e k` declares `A` with annotation `k`. -/

namespace Ann

private def aN : Name := .str .base "A"
private def aD (k : Nat) : TypeDecl Nat := { ann := k, name := aN }
private def e (k : Nat) : Env Nat :=
  Env.empty.addType (aD k) (by simp) (by simp [aD, TypeDecl.paramNames])

/-- `e k` names `A` as a type, and nothing else. -/
private theorem typeOf?_e (k : Nat) (n : Name) :
    (e k).typeOf? n = if aN == n then some (aD k) else none := by
  rw [e, Env.typeOf?_addType, Env.typeOf?_empty]
  rfl

private theorem typeOf?_e_self (k : Nat) : (e k).typeOf? aN = some (aD k) := by
  simp [typeOf?_e]

/-- The only type of `e k` is `A`. -/
private theorem typeOf?_e_inv {k : Nat} {n : Name} {d : TypeDecl Nat}
    (h : (e k).typeOf? n = some d) : n = aN ∧ d = aD k := by
  rw [typeOf?_e] at h
  split at h
  · next hn => exact ⟨(beq_iff_eq.mp hn).symm, (Option.some.inj h).symm⟩
  · cases h

/-- `e k` declares no datatype. -/
private theorem dataOf?_e (k : Nat) (n : Name) : (e k).dataOf? n = none := by
  rw [e, Env.dataOf?_addType, Env.dataOf?_empty]
  split <;> rfl

/-- `e k` declares no instruction. -/
private theorem not_declaresInsn_e {k : Nat} {n : Name} {σ : InsnSig (e k)} {k₀ : InsnKind} :
    ¬ (e k).DeclaresInsn n σ k₀ := fun h => by
  obtain ⟨σ₀, h₀, -⟩ := Env.declaresInsn_addType h
  exact Env.not_declaresInsn_empty h₀

/-- `A`'s annotation in `e k` is `k`. -/
private theorem annOf?_e (k : Nat) : (e k).annOf? aN = some k :=
  Env.annOf?_of_typeOf? (typeOf?_e_self k)

/-- `e k₂` refines `e k₁` under any relation that relates `k₁` to `k₂`. -/
private theorem e_leBy {R : Nat → Nat → Prop} {k₁ k₂ : Nat} (hk : R k₁ k₂) :
    Env.LeBy R (e k₁) (e k₂) :=
  { type := fun hd => by
      obtain ⟨rfl, rfl⟩ := typeOf?_e_inv hd
      exact ⟨aD k₂, typeOf?_e_self k₂, rfl, hk⟩
    data := fun hd => by simp [dataOf?_e] at hd
    insn := fun hd => (not_declaresInsn_e hd).elim }

/-- Raising an annotation refines, under `≤`. -/
example : Env.LeBy (· ≤ ·) (e 1) (e 2) := e_leBy (by decide)

/-- Lowering one does not: `LeBy.annOf?` would relate `2` to `1`. -/
example : ¬ Env.LeBy (· ≤ ·) (e 2) (e 1) := fun h => by
  obtain ⟨a, ha, r⟩ := h.annOf? (annOf?_e 2)
  rw [annOf?_e] at ha
  obtain rfl := Option.some.inj ha
  exact absurd r (by decide)

/-- `≤` requires equal annotations: `e 2` does not refine `e 1`. -/
example : ¬ e 1 ≤ e 2 := fun h => by
  obtain ⟨a, ha, r⟩ := Env.LeBy.annOf? h (annOf?_e 1)
  rw [annOf?_e] at ha
  obtain rfl := Option.some.inj ha
  exact absurd r (by decide)

/-- With equal annotations, `≤` holds. -/
example : e 1 ≤ e 1 := e_leBy rfl

/-- The relation that ignores annotations still relates `e 2` to `e 1`. -/
example : Env.LeBy (fun _ _ => True) (e 2) (e 1) := e_leBy trivial

/-! References carry along any `LeBy R`, not only `≤`. -/

/-- `A`, as a type of `e k`. -/
private def aRef (k : Nat) : TypeRef (e k) 0 :=
  TypeRef.ofAddType Env.empty (aD k) (by simp) (by simp [aD, TypeDecl.paramNames])

/-- Along the relation that ignores annotations, where `≤` does not hold. -/
example : ((aRef 2).ofLE (e_leBy (R := fun _ _ => True) trivial : Env.LeBy _ (e 2) (e 1))).name =
    aN := by
  simp [aRef, aD]

/-- Along `≤` on the annotations. -/
example : ((aRef 1).ofLE (e_leBy (R := (· ≤ ·)) (by decide) : Env.LeBy _ (e 1) (e 2))).name =
    aN := by
  simp [aRef, aD]

end Ann

/-! ## Specialization

`t` declares an abstract type `Box`, an ordinary instruction `mkBox : Box` and an ordinary
instruction `Box.case` with the signature of `Box`'s case instruction.  `s` declares `Box` as the
datatype with the one constructor `mkBox`.  `s` refines `t`: `Box` becomes a datatype, `mkBox`
its constructor and `Box.case` its case instruction. -/

namespace Spec

private def boxN : Name := .str .base "Box"
private def mkN : Name := .str .base "mkBox"
private def boxD : TypeDecl Unit := { ann := (), name := boxN }

/-! ### `t`, abstract -/

private def t₀ : Env Unit := Env.empty.addType boxD (by simp)
private def boxT : TypeExpr t₀ 0 := .app (TypeRef.ofAddType Env.empty boxD (by simp)) #v[]
private def mkSig : InsnSig t₀ := { ann := (), argTypes := #[], returnType := some boxT }
-- `t₁` and `t` are `abbrev`s, so that `simp` and `rw` see a signature carried into them as one
-- of theirs.
private abbrev t₁ : Env Unit := t₀.addInsn mkN mkSig (by simp [t₀, boxD, boxN, mkN])
private def boxCaseSig : InsnSig t₁ :=
  { ann := (), argTypes := #[⟨"scrutinee", boxT.ofSubset (Env.subset_addInsn _ _ _ _)⟩],
    returnType := none, succs := #[⟨"mkBox", #[]⟩] }
private abbrev t : Env Unit :=
  t₁.addInsn boxN.caseName boxCaseSig (by simp [t₁, t₀, boxD, boxN, mkN, Name.caseName])

/-! ### `s`, the datatype -/

private theorem boxFresh : Env.empty.FreshTypes #[boxD] := by
  simp [Env.FreshTypes, boxD, TypeDecl.paramNames]
private def boxCtors :
    Array (Array (Ctor Unit (DataTy Env.empty (Env.empty.addTypes #[boxD] boxFresh)))) :=
  #[#[{ ann := (), name := mkN, args := #[] }]]
private theorem ctorsFresh : (Env.empty.addTypes #[boxD] boxFresh).FreshNames
    (Env.ctorNames boxCtors ++ Env.caseNames #[boxD]) := by
  simp [boxCtors, boxD, boxN, mkN, Env.caseNames, Name.caseName]
private theorem boxAdm : Env.admissible #[boxD] boxCtors = true := by decide
-- An `abbrev`, as `t` is, so that the derived signatures are seen as `s`'s.
private abbrev s : Env Unit := Env.empty.addData #[boxD] boxFresh boxCtors ctorsFresh boxAdm

/-! ### What each declares -/

/-- The only type of `t` is `Box`. -/
private theorem typeOf?_t {n : Name} {d : TypeDecl Unit} (h : t.typeOf? n = some d) :
    n = boxN ∧ d = boxD := by
  rw [t, Env.typeOf?_addInsn, show t₁.typeOf? n = _ from Env.typeOf?_addInsn t₀ mkN mkSig _ n,
    show t₀.typeOf? n = _ from Env.typeOf?_addType Env.empty boxD _ n, Env.typeOf?_empty] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · next hn => exact ⟨(beq_iff_eq.mp hn).symm, (Option.some.inj h).symm⟩
  · cases h

/-- `t` declares no datatype. -/
private theorem dataOf?_t (n : Name) : t.dataOf? n = none := by
  rw [t, Env.dataOf?_addInsn, show t₁.dataOf? n = _ from Env.dataOf?_addInsn t₀ mkN mkSig _ n,
    show t₀.dataOf? n = _ from Env.dataOf?_addType Env.empty boxD _ n, Env.dataOf?_empty]
  simp

/-- The instructions of `t` are `Box.case` and `mkBox`, both ordinary. -/
private theorem declaresInsn_t {n : Name} {σ : InsnSig t} {k : InsnKind}
    (h : t.DeclaresInsn n σ k) :
    (n = boxN.caseName ∧ σ = boxCaseSig.ofSubset (Env.subset_addInsn _ _ _ _) ∧ k = .decl) ∨
      (n = mkN ∧ σ = (mkSig.ofSubset (Env.subset_addInsn _ _ _ _)).ofSubset
        (Env.subset_addInsn _ _ _ _) ∧ k = .decl) := by
  rcases Env.declaresInsn_addInsn h with ⟨rfl, rfl, rfl⟩ | ⟨σ₀, h₀, rfl⟩
  · exact .inl ⟨rfl, rfl, rfl⟩
  rcases Env.declaresInsn_addInsn h₀ with ⟨rfl, rfl, rfl⟩ | ⟨σ₁, h₁, rfl⟩
  · exact .inr ⟨rfl, rfl, rfl⟩
  obtain ⟨σ₂, h₂, -⟩ := Env.declaresInsn_addType h₁
  exact (Env.not_declaresInsn_empty h₂).elim

/-- `s` declares `Box` as a type. -/
private theorem typeOf?_s : s.typeOf? boxN = some boxD :=
  Env.typeOf?_addData (d := boxD) (j := 0) rfl

/-- `mkBox`'s successor in `Box.case` is named `mkBox`. -/
private theorem lastString_mkN : mkN.lastString = "mkBox" := rfl

/-! ### The refinement -/

/-- `s` refines `t`. -/
private theorem t_le_s : t ≤ s := show Env.LeBy _ t s from
  { type := fun hd => by
      obtain ⟨rfl, rfl⟩ := typeOf?_t hd
      exact ⟨boxD, typeOf?_s, rfl, rfl⟩
    data := fun hd => by simp [dataOf?_t] at hd
    insn := fun hd => by
      rcases declaresInsn_t hd with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · refine ⟨_, _, Env.declaresInsn_addData_case (cfresh := ctorsFresh) (adm := boxAdm) 0,
          .inl rfl, ?_⟩
        rw [InsnSig.refinedBy_ofSubset_left]
        -- Two passes, as the DSL's: the derived signature's lemmas first, before `simp` unfolds
        -- the group inside its arguments.  What they leave is closed by `rfl` or by `simp`.
        refine ⟨?_, rfl⟩
        apply InsnSig.EqUpToAnn.of_toRaw <;>
          (try simp only [Env.typeParams_caseSig, Env.argTypes_caseSig,
            Env.variadic_caseSig, Env.returnType_caseSig, Env.regions_caseSig,
            Env.succs_caseSig, boxCaseSig, Array.map_empty, Option.map_none]) <;>
          first
          | rfl
          | simp [boxT, boxD, boxCtors, lastString_mkN, TypeExpr.Raw.vars,
            TypeDecl.arity]
      · refine ⟨_, _, Env.declaresInsn_addData_ctor (cfresh := ctorsFresh) (adm := boxAdm) 0 0,
          .inl rfl, ?_⟩
        rw [InsnSig.refinedBy_ofSubset_left, InsnSig.refinedBy_ofSubset_left]
        refine ⟨?_, rfl⟩
        apply InsnSig.EqUpToAnn.of_toRaw <;>
          (try simp only [Env.typeParams_ctorSig, Env.argTypes_ctorSig,
            Env.variadic_ctorSig, Env.returnType_ctorSig, Env.regions_ctorSig,
            Env.succs_ctorSig, mkSig, Array.map_empty, Option.map_none]) <;>
          first
          | rfl
          | simp [boxT, boxD, boxCtors, TypeExpr.Raw.vars, TypeDecl.arity] }

/-- `mkBox`, as an ordinary instruction of `t`. -/
private def mkRef : InsnRef t ((mkSig.ofSubset (Env.subset_addInsn _ _ _ _)).ofSubset
    (Env.subset_addInsn _ _ _ _)) :=
  (InsnRef.ofAddInsn t₀ mkN mkSig _).ofSubset (Env.subset_addInsn _ _ _ _)

/-- Carried into `s`, the reference is `Box`'s constructor. -/
example : (mkRef.ofLE t_le_s).ctorAddr? = some ⟨boxN, 0, 0⟩ := by
  rw [InsnRef.ctorAddr?_eq, name_InsnRef_ofLE, mkRef, name_InsnRef_carry,
    InsnRef.name_ofAddInsn]
  exact Env.ctorAddr?_of_declaresInsn
    (Env.declaresInsn_addData_ctor (cfresh := ctorsFresh) (adm := boxAdm) 0 0)

end Spec

end

end Strata.Mantle.RefineTest
