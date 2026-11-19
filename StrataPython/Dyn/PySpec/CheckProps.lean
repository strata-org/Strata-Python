/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Check

set_option autoImplicit false

/-! # Properties of return schemas

Key results:
- `returnSchema_no_false`: no condition that `returnSchema` gives contains `false`, as the constant
  or as the literal `False`. So a stop of a return type's schema (`docs/PythonToDyn.md` §12.3,
  *Return schema*) only weakens the free clauses, and never gives a clause that assumes `false`.
- `returnSchema_no_call_state`: no condition that `returnSchema` gives reads the call's arguments,
  a ghost or the state at the call; it reads the result, its own binders and model classes.

Definitions a reader needs: `returnSchema`, `schemaLevels`, `schemaChildren`, `atomChildren`,
`Guard.wrapAll` and `returnTypeTest` (`Check.lean`); `CExpr.hasFalse` and `CExpr.readsCallState`
(`Clause.lean`).
-/

namespace StrataPython.Dyn.PySpec

open StrataPython.Specs

public section

/-- A condition that contains no `false` and reads no state of the call. -/
def CExpr.Clean (e : CExpr) : Prop := e.hasFalse = false ∧ e.readsCallState = false

/-- A guard whose expression is clean. -/
def Guard.Clean : Guard → Prop
  | .present _ v => v.Clean
  | .isA t => t.Clean
  | .each _ c => c.Clean
  | .entries _ _ d => d.Clean

/-- A position whose value and guards are clean. -/
def SchemaPosition.Clean (p : SchemaPosition) : Prop := p.value.Clean ∧ ∀ g ∈ p.guards, g.Clean

/-- A clause whose test and guards are clean. -/
def SchemaClause.Clean (c : SchemaClause) : Prop := c.test.Clean ∧ ∀ g ∈ c.guards, g.Clean

/-- A chain of `or`s of clean conditions is clean. -/
private theorem foldl_or_clean (rest : List CExpr) (acc : CExpr) (hacc : acc.Clean)
    (h : ∀ x ∈ rest, x.Clean) : (rest.foldl .or acc).Clean := by
  induction rest generalizing acc with
  | nil => simpa using hacc
  | cons x xs ih =>
    have hx := h x (by simp)
    apply ih
    · exact ⟨by simp [CExpr.hasFalse, hacc.1, hx.1], by simp [CExpr.readsCallState, hacc.2, hx.2]⟩
    · intro y hy
      exact h y (by simp [hy])

/-- The disjunction of a nonempty array of clean conditions is clean. -/
private theorem disj_clean (cs : Array CExpr) (x : CExpr) (hx : x ∈ cs) (h : ∀ y ∈ cs, y.Clean) :
    (disj cs).Clean := by
  simp only [disj]
  split
  · rename_i hnil
    simp [← Array.mem_toList_iff, hnil] at hx
  · rename_i c rest hcons
    apply foldl_or_clean
    · exact h c (by rw [← Array.mem_toList_iff, hcons]; simp)
    · intro y hy
      exact h y (by rw [← Array.mem_toList_iff, hcons]; simp [hy])

/-- A test of a return type on a clean value is clean: it is a disjunction of class tests and a
`None` test of the value, and has at least one of them. -/
private theorem returnTypeTest_clean (t : Table) (tp : SpecType) (v e : CExpr)
    (h : returnTypeTest t tp v = some e) (hv : v.Clean) : e.Clean := by
  have hv1 := hv.1
  have hv2 := hv.2
  unfold returnTypeTest at h
  dsimp only at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i _ hne
      injection h with h
      subst h
      -- Some class atom, or a literal's class, is among the classes that the test names.
      have hcls : ∃ c, c ∈ (typeAtoms t tp).classes ++
          (if (typeAtoms t tp).strs.isEmpty then #[] else #[builtin "str"]) ++
          (if (typeAtoms t tp).ints.isEmpty then #[] else #[builtin "int"]) := by
        simp only [Bool.and_eq_true, not_and] at hne
        by_cases h1 : (typeAtoms t tp).classes.isEmpty
        · by_cases h2 : (typeAtoms t tp).strs.isEmpty
          · have h3 := hne ⟨h1, h2⟩
            simp only [Array.isEmpty_iff] at h3
            exact ⟨builtin "int", by simp [h3]⟩
          · simp only [Array.isEmpty_iff] at h2
            exact ⟨builtin "str", by simp [h2]⟩
        · obtain ⟨c, hc⟩ := Array.exists_mem_of_ne_empty _ (by simpa using h1)
          exact ⟨c, by simp [hc]⟩
      obtain ⟨c, hc⟩ := hcls
      apply disj_clean _ _ (Array.mem_append_left _ (Array.mem_map_of_mem (a := c) ?_))
      · intro y hy
        simp only [Array.mem_append, Array.mem_map, Array.mem_flatMap] at hy
        rcases hy with ⟨d, _, rfl⟩ | hy
        · split <;> exact ⟨by simp [CExpr.hasFalse, hv1], by simp [CExpr.readsCallState, hv2]⟩
        · split at hy
          · simp only [Array.mem_singleton] at hy
            subst hy
            exact ⟨by simp [CExpr.hasFalse, hv1], by simp [CExpr.readsCallState, hv2]⟩
          · simp at hy
      · simp only [Array.mem_flatMap]
        refine ⟨c, hc, ?_⟩
        split <;> simp [builtin]

/-- A guard chain of clean guards around a clean condition is clean. -/
private theorem wrapAll_clean (gs : List Guard) (b : CExpr) (hgs : ∀ g ∈ gs, g.Clean) (hb : b.Clean) :
    (Guard.wrapAll gs b).Clean := by
  induction gs with
  | nil => simpa [Guard.wrapAll] using hb
  | cons g gs ih =>
    have hg := hgs g (by simp)
    have hrest := ih (fun g' hg' => hgs g' (by simp [hg']))
    simp only [Guard.wrapAll, List.foldr] at hrest ⊢
    cases g <;> simp_all [Guard.Clean, CExpr.Clean, CExpr.hasFalse, CExpr.readsCallState]

/-- The clauses of a clean position's children, and the children's positions, are clean: their
values read the position's value, a key of it or a binder, and their tests are return-type tests
of such values. -/
private theorem atomChildren_clean (t : Table) (p : SchemaPosition) (a : SpecAtomType) (hp : p.Clean) :
    ∀ x ∈ atomChildren t p a, x.1.Clean ∧ x.2.Clean := by
  obtain ⟨hv, hg⟩ := hp
  have hv1 := hv.1
  have hv2 := hv.2
  have hitem : ∀ m, (CExpr.item p.value (.str m)).Clean := fun _ =>
    ⟨by simp [CExpr.hasFalse, hv1], by simp [CExpr.readsCallState, hv2]⟩
  have hin : ∀ m, (CExpr.contains m p.value).Clean := fun _ =>
    ⟨by simp [CExpr.hasFalse, hv1], by simp [CExpr.readsCallState, hv2]⟩
  have hbinder : ∀ x, (CExpr.binder x).Clean := fun _ => ⟨rfl, rfl⟩
  have happ : ∀ g : Guard, g.Clean → ∀ g' ∈ p.guards ++ [g], g'.Clean := by
    intro g hg' g' hmem
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl
    · exact hg g' hmem
    · exact hg'
  intro x hx
  unfold atomChildren at hx
  dsimp only at hx
  split at hx
  · simp only [List.mem_filterMap] at hx
    obtain ⟨⟨⟨m, ft⟩, i⟩, _, hsome⟩ := hx
    dsimp only at hsome
    split at hsome
    · simp only [Option.some.injEq] at hsome
      subst hsome
      refine ⟨⟨?_, hg⟩, ⟨hitem m, hg⟩⟩
      split
      · rename_i y hy
        have hy' := returnTypeTest_clean _ _ _ _ hy (hitem m)
        exact ⟨by simp [CExpr.hasFalse, hv1, hy'.1], by simp [CExpr.readsCallState, hv2, hy'.2]⟩
      · exact hin m
    · cases hrt : returnTypeTest t ft (CExpr.item p.value (.str m)) with
      | none => simp [hrt] at hsome
      | some y =>
        simp only [hrt, Option.map_some, Option.some.injEq] at hsome
        subst hsome
        have hy' := returnTypeTest_clean _ _ _ _ hrt (hitem m)
        exact ⟨⟨⟨by simp [CExpr.hasFalse, hv1, hy'.1], by simp [CExpr.readsCallState, hv2, hy'.2]⟩, hg⟩,
          ⟨hitem m, happ _ hv⟩⟩
  · split at hx
    · split at hx
      · rename_i y hy
        simp only [List.mem_singleton] at hx
        subst hx
        exact ⟨⟨returnTypeTest_clean _ _ _ _ hy (hbinder _), happ _ hv⟩, ⟨hbinder _, happ _ hv⟩⟩
      · simp at hx
    · split at hx
      · rename_i test htest
        simp only [List.mem_singleton] at hx
        subst hx
        refine ⟨⟨?_, happ _ hv⟩, ⟨hbinder _, happ _ hv⟩⟩
        split at htest <;> simp only [Option.some.injEq, reduceCtorEq] at htest
        · rename_i y z hy hz
          subst htest
          have hy' := returnTypeTest_clean _ _ _ _ hy (hbinder _)
          have hz' := returnTypeTest_clean _ _ _ _ hz (hbinder _)
          exact ⟨by simp [CExpr.hasFalse, hy'.1, hz'.1], by simp [CExpr.readsCallState, hy'.2, hz'.2]⟩
        · rename_i y hy _
          subst htest
          exact returnTypeTest_clean _ _ _ _ hy (hbinder _)
        · rename_i z _ hz
          subst htest
          exact returnTypeTest_clean _ _ _ _ hz (hbinder _)
      · simp at hx
    · simp at hx
  · simp at hx

/-- The clauses and positions below a clean position are clean: the guard that a union adds is a
return-type test of the position's value. -/
private theorem schemaChildren_clean (t : Table) (p : SchemaPosition) (hp : p.Clean) :
    ∀ x ∈ schemaChildren t p, x.1.Clean ∧ x.2.Clean := by
  intro x hx
  unfold schemaChildren at hx
  split at hx
  · simp at hx
  · split at hx
    · simp at hx
    · split at hx
      · dsimp only at hx
        split at hx
        · split at hx
          · rename_i test htest
            refine atomChildren_clean t _ _ ?_ x hx
            refine ⟨hp.1, ?_⟩
            intro g hg
            simp only [List.mem_append, List.mem_singleton] at hg
            rcases hg with hg | rfl
            · exact hp.2 g hg
            · exact returnTypeTest_clean _ _ _ _ htest hp.1
          · simp at hx
        · refine atomChildren_clean t _ _ ?_ x hx
          exact ⟨hp.1, hp.2⟩
      · simp at hx

/-- Every clause that `schemaLevels` makes from clean positions is clean, by induction on the
levels: each level's positions come from `schemaChildren` of the level above. -/
private theorem schemaLevels_clean (t : Table) (fuel : Nat) (ps : List SchemaPosition) (cap : Nat)
    (hps : ∀ p ∈ ps, p.Clean) : ∀ c ∈ schemaLevels t fuel ps cap, c.Clean := by
  induction fuel generalizing ps cap with
  | zero => simp [schemaLevels]
  | succ fuel ih =>
    intro c hc
    unfold schemaLevels at hc
    split at hc
    · simp at hc
    · have hstep : ∀ x ∈ (ps.flatMap (schemaChildren t)).take cap, x.1.Clean ∧ x.2.Clean := by
        intro x hx
        obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp (List.mem_of_mem_take hx)
        exact schemaChildren_clean t p (hps p hp) x hxp
      simp only [List.mem_append, List.mem_map] at hc
      rcases hc with ⟨x, hx, rfl⟩ | hc
      · exact (hstep x hx).1
      · refine ih _ _ ?_ c hc
        intro q hq
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
        exact (hstep x hx).2

/-- Every condition of a return type's schema is clean, for every table, type and `forceGuard`. -/
private theorem returnSchema_clean (t : Table) (tp : SpecType) (forceGuard : Bool) :
    ∀ c ∈ returnSchema t tp forceGuard, c.2.Clean := by
  intro c hc
  unfold returnSchema at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hclean := schemaLevels_clean t _ _ _ (by
    intro p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact ⟨⟨rfl, rfl⟩, by simp⟩) d hd
  exact wrapAll_clean _ _ hclean.2 hclean.1

/-- No condition of a return type's schema contains `false`, as the constant or as the literal
`False`, for every table, type and `forceGuard`. Each stop of the schema, at a union, an alias met
again, the depth bound, the alias-chain bound or the budget, gives fewer clauses. Past the
alias-chain bound, a clause may also lose a class test. No stop gives `false`. -/
theorem returnSchema_no_false (t : Table) (tp : SpecType) (forceGuard : Bool) :
    ∀ c ∈ returnSchema t tp forceGuard, c.2.hasFalse = false :=
  fun c hc => (returnSchema_clean t tp forceGuard c hc).1

/-- No condition of a return type's schema reads a parameter, the `**kw` dict, the binding or
keyword test of the arguments, a ghost or an `OLD`, for every table, type and `forceGuard`. It
reads the call's result, its own binders and, for a model class, the class's global cell. -/
theorem returnSchema_no_call_state (t : Table) (tp : SpecType) (forceGuard : Bool) :
    ∀ c ∈ returnSchema t tp forceGuard, c.2.readsCallState = false :=
  fun c hc => (returnSchema_clean t tp forceGuard c hc).2

end -- public section

end StrataPython.Dyn.PySpec
