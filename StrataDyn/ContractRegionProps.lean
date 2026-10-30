/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.ContractRegion
import all StrataDyn.ContractRegion
import all StrataDyn.DomDecide
import all StrataDyn.Util.LabelMapProps

set_option autoImplicit false

/-!
# Deciding the rules for contract regions

The fast checks of `StrataDyn/ContractRegion.lean` give the answers of the plain statements.

## Main theorems

* `Body.acyclicB_iff`: the reference check accepts exactly the blocks of which no nonempty list
  is `Body.Closed`, that is, the blocks with no cycle of transfers;
* `Body.Acyclic.eq_nil`: no nonempty list of the blocks of an acyclic body is `Body.Closed`;
* `Body.acyclicB_eq_acyclicFast`: Kahn's algorithm, with its answer checked, gives the answer of
  the reference check, so compiled code runs it (`@[csimp]`);
* `Region.failuresToB_iff`: the check through a set of labels decides `Region.FailuresTo`;
* `Region.oldScoped_iff`: `Region.OldScoped` holds exactly when each outermost `old` region of the
  clause is shaped and dominance-correct, entered where only what `Region.oldSees` gives is
  available.

The `Decidable` instances of `Body.Acyclic` and `Region.FailuresTo` come after these theorems, so
that compiled code runs the fast checks.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

namespace Body

/-- `labelSet bs` maps exactly the labels of the blocks of `bs`. -/
private theorem isSome_find?_labelSet {bs : List (Block env α)} {l : Label} :
    ((labelSet bs).find? l).isSome = true ↔ ∃ b ∈ bs, b.label = l := by
  simpa [labelSet] using LabelMap.isSome_find?_foldl_insert (·.label) (fun _ => ()) bs ∅ l

/-- `unpeeled bs` keeps every block of a `Closed` list of blocks of `bs`. -/
private theorem mem_unpeeled {bs S : List (Block env α)} (hS : ∀ b ∈ S, b ∈ bs)
    (hc : Closed S) : ∀ b ∈ S, b ∈ unpeeled bs := by
  intro b hb
  obtain ⟨c, hcS, e, he, hec⟩ := hc b hb
  refine List.mem_filter.mpr ⟨hS b hb, List.any_eq_true.mpr ⟨e, he, ?_⟩⟩
  exact isSome_find?_labelSet.mpr ⟨c, hS c hcS, hec.symm⟩

/-- `peel n bs` keeps every block of a `Closed` list of blocks of `bs`. -/
private theorem mem_peel {S : List (Block env α)} (hc : Closed S) :
    ∀ (n : Nat) (bs : List (Block env α)), (∀ b ∈ S, b ∈ bs) → ∀ b ∈ S, b ∈ peel n bs
  | 0, _, hS => hS
  | n + 1, bs, hS => by
    have hu := mem_unpeeled hS hc
    simp only [peel]
    split
    · exact mem_peel hc n _ hu
    · exact hu

/-- `peel n bs` holds only blocks of `bs`. -/
private theorem mem_of_mem_peel :
    ∀ (n : Nat) (bs : List (Block env α)) (b : Block env α), b ∈ peel n bs → b ∈ bs
  | 0, _, _, h => h
  | n + 1, bs, b, h => by
    simp only [peel] at h
    split at h
    · exact (List.mem_filter.mp (mem_of_mem_peel n _ b h)).1
    · exact (List.mem_filter.mp h).1

/-- With at least as many rounds as blocks, `peel` removes every block, or leaves a `Closed`
list: a round that removes no block leaves only blocks that transfer to blocks left. -/
private theorem peel_eq_nil_or_closed :
    ∀ (n : Nat) (bs : List (Block env α)), bs.length ≤ n → peel n bs = [] ∨ Closed (peel n bs)
  | 0, bs, h => .inl (by simpa [peel] using Nat.le_zero.mp h)
  | n + 1, bs, h => by
    simp only [peel]
    split
    · rename_i hlt
      exact peel_eq_nil_or_closed n _ (by omega)
    · rename_i hge
      have hall := List.length_filter_eq_length_iff.mp
        (Nat.le_antisymm (List.length_filter_le _ _) (Nat.not_lt.mp hge))
      refine .inr fun b hb => ?_
      obtain ⟨e, he, hl⟩ := List.any_eq_true.mp (List.mem_filter.mp hb).2
      obtain ⟨c, hc, hcl⟩ := isSome_find?_labelSet.mp hl
      exact ⟨c, List.mem_filter.mpr ⟨hc, hall c hc⟩, e, he, hcl.symm⟩

/-- The reference check accepts `bs` exactly when no nonempty list of the blocks of `bs` is
`Closed`, that is, when the transfers of `bs` have no cycle. -/
theorem acyclicB_iff {bs : List (Block env α)} :
    acyclicB bs = true ↔ ∀ S : List (Block env α), (∀ b ∈ S, b ∈ bs) → Closed S → S = [] := by
  constructor
  · intro h S hS hc
    have hmem := mem_peel hc bs.length bs hS
    rw [acyclicB, List.isEmpty_iff] at h
    rw [h] at hmem
    exact List.eq_nil_iff_forall_not_mem.mpr fun b hb => List.not_mem_nil (hmem b hb)
  · intro h
    rw [acyclicB, List.isEmpty_iff]
    rcases peel_eq_nil_or_closed bs.length bs (Nat.le_refl _) with h₁ | h₁
    · exact h₁
    · exact h _ (fun b hb => mem_of_mem_peel _ _ b hb) h₁

/-- An acyclic body has no cycle of transfers: if each block of a list `S` of its blocks
transfers to a block of `S`, as the blocks of a cycle do, then `S` is empty. -/
theorem Acyclic.eq_nil {bs S : List (Block env α)} (h : Acyclic bs) (hS : ∀ b ∈ S, b ∈ bs)
    (hc : Closed S) : S = [] :=
  acyclicB_iff.mp h S hS hc

/-- If every transfer between blocks of `bs` goes to a smaller rank, then no nonempty list of the
blocks of `bs` is `Closed`: following the transfers of such a list, the ranks would decrease
forever. -/
private theorem eq_nil_of_ranksDecrease {rank : LabelMap Nat} {bs S : List (Block env α)}
    (h : ranksDecrease rank bs = true) (hS : ∀ b ∈ S, b ∈ bs) (hc : Closed S) : S = [] := by
  let R : Block env α → Nat := fun b => (rank.find? b.label).getD 0
  have hdec : ∀ b ∈ S, ∃ c ∈ S, R c < R b := by
    intro b hb
    obtain ⟨c, hcS, e, he, hec⟩ := hc b hb
    have hb' := List.all_eq_true.mp h b (hS b hb)
    have hc' := List.all_eq_true.mp h c (hS c hcS)
    cases hrc : rank.find? c.label with
    | none => simp [hrc] at hc'
    | some rc =>
      cases hrb : rank.find? b.label with
      | none => simp [hrb] at hb'
      | some rb =>
        simp only [hrb] at hb'
        have hlt := List.all_eq_true.mp hb' e he
        rw [hec, hrc] at hlt
        exact ⟨c, hcS, by simpa [R, hrb, hrc] using hlt⟩
  have hge : ∀ k, ∀ b ∈ S, k ≤ R b := by
    intro k
    induction k with
    | zero => exact fun _ _ => Nat.zero_le _
    | succ k ih =>
      intro b hb
      obtain ⟨c, hcS, hlt⟩ := hdec b hb
      exact Nat.lt_of_le_of_lt (ih c hcS) hlt
  cases S with
  | nil => rfl
  | cons b S => exact absurd (hge (R b + 1) b List.mem_cons_self) (Nat.not_succ_le_self _)

/-- A list that `closedB` accepts is `Closed`. -/
private theorem closed_of_closedB {S : List (Block env α)} (h : closedB S = true) : Closed S := by
  intro b hb
  obtain ⟨e, he, hl⟩ := List.any_eq_true.mp (List.all_eq_true.mp h b hb)
  obtain ⟨c, hc, hcl⟩ := isSome_find?_labelSet.mp hl
  exact ⟨c, hc, e, he, hcl.symm⟩

/-- Compiled code runs `acyclicFast` for `acyclicB`.  When the order of Kahn's algorithm makes
the ranks decrease, the blocks have no cycle; when the blocks it leaves are a nonempty `Closed`
list, they have one; otherwise `acyclicFast` is the reference check itself. -/
@[csimp] theorem acyclicB_eq_acyclicFast : @acyclicB = @acyclicFast := by
  funext env α bs
  simp only [acyclicFast]
  split
  · rename_i h
    exact acyclicB_iff.mpr fun S hS hc => eq_nil_of_ranksDecrease h hS hc
  · split
    · rename_i h
      simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h
      cases hb : acyclicB bs with
      | false => rfl
      | true =>
        exact absurd (acyclicB_iff.mp hb _ (fun b hb => (List.mem_filter.mp hb).1)
          (closed_of_closedB h.2)) h.1
    · rfl

end Body

/-- Deciding `Body.Acyclic` by `Body.acyclicB`, which compiled code runs as
`Body.acyclicFast`. -/
instance (bs : List (Block env α)) : Decidable (Body.Acyclic bs) :=
  inferInstanceAs (Decidable (_ = true))

/-- The check through the set of labels that `ok` accepts decides `Region.FailuresTo`. -/
theorem Region.failuresToB_iff {ok : Block env α → Bool} {r : Region env α} :
    r.failuresToB ok = true ↔ r.FailuresTo ok := by
  simp only [Region.failuresToB, Region.FailuresTo, List.all_eq_true, Body.isSome_find?_labelSet,
    List.mem_filter]
  constructor
  · intro h b hb i hi k hk
    obtain ⟨t, ⟨ht, hok⟩, hl⟩ := h b hb i hi k hk
    exact ⟨t, ht, hl, hok⟩
  · intro h b hb i hi k hk
    obtain ⟨t, ht, hl, hok⟩ := h b hb i hi k hk
    exact ⟨t, ⟨ht, hok⟩, hl⟩

/-- Deciding `Region.FailuresTo` by `Region.failuresToB`. -/
instance (ok : Block env α → Bool) (r : Region env α) : Decidable (r.FailuresTo ok) :=
  decidable_of_iff _ Region.failuresToB_iff

/-- The clause `r` satisfies `Region.OldScoped` exactly when each of its outermost `old` regions is
shaped and dominance-correct, entered where only what `Region.oldSees` gives is available: the
function's parameters, as `isParam` says, the values that the constants of `r` define, and the
parameters of the regions nested in `r` that enclose that `old` region.  So every value that such
a region uses is one of these, or is defined in it at a point that every path to the use passes
through. -/
theorem Region.oldScoped_iff {isParam : ValId → Bool} {r : Region env α} :
    r.OldScoped isParam ↔ ∀ p ∈ Block.oldRegionsList [] r.blocks.toList,
      Body.Shaped p.1.blocks.toList ∧
        Body.DomCorrect (Region.oldSees isParam (Region.constIds [r]) p.2 · = true)
          p.1.blocks.toList := by
  simp only [Region.OldScoped, Region.domOK_iff]

end

end Strata.Dyn
