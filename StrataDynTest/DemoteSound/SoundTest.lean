/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.DemoteSound.Sound
import all StrataDynTest.DemoteSound.CertTest

set_option autoImplicit false

/-!
# Demotion's certificate, on the linked loop with a swap

The original loop uses five slots; adding its two defaults and allocations, with extra slot
capacity, computes its padded form. The demotion certificate is lifted from the promotion
certificate in `CertTest.lean`, not from a run comparison or the pass. All three linked forms
validate there for any integer default and branch rule. The padding writes only added slots,
and its operands are earlier padding results. Rejection pairs pin both slot bounds, original-slot reads, forward
reads of added slots and forbidden cell reads. Region preservation holds for every module.
The axioms of the certificate and soundness theorems are pinned.
-/

namespace Strata.Dyn.DemoteSoundTest

open Strata.Dyn.Exec
open Strata.Dyn.DemoteSound

variable {M : RunModel} (br : Fn M.interp (Exit M.interp [[], []]) [M.bool]) (k : M.interp M.int)

/-- The unpadded loop: its entry only jumps to the head, and slots zero through four hold
its parameters and the head's parameters. -/
def originalMod : LModule M := ⟨#[original br], #[]⟩

/-- The two default computations and allocations, leaving space for all of the demoted loop's
slots. The padded original leaves the write-result slots unused. -/
def entryPadding : EntryPadding M where
  slots := 8
  insns := [.const 7 ⟨M.int, k⟩, .refNew 5 M.int 7, .const 8 ⟨M.int, k⟩, .refNew 6 M.int 8]

/-- The example's destinations are added slots, and each allocation reads an earlier default
result. Its padding touches no slot of the five-slot original. -/
theorem entryPadding_fresh : (entryPadding k).Fresh 5 := by
  simp [entryPadding, EntryPadding.Fresh, FreshCode, LInsn.dst]

/-- There is one function; unused padding indices add nothing. Regions cannot be padded. -/
def padding : Padding M where
  funcs := fun i => if i = 0 then entryPadding k else ⟨0, []⟩

/-- Computing the padded original recovers the promotion target, without changing
its head, swap or return blocks. -/
theorem padded_original : (padding k).apply (originalMod br) =
    ⟨#[padded br k], #[]⟩ := by
  simp [padding, originalMod, Padding.apply, EntryPadding.apply, entryPadding, original, padded,
    loopTail]

/-- The loop with the swap is certified as a demotion of its unpadded original, with the
explicit entry padding. The promotion certificate proves the linked-code hypothesis. -/
theorem demotion_ok :
    DemotionOK (originalMod br) ⟨#[demoted br k], #[]⟩ (padding k) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    match i, hi with
    | 0, _ => exact entryPadding_fresh k
    | n + 1, hi => exact absurd hi (by simp [originalMod])
  · rw [padded_original]
    exact DemoteSoundTest.promotion_ok br k

/-! ## Padding constraints, with accepted twins -/

/-- Close a concrete padding constraint, whether an accepted prefix or an isolated rejection. -/
local macro "padding_ok" : tactic =>
  `(tactic| simp [EntryPadding.Fresh, FreshCode, LInsn.dst])

-- A destination cannot overwrite an original slot or exceed the added capacity.
example : (⟨8, [.const 5 ⟨M.int, k⟩]⟩ : EntryPadding M).Fresh 5 := by padding_ok
example : ¬ (⟨8, [.const 4 ⟨M.int, k⟩]⟩ : EntryPadding M).Fresh 5 := by padding_ok
example : (⟨8, [.const 12 ⟨M.int, k⟩]⟩ : EntryPadding M).Fresh 5 := by padding_ok
example : ¬ (⟨8, [.const 13 ⟨M.int, k⟩]⟩ : EntryPadding M).Fresh 5 := by padding_ok

-- Allocations and pure operations cannot read original slots.
example : (⟨8, [.const 7 ⟨M.int, k⟩, .refNew 5 M.int 7]⟩ : EntryPadding M).Fresh 5 := by padding_ok
example : ¬ (⟨8, [.const 7 ⟨M.int, k⟩, .refNew 5 M.int 1]⟩ : EntryPadding M).Fresh 5 := by padding_ok
example : (⟨8, [.const 7 ⟨M.int, k⟩, .pure 5 [M.int] M.int id [7]]⟩ : EntryPadding M).Fresh 5 := by
  padding_ok
example : ¬ (⟨8, [.const 7 ⟨M.int, k⟩, .pure 5 [M.int] M.int id [1]]⟩ : EntryPadding M).Fresh 5 := by
  padding_ok

-- Even an added slot must be defined before it is read; the reversed order is rejected.
example : ¬ (⟨8, [.refNew 5 M.int 7, .const 7 ⟨M.int, k⟩]⟩ : EntryPadding M).Fresh 5 := by padding_ok
example : ¬ (⟨8, [.pure 5 [M.int] M.int id [7], .const 7 ⟨M.int, k⟩]⟩ : EntryPadding M).Fresh 5 := by
  padding_ok

-- Replacing an allocation by a cell read is not padding, even on added slots.
example : ¬ (⟨8, [.const 7 ⟨M.int, k⟩, .refGet 5 M.int 7]⟩ : EntryPadding M).Fresh 5 := by padding_ok

/-- No padding can change a region, even when the original has regions. -/
example (p : Padding M) (m : LModule M) : (p.apply m).regions = m.regions := rfl

/--
info: '_private.StrataDynTest.DemoteSound.SoundTest.0.Strata.Dyn.DemoteSoundTest.demotion_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms demotion_ok

/--
info: 'Strata.Dyn.DemoteSound.demote_sound_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms demote_sound_eq

/--
info: 'Strata.Dyn.DemoteSound.demote_sound_runs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms demote_sound_runs

end Strata.Dyn.DemoteSoundTest
