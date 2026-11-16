/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.Cert

set_option autoImplicit false

/-!
# A certificate of demotion against the padded original

A demotion is the source of a promotion whose target is its original with entry padding.
The padding is explicit: extra slot capacity and a prefix of literal or pure computations and
cell allocations for each function. Applying it changes only function slot capacity and entry
instructions; all other blocks, edges and body metadata stay as they are, and regions are
unchanged. The padded original is computed, not a third module chosen independently.

The certificate `DemotionOK` requires `Padding.Fresh` relative to the original: every padding
destination is in the added slots, and every operand is a result of an earlier padding
instruction (`FreshCode`). Freshness is relative to the original's declared slot count, which
bounds the slots it uses when it validates (`WF`). So the padding of a validated original
neither reads nor writes a slot of it, and never reads an added slot before defining it. The
promotion part remains `PromotionOK`, and is the only part the soundness theorems use.
This does not assert that the pass produced the demoted module, or that the padding is harmless
compared with the original. Validation of the padded original, including the new instructions'
types, is a hypothesis of the soundness theorems, not part of this certificate.

Padding traverses the functions once and prepends the added instructions to each entry.
-/

namespace Strata.Dyn.DemoteSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-- A padding prefix defines only slots in the added range and reads only previously defined
padding results. Starting with no defined slots gives a closed computation of defaults and
allocations, with no rule tree (`sem`), call, cell read or cell write. -/
def FreshCode (lo hi : Nat) : List Nat → List (LInsn M) → Prop
  | _, [] => True
  | defined, i :: is =>
    lo ≤ i.dst ∧ i.dst < hi ∧
      (match i with
      | .const .. => True
      | .pure _ _ _ _ args => ∀ a ∈ args, a ∈ defined
      | .refNew _ _ v => v ∈ defined
      | _ => False) ∧
      FreshCode lo hi (i.dst :: defined) is

/-- The prefix and extra slot capacity for a function entry. `EntryPadding.Fresh` restricts
this data relative to the function's own slot count before it can be certified. -/
structure EntryPadding (M : RunModel) where
  slots : Nat
  insns : List (LInsn M)

/-- Every destination is in the slots added beyond `slots`, and every operand is a result
defined earlier in the prefix. No slot below `slots` can be read or written. -/
def EntryPadding.Fresh (p : EntryPadding M) (slots : Nat) : Prop :=
  FreshCode slots (slots + p.slots) [] p.insns

/-- Add the prefix at block zero, keeping every block's parameters, scope and terminator.
Additional slot capacity does not renumber any existing slot. -/
def EntryPadding.apply (p : EntryPadding M) (g : LBody M) : LBody M :=
  { g with
    slots := g.slots + p.slots
    blocks := g.blocks.modify 0 (fun b => { b with insns := p.insns ++ b.insns }) }

/-- Entry padding indexed by linked function, without adding or removing bodies. -/
structure Padding (M : RunModel) where
  funcs : Nat → EntryPadding M

/-- The padded original, determined by the original and the added entry instructions and slots.
Only function entries receive instructions; regions are unchanged. -/
def Padding.apply (p : Padding M) (m : LModule M) : LModule M :=
  ⟨m.funcs.mapIdx (fun i g => (p.funcs i).apply g), m.regions⟩

/-- Each function's padding is closed and uses only slots added beyond that function's own
declared slot count, so it does not read or write any slot of a validated original. -/
def Padding.Fresh (p : Padding M) (m : LModule M) : Prop :=
  ∀ i (hi : i < m.funcs.size), (p.funcs i).Fresh (m.funcs[i]'hi).slots

/-- The padding is fresh relative to the original, and the demoted module's cells are promoted
by the computed padded original. The promotion part reuses ref-to-reg's soundness in the
opposite direction, and the soundness theorems use it alone; freshness restricts what counts as
a padding. -/
def DemotionOK (original demoted : LModule M) (padding : Padding M) : Prop :=
  padding.Fresh original ∧ RefToRegSound.PromotionOK demoted (padding.apply original)

end

end Strata.Dyn.DemoteSound
