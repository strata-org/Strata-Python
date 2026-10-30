/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataPython.Dyn.Env
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# One part of P6: each `finally` body pushes the completion it was entered with

P6 of the canonical form asks that each `finally` body be one group of blocks, entered with the
pending completion.  A `finally`
body starts in a block `fin` whose first instruction is `py.pushPending`
(`docs/PythonToDyn.md` §7.2).  `FinallyEntered` asks that every such block push its own first
parameter, a `py.Completion`, and that `py.pushPending` occur nowhere else.  So the completion that
a `finally` body pushes is the one it was entered with.

The check does not verify that each `finally` body is emitted once: a copy of a body would be a
second `fin` block like the first.  Nor does it look at which completion the dispatch at the end
of the body cases on, or which completion a jump to `fin` passes, or see a `finally` body whose
first block does not start with `py.pushPending`.  The goldens of the corpus programs with a `finally` pin that
the translator emits each body once.  It does not cover a `with` statement either, whose `fin`
block starts by building the arguments of `__exit__`, not with `py.pushPending`.

A stricter check would also ask that no two `fin` blocks end in the same successors.  That clause
is left out: it rejects valid Python, such as a function with two `try`/`finally` statements
whose `finally` bodies both `return`, since both `fin` blocks then end in `ret`.  And it cannot
tell a copy from two different bodies: a copy whose body ends in a dispatch gets fresh arm blocks,
and two different bodies that both return look alike.
-/

namespace StrataPython.Dyn.PyCanonical

open Strata.Dyn

public section

variable {α : Type}

/-- The name of the operation the instruction applies, if it applies one. -/
@[expose] def insnName? : Instruction Py.env α → Option Name
  | .apply _ _ r .. => some r.name
  | .const .. => none

/-- The block starts a `finally` body: its first instruction is `py.pushPending`. -/
@[expose] def IsFin (b : Block Py.env α) : Prop :=
  (b.instrs[0]?.bind insnName?) = some Py.pushPending.name

instance : DecidablePred (IsFin (α := α)) := fun b =>
  inferInstanceAs (Decidable ((b.instrs[0]?.bind insnName?) = some Py.pushPending.name))

/-- The block holds `py.pushPending` only as its first instruction, and if it starts a `finally`
body, it pushes its own first parameter, a `py.Completion`. -/
@[expose] def FinEntered (b : Block Py.env α) : Prop :=
  (∀ i ∈ b.instrs.toList.drop 1, insnName? i ≠ some Py.pushPending.name) ∧
    (IsFin b → ∃ p, b.params[0]? = some p ∧ p.type = Py.Completion ∧
      (b.instrs[0]?.map (·.args)) = some #[p.id])

/-- Whether the block holds `FinEntered`. -/
@[expose] def finEnteredB (b : Block Py.env α) : Bool :=
  (b.instrs.toList.drop 1).all (fun i => insnName? i != some Py.pushPending.name) &&
    (!decide (IsFin b) ||
      (b.params[0]?).any fun p =>
        decide (p.type = Py.Completion) && (b.instrs[0]?.map (·.args)) == some #[p.id])

/-- One part of P6: every block of `fn` holds `FinEntered`, so the first block of each `finally`
body pushes the completion it was entered with, and no other block pushes one. -/
@[expose] def FinallyEntered (fn : Func Py.env α) : Prop :=
  ∀ b ∈ fn.allBlocks, FinEntered b

/-- Whether `fn` holds `FinallyEntered`. -/
@[expose] def checkFinallyEntered (fn : Func Py.env α) : Bool :=
  fn.allBlocks.all finEnteredB

end

end StrataPython.Dyn.PyCanonical
