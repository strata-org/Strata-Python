/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Dom
public import StrataDyn.DomDecide
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Loops

The loops of a body, found in its control-flow graph.  A *back edge* is a transfer to a block
whose start dominates the point the transfer leaves from.  The *natural loop* of a back edge
from `u` to the block `h` holds `h` and every block whose start reaches `u` without passing
through `h`'s start.  In a body whose blocks are all reachable, as `Func.WF` asks, a block is in
the loop exactly when control can go from it around the loop again, and code after a `break` or
a `return` is not.  A head with several back edges, as a loop with a `continue` has, has one
natural loop per back edge.  A body with a cycle but no back edge on it, a loop with two
entries, is *irreducible*.

`StrataDyn/LoopsProps.lean` proves that `Body.backEdges` and `Body.loopBlocks` compute what
`Body.IsBackEdge` and `Body.InLoop` state.  Both decide paths with `Body.reachAvoidB`, the
proved search of `StrataDyn/DomDecide.lean`.  That search is cubic in the size of the body, and
runs once per transfer, and once per block of the body for each loop, so this is the simple
version.  `StrataDyn/LoopsFast.lean` gives the fast one and proves it equal.  Its `@[csimp]`
lemmas replace these in compiled code, so code that runs loop finding imports it.

## Main definitions

* `Body.PathAvoid`: a path between two points that avoids a third;
* `Body.IsBackEdge`, `Body.InLoop`: back edges and natural loops;
* `Body.transfers`: the transfers of a body, which `Body.backEdges` filters;
* `Body.backEdges`, `Body.loopBlocks`: the computations.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

namespace Body

variable (bs : List (Block env α))

/-- Some path from `x` reaches `y` without passing through `d`. -/
inductive PathAvoid (d : Point) : Point → Point → Prop
  | refl {x : Point} : x ≠ d → PathAvoid d x x
  | step {x u w : Point} : PathAvoid d x u → Edge bs u w → w ≠ d → PathAvoid d x w

/-- A back edge from the point `u` to the block `h`: a transfer from `u` to `h`, whose start
dominates `u`. -/
@[expose] def IsBackEdge (u : Point) (h : Label) : Prop :=
  ∃ v, Jump bs u v ∧ v.label = h ∧ Dom bs ⟨h, 0⟩ u

/-- The block `b` is in the natural loop of the back edge from `u` to `h`: it is `h`, or its
start reaches `u` without passing through `h`'s start. -/
@[expose] def InLoop (u : Point) (h : Label) (b : Block env α) : Prop :=
  b ∈ bs ∧ (b.label = h ∨ PathAvoid bs ⟨h, 0⟩ ⟨b.label, 0⟩ u)

/-- The body entered at `b`: `b` first, then its other blocks. -/
@[expose] def enteredAt (b : Block env α) : List (Block env α) :=
  b :: bs.filter (·.label != b.label)

/-- The transfers to blocks of the body, each as the point it leaves from and the label of its
target. -/
@[expose] def transfers : List (Point × Label) :=
  bs.flatMap fun b => (List.range (b.instrs.size + 1)).flatMap fun k =>
    (targets b k).filterMap fun l =>
      if bs.any (·.label == l) then some (⟨b.label, k⟩, l) else none

/-- The back edges, each as the point it leaves from and the label of its target, each once. -/
@[expose] def backEdges : List (Point × Label) :=
  ((transfers bs).filter fun (u, l) => !reachAvoidB bs ⟨l, 0⟩ u).eraseDups

/-- The labels of the natural loop of the back edge from `u` to `h`, in the body's order. -/
@[expose] def loopBlocks (u : Point) (h : Label) : List Label :=
  (bs.filter fun b => b.label == h || reachAvoidB (enteredAt bs b) ⟨h, 0⟩ u).map (·.label)

end Body

end

end Strata.Dyn
