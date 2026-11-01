/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Model invariants

A run stops with a gap whose message starts with `modelInvariantPrefix` when a precondition of the
model itself doesn't hold: a case that the model's own code or the translator rules out.  It is a gap, not a failure,
so that ref-to-reg keeps such a run (`Exec.Improves` lets a target do anything after a failure).
`isModelInvariant` recognises one; the semantics tests count such a gap as a failure of the test,
never as an allowed gap, so a reachable one is still a bug.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- The beginning of the message of a model-invariant gap. -/
def modelInvariantPrefix : String := "model invariant: "

/-- Whether the gap message `msg` is a model invariant's. -/
def isModelInvariant (msg : String) : Bool := msg.startsWith modelInvariantPrefix

end

end StrataPython.Dyn.Sem
