/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The rules of `Func.WF` that a function breaks

The checker's tests name the rules of `Func.WF` that a rejected function breaks, so that each
test shows which rule rejects it.  `WFParts.broken` names them, and `WFParts.failing` names those
that the function of a failed build breaks.
-/

namespace Strata.Dyn.WFParts

public section

open Build (FailedFunc)

variable {env : Env Unit} [base ≼ env] {α β : Type}

/-- The rules of `Func.WF` that `f` breaks, by name, in the order of `Func.WF`'s fields.  The
four parts of `Func.ContractRegionsWF` and the two of `Func.OldWF` each have their own name:

* `extern`, `params`, `labels`, `unique names`, `names`: the fields `externIff`, `entryParams`,
  `labelsDistinct`, `valueNamesUnique` and `valuesNamed`;
* `body`, `scoping`, `contract`, `modes`: `Func.BodyWF`, `Func.Reachable` with `Func.Scopable`,
  `Func.ContractWF` and `Func.ClauseModesWF`;
* `failures`, `propagates`, `terminators`, `acyclic`: `Func.ClauseFailuresWF`,
  `Region.Propagates`, `Region.EndsInControl` and `Region.Acyclic` of the contract's regions;
* `old`, `old scope`: `Func.OldPlaced` and `Func.OldScoped`;
* `ghosts`: `Func.GhostsInContract`. -/
def broken (f : Func env α) : List String :=
  (if decide (f.extern = f.blocks.isEmpty) then [] else ["extern"]) ++
  (if decide (f.extern = false → ∀ b ∈ f.blocks[0]?, b.params = f.params) then []
    else ["params"]) ++
  (if decide (Label.Distinct (Label.exit :: f.labels)) then [] else ["labels"]) ++
  (if decide f.names.toList.Nodup then [] else ["unique names"]) ++
  (if decide (ValDecl.idBound f.defs ≤ f.names.size) then [] else ["names"]) ++
  (if decide f.BodyWF then [] else ["body"]) ++
  (if decide (f.Reachable ∧ f.Scopable) then [] else ["scoping"]) ++
  (if decide f.ContractWF then [] else ["contract"]) ++
  (if decide f.ClauseModesWF then [] else ["modes"]) ++
  (if decide f.ClauseFailuresWF then [] else ["failures"]) ++
  (if decide (Region.Propagates f.contract.regions) then [] else ["propagates"]) ++
  (if decide (Region.EndsInControl f.contract.regions) then [] else ["terminators"]) ++
  (if decide (Region.Acyclic f.contract.regions) then [] else ["acyclic"]) ++
  (if decide f.OldPlaced then [] else ["old"]) ++
  (if decide f.OldScoped then [] else ["old scope"]) ++
  (if decide f.GhostsInContract then [] else ["ghosts"])

/-- The rules that the function of a failed build breaks, as `broken` names them, or `misuse` if
the build failed by a misuse.  Empty for a build that gave a checked function. -/
def failing (b : Except (FailedFunc env α β) {fn : Func env α // fn.WF}) : List String :=
  match b with
  | .ok _ => []
  | .error e => if !e.misuses.isEmpty then ["misuse"] else broken e.func

end

end Strata.Dyn.WFParts
