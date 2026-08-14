/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Specs.Decls

/-!
## Properties of SpecExpr

Key results:
- `SpecExpr.hasFreeVar_implies_mentionsVar` - every free-variable occurrence is
  also a conservative variable mention.
-/

public section

namespace StrataPython.Specs

theorem SpecExpr.hasFreeVar_implies_mentionsVar (e : SpecExpr) (name : String) :
    e.hasFreeVar name → e.mentionsVar name := by
  induction e <;> simp_all [SpecExpr.hasFreeVar, SpecExpr.mentionsVar] <;> grind

end StrataPython.Specs
end
