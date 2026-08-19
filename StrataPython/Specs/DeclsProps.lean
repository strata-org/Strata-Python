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
- `PCmpOp.ofTag_tag` - `PCmpOp.ofTag?` inverts `PCmpOp.tag` for every variant,
  proved exhaustively so a new constructor breaks the proof at elaboration time.
-/

public section

namespace StrataPython.Specs

theorem SpecExpr.hasFreeVar_implies_mentionsVar (e : SpecExpr) (name : String) :
    e.hasFreeVar name → e.mentionsVar name := by
  induction e <;> simp_all [SpecExpr.hasFreeVar, SpecExpr.mentionsVar] <;> grind

theorem PCmpOp.ofTag_tag (op : PCmpOp) : PCmpOp.ofTag? op.tag = some op := by
  cases op <;> simp [PCmpOp.tag, PCmpOp.ofTag?]

end StrataPython.Specs
end
