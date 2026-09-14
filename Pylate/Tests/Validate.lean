/-
The rule-database validator as a gate.

`RuleValidate` reported its conditions to nobody: no module imported it, so it
was not built and never ran. A validator that does not run is a validator that
cannot fail, which is the same fail-open shape as the empty rule set this suite
family exists to prevent. This suite runs it over the live compiled rules and
fails on any blocking finding.

Non-blocking findings are printed rather than asserted. `unkeyed-syntax` is the
loudest of them at 49, and it is a measurement of REFACTOR_PLAN section 1's
remaining work, not a defect to fix here.
-/
import Pylate.RuleLang.Validate

namespace Pylate.Tests.Validate

open Pylate
open Pylate.RuleDriven

private def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def runAll : IO Unit := do
  let report := Validate.report compiledBuiltinRules
  let blocking := report.blocking
  for finding in blocking do
    IO.println s!"  BLOCKING [{finding.condition}] {finding.rule}: {finding.detail}"
  ensure blocking.isEmpty
    s!"rule validator: {blocking.length} blocking findings"
  -- The counts are printed so a change in them is visible in the suite output
  -- even when nothing blocks.
  let counts := report.byCondition
  let shown := counts.map (fun (condition, count) => s!"{condition}={count}")
  IO.println s!"RuleValidate: 0 blocking ({", ".intercalate shown})"

end Pylate.Tests.Validate
