/-
Every focused Lean suite as one Lake target: `lake exe pylateTests`.
-/
import Pylate.Tests.Emptiness
import Pylate.Tests.Calls
import Pylate.Tests.Compatibility
import Pylate.Tests.ContractPrelude
import Pylate.Tests.Contracts
import Pylate.Tests.EmptinessRules
import Pylate.Tests.Expressions
import Pylate.Tests.Fixpoint
import Pylate.Tests.KnownMethods
import Pylate.Tests.Plan
import Pylate.Tests.Protocols
import Pylate.Tests.Statements
import Pylate.Tests.TypedDictPolicy
import Pylate.Tests.SyntaxPlans
import Pylate.Tests.Validate
import Pylate.Tests.StructuralExpressions
import Pylate.Tests.ShapePolicy

def main : IO Unit := do
  Pylate.Tests.Emptiness.runAll
  Pylate.Tests.Calls.runAll
  Pylate.Tests.Compatibility.runAll
  Pylate.Tests.ContractPrelude.runAll
  Pylate.Tests.Contracts.runAll
  Pylate.Tests.ShapePolicy.runAll
  Pylate.Tests.EmptinessRules.runAll
  Pylate.Tests.Expressions.runAll
  Pylate.Tests.Fixpoint.runAll
  Pylate.Tests.KnownMethods.runAll
  Pylate.Tests.Plan.runAll
  Pylate.Tests.Protocols.runAll
  Pylate.Tests.Statements.runAll
  Pylate.Tests.TypedDictPolicy.runAll
  Pylate.Tests.SyntaxPlans.runAll
  Pylate.Tests.Validate.runAll
  Pylate.Tests.StructuralExpressions.runAll
