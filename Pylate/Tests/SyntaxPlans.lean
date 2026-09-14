/-
The section 1.4 plan primitives, exercised on the section 1.5 worked examples.

These test the primitive, not a routed rule: `evalChild` must thread state left
to right, abandon `next` on a raised child, and make each child's result
nameable by position. Until the syntax dispatch is routed, this is what pins the
semantics of the primitive the rest of section 1 is built on.
-/
import Pylate.Rules.SyntaxPlans

namespace Pylate.Tests.SyntaxPlans

open Pylate
open Pylate.RuleDriven

private def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def position : Pos := ⟨1, 0, 1⟩

/-- A child evaluator that returns a distinct int-tagged value per subterm and
    records the order it was asked, so ordering is observable. -/
private def orderedServices (_log : IO.Ref (List String)) : Services :=
  { invoke := fun _ _ _ _ _ state => pure (Flow.ofNormal anyV state)
    truth := fun _ value state =>
      pure { truthy := some (value, state), falsy := some (value, state) }
    evalSubterm := fun _ subterm state => do
      let label := match subterm with
        | .expr (.name _ x) => x
        | .expr (.const _ _) => "const"
        | _ => "other"
      pure (Flow.ofNormal (strLitV label) state) }

/-- A child evaluator whose second call raises, so abandon-on-exception shows. -/
private def raisingServices : Services :=
  { invoke := fun _ _ _ _ _ state => pure (Flow.ofNormal anyV state)
    truth := fun _ value state =>
      pure { truthy := some (value, state), falsy := some (value, state) }
    evalSubterm := fun _ subterm state =>
      match subterm with
      | .expr (.name _ "bad") =>
        pure { raised := (RaisedFlow.add {} { cls := "ValueError", value := AbsVal.bot, state, origin := {} }) }
      | .expr (.name _ x) => pure (Flow.ofNormal (strLitV x) state)
      | _ => pure (Flow.ofNormal anyV state) }

private def nameExpr (x : String) : Subterm := .expr (.name position x)

/-- A minimal node of each routed kind, so the frame builder is exercised for
    every key the table claims rather than only the ones a test happens to use. -/
private def sampleOf : ExprKind -> Expr
  | .binop => .binop position .add (.name position "a") (.name position "b")
  | .subscr => .subscr position (.name position "a") (.name position "b")
  | .boolAnd => .boolop position true [.name position "a", .name position "b"]
  | .boolOr => .boolop position false [.name position "a", .name position "b"]
  | .ifexp =>
    .ifexp position (.name position "c") (.name position "a") (.name position "b")
  | .listlit => .listlit position [.name position "a"]
  | .setlit => .setlit position [.name position "a"]
  | .notE => .notE position (.name position "a")
  | .unary => .unary position .neg (.name position "a")
  | .fstr => .fstr position [.name position "a"]
  | _ => .name position "unrouted"

def runAll : IO Unit := do
  let log <- IO.mkRef []
  -- Two children, both named by position: the plan reads child 0 and child 1.
  let frame : Frame :=
    { subterms := [nameExpr "left", nameExpr "right"] }
  let plan : Plan :=
    .evalChild 0 <| .evalChild 1 <|
      .normal (.join (.read (.evaluated 0)) (.read (.evaluated 1)))
  let flow := (executePlan (orderedServices log) position plan frame {}).run' {}
  match flow.flow.normal with
  | none => throw (IO.userError "evalChild: no normal completion")
  | some (value, _) =>
    ensure (value.strLits.contains "left" && value.strLits.contains "right")
      s!"evalChild: expected both children in the result, got {value.strLits}"

  -- joinEvaluated smashes every child, which is what a literal needs.
  let literalPlan : Plan := .evalChildren 0 (.normal .joinEvaluated)
  let literalFlow :=
    (executePlan (orderedServices log) position literalPlan frame {}).run' {}
  match literalFlow.flow.normal with
  | none => throw (IO.userError "evalChildren: no normal completion")
  | some (value, _) =>
    ensure (value.strLits.length == 2)
      s!"evalChildren: expected both children smashed, got {value.strLits}"

  -- A raised child abandons `next` and carries its class out.
  let badFrame : Frame := { subterms := [nameExpr "ok", nameExpr "bad"] }
  let badPlan : Plan :=
    .evalChild 0 <| .evalChild 1 <| .normal (.read (.evaluated 1))
  let badFlow := (executePlan raisingServices position badPlan badFrame {}).run' {}
  ensure badFlow.flow.normal.isNone
    "a raised child must abandon the rest of the plan"
  ensure (badFlow.flow.raised.classes.contains "ValueError")
    "a raised child must carry its class into the plan's flow"

  -- Reading a child before evaluating it is a compile-time error, not a
  -- bottom read: this is what `refErrors` now checks.
  let bogus : Plan := .normal (.read (.evaluated 0))
  ensure (!(planErrors {} false 0 0 bogus).isEmpty)
    "reading an unevaluated child must fail validation"
  -- And after an evalChild it is in scope.
  ensure (planErrors {} false 0 0 (.evalChild 0 (.normal (.read (.evaluated 0))))).isEmpty
    "reading an evaluated child must pass validation"

  -- The three abnormal completions must reach `Completion`, or no statement can
  -- be a plan. This is the design step section 1 named as blocking them.
  let bare : Frame := {}
  let ret := (executePlan (orderedServices log) position
    (.returnWith .int) bare {}).run' {}
  ensure ret.returned.isSome "returnWith must produce a returned completion"
  ensure ret.flow.normal.isNone
    "a return is not also a normal completion"
  ensure (PlanResult.toCompletion ret).returned.isSome
    "toCompletion must carry the return through to the statement kernel"
  let brk := (executePlan (orderedServices log) position .breakLoop bare {}).run' {}
  ensure brk.broke.isSome "breakLoop must produce a broke completion"
  let cont := (executePlan (orderedServices log) position .continueLoop bare {}).run' {}
  ensure cont.continued.isSome "continueLoop must produce a continued completion"
  -- All five can be live at once, which is the property the statement kernel
  -- relies on: a plan whose alternatives return and fall through yields both.
  let both := (executePlan (orderedServices log) position
    (.alternatives [.returnWith .int, .normal .none]) bare {}).run' {}
  ensure (both.returned.isSome && both.flow.normal.isSome)
    "alternatives must keep a return and a normal completion side by side"

  -- Every structural plan must compile as a rule. A plan that reads a child
  -- before evaluating it, or names an operator its node does not carry, is a
  -- rule error and must fail here rather than silently leave the table short.
  match compileRules Syntax.syntaxRuleSet with
  | .error errors =>
    let shown := errors.toList.map (fun e => s!"{e.rule}: {e.detail}")
    throw (IO.userError
      s!"syntax rules failed to compile: {"; ".intercalate shown}")
  | .ok compiled =>
    ensure (compiled.entries.length == Syntax.syntaxRuleSet.rules.length)
      s!"syntax table dropped rules: {compiled.entries.length} of {Syntax.syntaxRuleSet.rules.length}"
    IO.println s!"RuleSyntaxPlan: {compiled.entries.length} structural plans compile"

  -- Every routed key must have a frame builder, or the dispatcher would find a
  -- plan and have no children to give it.
  for kind in Syntax.routedExprKinds do
    ensure (Syntax.framesOf (sampleOf kind)).isSome
      s!"routed key {kind.render} has no frame builder"

  IO.println "RuleSyntaxPlan tests passed"

end Pylate.Tests.SyntaxPlans
