import Pylate.Transfers.Expressions

namespace Pylate.Tests.Expressions

open Pylate
open Pylate.RuleDriven
open Pylate.RuleDriven.Expressions

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position : Pos := ⟨9701, 7, 3⟩

def services : Services where
  invokeUser := fun _ _ _ _ _ _ =>
    pure {}

def residual (context : Actx) : IO Residual :=
  match context.residuals.find? (·.1 == position.id) with
  | some (_, found) => pure found
  | none => throw (IO.userError "expected a residual")

def caseIs (result : Residual) (tag outcome : String) : Bool :=
  result.cases.contains (tag, outcome)

def errorIs (result : Residual) (tag cls : String) : Bool :=
  result.errors.contains s!"{tag} -> {cls}"

def hasRaised (flow : Flow) (cls : String) : Bool :=
  flow.raised.cases.any (·.cls == cls)

def testTruthRows : IO Unit := do
  let (flow, context) :=
    (truth services position (V [.tint]) {}).run
      { policy := Policy.audit }
  let result ← residual context
  ensure (result.kind == "truth") "truth residual kind differs"
  ensure (result.desc == "truthiness") "truth residual description differs"
  ensure (caseIs result "int" "builtin bool")
    "truth builtin row differs"
  ensure (flow.truthy.isSome && flow.falsy.isSome)
    "truth no longer matches the direct oracle's coarse split"

def testUnaryRows : IO Unit := do
  let (normal, normalContext) :=
    (negate services position (V [.tbool]) {}).run
      { policy := Policy.audit }
  let normalResult ← residual normalContext
  ensure (caseIs normalResult "bool" "builtin int.__neg__")
    "bool negation route differs"
  ensure normal.normal.isSome "bool negation lost normal completion"
  let (failed, failedContext) :=
    (negate services position (V [.tstr]) {}).run
      { policy := Policy.audit }
  let failedResult ← residual failedContext
  ensure (errorIs failedResult "str" "TypeError")
    "unsupported negation error row differs"
  ensure (failed.normal.isNone && hasRaised failed "TypeError")
    "unsupported negation flow differs"

def testBinaryRows : IO Unit := do
  let (added, addContext) :=
    (binary services position .add (V [.tint]) (V [.tbool]) {}).run
      { policy := Policy.audit }
  let addResult ← residual addContext
  ensure (addResult.kind == "binop" && addResult.desc == "binop Add")
    "binary residual heading differs"
  ensure (caseIs addResult "(int,bool)" "builtin int numeric slot")
    "binary builtin route differs"
  ensure added.normal.isSome "integer addition lost normal completion"
  let (divided, divContext) :=
    (binary services position .div (V [.tint]) (V [.tint]) {}).run
      { policy := Policy.audit }
  let divResult ← residual divContext
  ensure (caseIs divResult "(int,int)" "builtin int numeric slot")
    "division route differs"
  ensure (errorIs divResult "(int,int)" "ZeroDivisionError")
    "division raised row differs"
  ensure (divided.normal.isSome && hasRaised divided "ZeroDivisionError")
    "division flow differs"
  let (failed, failedContext) :=
    (binary services position .add (V [.tint]) (V [.tstr]) {}).run
      { policy := Policy.audit }
  let failedResult ← residual failedContext
  ensure (errorIs failedResult "(int,str)" "TypeError")
    "terminal binary TypeError row differs"
  ensure (failed.normal.isNone && hasRaised failed "TypeError")
    "terminal binary failure flow differs"

def testComparisonRows : IO Unit := do
  let (equal, equalContext) :=
    (comparison services position .eq (V [.tint]) (V [.tstr]) {}
      "left == right").run { policy := Policy.audit }
  let equalResult ← residual equalContext
  ensure (equalResult.kind == "comparison" &&
      equalResult.desc == "comparison Eq")
    "comparison residual heading differs"
  ensure (caseIs equalResult "(int,str)" "builtin bool")
    "equality fallback row differs"
  ensure equal.normal.isSome "equality fallback lost normal completion"
  let (ordered, orderedContext) :=
    (comparison services position .lt (V [.tint]) (V [.tstr]) {}
      "left < right").run { policy := Policy.audit }
  let orderedResult ← residual orderedContext
  ensure (errorIs orderedResult "(int,str)" "TypeError")
    "ordered comparison error row differs"
  ensure (ordered.normal.isNone && hasRaised ordered "TypeError")
    "ordered comparison failure flow differs"

def testIdentityRow : IO Unit := do
  let source := "left is right"
  let (flow, context) :=
    (comparison services position .isOp
      (V [.tnone, .tint]) (V [.tnone]) {} source).run
        { policy := Policy.audit }
  let result ← residual context
  ensure (result.kind == "identity" && result.desc == source)
    "identity residual heading differs"
  ensure (caseIs result "(none|int,none)" "bool")
    "identity row differs"
  ensure flow.normal.isSome "identity lost normal completion"

def testMembershipRows : IO Unit := do
  let (builtin, builtinContext) :=
    (membership services position false (V [.tlist]) (V [.tdict]) {}).run
      { policy := Policy.audit }
  let builtinResult ← residual builtinContext
  ensure (builtinResult.kind == "membership" &&
      builtinResult.desc == "comparison In")
    "membership residual heading differs"
  ensure (caseIs builtinResult "dict" "builtin contains")
    "builtin membership row differs"
  ensure builtin.normal.isSome "dict membership lost oracle normal flow"
  ensure (!hasRaised builtin "TypeError")
    "dict membership strengthened beyond the direct oracle"
  ensure (builtinContext.obligations.any (·.kind == "hashability"))
    "dict membership lost the oracle hashability obligation"
  let (failed, failedContext) :=
    (membership services position true (V [.tint]) (V [.tint]) {}).run
      { policy := Policy.audit }
  let failedResult ← residual failedContext
  ensure (failedResult.desc == "comparison NotIn")
    "not-in residual description differs"
  ensure (errorIs failedResult "int" "TypeError")
    "unsupported membership error row differs"
  ensure (failed.normal.isNone && hasRaised failed "TypeError")
    "unsupported membership flow differs"

def runAll : IO Unit := do
  testTruthRows
  testUnaryRows
  testBinaryRows
  testComparisonRows
  testIdentityRow
  testMembershipRows
  IO.println "RuleExpressions focused tests passed"

end Pylate.Tests.Expressions
