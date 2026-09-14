/-
Emptiness-driven routing of the removal rules, and the reduced product a fresh
collection must satisfy.
-/
import Pylate.Rules.Builtins
import Pylate.Transfers.Iteration

namespace Pylate.Tests.EmptinessRules

open Pylate
open Pylate.RuleDriven

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position : Pos := ⟨9501, 4, 0⟩

def services : Services :=
  compiledBuiltinRules.services
    { Services.opaque with
      applyContracts := Contracts.applyContracts {
        classInfo := fun _ => pure none
        resolveMethod := fun _ _ => pure none
        invokeUser := fun _ _ _ _ _ state => pure (Flow.ofNormal anyV state)
        unknownProtocol := fun _ _ _ state => pure (Flow.ofNormal anyV state)
        truthValue := fun _ _ state => pure (Flow.ofNormal (V [.tbool]) state)
        consumeElements := fun _ value _ state =>
          pure (Flow.ofNormal value state)
        invokeCallable := fun _ _ _ state => pure (Flow.ofNormal anyV state)
        consumeMappingPairs := fun _ _ state => pure (Flow.ofNormal anyV state)
        recursiveAnnotation := fun _ _ value state =>
          pure (Flow.ofNormal value state)
      } }

def run (name : String) (receiver : AbsVal) (arguments : List AbsVal)
    (state : AState) : Flow :=
  (services.invoke position (.method name) (some receiver) arguments []
    state).run { policy := Policy.audit } |>.1

def collection (site : NodeId) (cls : LocCls) (element : AbsVal)
    (emptiness : Emptiness) : AbsVal × AState :=
  let location : Loc := ⟨site, cls, true⟩
  let state := (({} : AState).heapSet location .elem element)
  (V [cls.tag] [location], strongEmptinessUpdate state location emptiness)

def hasRaised (flow : Flow) (cls : String) : Bool :=
  flow.raised.cases.any (·.cls == cls)

def testListPopByEmptiness : IO Unit := do
  let (empty, emptyState) := collection 10 .list AbsVal.bot .empty
  let emptyFlow := run "pop" empty [] emptyState
  ensure (emptyFlow.normal.isNone && hasRaised emptyFlow "IndexError")
    "pop of a definitely empty list must raise only IndexError"

  let (full, fullState) := collection 11 .list (V [.tint]) .nonempty
  let fullFlow := run "pop" full [] fullState
  ensure (fullFlow.normal.isSome && !(hasRaised fullFlow "IndexError"))
    "pop of a definitely nonempty list must not raise IndexError"

  let indexed := run "pop" full [V [.tint]] fullState
  ensure (indexed.normal.isSome && hasRaised indexed "IndexError")
    "an explicit index on a nonempty list keeps IndexError"

  let (unknown, unknownState) := collection 12 .list (V [.tint]) .top
  let unknownFlow := run "pop" unknown [] unknownState
  ensure (unknownFlow.normal.isSome && hasRaised unknownFlow "IndexError")
    "pop of a maybe-empty list must keep both outcomes"

def testSetPopByEmptiness : IO Unit := do
  let (empty, emptyState) := collection 20 .set AbsVal.bot .empty
  let emptyFlow := run "pop" empty [] emptyState
  ensure (emptyFlow.normal.isNone && hasRaised emptyFlow "KeyError")
    "pop of a definitely empty set must raise only KeyError"

  let (full, fullState) := collection 21 .set (V [.tint]) .nonempty
  let fullFlow := run "pop" full [] fullState
  ensure (fullFlow.normal.isSome && !(hasRaised fullFlow "KeyError"))
    "pop of a definitely nonempty set must not raise KeyError"

  let (unknown, unknownState) := collection 22 .set (V [.tint]) .top
  let unknownFlow := run "pop" unknown [] unknownState
  ensure (unknownFlow.normal.isSome && hasRaised unknownFlow "KeyError")
    "pop of a maybe-empty set must keep both outcomes"

def testCopyReducedProduct : IO Unit := do
  let (full, fullState) := collection 30 .list (V [.tstr]) .nonempty
  let copied := run "copy" full [] fullState
  let some (value, output) := copied.normal
    | throw (IO.userError "copy lost its normal completion")
  let some fresh := value.locs.head?
    | throw (IO.userError "copy returned no location")
  ensure (fresh != ⟨30, .list, true⟩) "copy aliased its source"
  ensure (output.emptinessGet fresh != .empty)
    "a copy holding elements was recorded as definitely empty"
  ensure (Tag.tstr ∈ (output.heapGet fresh .elem).tags)
    "copy lost the source element summary"

  let (empty, emptyState) := collection 31 .list AbsVal.bot .empty
  let emptyCopy := run "copy" empty [] emptyState
  let some (emptyValue, emptyOutput) := emptyCopy.normal
    | throw (IO.userError "copy of an empty list lost its completion")
  let some emptyFresh := emptyValue.locs.head?
    | throw (IO.userError "copy returned no location")
  ensure (emptyOutput.emptinessGet emptyFresh == .empty)
    "copy of an empty list is empty"

def testClearAndGrow : IO Unit := do
  let (full, fullState) := collection 40 .list (V [.tint]) .nonempty
  let cleared := run "clear" full [] fullState
  let some (_, clearedState) := cleared.normal
    | throw (IO.userError "clear lost its completion")
  ensure (clearedState.emptinessGet ⟨40, .list, true⟩ == .empty)
    "clear did not establish Empty"
  ensure (clearedState.heapGet ⟨40, .list, true⟩ .elem).isBot
    "clear left an element summary behind"

  let (empty, emptyState) := collection 41 .list AbsVal.bot .empty
  let grown := run "append" empty [V [.tstr]] emptyState
  let some (_, grownState) := grown.normal
    | throw (IO.userError "append lost its completion")
  ensure (grownState.emptinessGet ⟨41, .list, true⟩ == .nonempty)
    "append did not establish NonEmpty"

/-- A validation error in the rule set degrades the engine to its fallback, so
    the compiled set must be checked, not assumed. -/
def testRuleSetCompiles : IO Unit := do
  match compileRules builtinRuleSet with
  | .ok rules =>
    ensure (rules.entries.length == builtinRuleSet.rules.length)
      s!"compiled {rules.entries.length} of {builtinRuleSet.rules.length} rules"
    ensure (compiledBuiltinRules.entries.length == rules.entries.length)
      "the shared compiled rule set is not the validated one"
  | .error errors =>
    throw (IO.userError
      s!"builtin rule set is invalid: {errors.toList.map (·.detail)}")

def runAll : IO Unit := do
  testRuleSetCompiles
  testListPopByEmptiness
  testSetPopByEmptiness
  testCopyReducedProduct
  testClearAndGrow
  IO.println "RuleEmptinessRules tests passed"

end Pylate.Tests.EmptinessRules
