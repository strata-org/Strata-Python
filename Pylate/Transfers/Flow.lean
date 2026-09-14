/-
Explicit flow domains for the rule interpreter.

Unlike Flow and AMulti, absence of normal completion is represented directly,
and raised classes retain their own value and heap state until a legacy
adapter deliberately joins them.
-/
import Pylate.Machine

namespace Pylate.RuleDriven

open Pylate

-- `Flow`, `Normal` and most of their API live in `Engine/Exc.lean`: there is
-- one transfer result, not a copy of a legacy one. Only the parts that need
-- the analyzer monad stay here, declared into the type's own namespace.

/-- Continue from a normal completion, keeping the incoming exceptions. -/
def _root_.Pylate.Flow.bindNormal (flow : Flow)
    (next : AbsVal -> AState -> M Flow) : M Flow := do
  match flow.normal with
  | none => pure flow
  | some (value, state) =>
    let result <- next value state
    pure { result with raised := flow.raised.join result.raised }


structure TruthFlow where
  truthy : Option Normal := none
  falsy  : Option Normal := none
  raised : RaisedFlow := {}
deriving Repr, Inhabited

namespace TruthFlow

def join (left right : TruthFlow) : TruthFlow :=
  { truthy := joinNormal left.truthy right.truthy
    falsy := joinNormal left.falsy right.falsy
    raised := left.raised.join right.raised }

end TruthFlow

abbrev ReturnFlow := AbsVal × AState

def joinReturn : Option ReturnFlow -> Option ReturnFlow -> Option ReturnFlow :=
  joinNormal

structure Completion where
  normal    : Option AState := none
  returned  : Option ReturnFlow := none
  broke     : Option AState := none
  continued : Option AState := none
  raised    : RaisedFlow := {}
deriving Repr, Inhabited

namespace Completion

def ofNormal (state : AState) : Completion := { normal := some state }

def join (left right : Completion) : Completion :=
  { normal := joinOpt left.normal right.normal
    returned := joinReturn left.returned right.returned
    broke := joinOpt left.broke right.broke
    continued := joinOpt left.continued right.continued
    raised := left.raised.join right.raised }

/-- Compatibility boundary for statement families not yet migrated to the rule engine. -/
def toAMulti (flow : Completion) : AMulti :=
  let (retVal, retSt) := match flow.returned with
    | some (value, state) => (value, some state)
    | none => (AbsVal.bot, none)
  { normal := flow.normal
    brk := flow.broke
    cont := flow.continued
    retSt
    retVal
    excSt := flow.raised.state?
    excs := flow.raised.classes }

end Completion

end Pylate.RuleDriven
