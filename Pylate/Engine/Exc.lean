/-
Exceptional flow values: the (state, class set) pair a transfer
threads, and the (value, state, exc) result triple.
-/
import Pylate.Cells.State
import Pylate.Syntax.Nodes

namespace Pylate

structure Exc where
  st   : Option AState := none
  tags : Fset String := []
deriving Inhabited

def Exc.add (e : Exc) (st : AState) (ts : Fset String) : Exc :=
  if ts.isEmpty then e
  else { st := joinOpt e.st (some st), tags := Fset.union ts e.tags }

def Exc.joinE (a b : Exc) : Exc :=
  { st := joinOpt a.st b.st, tags := Fset.union a.tags b.tags }

def Exc.isEmpty (e : Exc) : Bool := e.tags.isEmpty

/-- Where an exception came from decides what the abort policy may do with it.
    `internal` signals are raised and consumed inside one transfer and must
    never reach the policy or the enclosing statement. -/
inductive Provenance
  | machine
  | user
  | internal
deriving Repr, Inhabited, BEq, DecidableEq

structure RaisedCase where
  cls   : String
  value : AbsVal
  state : AState
  /-- The raise site. Two raises of the same class from different places are
      different completions with different states, and a handler entered from
      one of them should see that one's state. Deliberately has no default: it
      is the key, so a construction site that omitted it would silently merge
      into another raise's bucket. -/
  origin : Pos
  /-- Provenance, carried so policy can be applied where the exception
      escapes rather than where it was constructed. -/
  from? : Provenance := .machine
deriving Repr, Inhabited

structure RaisedFlow where
  cases : List RaisedCase := []
deriving Repr, Inhabited

namespace RaisedFlow

/-- Keyed by class *and* origin, so two raise sites of the same class stay
    separate completions. Keying by class alone merged them here, before any
    handler could see either state, which is why a handler could not tell which
    raise it was entered from. The pair is syntactic, so the number of cases is
    bounded by the raise sites in the program and a loop fixpoint still
    converges: the same site recurring merges with itself. -/
def add (flow : RaisedFlow) (fresh : RaisedCase) : RaisedFlow :=
  match flow.cases.find? (fun c => c.cls == fresh.cls && c.origin == fresh.origin) with
  | none => { cases := flow.cases ++ [fresh] }
  | some _ =>
    { cases := flow.cases.map fun old =>
        if old.cls == fresh.cls && old.origin == fresh.origin then
          { old with
            value := old.value.join fresh.value
            state := old.state.join fresh.state }
        else old }

def join (left right : RaisedFlow) : RaisedFlow :=
  right.cases.foldl add left

/-- Class order is irrelevant to the set, but preserving case order keeps the
    legacy `Exc` view stable across conversions. -/
def classes (flow : RaisedFlow) : Fset String :=
  flow.cases.foldr (fun raised out => Fset.insert raised.cls out) []

def state? (flow : RaisedFlow) : Option AState :=
  flow.cases.foldl (fun out raised => joinOpt out (some raised.state)) none

def toExc (flow : RaisedFlow) : Exc :=
  { st := flow.state?, tags := flow.classes }

end RaisedFlow

/-- The joined `Exc` view expanded back into per-class cases. The joined state
    is shared, so this direction cannot recover per-class precision; it exists
    for transfers not yet converted. -/
def Exc.toRaised (e : Exc) : RaisedFlow :=
  match e.st with
  | none => {}
  | some state =>
    -- `Pos` default is the origin-unknown sentinel: the `Exc` view already threw
    -- the raise sites away, so every class comes back attributed to nowhere and
    -- they all share one bucket. Anything routed through here loses the
    -- per-site distinction, which is the reason to retire this view.
    { cases := e.tags.map fun cls =>
        { cls, value := AbsVal.bot, state, origin := {} } }

instance : Coe Exc RaisedFlow := ⟨Exc.toRaised⟩

abbrev Normal := AbsVal × AState

def joinNormal : Option Normal -> Option Normal -> Option Normal
  | none, right => right
  | left, none => left
  | some (leftValue, leftState), some (rightValue, rightState) =>
    some (leftValue.join rightValue, leftState.join rightState)

/-- The single result of a transfer: the normal completion if one is reachable,
    and the per-class exceptional completions. Absence of normal completion is
    represented directly rather than by a bottom value beside a carrier state.
-/
structure Flow where
  normal : Option Normal := none
  raised : RaisedFlow := {}
deriving Inhabited, Repr

namespace Flow

def empty : Flow := {}

def ofNormal (value : AbsVal) (state : AState) : Flow :=
  { normal := some (value.reduce, state) }

def join (left right : Flow) : Flow :=
  { normal := joinNormal left.normal right.normal
    raised := left.raised.join right.raised }

def addRaised (flow : Flow) (raised : RaisedCase) : Flow :=
  { flow with raised := flow.raised.add raised }

end Flow

/-- The former legacy expression result. It is the same type now; the alias
    remains only until the last `ERes` mention is renamed. -/
abbrev ERes := Flow

def Flow.exc (r : ERes) : Exc := r.raised.toExc

def Flow.hasNormal (r : ERes) : Bool := r.normal.isSome

/-- Builds an `ERes` from a value/state/raised triple, reading a bottom value as
    "no normal completion". Sites written in triple form go through this. -/
def Flow.of (value : AbsVal) (state : AState)
    (raised : RaisedFlow := {}) : ERes :=
  if value.isBot then { raised } else { normal := some (value, state), raised }

/-- No normal completion: only the exceptional ones. -/
def Flow.ofRaised (raised : RaisedFlow) : ERes := { raised }

/-- The normal state when one is reachable, and the caller's state otherwise.
    Sites that consume a state unconditionally must name the fallback they mean,
    rather than relying on a carrier state stored beside a bottom value. -/
def Flow.stateOr (r : ERes) (fallback : AState) : AState :=
  match r.normal with
  | some (_, state) => state
  | none => fallback

/-- The normal value, or bottom when no normal completion is reachable. -/
def Flow.val (r : ERes) : AbsVal :=
  match r.normal with
  | some (value, _) => value
  | none => AbsVal.bot

end Pylate
