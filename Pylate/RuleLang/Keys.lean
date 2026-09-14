/-
What the heap knows about a mapping key, shared by the subscript rules and
the dict-method rules.

A key expression contributes a set of candidate literals plus the ways it can
escape that set (an open string, an unhashable operand, an unknown value).
`keyPresence` then answers, per location, whether a literal key is there.

The presence answer is only as good as the invariant that a `k:` cell records
may-be-absence as `.tmissing`. Two writers maintain it: a dict literal, whose
key set is syntactically fixed and wholly present at allocation, and
`retireKeys`, which joins `.tmissing` when keys are removed. A cell that does
not exist at all therefore means "nothing is known", never "absent" -- a
dynamic `d[k] = v` store records only the `key`/`val` summaries, so its key
has no cell of its own.
-/
import Pylate.RuleLang.Plan
import Pylate.Tables.ShapePolicy

namespace Pylate.RuleDriven

open Pylate

structure KeyCases where
  literals     : Fset String := []
  openString   : Bool := false
  userEquality : Bool := false
  unknown      : Bool := false
  absent       : Bool := false
  unhashable   : Bool := false
deriving Inhabited

def keyCases (value : AbsVal) : KeyCases := Id.run do
  let mut result : KeyCases :=
    { literals := if Tag.tstr ∈ value.tags then value.strLits else []
      openString := Tag.tstr ∈ value.tags && value.strOpen }
  for tag in value.tags do
    match tag with
    | .tobj _ =>
      result := { result with userEquality := true, unhashable := true }
    | .tany =>
      result := { result with unknown := true }
    | .tlist | .tdict | .tdictkeys | .tdictitems | .tdictvalues | .tset =>
      result := { result with unhashable := true }
    | .ttuple =>
      result := { result with absent := true, unhashable := true }
    | .tnone | .tbool | .tint | .tfloat | .tcomplex | .tbytes
    | .trange | .tgen
    | .ttype | .tunion | .tfunc | .tnotimpl =>
      result := { result with absent := true }
    | .tstr | .tunbound | .tuninit | .tmissing => pure ()
  return result

/-- Whether a key escapes the literal set it contributed, so that no set of
    per-key facts can rule a `KeyError` out. -/
def KeyCases.escapes (keys : KeyCases) : Bool :=
  keys.openString || keys.userEquality || keys.unknown || keys.absent

inductive Presence
  | present
  | missing
  | unknown
deriving Repr, DecidableEq, Inhabited

/-- What one location's heap says about one literal key. -/
def keyPresence (state : AState) (location : Loc) (key : String) : Presence :=
  let cell := state.heapGet location (.literalKey key)
  if cell.isBot then .unknown
  else if Tag.tmissing ∈ cell.tags then
    if (cell.withoutTags [.tmissing]).isBot then .missing else .unknown
  else .present

/-- The value a proven-present key holds, which is tighter than the `val`
    summary whenever the mapping's values are not all of one type. -/
def keyValue (state : AState) (location : Loc) (key : String) : AbsVal :=
  (state.heapGet location (.literalKey key)).withoutTags [.tmissing]

/-- Whether every candidate literal is present at this location, which is what
    licenses dropping the `KeyError`. An escaping key never qualifies. -/
def allKeysPresent (state : AState) (location : Loc) (keys : KeyCases) :
    Bool :=
  !keys.escapes && !keys.literals.isEmpty
    && keys.literals.all (fun key => keyPresence state location key == .present)

end Pylate.RuleDriven
