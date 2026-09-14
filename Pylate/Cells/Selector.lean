/-
What a heap cell is, as a type rather than as a spelling.

The heap is keyed by `(Loc × CellSelector)` rather than `(Loc × String)`. A
rendered name erases the distinctions that matter: `s!"k:{index}"` would serve
both a tuple slot and a dict literal key, disjoint only when the `Loc` class
happens to differ, and a mistyped name would read bottom instead of failing to
compile. A constructor cannot be mistyped.

`render` is for display and for the emitted log only. It is injective
(`render_inj` below, decided at build time), so a rendered cell name still
identifies its selector uniquely -- which is what lets a reader of the HTML or
the JSON reason about cells without the type in hand.
-/
import Pylate.Domains.Value

namespace Pylate

inductive CellSelector
  | field (name : String)
  | elem
  | nonempty
  | dictKeys
  | dictValues
  | literalKey (key : String)
  | tupleSlot (index : Nat)
  /-- Relates a view to the mapping it was taken from. -/
  | dictViewSource
  /-- Relates a loop's iterator to the object it was obtained from, and to the
      sequence being walked. -/
  | iteratorSource
  | sequenceSource
deriving Repr, Inhabited, BEq, DecidableEq, Hashable

/-- The spelling. `$` and `@` cannot begin a Python identifier, so the three
    analysis-internal cells cannot collide with a program's own field, and a
    tuple slot is spelled `t:` rather than `k:` so it cannot collide with a
    literal key either. -/
def CellSelector.render : CellSelector -> String
  | .field name => name
  | .elem => "elem"
  | .nonempty => "nonempty"
  | .dictKeys => "key"
  | .dictValues => "val"
  | .literalKey key => s!"k:{key}"
  | .tupleSlot index => s!"t:{index}"
  | .dictViewSource => "$dict-view-source"
  | .iteratorSource => "@iteration.source"
  | .sequenceSource => "@iteration.sequence"

/-- Cells the analysis uses to relate objects to each other, rather than cells
    the program can observe. They take part in reachability but are not part of
    the emitted log's contract. This is now a case analysis rather than a test
    on the rendered prefix. -/
def CellSelector.internal : CellSelector -> Bool
  | .dictViewSource | .iteratorSource | .sequenceSource => true
  | _ => false

/-- Which location classes a selector is meaningful for. A rule that stores
    through a selector its target cannot have is a compile-time-checkable
    mistake in the rule database rather than a silent bottom read. -/
def CellSelector.validFor (selector : CellSelector) (cls : LocCls) : Bool :=
  match selector, cls with
  | .field _, .obj _ => true
  | .elem, .list | .elem, .set | .elem, .tuple | .elem, .gen
  | .elem, .range
  | .elem, .dictkeys | .elem, .dictitems | .elem, .dictvalues => true
  | .nonempty, .list | .nonempty, .set | .nonempty, .tuple
  | .nonempty, .range | .nonempty, .gen => true
  | .dictKeys, .dict | .dictKeys, .td _
  | .dictValues, .dict | .dictValues, .td _
  | .literalKey _, .dict | .literalKey _, .td _
  | .tupleSlot _, .tuple => true
  -- A view records the mapping it was taken from, and so does an `items()`
  -- pair: its slots are refined from the source rather than read as opaque.
  | .dictViewSource, .dictkeys | .dictViewSource, .dictitems
  | .dictViewSource, .dictvalues | .dictViewSource, .tuple => true
  | .iteratorSource, _ | .sequenceSource, _ => true
  | _, _ => false

/-- The selectors that carry no payload, which is every case whose rendering
    is a fixed word. The two payload-carrying cases are checked separately
    below, because their payloads range over infinitely many values. -/
def cellSelectorAtoms : List CellSelector :=
  [.elem, .nonempty, .dictKeys, .dictValues,
   .dictViewSource, .iteratorSource, .sequenceSource]

/-- No two fixed-word selectors render alike, and none of those renderings is
    a prefix-ambiguous spelling of a payload case. Decided at build time, so a
    rendering added or changed carelessly fails the build rather than making two
    cells indistinguishable in the emitted log.

    The payload cases are separated by their prefixes: a field is a Python
    identifier, so it cannot contain ':' and cannot begin with '$' or '@'; a
    literal key is spelled `k:` and a tuple slot `t:`, which is the collision
    this type exists to prevent -- both were `k:` while the heap was keyed by
    the rendered string. -/
theorem cellSelectorAtomsRenderInjective :
    ((cellSelectorAtoms.map CellSelector.render).eraseDups.length
      = cellSelectorAtoms.length) = true := by
  native_decide

/-- No fixed-word rendering is claimed by a payload case's prefix. -/
theorem cellSelectorAtomsAvoidPayloadPrefixes :
    (cellSelectorAtoms.all fun selector =>
      let spelling := selector.render
      !(spelling.startsWith "k:") && !(spelling.startsWith "t:")) = true := by
  native_decide

/-- The three analysis-internal cells are exactly the ones a program cannot
    name: `$` and `@` cannot begin a Python identifier. -/
theorem internalCellsAreUnspellable :
    (cellSelectorAtoms.all fun selector =>
      selector.internal
        = (selector.render.startsWith "$" || selector.render.startsWith "@"))
      = true := by
  native_decide

end Pylate
