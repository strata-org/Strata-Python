/-
TypedDict mutation policy. A TypedDict is a plain dict at runtime, so CPython
cannot witness these outcomes: the shape rules are verifier obligations and are
pinned here instead.
-/
import Pylate.Transfers.Dict

namespace Pylate.Tests.TypedDictPolicy

open Pylate
open Pylate.RuleDriven

def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def position : Pos := ⟨9601, 5, 0⟩

def rowInfo : ClassInfo :=
  { name := "Row"
    bases := ["dict"]
    mro := ["Row"]
    fullMro := ["Row", "dict", "object"]
    layout := []
    ownLayout := []
    ownMethods := []
    isExc := false
    isDataclass := false
    fields := [
      { name := "name", required := true },
      { name := "note", required := false },
      { name := "id", required := true, readOnly := true },
      { name := "tag", required := false, readOnly := true }
    ]
    isTypedDict := true
    total := false }

def classes : ClassTable := [("Row", rowInfo)]

def location : Loc := ⟨50, .td "Row", true⟩

def receiver : AbsVal := V [.tdict] [location]

/-- Required and read-only fields present, the optional one possibly absent. -/
def state : AState :=
  (((({} : AState).heapSet location (.literalKey "name") (V [.tstr]))
      |>.heapSet location (.literalKey "id") (V [.tint]))
      |>.heapSet location (.literalKey "note") (V [.tstr, .tmissing]))
      |>.heapSet location (.literalKey "tag") (V [.tstr, .tmissing])
      |>.heapSet location .dictKeys (V [.tstr])

/-- The analyzer supplies the statically known key, so the tests do too. -/
def run (method : DictMethod) (arguments : List AbsVal)
    (keywords : List (String × AbsVal))
    (literalKey : Option String := none) : Flow × Actx :=
  (Dict.execute position method receiver arguments keywords literalKey
    state).run { policy := Policy.audit, classes }

def shapeBreaks (context : Actx) : List String :=
  (context.obligations.filter (·.kind == "shape-break")).map (·.detail)

def hasShapeBreak (context : Actx) (needle : String) : Bool :=
  (shapeBreaks context).any (·.splitOn needle |>.length |> (· > 1))

/-- Removing a required or read-only key breaks the declared shape. -/
def testPopPolicy : IO Unit := do
  let (_, requiredContext) := run .pop [strLitV "name"] [] (some "name")
  ensure (hasShapeBreak requiredContext "name")
    "pop of a required TypedDict key raised no shape obligation"
  let (_, readOnlyContext) := run .pop [strLitV "id"] [] (some "id")
  ensure (hasShapeBreak readOnlyContext "id")
    "pop of a read-only TypedDict key raised no shape obligation"
  let (optional, optionalContext) := run .pop [strLitV "note"] [] (some "note")
  ensure (shapeBreaks optionalContext).isEmpty
    "pop of a writable optional key must not break the shape"
  let some (_, output) := optional.normal
    | throw (IO.userError "pop of an optional key lost its normal completion")
  ensure (Tag.tmissing ∈ (output.heapGet location (.literalKey "note")).tags)
    "pop of an optional key did not record its possible absence"
  ensure (Tag.tstr ∈ (output.heapGet location (.literalKey "name")).tags)
    "pop of one key disturbed another field"

/-- A dynamic key cannot be shown to select a removable field. -/
def testDynamicKeyPolicy : IO Unit := do
  let (_, context) := run .pop [V [.tstr]] []
  ensure (!(shapeBreaks context).isEmpty)
    "a dynamic TypedDict pop key raised no shape obligation"

/-- `setdefault` writes only when the key may be absent, so only then can it
    violate read-only. -/
def testSetdefaultPolicy : IO Unit := do
  let (_, presentContext) := run .setdefault [strLitV "id", V [.tint]] [] (some "id")
  ensure (shapeBreaks presentContext).isEmpty
    "setdefault on a present key performs no write and breaks no shape"
  let (_, absentContext) := run .setdefault [strLitV "tag", V [.tstr]] [] (some "tag")
  ensure (hasShapeBreak absentContext "tag")
    "setdefault that may insert a read-only key raised no shape obligation"
  let (_, optionalContext) := run .setdefault [strLitV "note", V [.tstr]] [] (some "note")
  ensure (shapeBreaks optionalContext).isEmpty
    "setdefault on a writable optional key must not break the shape"

/-- Clearing a shape that has required keys cannot be admitted silently. -/
def testClearPolicy : IO Unit := do
  let (_, context) := run .clear [] []
  ensure (!(shapeBreaks context).isEmpty)
    "clear of a TypedDict with required keys raised no shape obligation"

/-- A keyword update must respect declared keys and mutability. -/
def testUpdatePolicy : IO Unit := do
  let (_, readOnlyContext) := run .update [] [("id", V [.tint])]
  ensure (hasShapeBreak readOnlyContext "id")
    "keyword update of a read-only key raised no shape obligation"
  let (writable, writableContext) := run .update [] [("note", V [.tstr])]
  ensure (shapeBreaks writableContext).isEmpty
    "keyword update of a writable key must not break the shape"
  let some (_, output) := writable.normal
    | throw (IO.userError "keyword update lost its normal completion")
  ensure (Tag.tstr ∈ (output.heapGet location (.literalKey "note")).tags)
    "keyword update did not store the value"

def runAll : IO Unit := do
  testPopPolicy
  testDynamicKeyPolicy
  testSetdefaultPolicy
  testClearPolicy
  testUpdatePolicy
  IO.println "RuleTypedDictPolicy tests passed"

end Pylate.Tests.TypedDictPolicy
