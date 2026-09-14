/-
The TypedDict shape policy as one table.

Every mutating operation on a TypedDict asks the same question in a different
place: does what this does to this key break the declared shape, and if so what
is owed? That question was answered at 26 `oblige "shape-break"` sites across
four files, in eleven distinct policies each written twice -- once for the rule
transfers and once for the direct analyzer.

Duplication that no test distinguishes is how a divergence gets in, and one did:
`updateTypedDictField` exists three times and two copies dropped the heap write
for an undeclared key, so `row["bogus"] = 1` failed a later entailment check
while `row.update(bogus=1)` passed it in the same program. Both raised
`shape-break`, so the store was flagged either way; what diverged was the heap.

So the policy is data. A row is (operation, test, detail): which operation, what
must hold of the resolved field for the shape to break, and which sentence says
so. `coverage` states which tests each operation can encounter, and
`RuleValidate` fails a rule set whose table omits one -- an omitted row is a
policy that silently permits, which is the shape of the defect this replaces.
-/
import Pylate.Syntax.Nodes

namespace Pylate

/-- The mutating operations that can break a declared shape. Reads cannot: they
    may raise `KeyError`, which is a different obligation. -/
inductive ShapeOp
  | setItem
  | update
  | setDefault
  | pop
  | popItem
  | clear
deriving Repr, BEq, Inhabited

def ShapeOp.render : ShapeOp -> String
  | .setItem => "store"
  | .update => "update"
  | .setDefault => "setdefault"
  | .pop => "pop"
  | .popItem => "popitem"
  | .clear => "clear"

/-- How an operation refers to the value it writes, for the declared-type
    obligation. In the table because it is a wording decision, and because the
    three copies of the write differed in exactly this word and nothing else. -/
def ShapeOp.valueVerb : ShapeOp -> String
  | .setItem => "stored"
  | .update => "updated"
  | .setDefault => "inserted"
  | .pop | .popItem | .clear => "removed"

/-- The declared-type obligation for a value written to a declared field. This is
    not a shape break: the key is legal, the value is not. -/
def declaredTypeObligation (operation : ShapeOp) (typeName key : String) :
    String :=
  s!"{typeName}.{key}: {operation.valueVerb} value does not satisfy the declared type"

/-- What must hold for the operation to break the shape.

    These are stated over the *resolved* field, so a key that does not resolve --
    dynamic, or not a string -- is its own test rather than a missing field. That
    distinction is the one the hand-written sites got wrong most often: an
    unresolved key is not an undeclared key, and it owes a different proof. -/
inductive ShapeTest
  /-- Declared read-only: any write breaks it. -/
  | readOnly
  /-- Not in the declared field set: adding it changes the shape. -/
  | undeclared
  /-- Removing it breaks the shape, because it must be there or must not change. -/
  | requiredOrReadOnly
  /-- A whole-object removal, where any required or read-only field is enough. -/
  | anyRequiredOrReadOnly
  /-- The key is not a literal string, so no single field resolves and the
      operation must be shown to select a legal one. -/
  | unresolvedKey
deriving Repr, BEq, Inhabited

/-- Which sentence a row renders. Kept separate from the test because two
    operations can fail the same test and owe differently worded proofs, and
    because a function-valued field would stop the table being data. -/
inductive ShapeDetail
  | storesToReadOnly
  | writesReadOnly
  | mayWriteReadOnly
  | addsUndeclared
  | removesProtected
  | mayRemoveProtected
  | removesProtectedWholesale
  | mustSelectRemovable
  | mayAddNonStringKey
deriving Repr, BEq, Inhabited

structure ShapePolicy where
  operation : ShapeOp
  test      : ShapeTest
  detail    : ShapeDetail
deriving Repr, BEq, Inhabited

/-- The table. Eleven rows, one per distinct policy the hand-written sites
    implemented; the twelve remaining sites were the second copy of one of these. -/
def shapePolicies : List ShapePolicy :=
  [ ⟨.setItem, .readOnly, .storesToReadOnly⟩
  , ⟨.setItem, .undeclared, .addsUndeclared⟩
  , ⟨.update, .readOnly, .writesReadOnly⟩
  , ⟨.update, .undeclared, .addsUndeclared⟩
  , ⟨.update, .unresolvedKey, .mayAddNonStringKey⟩
  , ⟨.setDefault, .readOnly, .mayWriteReadOnly⟩
  , ⟨.setDefault, .undeclared, .addsUndeclared⟩
  , ⟨.pop, .requiredOrReadOnly, .removesProtected⟩
  , ⟨.pop, .unresolvedKey, .mustSelectRemovable⟩
  , ⟨.popItem, .requiredOrReadOnly, .mayRemoveProtected⟩
  , ⟨.clear, .anyRequiredOrReadOnly, .removesProtectedWholesale⟩
  ]

/-- Which tests each operation can encounter, so an omitted row is detectable.

    A write can meet a read-only field, an undeclared key, or a key that does not
    resolve. A removal that names a field -- including `popitem`, which loops the
    declared fields and names the one it would remove -- meets the per-field
    test. `clear` is the only genuinely existential one: it names no key, so any
    protected field is enough. Wiring the sites is what corrected `popitem` here;
    it had been grouped with `clear` by its wording rather than by its guard. -/
def ShapeOp.coverage : ShapeOp -> List ShapeTest
  | .setItem => [.readOnly, .undeclared]
  | .update => [.readOnly, .undeclared, .unresolvedKey]
  | .setDefault => [.readOnly, .undeclared]
  | .pop => [.requiredOrReadOnly, .unresolvedKey]
  | .popItem => [.requiredOrReadOnly]
  | .clear => [.anyRequiredOrReadOnly]

def allShapeOps : List ShapeOp :=
  [.setItem, .update, .setDefault, .pop, .popItem, .clear]

/-- The rows an operation is missing. Empty for a complete table; `RuleValidate`
    turns a non-empty result into a blocking finding. -/
def missingShapePolicies : List (ShapeOp × ShapeTest) :=
  allShapeOps.flatMap fun operation =>
    operation.coverage.filterMap fun test =>
      if shapePolicies.any (fun row => row.operation == operation &&
          row.test == test)
      then none else some (operation, test)

/-- `setItem` does not name a policy for `unresolvedKey` on purpose: a dynamic
    subscript store is handled by the key-membership obligation, which is about
    which key is written rather than about the shape. Recorded here so the
    absence is a decision and not an omission. -/
def shapeCoverageComplete : Bool := missingShapePolicies.isEmpty

def ShapeDetail.render (detail : ShapeDetail) (operation : ShapeOp)
    (typeName key : String) : String :=
  -- Three operations word a read-only write three ways, so that is three details
  -- rather than one shared arm. Unifying the wording is a separate decision; the
  -- goldens pin the current sentences to the character.
  match detail with
  | .storesToReadOnly =>
    s!"store to read-only TypedDict key {typeName}.{key}"
  | .writesReadOnly =>
    s!"{operation.render} writes read-only TypedDict key {typeName}.{key}"
  | .mayWriteReadOnly =>
    s!"{operation.render} may write read-only TypedDict key {typeName}.{key}"
  | .addsUndeclared =>
    s!"{operation.render} of undeclared key {key} breaks the {typeName} shape"
  | .removesProtected =>
    s!"{operation.render} of {typeName}.{key} violates required/read-only shape"
  | .mayRemoveProtected =>
    s!"{operation.render} may remove required/read-only TypedDict key {typeName}.{key}"
  | .removesProtectedWholesale =>
    s!"{operation.render} on TypedDict {typeName} removes required or read-only keys"
  | .mustSelectRemovable =>
    s!"dynamic {operation.render} on TypedDict {typeName} must select a removable optional key"
  | .mayAddNonStringKey =>
    s!"mapping {operation.render} on TypedDict {typeName} may add a non-string key"

/-- Whether a resolved field fails a test. `unresolvedKey` and
    `anyRequiredOrReadOnly` are not about one field, so they are decided by the
    caller and answer `false` here rather than being silently true.

    The table answers questions about the *declared field*. Heap facts stay at
    the call site: `setdefault` owes its obligation only when the cell may be
    absent, and a mapping update only when the source keys may be non-string.
    Those are properties of this object at this moment, not of the declaration,
    and folding them in would make the table depend on the state. -/
def ShapeTest.holdsFor (test : ShapeTest) (field : FieldDecl) : Bool :=
  match test with
  | .readOnly => field.readOnly
  | .undeclared => false
  | .requiredOrReadOnly => field.required || field.readOnly
  | .anyRequiredOrReadOnly => false
  | .unresolvedKey => false

/-- The obligation an operation owes for a resolved field, if any.

    One lookup replaces the open-coded predicate at each site, so the eleven
    policies have one definition and a new operation cannot quietly inherit
    silence by forgetting an `if`. -/
def shapeObligation (operation : ShapeOp) (typeName : String)
    (field : FieldDecl) : Option String :=
  (shapePolicies.find? fun row =>
      row.operation == operation && row.test.holdsFor field).map fun row =>
    row.detail.render row.operation typeName field.name

/-- The obligation for a key that resolves to no declared field. -/
def undeclaredKeyObligation (operation : ShapeOp) (typeName key : String) :
    Option String :=
  (shapePolicies.find? fun row =>
      row.operation == operation && row.test == .undeclared).map fun row =>
    row.detail.render row.operation typeName key

/-- The obligation for a key that is not a literal string. -/
def unresolvedKeyObligation (operation : ShapeOp) (typeName : String) :
    Option String :=
  (shapePolicies.find? fun row =>
      row.operation == operation && row.test == .unresolvedKey).map fun row =>
    row.detail.render row.operation typeName ""

/-- The obligation for a removal that names no key. -/
def wholesaleRemovalObligation (operation : ShapeOp) (typeName key : String) :
    Option String :=
  (shapePolicies.find? fun row =>
      row.operation == operation && row.test == .anyRequiredOrReadOnly).map
    fun row => row.detail.render row.operation typeName key

end Pylate
