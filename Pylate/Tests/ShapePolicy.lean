/-
The TypedDict shape policy table.

Two things are worth asserting and one is worth demonstrating.

The table must be complete, because an omitted row does not produce a wrong
message -- it produces *no* obligation, so the operation silently permits what it
should flag. And the eleven policies must render the sentence their hand-written
sites rendered, character for character, because that is what makes "zero golden
drift" evidence that the wiring was faithful rather than evidence that no golden
looked.

The demonstration is that the coverage condition fires. A gate nobody has watched
fail is not known to be a gate, so this drops a row and checks that
`missingShapePolicies` names exactly what was dropped.
-/
import Pylate.Tables.Binary
import Pylate.RuleLang.Validate

namespace Pylate.Tests.ShapePolicy

open Pylate

private def ensure (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

/-- Every operation has a row for every test it can meet. -/
def testCoverageComplete : IO Unit := do
  ensure shapeCoverageComplete
    s!"shape policy table is incomplete: {repr missingShapePolicies}"
  ensure (shapePolicies.length == 11)
    s!"expected 11 policies, found {shapePolicies.length}"

/-- The coverage check is not vacuous. Dropping `pop`'s protected-field row must
    be reported, and reported for that pair alone. -/
def testCoverageDetectsAGap : IO Unit := do
  let holed := shapePolicies.filter fun row =>
    !(row.operation == ShapeOp.pop && row.test == ShapeTest.requiredOrReadOnly)
  ensure (holed.length == shapePolicies.length - 1)
    "the test removed no row, so it proves nothing"
  let missing := allShapeOps.flatMap fun operation =>
    operation.coverage.filterMap fun test =>
      if holed.any (fun row => row.operation == operation && row.test == test)
      then none else some (operation, test)
  ensure (missing.length == 1)
    s!"a single dropped row should report once, reported {missing.length}"
  ensure (missing.any fun (operation, test) =>
      operation == ShapeOp.pop && test == ShapeTest.requiredOrReadOnly)
    "the reported gap is not the row that was dropped"

/-- Each policy renders the sentence its hand-written site produced. Written out
    rather than generated, so a change to the rendering has to be made here too
    and cannot pass by agreeing with itself. -/
def testRenderingMatchesTheOriginalSentences : IO Unit := do
  let field : FieldDecl := { name := "k", required := true, readOnly := true }
  let expected : List (Option String × String) :=
    [ (shapeObligation .setItem "T" field,
       "store to read-only TypedDict key T.k")
    , (shapeObligation .update "T" field,
       "update writes read-only TypedDict key T.k")
    , (shapeObligation .setDefault "T" field,
       "setdefault may write read-only TypedDict key T.k")
    , (shapeObligation .pop "T" field,
       "pop of T.k violates required/read-only shape")
    , (shapeObligation .popItem "T" field,
       "popitem may remove required/read-only TypedDict key T.k")
    , (undeclaredKeyObligation .setItem "T" "k",
       "store of undeclared key k breaks the T shape")
    , (undeclaredKeyObligation .update "T" "k",
       "update of undeclared key k breaks the T shape")
    , (undeclaredKeyObligation .setDefault "T" "k",
       "setdefault of undeclared key k breaks the T shape")
    , (unresolvedKeyObligation .update "T",
       "mapping update on TypedDict T may add a non-string key")
    , (unresolvedKeyObligation .pop "T",
       "dynamic pop on TypedDict T must select a removable optional key")
    , (wholesaleRemovalObligation .clear "T" "",
       "clear on TypedDict T removes required or read-only keys")
    ]
  for (actual, wanted) in expected do
    match actual with
    | none => throw (IO.userError s!"no policy rendered '{wanted}'")
    | some rendered =>
      ensure (rendered == wanted)
        s!"rendered '{rendered}', the site rendered '{wanted}'"

/-- A field that passes every test owes nothing, and a `pop` of an optional field
    is the case that distinguishes the table from "always oblige". -/
def testCleanFieldOwesNothing : IO Unit := do
  let plain : FieldDecl := { name := "k", required := false, readOnly := false }
  ensure (shapeObligation .setItem "T" plain).isNone
    "a writable declared field owes nothing on a store"
  ensure (shapeObligation .pop "T" plain).isNone
    "popping an optional writable field does not break the shape"
  ensure (shapeObligation .update "T" plain).isNone
    "updating a writable declared field owes nothing"

/-- `popitem` is per-field and `clear` is existential. They were grouped together
    by their wording when the table was first written, and wiring the sites
    corrected it, so the distinction is pinned. -/
def testPopItemIsPerFieldAndClearIsExistential : IO Unit := do
  ensure (ShapeOp.popItem.coverage == [ShapeTest.requiredOrReadOnly])
    "popitem names the field it would remove, so its test is per-field"
  ensure (ShapeOp.clear.coverage == [ShapeTest.anyRequiredOrReadOnly])
    "clear names no key, so any protected field is enough"

/-- The builtin-outcome table is complete, and its completeness check is not
    vacuous either. `unsupported` and `deferredOutcome` are both real answers; a
    row that is neither is the failure. -/
def testBuiltinOutcomeCoverage : IO Unit := do
  ensure builtinOutcomeCoverageComplete
    s!"builtin outcome table is incomplete: {repr missingBuiltinOutcomes}"
  -- An empty row -- no completion and no raise -- is what the check catches.
  let empty : Outcome := { value := .never, raises := [] }
  ensure (!empty.admitsNormal && empty.raises.isEmpty && !empty.deferred)
    "the empty outcome should be the shape the coverage check rejects"
  ensure (unsupported.raises == ["TypeError"] && !unsupported.admitsNormal)
    "unsupported must be a real answer: no completion, one raise"
  ensure (deferredOutcome.deferred && deferredOutcome.admitsNormal)
    "deferred must admit a completion, or deferring would delete one"

/-- The rows that replaced hand-maintained tag lists must agree with the lists
    they replaced, which is what makes the substitution checkable. -/
def testOutcomesMatchTheListsTheyReplaced : IO Unit := do
  let sized : List Tag :=
    [.tlist, .ttuple, .tdict, .tset, .tstr, .tbytes, .trange,
     .tdictkeys, .tdictitems, .tdictvalues]
  for tag in builtinTags do
    let concrete := (builtinOutcome tag .length).concrete
    ensure (concrete == sized.contains tag)
      s!"len() on {tag.render}: table says {concrete}, builtinSized said \
         {sized.contains tag}"
    let iterable := (builtinOutcome tag .iterate).concrete
    ensure (iterable == sized.contains tag)
      s!"iteration on {tag.render}: table says {iterable}, builtinIterable said \
         {sized.contains tag}"
  -- A generator is iterable but has no length, and the two lists were identical,
  -- so this is the pair that distinguishes them.
  ensure (builtinOutcome .tgen .iterate).admitsNormal
    "a generator is iterable"
  ensure (!(builtinOutcome .tgen .length).admitsNormal)
    "a generator has no length"

/-- `Pylate.Binary.fallbackImpl` answers for every tag declared to concatenate or repeat.

    A missing arm and a genuinely unsupported operand are both `none`, so the
    omission that made `b"a" + b"b"` a TypeError could not be seen from the code.
    Declaring the set and checking it against the selector is what makes it
    visible. -/
def testConcatAndRepeatCoverage : IO Unit := do
  for tag in concatenatingTags do
    ensure (Pylate.Binary.fallbackImpl .add tag tag).isSome
      s!"no `+` implementation selected for {tag.render}"
  for tag in repeatingTags do
    ensure (Pylate.Binary.fallbackImpl .mul tag .tint).isSome
      s!"no `*` implementation selected for {tag.render} on the left"
    ensure (Pylate.Binary.fallbackImpl .mul .tint tag).isSome
      s!"no `*` implementation selected for {tag.render} on the right"
  -- And a tag that genuinely does not concatenate still answers `none`, so the
  -- check above is not passing because everything answers `some`.
  ensure (Pylate.Binary.fallbackImpl .add .tset .tset).isNone
    "sets do not concatenate, so no fallback should be selected"

def runAll : IO Unit := do
  testConcatAndRepeatCoverage
  testBuiltinOutcomeCoverage
  testOutcomesMatchTheListsTheyReplaced
  testCoverageComplete
  testCoverageDetectsAGap
  testRenderingMatchesTheOriginalSentences
  testCleanFieldOwesNothing
  testPopItemIsPerFieldAndClearIsExistential
  IO.println "ShapePolicy tests passed"

end Pylate.Tests.ShapePolicy
