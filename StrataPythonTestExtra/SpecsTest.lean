/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Specs
meta import all StrataPython.Specs.DDM
meta import StrataPython.PythonDialect
meta import StrataPythonTest.Util.Python

open StrataDDM (SourceRange)
open StrataPython
open StrataPython.Specs

meta section
def testDir : System.FilePath := "StrataPythonTestExtra/Specs"

def expectedPySpec :=
#strata
program PythonSpecs;
extern "BaseClass" from "basetypes.BaseClass";
function "dict_function" {
  args: [
    x : ident("typing.Dict", ident("builtins.int"), ident("typing.Any")) [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "list_function" {
  args: [
    x : ident("typing.List", ident("builtins.int")) [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "sequence_function" {
  args: [
    x : ident("typing.Sequence", ident("builtins.int")) [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "base_function"{
  args: [
    x : ident("basetypes.BaseClass") [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
class "MainClass" {
  bases: []
  fields: []
  classVars: []
  subclasses: []
  exhaustive: false
  function "main_method"{
    args: [
      self : ident("main.MainClass") [default: ]
      x : ident("basetypes.BaseClass") [default: ]
    ]
    kwonly: [
    ]
    return: ident("typing.Any")
    overload: false
    preconditions: [
    ]
    postconditions: [
    ]
  }
}
function "main_function"{
  args: [
    x : ident("main.MainClass") [default: ]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
  preconditions: [
  ]
  postconditions: [
  ]
}
function "kwargs_function"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: kw : ident("builtins.int")
  return: ident("typing.Any")
  overload: false
  preconditions: [
    ensure(isinstance(kw[name], "str"), "Expected name to be str")
    ensure(kw[count] >=_int 1, "Expected count >= 1")
  ]
  postconditions: [
  ]
}
type "TestRequest" = dict(
  Name : ident("builtins.str") [required=true]
  Items : ident("typing.List", ident("builtins.str")) [required=false]
  Tags : ident("typing.Mapping", ident("builtins.str"), ident("builtins.str")) [required=false]
)
function "fstring_and_regex"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: params : dict(
    Name : ident("builtins.str") [required=true]
    Items : ident("typing.List", ident("builtins.str")) [required=false]
    Tags : ident("typing.Mapping", ident("builtins.str"), ident("builtins.str")) [required=false]
  )
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(stringLen(params[Name]) >=_int 1, "Expected len(params[\"Name\"]) >= 1, got "{stringLen(params[Name])})
    ensure(stringLen(params[Name]) <=_int 100, "Expected len(params[\"Name\"]) <= 100, got "{stringLen(params[Name])})
    ensure(regex(params[Name], "^[a-zA-Z]+$"), "params[\"Name\"] did not match pattern")
    ensure(Items in params => forall(params[Items], item, stringLen(item) >=_int 1), "Expected len(item) >= 1, got "{stringLen(item)})
    ensure(Items in params => forall(params[Items], item, stringLen(item) <=_int 50), "Expected len(item) <= 50, got "{stringLen(item)})
    ensure(Tags in params => forallDict(params[Tags], tag_key, tag_val, stringLen(tag_key) >=_int 1), "Expected len(tag_key) >= 1, got "{stringLen(tag_key)})
  ]
  postconditions: [
  ]
}
type "FloatRequest" = dict(
  SampleSize : ident("builtins.float") [required=false]
  Score : ident("builtins.float") [required=false]
  Count : ident("builtins.int") [required=false]
)
function "float_and_negative_bounds"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: fp : dict(
    SampleSize : ident("builtins.float") [required=false]
    Score : ident("builtins.float") [required=false]
    Count : ident("builtins.int") [required=false]
  )
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(Score in fp => fp[Score] >=_float "0.0", "Expected Score >= 0.0")
    ensure(Score in fp => fp[Score] <=_float "1.0", "Expected Score <= 1.0")
    ensure(not(Score in fp) => fp[SampleSize] >=_float "0", "Expected SampleSize >= 0 when no Score")
    ensure(SampleSize in fp => fp[SampleSize] >=_float "0", "Expected SampleSize >= 0")
    ensure(Score in fp => fp[Score] >=_float "-0.5", "Expected Score >= -0.5")
    ensure(Count in fp => fp[Count] >=_int -1, "Expected Count >= -1")
  ]
  postconditions: [
  ]
}
class "InnerHelper" {
  bases: []
  fields: []
  classVars: []
  subclasses: []
  exhaustive: false
}
class "ClassWithInit" {
  bases: []
  fields: [
    helper : ident("main._InnerHelper") "_InnerHelper()"
  ]
  classVars: []
  subclasses: [
    class "_InnerHelper" {
      bases: ["main.InnerHelper"]
      fields: []
      classVars: []
      subclasses: []
      exhaustive: false
      function "do_work"{
        args: [
          self : ident("main._InnerHelper") [default: ]
        ]
        kwonly: [
        ]
        return: ident("_types.NoneType")
        overload: false
        preconditions: [
        ]
        postconditions: [
        ]
      }
    }
  ]
  exhaustive: false
}
#end

meta def testCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "main.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "main"))
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let pgm := toDDMProgram sigs
        let pgmCommands := pgm.commands.map (·.mapAnn (fun _ => ()))
        let expCommands := expectedPySpec.commands.map (·.mapAnn (fun _ => ()))
        if pgmCommands != expCommands then
          -- Find first differing command index
          let mut diffMsg := s!"actual has {pgmCommands.size} commands, expected {expCommands.size}"
          for i in [:pgmCommands.size.max expCommands.size] do
            let actual := pgmCommands[i]?
            let expected := expCommands[i]?
            if actual != expected then
              diffMsg := s!"Command {i} differs."
              break
          throw <| IO.userError s!"PySpec output mismatch. {diffMsg}"
        -- from re import compile resolves via prelude without warnings
        if !warnings.isEmpty then
          let warnStr := warnings.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
          throw <| IO.userError s!"Unexpected warnings:{warnStr}"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval testCase

/-- Translate a `native_cases/<stem>.py` fixture, returning its signatures and
    warnings. `check` receives them on success; a translation error is rethrown. -/
meta def runNativeCase (stem : String)
    (check : Array Signature → Array String → IO Unit) : IO Unit :=
  withPython fun pythonCmd => do
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
      IO.FS.withTempDir fun strataDir => do
        let r ←
          translateFile
            (pythonCmd := toString pythonCmd)
            (dialectFile := dialectFile)
            (strataDir := strataDir)
            (pythonFile := testDir / "native_cases" / (stem ++ ".py"))
            (searchPath := testDir)
            (StrataPython.ModuleName.ofString! ("native_cases." ++ stem))
            |>.toBaseIO
        match r with
        | .ok (sigs, warnings) => check sigs warnings
        | .error e => throw <| IO.userError e

/-- Like `runNativeCase` but expects a translation error whose message contains
    `needle` (empty `needle` accepts any error). -/
meta def expectNativeCaseError (stem : String) (needle : String) : IO Unit :=
  withPython fun pythonCmd => do
    IO.FS.withTempFile fun _handle dialectFile => do
      IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
      IO.FS.withTempDir fun strataDir => do
        let r ←
          translateFile
            (pythonCmd := toString pythonCmd)
            (dialectFile := dialectFile)
            (strataDir := strataDir)
            (pythonFile := testDir / "native_cases" / (stem ++ ".py"))
            (searchPath := testDir)
            (StrataPython.ModuleName.ofString! ("native_cases." ++ stem))
            |>.toBaseIO
        match r with
        | .ok _ => throw <| IO.userError s!"{stem}: expected a hard error, but translation succeeded"
        | .error e =>
          unless e.contains needle do
            throw <| IO.userError s!"{stem}: expected error containing \"{needle}\", got: {e}"

meta def findFn (sigs : Array Signature) (name : String) : IO Specs.FunctionDecl := do
  let some d := sigs.findSome?
      (fun | .functionDecl d => if d.name == name then some d else none | _ => none)
    | throw <| IO.userError s!"function `{name}` not found"
  return d

meta def findClass (sigs : Array Signature) (name : String) : IO Specs.ClassDef := do
  let some d := sigs.findSome?
      (fun | .classDef d => if d.name == name then some d else none | _ => none)
    | throw <| IO.userError s!"class `{name}` not found"
  return d

meta def findMethod (c : Specs.ClassDef) (name : String) : IO Specs.FunctionDecl := do
  let some d := c.methods.findSome? (fun d => if d.name == name then some d else none)
    | throw <| IO.userError s!"method `{name}` not found"
  return d

meta def expect (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

-- Native `@requires(lambda …: pred)` populates `FunctionDecl.preconditions`, with the
-- predicate content preserved (`x >= 0`, not a placeholder).
#guard_msgs in
#eval runNativeCase "requires_basic" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 1) s!"expected 1 precondition, got {f.preconditions.size}"
  expect (f.preconditions[0]!.formula.softBEq (.intGe (.var "x" .none) (.intLit 0 .none) .none))
    "precondition formula did not match `x >= 0`"

-- Native `@ensures(lambda result: pred)` populates `FunctionDecl.postconditions`.
#guard_msgs in
#eval runNativeCase "ensures_basic" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.postconditions.size == 1) s!"expected 1 postcondition, got {f.postconditions.size}"
  expect (f.postconditions[0]!.softBEq (.intGe (.var "result" .none) (.intLit 0 .none) .none))
    "postcondition formula did not match `result >= 0`"

-- Native `@modifies(lambda …: target)` populates `FunctionDecl.modifies`.
#guard_msgs in
#eval runNativeCase "modifies_basic" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.modifies.size == 1) s!"expected 1 modifies target, got {f.modifies.size}"
  expect (f.modifies[0]!.softBEq (.var "x" .none)) "modifies target did not match `x`"

-- Native `@snapshot(lambda …: capture, name="v0")` populates `FunctionDecl.snapshots`.
#guard_msgs in
#eval runNativeCase "snapshot_basic" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.snapshots.size == 1) s!"expected 1 snapshot, got {f.snapshots.size}"
  expect (f.snapshots[0]!.name == "v0") s!"expected snapshot name `v0`, got {f.snapshots[0]!.name}"
  expect (f.snapshots[0]!.capture.softBEq (.var "x" .none)) "snapshot capture did not match `x`"

-- Native `@ghost(name="g")` populates `FunctionDecl.ghosts`; name-only carries no
-- type/init.
#guard_msgs in
#eval runNativeCase "ghost_basic" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.ghosts.size == 1) s!"expected 1 ghost, got {f.ghosts.size}"
  expect (f.ghosts[0]!.name == "g") s!"expected ghost name `g`, got {f.ghosts[0]!.name}"
  expect (f.ghosts[0]!.type.isNone && f.ghosts[0]!.init.isNone) "ghost `g` should have no type= or init="

-- Native `@ghost(name="g", type=int, init=0)` captures the declared type and initializer.
#guard_msgs in
#eval runNativeCase "ghost_typed" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.ghosts.size == 1) s!"expected 1 ghost, got {f.ghosts.size}"
  expect (f.ghosts[0]!.name == "g") s!"expected ghost name `g`, got {f.ghosts[0]!.name}"
  expect f.ghosts[0]!.type.isSome "expected ghost `g` to carry a declared type= (int)"
  let some ginit := f.ghosts[0]!.init
    | throw <| IO.userError "expected ghost `g` to carry an init= expression"
  expect (ginit.softBEq (.intLit 0 .none)) "ghost init= did not match `0`"

-- Native `@invariant(lambda self: pred)` populates `ClassDef.invariants` with the real
-- translated predicate (`self.x >= 0` ⇒ getIndex), not a placeholder.
#guard_msgs in
#eval runNativeCase "invariant_basic" fun sigs _ => do
  let c ← findClass sigs "C"
  expect (c.invariants.size == 1) s!"expected 1 invariant, got {c.invariants.size}"
  let expected : SpecExpr :=
    .intGe (.getIndex (.var "self" .none) "x" .none) (.intLit 0 .none) .none
  expect (c.invariants[0]!.softBEq expected)
    "invariant was not translated to `self.x >= 0` (placeholder or mismatch)"

-- Multiple `@requires` on one function accumulate (order-independent).
#guard_msgs in
#eval runNativeCase "requires_multiple" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 2) s!"expected 2 preconditions, got {f.preconditions.size}"
  expect (f.preconditions.any (·.formula.softBEq (.intGe (.var "x" .none) (.intLit 0 .none) .none)))
    "missing precondition `x >= 0`"
  expect (f.preconditions.any (·.formula.softBEq (.intLe (.var "x" .none) (.intLit 100 .none) .none)))
    "missing precondition `x <= 100`"

-- An extra positional argument after the lambda is warned about, but the predicate is still
-- recognized.
#guard_msgs in
#eval runNativeCase "requires_extra_positional" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 1)
    s!"expected the predicate to still be recognized (1 precondition), got {f.preconditions.size}"
  expect (warnings.any (·.contains "extra positional")) "expected a warning about extra positional arguments"

-- A contract binder matching the function's `**kwargs` parameter is NOT flagged as unbound
-- (`functionParamNames` includes it), and `kw["a"]` translates.
#guard_msgs in
#eval runNativeCase "requires_kwargs" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 1) s!"expected 1 precondition, got {f.preconditions.size}"
  expect (!warnings.any (·.contains "unbound at the use site"))
    "the **kwargs binder was wrongly flagged as unbound"

-- `@modifies(lambda self: self.x)` on a method may reference `self.x` (field access is on
-- for the not-yet-lowered targets) — the mirror of the `@requires` case below, which may
-- not.
#guard_msgs in
#eval runNativeCase "modifies_self" fun sigs _ => do
  let m ← findMethod (← findClass sigs "C") "m"
  expect (m.modifies.size == 1) s!"expected 1 modifies target, got {m.modifies.size}"
  expect (m.modifies[0]!.softBEq (.getIndex (.var "self" .none) "x" .none))
    "modifies target did not match `self.x` (getIndex self x)"

-- `self.x` inside `@requires` (a lowered kind) is unsupported: the predicate is dropped
-- with a warning, not stored or hard-errored.
#guard_msgs in
#eval runNativeCase "requires_self_method" fun sigs warnings => do
  let m ← findMethod (← findClass sigs "C") "m"
  expect (m.preconditions.size == 0)
    s!"expected `self.x` @requires to be dropped (0 preconditions), got {m.preconditions.size}"
  expect (warnings.any (·.contains "unsupported expression"))
    "expected an unsupported-expression warning for `self.x` in @requires"

-- A buried placeholder (`len("foo") >= 1` ⇒ `intGe(stringLen(placeholder), 1)`) is dropped
-- by the deep `containsPlaceholder` check, with a diagnostic. A shallow top-level check
-- would wrongly store it.
#guard_msgs in
#eval runNativeCase "requires_buried_placeholder" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 0)
    s!"expected the buried-placeholder predicate to be dropped (0 preconditions), got {f.preconditions.size}"
  expect (warnings.any (·.contains "unsupported expression in contract"))
    "expected a diagnostic for the dropped buried-placeholder predicate"

-- A malformed `@requires` (argument is not a lambda) is a hard error.
#guard_msgs in
#eval expectNativeCaseError "requires_malformed" "expects a lambda"

-- A qualified `@icontract.requires` is declined by the native scheme and rejected
-- downstream: it falls through to `pySpecValue`, which fails to resolve the
-- qualified name `icontract.requires` (an unknown identifier), so the decorator
-- is neither absorbed as a precondition nor accepted.
#guard_msgs in
#eval expectNativeCaseError "icontract_decline" "Unknown identifier icontract.requires"

-- Duplicate `@ghost(name="g")` on one declaration is a hard error.
#guard_msgs in
#eval expectNativeCaseError "ghost_dup" "duplicate"

-- Duplicate `@snapshot` name= on one method is a hard error (a distinct error site from
-- `ghost_dup`).
#guard_msgs in
#eval expectNativeCaseError "snapshot_dup" "duplicate"

-- An `@ensures` lambda binder that is neither a parameter nor `result` is still
-- recognized as a postcondition, but warned as unbound at the use site.
#guard_msgs in
#eval runNativeCase "ensures_unbound" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect (f.postconditions.size == 1) s!"expected 1 postcondition, got {f.postconditions.size}"
  expect (warnings.any (·.contains "unbound at the use site"))
    "expected a warning that the `@ensures` binder is unbound at the use site"

-- An unexpected keyword on `@requires` (empty allow-list) is a hard error.
#guard_msgs in
#eval expectNativeCaseError "requires_unexpected_kw" "unexpected keyword"

-- A non-string `@ghost(name=…)` is a hard error.
#guard_msgs in
#eval expectNativeCaseError "ghost_nonstring_name" "must be a string literal"

-- `@ghost` without a name= keyword is a hard error.
#guard_msgs in
#eval expectNativeCaseError "ghost_missing_name" "requires a name="

-- `@ghost` with a positional argument is a hard error.
#guard_msgs in
#eval expectNativeCaseError "ghost_positional" "takes no positional arguments"

-- `@snapshot` without a name= keyword is a hard error.
#guard_msgs in
#eval expectNativeCaseError "snapshot_missing_name" "requires a name="

-- `@invariant(lambda s: …)` (binder not `self`) is warned and the invariant is
-- skipped (not recognized).
#guard_msgs in
#eval runNativeCase "invariant_wrong_binder" fun sigs warnings => do
  let c ← findClass sigs "C"
  expect (c.invariants.size == 0) s!"expected the invariant to be skipped (0 invariants), got {c.invariants.size}"
  expect (warnings.any (·.contains "must be 'self'"))
    "expected a warning that the `@invariant` binder must be `self`"

-- `@invariant(lambda self, y: …)` (two binders) is warned and the invariant is
-- skipped.
#guard_msgs in
#eval runNativeCase "invariant_two_binders" fun sigs warnings => do
  let c ← findClass sigs "C"
  expect (c.invariants.size == 0) s!"expected the invariant to be skipped (0 invariants), got {c.invariants.size}"
  expect (warnings.any (·.contains "exactly one"))
    "expected a warning that the `@invariant` lambda must take exactly one parameter"

-- Integration: all five native method decorators on one function each populate
-- their own field, with no cross-wiring between the per-kind stores.
#guard_msgs in
#eval runNativeCase "mixed_method" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 1) s!"expected 1 precondition, got {f.preconditions.size}"
  expect (f.postconditions.size == 1) s!"expected 1 postcondition, got {f.postconditions.size}"
  expect (f.modifies.size == 1) s!"expected 1 modifies target, got {f.modifies.size}"
  expect (f.snapshots.size == 1) s!"expected 1 snapshot, got {f.snapshots.size}"
  expect (f.ghosts.size == 1) s!"expected 1 ghost, got {f.ghosts.size}"
  expect (f.snapshots[0]!.name == "v0") s!"expected snapshot name `v0`, got {f.snapshots[0]!.name}"
  expect (f.ghosts[0]!.name == "g") s!"expected ghost name `g`, got {f.ghosts[0]!.name}"

-- A class-level `@invariant` and a method-level `@requires` are recognized
-- independently: both fields populate.
#guard_msgs in
#eval runNativeCase "class_invariant_with_method_contract" fun sigs _ => do
  let c ← findClass sigs "C"
  expect (c.invariants.size == 1) s!"expected 1 class invariant, got {c.invariants.size}"
  let m ← findMethod c "m"
  expect (m.preconditions.size == 1) s!"expected 1 method precondition, got {m.preconditions.size}"

/-- Test that unsupported patterns emit appropriate warnings. -/
def warningTestCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "warnings.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "warnings"))
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        -- Check that we still produced some output despite warnings
        if sigs.isEmpty then
          throw <| IO.userError "Expected signatures from warnings.py but got none"
        -- Check that we got warnings (not zero)
        if warnings.isEmpty then
          throw <| IO.userError "Expected warnings from warnings.py but got none"
        -- Check for specific expected warning substrings
        let expectedWarnings := #[
          "unsupported comparison",               -- assert kw["x"] == 1
          "unsupported __init__ assignment",   -- self.name = "hello"
          "skipped Assign in function body",   -- x = kw["a"]
          "For: else clause not supported",    -- for/else loop
          "skipped Expr in function body"      -- kw["a"] (bare expression)
        ]
        for expected in expectedWarnings do
          if !warnings.any (·.contains expected) then
            let warnStr := warnings.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
            throw <| IO.userError
              s!"Missing expected warning containing \"{expected}\". Actual warnings:{warnStr}"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval warningTestCase


meta def testNegRoundTrip (v : Nat) : Bool :=
  DDM.Int.ofDDM (.negInt SourceRange.none ⟨.none, v⟩) = Int.negOfNat v

#guard testNegRoundTrip 0
#guard testNegRoundTrip 1

def testIntRoundTrip (v : Int) : Bool :=
  DDM.Int.ofDDM (toDDMInt SourceRange.none v) = v

#guard testIntRoundTrip 0
#guard testIntRoundTrip 1
#guard testIntRoundTrip (-1)
#guard testIntRoundTrip (42)
#guard testIntRoundTrip (-100)

/-- DDM `toDDM` → `fromDDM` round-trip for the contract fields. The recognition
    tests above never cross the DDM boundary, so a regression that dropped a
    (de)serialization clause would leave them green; this exercises the boundary
    directly and asserts field counts and key contents survive. -/
meta def serdeRoundTripTest : IO Unit := do
  let fd : Specs.FunctionDecl := {
    loc := .none
    nameLoc := .none
    name := "f"
    args := { args := #[], kwonly := #[] }
    returnType := SpecType.noneType .none
    isOverload := false
    preconditions := #[{ message := #[], formula := .intGe (.var "x" .none) (.intLit 0 .none) .none }]
    postconditions := #[.intGe (.var "result" .none) (.intLit 0 .none) .none]
    snapshots := #[{ name := "v0", capture := .var "x" .none, loc := .none }]
    modifies := #[.var "self_x" .none]
    ghosts := #[{ name := "g", type := some (SpecType.ident .none .builtinsInt),
                  init := some (.intLit 7 .none), loc := .none }]
  }
  let fd' ← match DDM.FunDecl.fromDDM (FunctionDecl.toDDM fd) with
    | .ok r => pure r
    | .error (_, msg) => throw <| IO.userError s!"FunDecl.fromDDM failed: {msg}"
  expect (fd'.preconditions.size == 1) s!"round-trip dropped preconditions: got {fd'.preconditions.size}"
  expect (fd'.preconditions[0]!.formula.softBEq (.intGe (.var "x" .none) (.intLit 0 .none) .none))
    "round-trip corrupted precondition formula"
  expect (fd'.postconditions.size == 1) s!"round-trip dropped postconditions: got {fd'.postconditions.size}"
  expect (fd'.postconditions[0]!.softBEq (.intGe (.var "result" .none) (.intLit 0 .none) .none))
    "round-trip corrupted postcondition formula"
  expect (fd'.snapshots.size == 1) s!"round-trip dropped snapshots: got {fd'.snapshots.size}"
  expect (fd'.snapshots[0]!.name == "v0") "round-trip corrupted snapshot name"
  expect (fd'.snapshots[0]!.capture.softBEq (.var "x" .none)) "round-trip corrupted snapshot capture"
  expect (fd'.modifies.size == 1) s!"round-trip dropped modifies: got {fd'.modifies.size}"
  expect (fd'.modifies[0]!.softBEq (.var "self_x" .none)) "round-trip corrupted modifies target"
  expect (fd'.ghosts.size == 1) s!"round-trip dropped ghosts: got {fd'.ghosts.size}"
  expect (fd'.ghosts[0]!.name == "g") "round-trip corrupted ghost name"
  expect fd'.ghosts[0]!.type.isSome "round-trip dropped ghost type="
  let some ginit := fd'.ghosts[0]!.init
    | throw <| IO.userError "round-trip dropped ghost init="
  expect (ginit.softBEq (.intLit 7 .none)) "round-trip corrupted ghost init expression"
  let cd : Specs.ClassDef := {
    loc := .none
    name := "C"
    methods := #[fd]
    invariants := #[.var "inv" .none]
  }
  let cd' ← match DDM.ClassDecl.fromDDM (ClassDef.toDDMDecl cd) with
    | .ok r => pure r
    | .error (_, msg) => throw <| IO.userError s!"ClassDecl.fromDDM failed: {msg}"
  expect (cd'.invariants.size == 1) s!"round-trip dropped invariants: got {cd'.invariants.size}"
  expect (cd'.invariants[0]!.softBEq (.var "inv" .none)) "round-trip corrupted invariant expression"
  expect (cd'.methods.size == 1) s!"round-trip dropped class method: got {cd'.methods.size}"
  expect (cd'.methods[0]!.snapshots.size == 1
          && cd'.methods[0]!.modifies.size == 1
          && cd'.methods[0]!.ghosts.size == 1)
    "round-trip dropped a class method's snapshot/modifies/ghost fields"

#guard_msgs in
#eval serdeRoundTripTest
end
