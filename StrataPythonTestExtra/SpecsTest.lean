/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import all StrataPython.Specs
meta import all StrataPython.Specs.DDM
meta import StrataPython.Specs.ToLaurel
meta import StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator
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
  function "__init__"{
    args: [
      self : ident("main.ClassWithInit") [default: ]
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

/-- Like `runNativeCase` but expects a translation error, and returns its message; `none` when
    `withPython` skips the Python tests. -/
meta def nativeCaseError (stem : String) : IO (Option String) := do
  let msg ← IO.mkRef none
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
        | .error e => msg.set (some e)
  msg.get

/-- Expect a translation error whose message contains `needle` (empty `needle` accepts any
    error). -/
meta def expectNativeCaseError (stem : String) (needle : String) : IO Unit := do
  let some e ← nativeCaseError stem | return
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

-- Native `@admit(lambda result: pred)` populates
-- `FunctionDecl.admittedPostconditions`, not `postconditions`.
#guard_msgs in
#eval runNativeCase "admit_basic" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
      (.intGe (.var "result" .none) (.intLit 0 .none) .none))
    "admitted postcondition formula did not match `result >= 0`"
  expect f.postconditions.isEmpty
    "@admit must not populate the verified `postconditions` store"

-- `@ensures` and `@admit` on one function populate their own stores with no
-- cross-wiring.
#guard_msgs in
#eval runNativeCase "admit_with_ensures" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.postconditions.size == 1)
    s!"expected 1 postcondition, got {f.postconditions.size}"
  expect (f.postconditions[0]!.softBEq (.intGe (.var "result" .none) (.intLit 0 .none) .none))
    "postcondition formula did not match `result >= 0`"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
      (.intLe (.var "result" .none) (.intLit 100 .none) .none))
    "admitted postcondition formula did not match `result <= 100`"

-- A dynamic-key dict comparison is admitted through the numeric fallback
-- rather than dropped (`isFieldRead` covers `getItem`).
#guard_msgs in
#eval runNativeCase "admit_dict_dynamic_ge" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect warnings.isEmpty s!"unexpected warnings: {warnings}"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
      (.pcmp .ge
        (.getItem (.var "d1" .none) (.var "k1" .none) .none)
        (.getItem (.var "d2" .none) (.var "k2" .none) .none)
        .none))
    "admitted postcondition did not match `d1[k1] >= d2[k2]`"

-- A constant-key subscript on a non-str-keyed dict is dropped with the same
-- message as the dynamic-key branch, not mistranslated as a string lookup.
#guard_msgs in
#eval runNativeCase "admit_int_dict_const_subscript" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect f.admittedPostconditions.isEmpty
    s!"expected the int-keyed subscript contract to be dropped, got {f.admittedPostconditions.size}"
  expect (warnings.any (·.contains "subscript subject is not a string-keyed Dict/Mapping/TypedDict"))
    s!"expected the non-string-keyed dict warning, got: {warnings}"

-- Native `@modifies(lambda …: target)` populates `FunctionDecl.modifies`.
#guard_msgs in
#eval runNativeCase "modifies_basic" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.modifies.size == 1) s!"expected 1 modifies target, got {f.modifies.size}"
  expect (f.modifies[0]!.softBEq (.var "x" .none)) "modifies target did not match `x`"

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

-- Field-to-field ordering uses generic comparisons in every role that permits
-- field access, including class invariants.
#guard_msgs in
#eval runNativeCase "invariant_field_order" fun sigs warnings => do
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  let ge ← findClass sigs "CGe"
  let le ← findClass sigs "CLe"
  expect (ge.invariants.size == 1) s!"expected 1 >= invariant, got {ge.invariants.size}"
  expect (le.invariants.size == 1) s!"expected 1 <= invariant, got {le.invariants.size}"
  expect (ge.invariants[0]!.softBEq
            (.pcmp .ge
              (.getIndex (.var "self" .none) "a" .none)
              (.getIndex (.var "self" .none) "b" .none)
              .none))
    "field-to-field >= invariant was not preserved"
  expect (le.invariants[0]!.softBEq
            (.pcmp .le
              (.getIndex (.var "self" .none) "a" .none)
              (.getIndex (.var "self" .none) "b" .none)
              .none))
    "field-to-field <= invariant was not preserved"

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

-- `len` of a `str` is `stringLen`; `len` of a list or of an `Any` is the generic `len`.
#guard_msgs in
#eval runNativeCase "len_by_type" fun sigs warnings => do
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 3) s!"expected 3 preconditions, got {f.preconditions.size}"
  expect (f.preconditions[0]!.formula.softBEq
      (.intGe (.len (.var "xs" .none) .none) (.intLit 1 .none) .none))
    s!"`len(xs) >= 1` on a list: got {f.preconditions[0]!.formula}"
  expect (f.preconditions[1]!.formula.softBEq
      (.intGe (.stringLen (.var "s" .none) .none) (.intLit 1 .none) .none))
    s!"`len(s) >= 1` on a str: got {f.preconditions[1]!.formula}"
  expect (f.preconditions[2]!.formula.softBEq
      (.intLe (.len (.var "a" .none) .none) (.intLit 3 .none) .none))
    s!"`len(a) <= 3` on an Any: got {f.preconditions[2]!.formula}"

-- `"@" in email` on a `str` is `containsKey`, whose meaning is CPython's `in` for any
-- container.
#guard_msgs in
#eval runNativeCase "in_any_container" fun sigs warnings => do
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 1) s!"expected 1 precondition, got {f.preconditions.size}"
  expect (f.preconditions[0]!.formula.softBEq (.containsKey (.var "email" .none) "@" .none))
    s!"`\"@\" in email`: got {f.preconditions[0]!.formula}"

-- Signatures that PySpec does not support are errors that reject the model.

#guard_msgs in
#eval expectNativeCaseError "varargs_param" "f: *args is not supported"

#guard_msgs in
#eval expectNativeCaseError "method_type_params" "get: type parameters are not supported"

-- `Optional[T]` reads as `Union[T, None]`, also as `typing.Optional[T]`, and `typing.X[...]`
-- reads as `X[...]`.
#guard_msgs in
#eval runNativeCase "optional_types" fun sigs warnings => do
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  let f ← findFn sigs "f"
  let tps := f.args.args.map (·.type)
  expect (tps.size == 4 && tps[0]! == tps[2]! && tps[1]! == tps[3]! && f.returnType == tps[0]!)
    s!"types: {tps.map toString}, returns {f.returnType}"
  expect (toString tps[0]! != toString tps[1]!) s!"types: {tps.map toString}"
  expect (toString tps[0]! == "Union[_types.NoneType, builtins.str]") s!"Optional[str]: {tps[0]!}"
  let g ← findFn sigs "g"
  expect ((g.args.args.map (toString ·.type)) == #["typing.List[builtins.str]", "typing.Dict[builtins.str, builtins.int]"])
    s!"g: {g.args.args.map (toString ·.type)}"

-- `Optional` with two arguments is an error, as in CPython.
#guard_msgs in
#eval expectNativeCaseError "optional_two_args" "Optional expects one argument."

-- After `import typing as t`, `t.Optional[int]` reads as `Optional[int]`.
#guard_msgs in
#eval runNativeCase "typing_alias_prefix" fun sigs warnings => do
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  let f ← findFn sigs "f"
  let tps := f.args.args.map (·.type)
  expect (tps.size == 2 && tps[0]! == tps[1]!) s!"types: {tps.map toString}"

-- A model that binds a typing name a second time, in the module or in a class body, is
-- rejected: PySpec would read the name as the typing import, and CPython as the other binding.
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_module" "'typing' has another binding than its typing import"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_class" "'typing' has another binding than its typing import"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_name" "'List' has another binding than its typing import"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_class_body" "'List' is bound in a class body"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_walrus" "'List' has another binding than its typing import"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_annassign" "'List' has another binding than its typing import"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_target" "'List' has another binding than its typing import"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_one_import" "'List' has another binding than its typing import"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_nested_class" "'Dict' is bound in a class body"
#guard_msgs in
#eval expectNativeCaseError "rebind_typing_alias_import" "'t' has another binding than its typing import"

-- A subscript through a module name that `import typing` didn't bind is an error.
#guard_msgs in
#eval expectNativeCaseError "prefix_other_module" "Could not interpret"

-- A pin of a result that is wrong today: after `m = 0`, PySpec still reads `m.ServiceClass`
-- through the import. The typing check covers typing names only.
#guard_msgs in
#eval runNativeCase "rebound_module_attr" fun sigs _ => do
  let f ← findFn sigs "f"
  expect ((f.args.args.map (toString ·.type)) == #["import_test.service.module.ServiceClass"])
    s!"f: {f.args.args.map (toString ·.type)}"

-- The same typing import twice, and a field without a value, are not other bindings.
#guard_msgs in
#eval runNativeCase "typing_import_kept" fun sigs warnings => do
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  let m ← findMethod (← findClass sigs "C") "m"
  expect ((m.args.args.map (toString ·.type)) == #["native_cases.typing_import_kept.C", "typing.List[builtins.int]"])
    s!"m: {m.args.args.map (toString ·.type)}"

-- A pin of a result that is wrong today: a method named `dict` shadows the builtin in the
-- class body, but PySpec still reads `-> dict` as the builtin. The check above covers typing
-- names only.
#guard_msgs in
#eval runNativeCase "method_named_dict" fun sigs _ => do
  let m ← findMethod (← findClass sigs "C") "m"
  expect (toString m.returnType == "builtins.dict") s!"m returns {m.returnType}"

-- A `u` prefix changes nothing: `Literal[u"a"]` is `Literal["a"]`.
#guard_msgs in
#eval runNativeCase "literal_u_prefix" fun sigs warnings => do
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  let f ← findFn sigs "f"
  expect (f.args.args[0]!.type.asStringLiteral == some "a")
    s!"expected Literal[\"a\"], got {f.args.args[0]!.type}"

-- Duplicate `@ghost(name="g")` on one declaration is a hard error.
#guard_msgs in
#eval expectNativeCaseError "ghost_dup" "duplicate"

-- An `@ensures` lambda binder that is neither a parameter nor `result` is still
-- recognized as a postcondition, but warned as unbound at the use site.
#guard_msgs in
#eval runNativeCase "ensures_unbound" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect (f.postconditions.size == 1) s!"expected 1 postcondition, got {f.postconditions.size}"
  expect (warnings.any (·.contains "unbound at the use site"))
    "expected a warning that the `@ensures` binder is unbound at the use site"

-- An `@admit` lambda binder that is neither a parameter nor `result` is still
-- recognized as an admitted postcondition, but warned as unbound at the use site.
#guard_msgs in
#eval runNativeCase "admit_unbound" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (warnings.any (·.contains "@admit: lambda parameter 'q' is unbound at the use site"))
    "expected a warning that the `@admit` binder is unbound at the use site"

-- Malformed `@admit` (argument is not a lambda) is a hard error.
#guard_msgs in
#eval expectNativeCaseError "admit_malformed" "expects a lambda"

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
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.modifies.size == 1) s!"expected 1 modifies target, got {f.modifies.size}"
  expect (f.ghosts.size == 1) s!"expected 1 ghost, got {f.ghosts.size}"
  expect (f.ghosts[0]!.name == "g") s!"expected ghost name `g`, got {f.ghosts[0]!.name}"

-- A class-level `@invariant` and a method-level `@requires` are recognized
-- independently: both fields populate.
#guard_msgs in
#eval runNativeCase "class_invariant_with_method_contract" fun sigs _ => do
  let c ← findClass sigs "C"
  expect (c.invariants.size == 1) s!"expected 1 class invariant, got {c.invariants.size}"
  let m ← findMethod c "m"
  expect (m.preconditions.size == 1) s!"expected 1 method precondition, got {m.preconditions.size}"

/-- A warning without its `file:line:col: ` prefix. -/
meta def warningText (w : String) : String :=
  ": ".intercalate ((w.splitOn ": ").drop 1)

-- A stub's `__init__` is read like any other method: the method `__init__` has the
-- typed parameters `region` and `n`, the body asserts and then the `@requires` as
-- preconditions, the `@admit` and the `@modifies` target. The top-level
-- `self.helper = self._Helper()` declares the field `helper`. The assignment nested in
-- the `if` declares no field: it is skipped with a warning, and the assert next to it
-- applies only when `n > 0`.
/--
info: program PythonSpecs;
class "C" {
  bases: []
  fields: [
    count : ident("builtins.int")
    helper : ident("native_cases.init_contract._Helper")"_Helper()"
  ]
  classVars: [
  ]
  subclasses: [
    class "_Helper" {
      bases: []
      fields: [
      ]
      classVars: [
      ]
      subclasses: [
      ]
      exhaustive: false
    }
  ]
  exhaustive: false
  function "__init__"{
    args: [
      self : ident("native_cases.init_contract.C") [default: ]
      region : ident("builtins.str") [default: ]
      n : ident("builtins.int") [default: ]
    ]
    kwonly: [
    ]
    return: ident("_types.NoneType")
    overload: false
    preconditions: [
      ensure(stringLen(region) >=_int 1, "region must not be empty")
      ensure(pcmp("gt", n, 0) => n <=_int 3, "n is small")
      ensure(stringLen(region) <=_int 10, )
    ]
    postconditions: [
      admitted stringLen(region) >=_int 2
    ]
    modifies: [
      (self[count])
    ]
  }
}

warnings: #[skipped Assign in function body]
-/
#guard_msgs in
#eval runNativeCase "init_contract" fun sigs warnings => do
  IO.println (toDDMProgram sigs)
  IO.println s!"warnings: {warnings.map warningText}"

-- The Laurel translation of a stub's `__init__` is a procedure like any other
-- method's: `self` is dropped from its inputs, each declared type, body assert and
-- `@requires` is a `requires` clause, and the `@admit` is a free postcondition.
/--
info: types:
  composite native_cases_init_contract_C { var count: Any var helper: native_cases_init_contract__Helper }
  composite native_cases_init_contract__Helper { }
procedures:
  procedure native_cases_init_contract_C@__init__(region: Any, n: Any)
  returns (result: Any)
  requires Any..isfrom_str(region) summary "declared type of parameter 'region'"
  requires Any..isfrom_int(n) summary "declared type of parameter 'n'"
  requires Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(region))), from_int(1))) summary "region must not be empty"
  requires Any_to_bool(PGt(n, from_int(0))) ==> Any_to_bool(PLe(n, from_int(3))) summary "n is small"
  requires Any_to_bool(PLe(from_int(Str.Length(Any..as_string!(region))), from_int(10))) summary "precondition 2"
  opaque
  free ensures Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(region))), from_int(2))) summary "admitted postcondition of 'native_cases_init_contract_C@__init__'"
  modifies *;
errors: #[]
-/
#guard_msgs in
#eval runNativeCase "init_contract" fun sigs _ => do
  let r := Specs.ToLaurel.signaturesToLaurel "init_contract.py" sigs
    (StrataPython.ModuleName.ofString! "native_cases.init_contract")
  IO.println "types:"
  for td in r.program.types do
    IO.println s!"  {Strata.Laurel.formatTypeDefinition td}"
  IO.println "procedures:"
  for proc in r.program.staticProcedures do
    IO.println s!"  {Strata.Laurel.formatProcedure proc}"
  IO.println s!"errors: {r.errors.map (·.message.message)}"

-- A method with `*args` is a hard error, which rejects the whole model.
#guard_msgs in
#eval expectNativeCaseError "args_method" "m: *args is not supported"

-- A stub `__init__` with `*args` is rejected like any other method.
#guard_msgs in
#eval expectNativeCaseError "args_init" "__init__: *args is not supported"

-- A positional-only parameter is a hard error.
#guard_msgs in
#eval expectNativeCaseError "posonly_function" "f: positional-only parameters are not supported"

-- Type parameters on a function are a hard error.
#guard_msgs in
#eval expectNativeCaseError "def_type_params" "f: type parameters are not supported"

-- Class keywords, a metaclass included, and type parameters on a class are hard errors.
#guard_msgs in
#eval expectNativeCaseError "class_keywords" "C: class keywords, such as metaclass=, are not supported"

#guard_msgs in
#eval expectNativeCaseError "class_metaclass" "C: class keywords, such as metaclass=, are not supported"

#guard_msgs in
#eval expectNativeCaseError "class_type_params" "C: type parameters are not supported"

-- The same holds for a nested class, and decorators on a nested class are a hard error too.
#guard_msgs in
#eval expectNativeCaseError "nested_class_keywords"
  "Inner: class keywords, such as metaclass=, are not supported"

#guard_msgs in
#eval expectNativeCaseError "nested_class_metaclass"
  "Inner: class keywords, such as metaclass=, are not supported"

#guard_msgs in
#eval expectNativeCaseError "nested_class_type_params" "Inner: type parameters are not supported"

#guard_msgs in
#eval expectNativeCaseError "nested_class_decorator"
  "Inner: decorators on a nested class are not supported"

-- The translation goes on after a class that it rejects: the function after the class is read,
-- and its own error is reported too.
/-- info: [true, true] -/
#guard_msgs in
#eval do
  let some e ← nativeCaseError "class_keywords_then_fn" | return
  IO.println [e.contains "C: class keywords, such as metaclass=, are not supported",
    e.contains "g: positional-only parameters are not supported"]

/-- The errors that `pySpecArg` reports for the parameter `x: int`, built by hand
    with the given source ranges and type comment. -/
meta def pySpecArgErrors (loc typeLoc : SourceRange) (comment : Option String) :
    IO (Array String) := do
  let r : SourceRange := { start := ⟨1⟩, stop := ⟨2⟩ }
  let intType : expr SourceRange := .Name r ⟨r, "int"⟩ (.Load r)
  let a : arg SourceRange := .mk_arg loc ⟨r, "x"⟩ ⟨typeLoc, some intType⟩
    ⟨r, comment.map (⟨r, ·⟩)⟩
  let ctx : PySpecContext := {
    eventSet := {}, pythonCmd := "", dialectFile := "", pythonFile := "t.py",
    strataDir := "", baseSearchPath := "", currentModulePrefix := none,
    fileMapsRef := ← IO.mkRef {}, currentModule := .ofString! "t" }
  let (_, s) ← (pySpecArg {} none a none).run ctx |>.run { errors := #[], warnings := #[] }
  return s.errors.map (·.message.message)

-- `pySpecArg` accepts a well-formed parameter. It reports a parameter without a
-- source range, an annotation with a source range, and a type comment.
/--
info: #[]
#[internal: argument x has no source location]
#[internal: the annotation of argument x has a source location]
#[x: type comments are not supported]
-/
#guard_msgs in
#eval do
  let r : SourceRange := { start := ⟨1⟩, stop := ⟨2⟩ }
  IO.println (← pySpecArgErrors r default none)
  IO.println (← pySpecArgErrors default default none)
  IO.println (← pySpecArgErrors r r none)
  IO.println (← pySpecArgErrors r default (some "int"))

/-- The errors that `translate` reports for the module body `body`. -/
meta def translateErrors (body : Array (stmt SourceRange)) : IO (Array String) := do
  let ctx : PySpecContext := {
    eventSet := {}, pythonCmd := "", dialectFile := "", pythonFile := "t.py",
    strataDir := "", baseSearchPath := "", currentModulePrefix := none,
    fileMapsRef := ← IO.mkRef {}, currentModule := .ofString! "t" }
  let (_, s) ← (translate body).run ctx |>.run { errors := #[], warnings := #[] }
  return s.errors.map (·.message.message)

/-- The errors that `translate` reports for the stub `def f(): ...`, built by hand with the
    given source range on each list or optional field, and the given type comment. -/
meta def functionDefErrors (fieldLoc : SourceRange) (comment : Option String) :
    IO (Array String) := do
  let r : SourceRange := { start := ⟨1⟩, stop := ⟨2⟩ }
  let noArgs : arguments SourceRange :=
    .mk_arguments r ⟨default, #[]⟩ ⟨default, #[]⟩ ⟨default, none⟩ ⟨default, #[]⟩
      ⟨default, #[]⟩ ⟨default, none⟩ ⟨default, #[]⟩
  let ellipsis : stmt SourceRange := .Expr r (.Constant r (.ConEllipsis r) ⟨default, none⟩)
  translateErrors #[.FunctionDef r ⟨r, "f"⟩ noArgs ⟨fieldLoc, #[ellipsis]⟩ ⟨fieldLoc, #[]⟩
    ⟨fieldLoc, none⟩ ⟨fieldLoc, comment.map (⟨r, ·⟩)⟩ ⟨fieldLoc, #[]⟩]

-- `translate` accepts a well-formed stub function. It reports a source range on a list or
-- optional field of the function, and a type comment, which the Python parser never gives.
/--
info: #[]
#[internal: the body of function f has a source location, internal: the decorator list of function f has a source location, internal: the return annotation of function f has a source location, internal: the type comment of function f has a source location, internal: the type parameter list of function f has a source location]
#[f: type comments are not supported]
-/
#guard_msgs in
#eval do
  let r : SourceRange := { start := ⟨1⟩, stop := ⟨2⟩ }
  IO.println (← functionDefErrors default none)
  IO.println (← functionDefErrors r none)
  IO.println (← functionDefErrors default (some "() -> None"))

-- `translate` accepts a well-formed `class C: pass`, and it reports a source range on the
-- class's name, which the Python parser never gives.
/--
info: #[]
#[internal: the name of class C has a source location]
-/
#guard_msgs in
#eval do
  let r : SourceRange := { start := ⟨1⟩, stop := ⟨2⟩ }
  let classC (nameLoc : SourceRange) : stmt SourceRange :=
    .ClassDef r ⟨nameLoc, "C"⟩ ⟨default, #[]⟩ ⟨default, #[]⟩ ⟨default, #[.Pass r]⟩
      ⟨default, #[]⟩ ⟨default, #[]⟩
  IO.println (← translateErrors #[classC default])
  IO.println (← translateErrors #[classC r])

/-- Print each class's methods with their parameters and `@overload` marks, then the
    Laurel procedures, the Laurel errors and the parser's warnings of the native case
    `stem`. -/
meta def printMethodsAndProcedures (stem : String) : IO Unit :=
  runNativeCase stem fun sigs warnings => do
    for sig in sigs do
      if let .classDef c := sig then
        let shown := c.methods.toList.map fun m =>
          let params := ", ".intercalate (m.args.args.toList.map (·.name))
          s!"{if m.isOverload then "@overload " else ""}{m.name}({params})"
        IO.println s!"class {c.name}: {shown}"
    let r := Specs.ToLaurel.signaturesToLaurel s!"{stem}.py" sigs
      (StrataPython.ModuleName.ofString! s!"native_cases.{stem}")
    IO.println s!"procedures: {r.program.staticProcedures.map (·.name.text)}"
    IO.println "errors:"
    for e in r.errors do
      IO.println s!"  {e.message.kind.category}: {e.message.message}"
    IO.println s!"warnings: {warnings.map warningText}"

-- The `@overload` stubs of `__init__` are recorded, and they get no Laurel procedure,
-- as top-level `@overload` stubs get none.
/--
info: class C: [@overload __init__(self, x), @overload __init__(self, x)]
procedures: []
errors:
warnings: #[]
-/
#guard_msgs in
#eval printMethodsAndProcedures "overload_init"

-- The `@overload` stubs of a method are recorded, and they get no Laurel procedure.
-- A plain definition of the same name, and any other method, get one.
/--
info: class C: [@overload m(self, x), @overload m(self, x), n(self)]
class D: [@overload m(self, x), @overload m(self, x), m(self, x)]
procedures: [native_cases_overload_method_C@n, native_cases_overload_method_D@m]
errors:
warnings: #[]
-/
#guard_msgs in
#eval printMethodsAndProcedures "overload_method"

-- A class defines each method name at most once without `@overload`.
#guard_msgs in
#eval expectNativeCaseError "duplicate_init" "C.__init__ is already defined"

#guard_msgs in
#eval expectNativeCaseError "duplicate_method" "C.m is already defined"

-- A stub's `__init__` follows the rules of every method: a default other than `None`
-- is a hard error.
#guard_msgs in
#eval expectNativeCaseError "init_default" "Unexpected value Python.Constant(Python.ConPos(0)"

-- Each contract on an `@overload` stub of a method (`@requires`, `@ensures`, `@admit`,
-- `@modifies`, `@ghost`) is rejected, since the stub gets no Laurel procedure that
-- could carry it. Stubs with only a signature still load (`overload_method` above).
/--
info: class P: [@overload m(self, x), @overload m(self, x)]
procedures: []
errors:
  unsupportedOverloadContract: A precondition (@requires or assert) is not supported on @overload stub 'P.m': x >=_int 0. No procedure is generated for it, so the precondition would be silently dropped. Attach the contract to a non-overload declaration instead.
  unsupportedPostcondition: Modeled @ensures cannot be verified for 'P.m': result >=_int 0. An @overload stub is a dispatch-only declaration; no procedure is generated for it, so the postcondition would be silently dropped. Attach the contract to a non-overload declaration instead.
  unsupportedAdmit: @admit is not supported on @overload stub 'P.m': pcmp("eq", result, 7). No procedure is generated for a dispatch-only declaration, so there is nothing to carry the assumed postcondition. Attach the @admit to a non-overload declaration instead.
  unsupportedOverloadContract: @modifies is not supported on @overload stub 'P.m': x. No procedure is generated for it, so the frame would be silently dropped. Attach the contract to a non-overload declaration instead.
  unsupportedOverloadContract: @ghost is not supported on @overload stub 'P.m': g. No procedure is generated for it, so the ghost would be silently dropped. Attach it to a non-overload declaration instead.
warnings: #[]
-/
#guard_msgs in
#eval printMethodsAndProcedures "overload_method_requires"

-- A stub whose body is not `...` gets a warning, once per such stub.
#guard_msgs in
#eval runNativeCase "overload_body_pass" fun _ warnings => do
  let n := (warnings.filter (·.contains "overload body is not `...`")).size
  expect (n == 1) s!"warnings: {warnings}"

-- The parser does not read the body of an `@overload` stub, so an assert in it is a
-- hard error.
#guard_msgs in
#eval expectNativeCaseError "overload_method_assert"
  "P.m: an @overload stub cannot have assert, if or for statements"

-- The same holds for a stub of a top-level function.
#guard_msgs in
#eval expectNativeCaseError "overload_function_assert"
  "f: an @overload stub cannot have assert, if or for statements"

-- An assert in an `@overload` stub's body is a hard error at any depth, on both paths. Each
-- stub of `overload_nested_assert` nests one assert in another kind of block, except
-- `no_assert`.
/--
info: [in_while, in_while_else, in_with, in_try, in_handler, in_try_else, in_finally, in_try_star, in_match, in_def, in_class, in_async_for, in_async_with, in_async_def, P.m]
-/
#guard_msgs in
#eval do
  let some e ← nativeCaseError "overload_nested_assert" | return
  let stubs := ["in_while", "in_while_else", "in_with", "in_try", "in_handler", "in_try_else",
    "in_finally", "in_try_star", "in_match", "in_def", "in_class", "in_async_for",
    "in_async_with", "in_async_def", "no_assert", "P.m"]
  IO.println <| stubs.filter fun n =>
    e.contains s!" {n}: an @overload stub cannot have assert, if or for statements"

-- Two `@overload` stubs of `__init__` that both assign `self.h = self._H()` declare
-- the field `h` once.
/--
info: fields: [h = _H()]
warnings: #[]
-/
#guard_msgs in
#eval runNativeCase "overload_init_fields" fun sigs warnings => do
  let c ← findClass sigs "C"
  IO.println s!"fields: {c.fields.toList.map fun f => s!"{f.name} = {f.constValue.getD "-"}"}"
  IO.println s!"warnings: {warnings.map warningText}"

-- Two `@overload` stubs of `__init__` that assign one field different classes are a
-- hard error.
#guard_msgs in
#eval expectNativeCaseError "overload_init_field_conflict"
  "C.__init__ assigns self.h both _H() and _G()"

-- A Dict[int, _] quantifier is rejected because the logical model has string keys.
#guard_msgs in
#eval expectNativeCaseError "requires_int_dict_quant"
  "dict quantifier requires str keys"

-- Literal string keys are str at runtime, so the dict quantifier is accepted.
#guard_msgs in
#eval runNativeCase "requires_literal_dict_quant" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.preconditions.size == 1) s!"expected 1 precondition, got {f.preconditions.size}"

-- Non-TypedDict `**kwargs` are rejected with a fatal user-code error, so a
-- contract referencing them cannot be silently weakened.
#guard_msgs in
#eval runNativeCase "requires_nontypeddict_kwargs" fun sigs _ => do
  let lowered := Specs.ToLaurel.signaturesToLaurel
    (testDir / "native_cases" / "requires_nontypeddict_kwargs.py") sigs
    (StrataPython.ModuleName.ofString! "native_cases.requires_nontypeddict_kwargs")
  let messages := lowered.errors.map (·.message.message)
  let expected := #[
    "**kw must use Unpack[TypedDict], got 'builtins.int'; **kw cannot be modeled",
    "Unknown identifier 'kw' in 'native_cases_requires_nontypeddict_kwargs_h'"]
  expect (messages == expected)
    s!"expected exactly the kwargs drop and dangling identifier errors, got {messages}"

/-! ## `OLD(expr)` recognition and rejection -/

-- `OLD` is a generic expression wrapper accepted by verified post-state predicates.
#guard_msgs in
#eval runNativeCase "old_ensures" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.postconditions.size == 1) s!"expected 1 postcondition, got {f.postconditions.size}"
  expect (f.postconditions[0]!.softBEq
            (.intGe (.old (.var "x" .none) .none) (.var "x" .none) .none))
    "postcondition formula did not match OLD(x) >= x"

-- Admitted post-state predicates have the same expression semantics as @ensures.
#guard_msgs in
#eval runNativeCase "old_admit" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
            (.intGe (.var "result" .none) (.old (.var "x" .none) .none) .none))
    "admitted postcondition did not match result >= OLD(x)"

-- OLD in roles without post-state semantics is a hard error.
#guard_msgs in
#eval expectNativeCaseError "old_in_requires" "only allowed in post-state predicates"

#guard_msgs in
#eval expectNativeCaseError "old_in_assert" "only allowed in post-state predicates"

#guard_msgs in
#eval expectNativeCaseError "old_in_modifies" "only allowed in post-state predicates"

#guard_msgs in
#eval expectNativeCaseError "old_in_ghost" "only allowed in post-state predicates"

#guard_msgs in
#eval expectNativeCaseError "old_in_invariant" "only allowed in post-state predicates"

-- OLD with wrong arity is a hard error.
#guard_msgs in
#eval expectNativeCaseError "old_arity" "OLD expected 1 argument"

-- OLD(result) is a hard error (result doesn't exist in the pre-state).
#guard_msgs in
#eval expectNativeCaseError "old_result" "does not exist in the pre-state"

-- A quantifier binder named `result` shadows the post-state result binder.
#guard_msgs in
#eval runNativeCase "old_result_shadowed" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
            (.old
              (.quantifier .exists (.overList "result") (.var "xs" .none)
                (.intGe (.var "result" .none) (.intLit 0 .none) .none) .none)
              .none))
    "quantifier-local result was confused with the post-state result binder"

-- Free uses of the post-state result remain invalid inside quantifiers.
#guard_msgs in
#eval expectNativeCaseError "old_result_free_body" "does not exist in the pre-state"

#guard_msgs in
#eval expectNativeCaseError "old_result_free_collection" "does not exist in the pre-state"

-- OLD does not make nonnumeric post-state orderings valid.
#guard_msgs in
#eval runNativeCase "old_nonnumeric" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect (f.admittedPostconditions.size == 0)
    s!"expected unsupported comparison to be dropped, got {f.admittedPostconditions.size}"
  expect (warnings.any (·.contains "unsupported comparison"))
    "expected an unsupported-comparison warning"

-- A bare `OLD` (not applied) is a hard error: OLD must be called.
#guard_msgs in
#eval expectNativeCaseError "old_bare" "must be called"

-- Nested OLD is structurally preserved; Laurel owns normalization/diagnostics.
#guard_msgs in
#eval runNativeCase "old_nested" fun sigs _ => do
  let f ← findFn sigs "f"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
            (.intGe (.old (.old (.var "x" .none) .none) .none) (.var "x" .none) .none))
    "nested OLD wrappers were not preserved structurally"

-- OLD with a keyword argument is a hard error.
#guard_msgs in
#eval expectNativeCaseError "old_kwargs" "no keyword arguments"

-- Method receiver fields are rejected during recognition because Laurel method
-- procedures do not retain the receiver as an input.
#guard_msgs in
#eval runNativeCase "old_field" fun sigs warnings => do
  let m ← findMethod (← findClass sigs "C") "m"
  expect m.admittedPostconditions.isEmpty
    s!"expected receiver contract to be dropped, got {m.admittedPostconditions.size}"
  expect (warnings.any (·.contains "method receiver field access"))
    "expected an unsupported method-receiver warning"
  let lowered := Specs.ToLaurel.signaturesToLaurel
    (testDir / "native_cases" / "old_field.py") sigs
    (StrataPython.ModuleName.ofString! "native_cases.old_field")
  expect lowered.errors.isEmpty
    s!"receiver rejection should prevent Laurel errors, got {lowered.errors.size}"

-- Exercise the symmetric receiver rejection for <=.
#guard_msgs in
#eval runNativeCase "old_field_le" fun sigs warnings => do
  let m ← findMethod (← findClass sigs "C") "m"
  expect m.admittedPostconditions.isEmpty
    s!"expected receiver contract to be dropped, got {m.admittedPostconditions.size}"
  expect (warnings.any (·.contains "method receiver field access"))
    "expected an unsupported method-receiver warning"

-- A quantifier binder may shadow the method receiver name. Its field reads are
-- local to the quantifier and remain lowerable.
#guard_msgs in
#eval runNativeCase "old_field_receiver_shadowed" fun sigs warnings => do
  let m ← findMethod (← findClass sigs "C") "m"
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  expect (m.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {m.admittedPostconditions.size}"
  expect (m.admittedPostconditions[0]!.softBEq
            (.quantifier .forall (.overList "self") (.var "xs" .none)
              (.intGe
                (.getIndex (.var "self" .none) "x" .none)
                (.intLit 0 .none)
                .none)
              .none))
    "quantifier-local self was confused with the method receiver"
  let lowered := Specs.ToLaurel.signaturesToLaurel
    (testDir / "native_cases" / "old_field_receiver_shadowed.py") sigs
    (StrataPython.ModuleName.ofString! "native_cases.old_field_receiver_shadowed")
  expect lowered.errors.isEmpty
    s!"shadowed receiver failed Laurel lowering with {lowered.errors.size} errors"

-- Non-receiver field reads remain supported. Unknown field types use a generic
-- runtime comparison rather than claiming integer semantics.
#guard_msgs in
#eval runNativeCase "old_field_arg" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
            (.pcmp .ge
              (.getIndex (.var "obj" .none) "value" .none)
              (.old (.getIndex (.var "obj" .none) "value" .none) .none)
              .none))
    "admitted postcondition did not preserve generic field comparison"
  let lowered := Specs.ToLaurel.signaturesToLaurel
    (testDir / "native_cases" / "old_field_arg.py") sigs
    (StrataPython.ModuleName.ofString! "native_cases.old_field_arg")
  expect lowered.errors.isEmpty
    s!"generic field comparison failed Laurel lowering with {lowered.errors.size} errors"

-- Exercise the symmetric generic <= fallback.
#guard_msgs in
#eval runNativeCase "old_field_arg_le" fun sigs warnings => do
  let f ← findFn sigs "f"
  expect warnings.isEmpty s!"expected no warnings, got {warnings}"
  expect (f.admittedPostconditions.size == 1)
    s!"expected 1 admitted postcondition, got {f.admittedPostconditions.size}"
  expect (f.admittedPostconditions[0]!.softBEq
            (.pcmp .le
              (.getIndex (.var "obj" .none) "value" .none)
              (.old (.getIndex (.var "obj" .none) "value" .none) .none)
              .none))
    "admitted postcondition did not preserve generic <= field comparison"
  let lowered := Specs.ToLaurel.signaturesToLaurel
    (testDir / "native_cases" / "old_field_arg_le.py") sigs
    (StrataPython.ModuleName.ofString! "native_cases.old_field_arg_le")
  expect lowered.errors.isEmpty
    s!"generic <= field comparison failed Laurel lowering with {lowered.errors.size} errors"

-- The generic fallback requires two field reads; a field compared with a bare
-- variable remains unsupported.
#guard_msgs in
#eval runNativeCase "old_field_mixed" fun sigs warnings => do
  let ge ← findFn sigs "f_ge"
  let le ← findFn sigs "f_le"
  expect ge.admittedPostconditions.isEmpty
    s!"expected mixed >= comparison to be dropped, got {ge.admittedPostconditions.size}"
  expect le.admittedPostconditions.isEmpty
    s!"expected mixed <= comparison to be dropped, got {le.admittedPostconditions.size}"
  let unsupported := warnings.filter (·.contains "unsupported comparison")
  expect (unsupported.size == 2)
    s!"expected 2 unsupported-comparison warnings, got {unsupported.size}"

/-- Test that recoverable unsupported patterns emit warnings without blocking output. -/
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
        if sigs.isEmpty then
          throw <| IO.userError "Expected signatures from warnings.py but got none"
        let loopWithDocstring ← findFn sigs "for_loop_with_docstring"
        if loopWithDocstring.preconditions.size != 1 then
          throw <| IO.userError
            s!"Expected the legacy loop with a docstring to retain 1 precondition, got \
               {loopWithDocstring.preconditions.size}"
        let expectedWarnings := #[
          "unsupported __init__ assignment",
          "skipped Assign in function body",
          "skipped Expr in function body"
        ]
        for expected in expectedWarnings do
          if !warnings.any (·.contains expected) then
            let warnStr := warnings.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
            throw <| IO.userError
              s!"Missing expected warning containing \"{expected}\". Actual warnings:{warnStr}"
        -- eq_bad_rhs must warn exactly once: a duplicated warning means the Eq
        -- fall-through is re-translating the unsupported right side.
        let unsupportedRhs := warnings.filter fun w =>
          w.contains "unsupported expression" && w.contains "bit_length"
        if unsupportedRhs.size != 1 then
          let warnStr := unsupportedRhs.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
          throw <| IO.userError
            s!"Expected exactly 1 unsupported-rhs warning for eq_bad_rhs, \
               got {unsupportedRhs.size}:{warnStr}"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval warningTestCase

/-- Unsupported quantifier shapes must abort PySpec translation rather than
    silently weakening the generated contract. One fixture covers each refusal
    branch for expression- and statement-form quantifiers. -/
def quantifierErrorTestCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "quantifier_errors.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "quantifier_errors"))
          |>.toBaseIO
      match r with
      | .ok _ =>
        throw <| IO.userError "Expected unsupported quantifiers to produce hard errors"
      | .error e =>
        let expectedErrors := #[
          ("any: iterable type is not a supported collection", 1),
          ("any: iterable could not be translated", 1),
          ("any: only `any(body for x in iterable)` is supported", 1),
          ("any: argument must be a generator expression", 1),
          ("any: exactly one `for` clause is supported", 1),
          ("any: list quantifier expects a single loop variable", 1),
          ("any: dict items quantifier expects `for k, v in d.items()`", 1),
          ("all: at most one `if` clause is supported", 1),
          ("any: quantifier body could not be translated", 2),
          ("all: quantifier guard could not be translated", 2),
          ("For: iterable type is not a supported collection", 1),
          ("For: iterable could not be translated", 1),
          ("For: loop body could not be fully translated", 3),
          ("For: else clause not supported", 1)
        ]
        for (expected, expectedCount) in expectedErrors do
          let actualCount := (e.splitOn expected).length - 1
          unless actualCount == expectedCount do
            throw <| IO.userError
              s!"Expected exactly {expectedCount} hard error(s) containing \"{expected}\", got {actualCount}. Actual errors:\n{e}"

#guard_msgs in
#eval quantifierErrorTestCase

/-- String-key maps cannot faithfully represent `Dict[int, _]` quantifiers. -/
private def dictIntKeyErrorTestCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "dict_int_key_warn.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "dict_int_key_warn"))
          |>.toBaseIO
      match r with
      | .ok _ =>
        throw <| IO.userError "expected Dict[int, _] quantifiers to be rejected"
      | .error e =>
        let actualCount := (e.splitOn "dict quantifier requires str keys").length - 1
        unless actualCount == 2 do
          throw <| IO.userError
            s!"expected 2 dictionary-key errors, got {actualCount}. Actual errors:\n{e}"

#guard_msgs in
#eval dictIntKeyErrorTestCase

/-- A dynamic subscript on a non-dict subject warns about the subject, not the key. -/
private def listSubscriptWarnTestCase : IO Unit := withPython fun pythonCmd => do
  IO.FS.withTempFile fun _handle dialectFile => do
    IO.FS.writeBinFile dialectFile StrataPython.Python.toIon
    IO.FS.withTempDir fun strataDir => do
      let r ←
        translateFile
          (pythonCmd := toString pythonCmd)
          (dialectFile := dialectFile)
          (strataDir := strataDir)
          (pythonFile := testDir / "list_subscript_warn.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "list_subscript_warn"))
          |>.toBaseIO
      match r with
      | .ok (_sigs, warnings) =>
        unless warnings.size == 3 do
          throw <| IO.userError s!"expected exactly 3 warnings, got {warnings.size}:\n  {warnings}"
        let expected := #[
          ("subscript subject is not a string-keyed Dict/Mapping/TypedDict", 1),
          ("dictionary subscript key must have type str", 0),
          ("unsupported comparison", 1),
          ("unsupported expression in assert; dropped", 1)]
        for (needle, expectedCount) in expected do
          let actualCount := warnings.filter (·.contains needle) |>.size
          unless actualCount == expectedCount do
            throw <| IO.userError
              s!"expected {expectedCount} warning(s) containing \"{needle}\", got {actualCount}:\n  {warnings}"
      | .error e => throw <| IO.userError e

#guard_msgs in
#eval listSubscriptWarnTestCase


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

/-- `SourceRange` tag for the round-trip samples. -/
def rtLoc : SourceRange := .none

/-- Round-trip a `SpecExpr` through `toDDM` then `fromDDM`. -/
def rtSpecExpr (e : SpecExpr) : SpecExpr := e.toDDM.fromDDM

/-- One representative `SpecExpr` per constructor. -/
def specExprSamples : List (String × SpecExpr) :=
  let x  := SpecExpr.var "x" rtLoc
  let y  := SpecExpr.var "y" rtLoc
  let i1 := SpecExpr.intLit 1 rtLoc
  let bt := SpecExpr.boolLit true rtLoc
  let bf := SpecExpr.boolLit false rtLoc
  [ ("placeholder",  .placeholder rtLoc),
    ("var",          x),
    ("old",          .old x rtLoc),
    ("getIndex",     .getIndex x "f" rtLoc),
    ("isInstanceOf", .isInstanceOf x "str" rtLoc),
    ("stringLen",    .stringLen x rtLoc),
    ("len",          .len x rtLoc),
    ("intLit",       i1),
    ("boolLit",      bt),
    ("noneLit",      .noneLit rtLoc),
    ("intGe",        .intGe x i1 rtLoc),
    ("intLe",        .intLe x i1 rtLoc),
    ("eq",           .pcmp .eq x y rtLoc),
    ("add",          .add x y rtLoc),
    ("sub",          .sub x y rtLoc),
    ("mul",          .mul x y rtLoc),
    ("floorDiv",     .floorDiv x y rtLoc),
    ("mod",          .mod x y rtLoc),
    ("pow",          .pow x y rtLoc),
    ("neg",          .neg x rtLoc),
    ("and",          .and bt bf rtLoc),
    ("or",           .or bt bf rtLoc),
    ("pcmp",         .pcmp .isIn x y rtLoc),
    ("floatLit",     .floatLit "3.14" rtLoc),
    ("floatGe",      .floatGe x (.floatLit "0.0" rtLoc) rtLoc),
    ("floatLe",      .floatLe x (.floatLit "1.0" rtLoc) rtLoc),
    ("enumMember",   .enumMember x #["A", "B"] rtLoc),
    ("regexMatch",   .regexMatch x "^a+$" rtLoc),
    ("containsKey",  .containsKey x "k" rtLoc),
    ("implies",      .implies bt bf rtLoc),
    ("not",          .not bt rtLoc),
    ("forallList",   .quantifier .forall (.overList "i") x bt rtLoc),
    ("forallDict",   .quantifier .forall (.overDictItems "k" "val") x bt rtLoc),
    ("forallKeys",   .quantifier .forall (.overDictKeys "k") x bt rtLoc),
    ("forallValues", .quantifier .forall (.overDictValues "val") x bt rtLoc),
    ("existsList",   .quantifier .exists (.overList "i") x bt rtLoc),
    ("existsKeys",   .quantifier .exists (.overDictKeys "k") x bt rtLoc),
    ("existsValues", .quantifier .exists (.overDictValues "val") x bt rtLoc),
    -- Surface form: `any(P(k, val) for k, val in d.items())`.
    ("existsDict",   .quantifier .exists (.overDictItems "k" "val") x bt rtLoc) ]

/-- DDM round-trip regression: every `SpecExpr` ctor must survive `toDDM`/`fromDDM` up to `softBEq`. -/
def specExprRoundTripTest : IO Unit := do
  for (name, e) in specExprSamples do
    let e' := rtSpecExpr e
    unless e'.softBEq e do
      throw <| IO.userError s!"round-trip mismatch for '{name}': {e} -> {e'}"

#guard_msgs in
#eval specExprRoundTripTest

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
    admittedPostconditions := #[
      .intGe (.var "result" .none) (.old (.var "x" .none) .none) .none
    ]
    modifies := #[.var "self_x" .none]
    ghosts := #[{ name := "g", type := some (SpecType.ident .none .builtinsInt),
                  init := some (.intLit 7 .none), loc := .none }]
  }
  let fd' ← match DDM.FunDecl.fromDDM (FunctionDecl.toDDM fd) with
    | .ok r => pure r
    | .error (_, msg) => throw <| IO.userError s!"FunDecl.fromDDM failed: {msg}"
  -- The DDM boundary accepts an optional `snapshots` clause for wire
  -- compatibility and intentionally discards its contents.
  let legacyDDM := match FunctionDecl.toDDM fd with
    | .mkFunDecl loc name args kwonly kwargs returnType isOverload
        preconditions postconditions _snapshots modifiesClause ghosts =>
      .mkFunDecl loc name args kwonly kwargs returnType isOverload
        preconditions postconditions
        ⟨.none, some (.mkSnapshotsClause .none ⟨.none, #[
          .mkSnapshotDecl .none ⟨.none, "v0"⟩ (SpecExpr.var "x" .none).toDDM
        ]⟩)⟩
        modifiesClause ghosts
  let legacyFd ← match DDM.FunDecl.fromDDM legacyDDM with
    | .ok r => pure r
    | .error (_, msg) => throw <| IO.userError s!"legacy FunDecl.fromDDM failed: {msg}"
  expect (legacyFd.name == fd.name) "legacy snapshots clause corrupted function declaration"
  expect (legacyFd.postconditions.size == fd.postconditions.size)
    "legacy snapshots clause corrupted postconditions"
  expect (legacyFd.postconditions[0]!.softBEq fd.postconditions[0]!)
    "legacy snapshots clause corrupted postcondition formula content"
  expect (legacyFd.admittedPostconditions.size == fd.admittedPostconditions.size)
    "legacy snapshots clause corrupted admitted postconditions"
  expect (legacyFd.admittedPostconditions[0]!.softBEq fd.admittedPostconditions[0]!)
    "legacy snapshots clause corrupted admitted postcondition formula content"
  expect (fd'.preconditions.size == 1) s!"round-trip dropped preconditions: got {fd'.preconditions.size}"
  expect (fd'.preconditions[0]!.formula.softBEq (.intGe (.var "x" .none) (.intLit 0 .none) .none))
    "round-trip corrupted precondition formula"
  expect (fd'.postconditions.size == 1) s!"round-trip dropped postconditions: got {fd'.postconditions.size}"
  expect (fd'.postconditions[0]!.softBEq
            (.intGe (.var "result" .none) (.intLit 0 .none) .none))
    "round-trip corrupted verified postcondition formula"
  expect (fd'.admittedPostconditions.size == 1)
    s!"round-trip dropped admitted postconditions: got {fd'.admittedPostconditions.size}"
  expect (fd'.admittedPostconditions[0]!.softBEq
            (.intGe (.var "result" .none) (.old (.var "x" .none) .none) .none))
    "round-trip corrupted admitted postcondition formula (old wrapping must survive)"
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
  expect (cd'.methods[0]!.admittedPostconditions.size == 1
          && cd'.methods[0]!.modifies.size == 1
          && cd'.methods[0]!.ghosts.size == 1)
    "round-trip dropped a class method's admitted/modifies/ghost fields"

#guard_msgs in
#eval serdeRoundTripTest

/-! ## Module-scope ghost declarations -/

meta def findModuleGhost (sigs : Array Signature) (name : String) : IO Specs.Ghost := do
  let some g := sigs.findSome?
      (fun | .ghostDecl g => if g.name == name then some g else none | _ => none)
    | throw <| IO.userError s!"module ghost `{name}` not found"
  return g

-- Explicit `init=` is retained; an omitted one stays nondeterministic.
#guard_msgs in
#eval runNativeCase "module_ghost_decl" fun sigs _ => do
  let counter ← findModuleGhost sigs "counter"
  let some tp := counter.type
    | throw <| IO.userError "module ghost 'counter' lost its declared type"
  expect (compare tp (SpecType.ident .none .builtinsInt) == .eq)
    "module ghost 'counter' type did not resolve to `int`"
  let some init := counter.init
    | throw <| IO.userError "module ghost 'counter' lost its initializer"
  expect (init.softBEq (.intLit 0 .none)) "initializer of 'counter' did not match `0`"
  let flag ← findModuleGhost sigs "flag"
  expect flag.init.isNone "module ghost 'flag' gained an initializer"
  let _ ← findFn sigs "read_counter"
  pure ()

-- A contract's ghost reference survives translation.
#guard_msgs in
#eval runNativeCase "module_ghost_ref" fun sigs _ => do
  let f ← findFn sigs "read_counter"
  expect (f.admittedPostconditions.size == 1)
    s!"contract referencing a module ghost was dropped: got \
       {f.admittedPostconditions.size} admitted postconditions"
  expect (f.admittedPostconditions[0]!.softBEq
      (.intGe (.var "result" .none) (.var "counter" .none) .none))
    "admitted postcondition did not match `result >= counter`"

-- A contract may reference a ghost declared later in the file.
#guard_msgs in
#eval runNativeCase "module_ghost_forward_ref" fun sigs _ => do
  let _ ← findModuleGhost sigs "later"
  let f ← findFn sigs "read_later"
  expect (f.admittedPostconditions.size == 1)
    s!"forward reference to a module ghost was dropped: got \
       {f.admittedPostconditions.size} admitted postconditions"
  expect (f.admittedPostconditions[0]!.softBEq
      (.intGe (.var "result" .none) (.var "later" .none) .none))
    "admitted postcondition did not match `result >= later`"

-- A parameter shadows a module ghost of the same name inside that procedure.
#guard_msgs in
#eval runNativeCase "module_ghost_shadowed" fun sigs _ => do
  let _ ← findModuleGhost sigs "counter"
  let f ← findFn sigs "takes_counter"
  expect (f.preconditions.size == 1)
    s!"expected 1 precondition, got {f.preconditions.size}"
  expect (f.preconditions[0]!.formula.softBEq
      (.intGe (.var "counter" .none) (.intLit 0 .none) .none))
    "precondition did not match `counter >= 0`"

-- A module ghost survives the DDM serialization round-trip.
#guard_msgs in
#eval runNativeCase "module_ghost_decl" fun sigs _ => do
  let counter ← findModuleGhost sigs "counter"
  let cmd := Signature.toDDM (.ghostDecl counter)
  let back ← match DDM.Command.fromDDM cmd with
    | .ok r => pure r
    | .error (_, msg) => throw <| IO.userError s!"Command.fromDDM failed: {msg}"
  let some counter' := (fun | .ghostDecl g => some g | _ => none) back
    | throw <| IO.userError "round-trip did not yield a ghostDecl"
  expect (counter'.name == "counter") s!"round-trip corrupted ghost name: {counter'.name}"
  let some tp := counter.type
    | throw <| IO.userError "source ghost 'counter' has no type to round-trip"
  let some tp' := counter'.type
    | throw <| IO.userError "round-trip dropped the ghost type"
  expect (compare tp' tp == .eq) "round-trip corrupted the ghost type"
  let some init' := counter'.init
    | throw <| IO.userError "round-trip dropped the ghost initializer"
  expect (init'.softBEq (.intLit 0 .none)) "round-trip corrupted the ghost initializer"

-- A repeated ghost name is a duplicate in the module-wide namespace.
#guard_msgs in
#eval expectNativeCaseError "module_ghost_dup" "duplicate"

-- A ghost's `type=` resolves a module-local alias declared before it.
#guard_msgs in
#eval runNativeCase "module_ghost_type_alias" fun sigs _ => do
  let counter ← findModuleGhost sigs "counter"
  let some tp := counter.type
    | throw <| IO.userError "module ghost 'counter' lost its aliased type"
  expect (compare tp (SpecType.ident .none .builtinsInt) == .eq)
    "aliased ghost type did not resolve to `int`"
  let some init := counter.init
    | throw <| IO.userError "module ghost 'counter' lost its initializer"
  expect (init.softBEq (.intLit 0 .none)) "initializer of 'counter' did not match `0`"

-- A ghost's `type=` resolves a TypedDict alias declared before it.
#guard_msgs in
#eval runNativeCase "module_ghost_typeddict_alias" fun sigs _ => do
  let pending ← findModuleGhost sigs "pending"
  let some tp := pending.type
    | throw <| IO.userError "module ghost 'pending' lost its TypedDict type"
  let expected := SpecType.typedDict .none #["k"] #[SpecType.ident .none .builtinsStr] #[true]
  expect (compare tp expected == .eq)
    "ghost type did not resolve to the TypedDict alias `Item`"

-- A ghost's `type=` resolves a user-declared class defined before it.
#guard_msgs in
#eval runNativeCase "module_ghost_class_ref" fun sigs _ => do
  let pending ← findModuleGhost sigs "pending"
  let some tp := pending.type
    | throw <| IO.userError "module ghost 'pending' lost its class type"
  let item : PythonIdent :=
    { pythonModule := ModuleName.ofString! "native_cases.module_ghost_class_ref"
      name := "Item" }
  expect (compare tp (SpecType.ident .none item) == .eq)
    "ghost type did not resolve to the user-declared class `Item`"

-- A ghost's `type=` sees only bindings declared before it (source order).
#guard_msgs in
#eval expectNativeCaseError "module_ghost_alias_after_ghost" "Unknown identifier MyInt"

-- A name that a typing import binds is bound by an assignment too, so the model is rejected.
#guard_msgs in
#eval expectNativeCaseError "module_ghost_import_shadows_alias" "'MyType' has another binding than its typing import"

-- A from-import of a model module rebinds an earlier assignment before the ghost reads it.
#guard_msgs in
#eval runNativeCase "module_ghost_from_import_shadows_alias" fun sigs _ => do
  let g ← findModuleGhost sigs "g"
  let some tp := g.type
    | throw <| IO.userError "module ghost 'g' lost its type"
  expect (toString tp == "import_test.service.module.ServiceClass") s!"ghost type: {tp}"

-- A rebind after the ghost does not change the binding the ghost resolved.
#guard_msgs in
#eval runNativeCase "module_ghost_rebind_after_ghost" fun sigs _ => do
  let counter ← findModuleGhost sigs "counter"
  let some tp := counter.type
    | throw <| IO.userError "module ghost 'counter' lost its type"
  expect (compare tp (SpecType.ident .none .builtinsInt) == .eq)
    "ghost type did not keep the binding from before the rebind"

-- Ghost scoping does not broaden module resolution: a forward alias reference
-- still errors.
#guard_msgs in
#eval expectNativeCaseError "forward_alias_rejected" "Unknown identifier LATER"

-- The main loop must not see pre-scanned import bindings early.
#guard_msgs in
#eval expectNativeCaseError "forward_import_rejected" "Unknown identifier MyAlias"

-- Import-created extern signatures keep their source position: the extern
-- rebinding of `T` must come after the class it shadows.
#guard_msgs in
#eval runNativeCase "extern_import_after_class" fun sigs _ => do
  let classIdx := sigs.findIdx? fun | .classDef d => d.name == "T" | _ => false
  let externIdx := sigs.findIdx? fun | .externTypeDecl n _ => n == "T" | _ => false
  let some c := classIdx | throw <| IO.userError "classDef T not found"
  let some e := externIdx | throw <| IO.userError "externTypeDecl T not found"
  unless c < e do
    throw <| IO.userError s!"extern T at {e} precedes classDef T at {c}"

-- Ghost scoping does not broaden module resolution: a forward class base
-- still errors.
#guard_msgs in
#eval expectNativeCaseError "forward_class_base_rejected" "Unknown base class 'B'"

-- A shadowed `ghost` name is an ordinary expression, not a declaration form.
#guard_msgs in
#eval runNativeCase "ghost_name_shadowed" fun sigs warnings => do
  let ghosts := sigs.filterMap fun | .ghostDecl g => some g.name | _ => none
  expect ghosts.isEmpty
    s!"a shadowed ghost name still produced ghost declaration(s): {ghosts}"
  expect (warnings.any (·.contains "skipped Expr at module level"))
    "the shadowed ghost call was not reported as a skipped expression"

-- A function definition shadowing `ghost` is detected like an assignment.
#guard_msgs in
#eval runNativeCase "ghost_name_shadowed_def" fun sigs warnings => do
  let ghosts := sigs.filterMap fun | .ghostDecl g => some g.name | _ => none
  expect ghosts.isEmpty
    s!"a def-shadowed ghost name still produced ghost declaration(s): {ghosts}"
  expect (warnings.any (·.contains "skipped Expr at module level"))
    "the def-shadowed ghost call was not reported as a skipped expression"

-- An import alias shadowing `ghost` is detected like an assignment.
#guard_msgs in
#eval runNativeCase "ghost_name_shadowed_import" fun sigs warnings => do
  let ghosts := sigs.filterMap fun | .ghostDecl g => some g.name | _ => none
  expect ghosts.isEmpty
    s!"an import-shadowed ghost name still produced ghost declaration(s): {ghosts}"
  expect (warnings.any (·.contains "skipped Expr at module level"))
    "the import-shadowed ghost call was not reported as a skipped expression"

-- A tuple assignment shadowing `ghost` is detected; the unsupported tuple
-- target itself stays a fatal error.
#guard_msgs in
#eval expectNativeCaseError "ghost_name_shadowed_tuple" "Unsupported target"

-- A module-level walrus binding shadowing `ghost` is detected like an
-- assignment.
#guard_msgs in
#eval runNativeCase "ghost_name_shadowed_walrus" fun sigs warnings => do
  let ghosts := sigs.filterMap fun | .ghostDecl g => some g.name | _ => none
  expect ghosts.isEmpty
    s!"a walrus-shadowed ghost name still produced ghost declaration(s): {ghosts}"
  expect (warnings.any (·.contains "skipped Expr at module level"))
    "the walrus-shadowed ghost call was not reported as a skipped expression"

-- A walrus nested inside another expression still shadows `ghost`.
#guard_msgs in
#eval runNativeCase "ghost_name_shadowed_walrus_nested" fun sigs warnings => do
  let ghosts := sigs.filterMap fun | .ghostDecl g => some g.name | _ => none
  expect ghosts.isEmpty
    s!"a nested-walrus-shadowed ghost name still produced ghost declaration(s): {ghosts}"
  expect (warnings.any (·.contains "skipped Expr at module level"))
    "the nested-walrus-shadowed ghost call was not reported as a skipped expression"

-- A walrus rebinding a type alias drops the stale binding: the later ghost
-- `type=` use is rejected instead of resolving to the pre-rebind value.
#guard_msgs in
#eval expectNativeCaseError "module_ghost_walrus_rebind_alias" "Unknown identifier MyInt"

-- A def rebinding a type alias drops the stale binding likewise.
#guard_msgs in
#eval expectNativeCaseError "module_ghost_def_shadows_alias" "Unknown identifier MyInt"

-- A tuple assignment rebinding a type alias drops the stale binding likewise
-- (the tuple target itself is also a fatal error in the main loop).
#guard_msgs in
#eval expectNativeCaseError "module_ghost_tuple_rebind_alias" "Unknown identifier MyInt"

-- A dotted un-aliased import binds its top-level name, so a scratch class of
-- that name drops its stale binding for later ghost types.
#guard_msgs in
#eval expectNativeCaseError "module_ghost_dotted_import_shadows_class"
  "Unknown identifier import_test"
end
