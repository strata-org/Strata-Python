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

/-- Golden DDM rendering of `Specs/operators.py`. Each precondition exercises a
    distinct operator arm of `transExpr`/`transCompare` so the expected program
    pins down the SpecExpr vocabulary every Python operator lowers to. -/
def expectedOps :=
#strata
program PythonSpecs;
type "OpRequest" = dict(
  a : ident("builtins.int") [required=true]
  b : ident("builtins.int") [required=true]
  c : ident("builtins.int") [required=true]
  score : ident("builtins.float") [required=true]
  items : ident("typing.List", ident("builtins.int")) [required=true]
  flag1 : ident("builtins.bool") [required=true]
  flag2 : ident("builtins.bool") [required=true])
function "arithmetic"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: kw : dict(
    a : ident("builtins.int") [required=true]
    b : ident("builtins.int") [required=true]
    c : ident("builtins.int") [required=true]
    score : ident("builtins.float") [required=true]
    items : ident("typing.List", ident("builtins.int")) [required=true]
    flag1 : ident("builtins.bool") [required=true]
    flag2 : ident("builtins.bool") [required=true])
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(add(kw[a], kw[b]) >=_int kw[c], "add in ge")
    ensure(sub(kw[a], kw[b]) >=_int kw[c], "sub in ge")
    ensure(mul(kw[a], kw[b]) >=_int kw[c], "mul in ge")
    ensure(floorDiv(kw[a], kw[b]) >=_int kw[c], "floordiv in ge")
    ensure(mod(kw[a], kw[b]) >=_int kw[c], "mod in ge")
    ensure(pow(kw[a], kw[b]) >=_int kw[c], "pow in ge")
    ensure(neg(kw[a]) >=_int kw[c], "neg in ge")
  ]
  postconditions: [
  ]
}
function "comparisons"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: kw : dict(
    a : ident("builtins.int") [required=true]
    b : ident("builtins.int") [required=true]
    c : ident("builtins.int") [required=true]
    score : ident("builtins.float") [required=true]
    items : ident("typing.List", ident("builtins.int")) [required=true]
    flag1 : ident("builtins.bool") [required=true]
    flag2 : ident("builtins.bool") [required=true])
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(pcmp("gt", kw[a], kw[b]), "gt")
    ensure(pcmp("lt", kw[a], kw[b]), "lt")
    ensure(pcmp("ne", kw[a], kw[b]), "ne")
    ensure(pcmp("eq", kw[a], 5), "eq int")
    ensure(pcmp("in", kw[a], kw[items]), "isin")
    ensure(pcmp("notIn", kw[a], kw[items]), "notin")
    ensure(kw[a] >=_int 1, "int ge")
    ensure(kw[a] <=_int 10, "int le")
    ensure(kw[score] >=_float "0.0", "float ge")
    ensure(kw[score] <=_float "1.0", "float le")
  ]
  postconditions: [
  ]
}
function "identity"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: kw : dict(
    a : ident("builtins.int") [required=true]
    b : ident("builtins.int") [required=true]
    c : ident("builtins.int") [required=true]
    score : ident("builtins.float") [required=true]
    items : ident("typing.List", ident("builtins.int")) [required=true]
    flag1 : ident("builtins.bool") [required=true]
    flag2 : ident("builtins.bool") [required=true])
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(pcmp("eq", kw[a], noneLit), "is none")
    ensure(pcmp("ne", kw[a], noneLit), "is not none")
  ]
  postconditions: [
  ]
}
function "boolean"{
  args: [
  ]
  kwonly: [
  ]
  kwargs: kw : dict(
    a : ident("builtins.int") [required=true]
    b : ident("builtins.int") [required=true]
    c : ident("builtins.int") [required=true]
    score : ident("builtins.float") [required=true]
    items : ident("typing.List", ident("builtins.int")) [required=true]
    flag1 : ident("builtins.bool") [required=true]
    flag2 : ident("builtins.bool") [required=true])
  return: ident("_types.NoneType")
  overload: false
  preconditions: [
    ensure(and(kw[flag1], kw[flag2]), "and")
    ensure(or(kw[flag1], kw[flag2]), "or")
    ensure(not(kw[flag1]), "not")
  ]
  postconditions: [
  ]
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
          (pythonFile := testDir / "operators.py")
          (searchPath := testDir)
          (.ofComponent (.ofString "operators"))
          |>.toBaseIO
      match r with
      | .ok (sigs, warnings) =>
        let pgm := toDDMProgram sigs
        let pgmCommands := pgm.commands.map (·.mapAnn (fun _ => ()))
        let expCommands := expectedOps.commands.map (·.mapAnn (fun _ => ()))
        if pgmCommands != expCommands then
          let mut diffMsg := s!"actual has {pgmCommands.size} commands, expected {expCommands.size}"
          for i in [:pgmCommands.size.max expCommands.size] do
            let actual := pgmCommands[i]?
            let expected := expCommands[i]?
            if actual != expected then
              diffMsg := s!"Command {i} differs."
              break
          throw <| IO.userError s!"Operator translation output mismatch. {diffMsg}"
        -- Every operator in operators.py is fully supported, so no warnings.
        if !warnings.isEmpty then
          let warnStr := warnings.foldl (init := "") fun acc w => s!"{acc}\n  {w}"
          throw <| IO.userError s!"Unexpected warnings:{warnStr}"
      | .error e =>
        throw <| IO.userError e

#guard_msgs in
#eval testCase
end
