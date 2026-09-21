/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

meta import all StrataPython.Specs.ToLaurel
meta import all StrataLaurel.Implementation.Grammar.AbstractToConcreteTreeTranslator

meta section

/-! # PySpec → Laurel Translation Tests

Tests for `signaturesToLaurel`: translating PySpec function/class/type
signatures into Laurel programs.
-/

namespace StrataPython.Specs.ToLaurel.Tests

open StrataPython (ModuleName)
open StrataPython.Specs
open StrataPython.Specs.ToLaurel
open Strata
open Strata.Laurel

/-! ## Test Infrastructure -/

private def testModule : ModuleName := .ofComponent (.ofString "test")

private def assertEq [BEq α] [ToString α] (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| .userError s!"expected: {expected}\n  actual: {actual}"

private def loc : SourceRange := default

private def identType (nm : PythonIdent) : SpecType :=
  SpecType.ident default nm

private def noneType : SpecType := SpecType.noneType default

private def mkUnion (types : Array SpecType) := SpecType.unionArray loc types

private def mkArg (name : String) (type : SpecType) (default : Option SpecDefault := none) : Arg :=
  { name, type, default := default }

private def mkFuncSig (name : String) (returnType : SpecType)
    (args : Array Arg := #[]) (kwonly : Array Arg := #[])
    : Signature :=
  .functionDecl {
    loc := loc, nameLoc := loc, name := name
    args := { args := args, kwonly := kwonly }
    returnType := returnType
    isOverload := false
    preconditions := #[], postconditions := #[]
  }

/-! ### Output Formatting -/

private def fmtHighType : HighType → String
  | .TVoid => "TVoid"
  | .TBool => "TBool"
  | .TInt => "TInt"
  | .TReal => "TReal"
  | .TFloat64 => "TFloat64"
  | .TString => "TString"
  | .TSet _ => "TSet"
  | .TMap _ _ => "TMap"
  | .UserDefined name => s!"UserDefined({name})"
  | .Applied _ _ => "Applied"
  | .Intersection _ => "Intersection"
  | .TBv n => s!"TBv({n})"
  | .Unknown => "Unknown"
  | .MultiValuedExpr _ => "MultiValuedExpr"
  -- The `.TVar` arm keeps `fmtHighType` total over `HighType`. No SPFE ToLaurel path
  -- constructs a `.TVar` — Python has no generic-type-parameter surface — so there is no
  -- end-to-end translation that produces one to pin; the guard below pins just this arm.
  | .TVar name => s!"TVar({name})"

private def fmtParam (p : Parameter) : String :=
  s!"{p.name}:{fmtHighType p.type.val}"

private def fmtProc (p : Procedure) : String :=
  let inputs := ", ".intercalate (p.inputs.map fmtParam)
  let returns := ", ".intercalate (p.outputs.map fmtParam)
  if returns.isEmpty then
    s!"procedure {p.name}({inputs})"
  else
    s!"procedure {p.name}({inputs}) returns({returns})"

private def fmtTypeDef : TypeDefinition → String
  | .Composite ty => s!"type {ty.name}"
  | .Constrained ty => s!"constrained {ty.name}"
  | .Datatype ty => s!"datatype {ty.name}"
  | .Alias ty => s!"alias {ty.name}"
  | .Opaque ty => s!"opaque {ty.name}"

/-! ### Test Runners -/

/-- Run signaturesToLaurel and print formatted output.
    Prints warnings (if any) before procedures so `#guard_msgs` can verify them. -/
private def runTest (sigs : Array Signature) (moduleName : ModuleName := testModule) : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs moduleName
  for err in result.errors do
    IO.println s!"warning: {err.phase}.{err.kind.category}: {err.message.message}"
  for td in result.program.types do
    IO.println (fmtTypeDef td)
  for proc in result.program.staticProcedures do
    IO.println (fmtProc proc)

/-- Run signaturesToLaurel expecting errors. Print error messages. -/
private def runTestErrors (sigs : Array Signature) (moduleName : ModuleName := testModule) : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs moduleName
  assert! result.errors.size > 0
  for err in result.errors do
    IO.println err.message.message

/-- Run signaturesToLaurel and print warning kinds (phase.category: message). -/
private def runTestWarningKinds (sigs : Array Signature) (moduleName : ModuleName := testModule) : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs moduleName
  assert! result.errors.size > 0
  for err in result.errors do
    IO.println s!"{err.phase}.{err.kind.category}: {err.message.message}"

/-- Helper to make a function signature with preconditions. -/
private def mkFuncSigWithPrecond (name : String) (returnType : SpecType)
    (preconditions : Array Assertion) (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc := loc, nameLoc := loc, name := name
    args := { args := args, kwonly := #[] }
    returnType := returnType
    isOverload := false
    preconditions := preconditions, postconditions := #[]
  }

/-! ## All function params and returns map to Any -/

/--
info: procedure test_returns_int(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_returns_bool(a:UserDefined(Any), b:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_returns_real(flag:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_with_kwonly(x:UserDefined(Any), verbose:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "returns_int" (identType .builtinsInt)
    (args := #[mkArg "x" (identType .builtinsStr)]),
  mkFuncSig "returns_bool" (identType .builtinsBool)
    (args := #[mkArg "a" (identType .builtinsInt),
               mkArg "b" (identType .builtinsFloat)]),
  mkFuncSig "returns_real" (identType .builtinsFloat)
    (args := #[mkArg "flag" (identType .builtinsBool)]),
  mkFuncSig "with_kwonly" (identType .builtinsStr)
    (args := #[mkArg "x" (identType .builtinsInt)])
    (kwonly := #[mkArg "verbose" (identType .builtinsBool) (default := some .none)])
]

/-! ## Complex types (Any, List, Dict, bytes) -/

/--
info: procedure test_takes_any(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_takes_list(items:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_returns_dict() returns(result:UserDefined(Any))
procedure test_typed_list() returns(result:UserDefined(Any))
procedure test_typed_dict() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "takes_any" (identType .builtinsInt)
    (args := #[mkArg "x" (identType .typingAny)]),
  mkFuncSig "takes_list" (identType .builtinsBool)
    (args := #[mkArg "items" (identType .typingList)]),
  mkFuncSig "returns_dict" (identType .typingDict),
  mkFuncSig "typed_list"
    (SpecType.ident loc .typingList #[identType .builtinsStr]),
  mkFuncSig "typed_dict"
    (SpecType.ident loc .typingDict
      #[identType .builtinsStr, identType .builtinsInt])
]

/-! ## Literal types, TypedDict, and string-literal unions → Any -/

/--
info: procedure test_int_literal_ret() returns(result:UserDefined(Any))
procedure test_str_literal_ret() returns(result:UserDefined(Any))
procedure test_typed_dict_ret() returns(result:UserDefined(Any))
procedure test_str_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "int_literal_ret" (SpecType.intLiteral loc 42),
  mkFuncSig "str_literal_ret"
    (SpecType.stringLiteral loc "hello"),
  mkFuncSig "typed_dict_ret"
    (SpecType.typedDict loc #["f"]
      #[identType .builtinsStr] #[true]),
  mkFuncSig "str_enum"
    (mkUnion #[SpecType.stringLiteral loc "A", SpecType.stringLiteral loc "B",
               SpecType.stringLiteral loc "C"])
]

/-! ## Optional type patterns (Union[None, T]) → Any -/

/--
info: procedure test_opt_str() returns(result:UserDefined(Any))
procedure test_opt_int() returns(result:UserDefined(Any))
procedure test_opt_bool(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_opt_typed_dict() returns(result:UserDefined(Any))
procedure test_opt_str_enum() returns(result:UserDefined(Any))
procedure test_opt_int_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "opt_str"
    (mkUnion #[noneType, identType .builtinsStr]),
  mkFuncSig "opt_int"
    (mkUnion #[noneType, identType .builtinsInt]),
  mkFuncSig "opt_bool"
    (mkUnion #[noneType, identType .builtinsBool])
    (args := #[mkArg "x"
      (mkUnion #[noneType, identType .builtinsStr])]),
  mkFuncSig "opt_typed_dict"
    (mkUnion #[noneType,
      SpecType.typedDict loc #["x"] #[identType .builtinsStr] #[true]]),
  mkFuncSig "opt_str_enum"
    (mkUnion #[noneType, SpecType.stringLiteral loc "A",
               SpecType.stringLiteral loc "B"]),
  mkFuncSig "opt_int_enum"
    (mkUnion #[noneType, SpecType.intLiteral loc 1, SpecType.intLiteral loc 2])
]

/-! ## Error cases (updated to verify MessageKind) -/

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f"
    (identType (PythonIdent.ofComponent "foo" "Bar"))]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f"
    (mkUnion #[identType .builtinsStr,
               identType .builtinsInt])]

/--
info: warning: pySpecToLaurel.unsupportedUnion: No type tester for 'foo.Bar' in type 'Union[_types.NoneType, foo.Bar]'
procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[mkFuncSig "f"
    (mkUnion #[noneType,
      identType (PythonIdent.ofComponent "foo" "Bar")])]

/-! ## Class and type definitions -/

/--
info: type test_MyClass
type test_MyAlias
procedure test_my_func(x:UserDefined(Any), y:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_MyClass@get_value() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "my_func" (identType .builtinsBool)
    (args := #[mkArg "x" (identType .builtinsInt),
               mkArg "y" (identType .builtinsStr) (some .none)]),
  .classDef {
    loc := loc, name := "MyClass"
    methods := #[
      { loc := loc, nameLoc := loc, name := "get_value"
        args := { args := #[mkArg "self" (identType .builtinsStr)], kwonly := #[] }
        returnType := identType .builtinsStr
        isOverload := false
        preconditions := #[]
        postconditions := #[] }
    ]
  },
  .typeDef {
    loc := loc, nameLoc := loc
    name := "MyAlias"
    definition := identType .builtinsStr
  }
]

/-! ## NoneType and void return -/

/--
info: procedure test_returns_none() returns(result:UserDefined(Any))
procedure test_takes_none(x:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  mkFuncSig "returns_none" noneType,
  mkFuncSig "takes_none" noneType
    (args := #[mkArg "x" noneType])
]

/-! ## Class types as UserDefined -/

/--
info: type test_Foo
procedure test_uses_class(x:UserDefined(test_Foo)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  .classDef {
    loc := loc, name := "Foo"
    methods := #[]
  },
  mkFuncSig "uses_class" (identType (.mkRaw testModule "Foo"))
    (args := #[mkArg "x" (identType (.mkRaw testModule "Foo"))])
]

/-! ## Empty input -/

#guard_msgs in
#eval runTest #[]

/-! ## Overload dispatch and method registry -/

/-- Helper to make an @overload function signature. -/
private def mkOverload (name : String) (returnType : SpecType)
    (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc := loc, nameLoc := loc, name := name
    args := { args := args, kwonly := #[] }
    returnType := returnType
    isOverload := true
    preconditions := #[], postconditions := #[]
  }

/-- Run signaturesToLaurel and print the full result: Laurel output,
    dispatch table, and method registry. Sorts by key for stable output. -/
private def runFullTest (sigs : Array Signature) (moduleName : ModuleName := testModule) : IO Unit := do
  let result := signaturesToLaurel "<test>" sigs moduleName
  if result.errors.size > 0 then
    IO.println s!"errors: {result.errors.size}"
    for err in result.errors do
      IO.println s!"  {err.message.message}"
  for td in result.program.types do
    IO.println (fmtTypeDef td)
  for proc in result.program.staticProcedures do
    IO.println (fmtProc proc)
  let overloadEntries := result.overloads.toArray.qsort (·.1 < ·.1)
  for (funcName, fnOverloads) in overloadEntries do
    IO.println s!"dispatch {funcName}:"
    let sorted := fnOverloads.entries.toArray.qsort (·.1 < ·.1)
    for (litVal, retType) in sorted do
      IO.println s!"  \"{litVal}\" -> {retType}"

/-- Run extractOverloads and print the dispatch table. -/
private def runDispatchTest (sigs : Array Signature) : IO Unit := do
  let (overloads, errors) := extractOverloads "<test>" sigs
  if errors.size > 0 then
    IO.println s!"errors: {errors.size}"
    for err in errors do
      IO.println s!"  {err.message.message}"
  let entries := overloads.toArray.qsort (·.1 < ·.1)
  for (funcName, fnOverloads) in entries do
    IO.println s!"dispatch {funcName}:"
    let sorted := fnOverloads.entries.toArray.qsort (·.1 < ·.1)
    for (litVal, retType) in sorted do
      IO.println s!"  \"{litVal}\" -> {retType}"

/-! ### Signature Builders

Concise helpers for constructing PySpec signatures.
Type shorthands: `str`, `int`, `bool_`, `float_`, `bytes`, `any`, `none_`, `list_`, `dict_`.
-/

private def str := SpecType.ident loc .builtinsStr
private def int := SpecType.ident loc .builtinsInt
private def bool_ := SpecType.ident loc .builtinsBool
private def float_ := SpecType.ident loc .builtinsFloat
private def bytes := SpecType.ident loc .builtinsBytes
private def bytearray := SpecType.ident loc .builtinsBytearray
private def complex_ := SpecType.ident loc .builtinsComplex
private def any := SpecType.ident loc .typingAny
private def none_ := SpecType.noneType loc
private def list_ := SpecType.ident loc .typingList
private def dict_ := SpecType.ident loc .typingDict
private def listOf (t : SpecType) := SpecType.ident loc .typingList #[t]
private def dictOf (k v : SpecType) := SpecType.ident loc .typingDict #[k, v]
private def pyClass (name : String) := SpecType.ident loc (.mkRaw testModule name)
private def externIdent (mod name : String) := PythonIdent.mkRaw (.ofString! mod) name

private def arg (name : String) (type : SpecType) (default : Option SpecDefault := none) : Arg :=
  { name, type, default := default }
private def optArg (name : String) (type : SpecType) : Arg :=
  { name, type, default := some .none }

private def func (name : String) (ret : SpecType) (args : Array Arg := #[])
    (kwonly : Array Arg := #[])
    (preconditions : Array Assertion := #[])
    (postconditions : Array SpecExpr := #[])
    (kwargs : Option (String × SpecType) := none) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args, kwonly, kwargs }
    returnType := ret
    isOverload := false
    preconditions, postconditions
  }

private def overload (name : String) (ret : SpecType) (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args, kwonly := #[] }
    returnType := ret
    isOverload := true
    preconditions := #[], postconditions := #[]
  }

private def classDef (name : String) (methods : Array FunctionDecl := #[]) : Signature :=
  .classDef { loc, name, methods }

private def method (name : String) (ret : SpecType) (args : Array Arg := #[]) : FunctionDecl :=
  { loc, nameLoc := loc, name
    args := { args := #[arg "self" str] ++ args, kwonly := #[] }
    returnType := ret
    isOverload := false
    preconditions := #[], postconditions := #[] }

private def typeDef (name : String) (definition : SpecType) : Signature :=
  .typeDef { loc, nameLoc := loc, name, definition }

private def externType (name : String) (ident : PythonIdent) : Signature :=
  .externTypeDecl name ident

/-! ## All function params and returns map to Any -/

/--
info: procedure test_returns_int(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_returns_bool(a:UserDefined(Any), b:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_returns_real(flag:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_with_kwonly(x:UserDefined(Any), verbose:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "returns_int" int (args := #[arg "x" str]),
  func "returns_bool" bool_ (args := #[arg "a" int, arg "b" float_]),
  func "returns_real" float_ (args := #[arg "flag" bool_]),
  func "with_kwonly" str
    (args := #[arg "x" int])
    (kwonly := #[optArg "verbose" bool_])
]

/-! ## Complex types (Any, List, Dict, bytes) -/

/--
info: procedure test_takes_any(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_takes_list(items:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_returns_dict() returns(result:UserDefined(Any))
procedure test_typed_list() returns(result:UserDefined(Any))
procedure test_typed_dict() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "takes_any" int (args := #[arg "x" any]),
  func "takes_list" bool_ (args := #[arg "items" list_]),
  func "returns_dict" dict_,
  func "typed_list" (listOf str),
  func "typed_dict" (dictOf str int)
]

/-! ## Literal types, TypedDict, and string-literal unions → Any -/

/--
info: procedure test_int_literal_ret() returns(result:UserDefined(Any))
procedure test_str_literal_ret() returns(result:UserDefined(Any))
procedure test_typed_dict_ret() returns(result:UserDefined(Any))
procedure test_str_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "int_literal_ret" (SpecType.intLiteral loc 42),
  func "str_literal_ret" (SpecType.stringLiteral loc "hello"),
  func "typed_dict_ret" (SpecType.typedDict loc #["f"] #[str] #[true]),
  func "str_enum"
    (mkUnion #[SpecType.stringLiteral loc "A", SpecType.stringLiteral loc "B",
               SpecType.stringLiteral loc "C"])
]

/-! ## Optional type patterns (Union[None, T]) → Any -/

/--
info: procedure test_opt_str() returns(result:UserDefined(Any))
procedure test_opt_int() returns(result:UserDefined(Any))
procedure test_opt_bool(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_opt_typed_dict() returns(result:UserDefined(Any))
procedure test_opt_str_enum() returns(result:UserDefined(Any))
procedure test_opt_int_enum() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "opt_str" (mkUnion #[none_, str]),
  func "opt_int" (mkUnion #[none_, int]),
  func "opt_bool" (mkUnion #[none_, bool_])
    (args := #[arg "x" (mkUnion #[none_, str])]),
  func "opt_typed_dict"
    (mkUnion #[none_, SpecType.typedDict loc #["x"] #[str] #[true]]),
  func "opt_str_enum"
    (mkUnion #[none_, SpecType.stringLiteral loc "A",
               SpecType.stringLiteral loc "B"]),
  func "opt_int_enum"
    (mkUnion #[none_, SpecType.intLiteral loc 1, SpecType.intLiteral loc 2])
]

/-! ## Error cases (updated to verify WarningKind) -/

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (SpecType.ident loc (PythonIdent.ofComponent "foo" "Bar"))]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[str, int])]

/--
info: warning: pySpecToLaurel.unsupportedUnion: No type tester for 'foo.Bar' in type 'Union[_types.NoneType, foo.Bar]'
procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f"
    (mkUnion #[none_, SpecType.ident loc (PythonIdent.ofComponent "foo" "Bar")])]

/-! ## Class and type definitions -/

/--
info: type test_MyClass
type test_MyAlias
procedure test_my_func(x:UserDefined(Any), y:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_MyClass@get_value() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "my_func" bool_ (args := #[arg "x" int, optArg "y" str]),
  classDef "MyClass" (methods := #[method "get_value" str]),
  typeDef "MyAlias" str
]

/-! ## NoneType and void return -/

/--
info: procedure test_returns_none() returns(result:UserDefined(Any))
procedure test_takes_none(x:UserDefined(Any)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  func "returns_none" none_,
  func "takes_none" none_ (args := #[arg "x" none_])
]

/-! ## Class types as UserDefined -/

/--
info: type test_Foo
procedure test_uses_class(x:UserDefined(test_Foo)) returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest #[
  classDef "Foo",
  func "uses_class" (pyClass "Foo") (args := #[arg "x" (pyClass "Foo")])
]

/-! ## Empty input -/

#guard_msgs in
#eval runTest #[]

/-! ## Overload dispatch and method registry -/

-- A realistic service spec: extern type imports, a factory function with
-- overloads dispatching on string literals, a service class with methods,
-- and a regular function.
/--
info: type test_SvcClient
procedure test_SvcClient@do_thing(x:UserDefined(Any)) returns(result:UserDefined(Any))
procedure test_helper() returns(result:UserDefined(Any))
dispatch create_client:
  "svc_a" -> mod.client.SvcClient
  "svc_b" -> mod.other.OtherClient
-/
#guard_msgs in
#eval runFullTest #[
  externType "SvcClient" (externIdent "mod.client" "SvcClient"),
  externType "OtherClient" (externIdent "mod.other" "OtherClient"),
  overload "create_client"
    (SpecType.ident loc (externIdent "mod.client" "SvcClient"))
    (args := #[arg "name" (SpecType.stringLiteral loc "svc_a")]),
  overload "create_client"
    (SpecType.ident loc (externIdent "mod.other" "OtherClient"))
    (args := #[arg "name" (SpecType.stringLiteral loc "svc_b")]),
  classDef "SvcClient" (methods := #[method "do_thing" int (args := #[arg "x" str])]),
  func "helper" bool_
]

-- Overloads with locally-defined class return types.
/--
info: type test_Alpha
type test_Beta
dispatch make:
  "a" -> test.Alpha
  "b" -> test.Beta
-/
#guard_msgs in
#eval runFullTest #[
  classDef "Alpha",
  classDef "Beta",
  overload "make" (pyClass "Alpha")
    (args := #[arg "kind" (SpecType.stringLiteral loc "a")]),
  overload "make" (pyClass "Beta")
    (args := #[arg "kind" (SpecType.stringLiteral loc "b")])
]

-- extractOverloads only processes externTypeDecl and @overload functions,
-- ignoring class defs, type defs, and regular functions.
/--
info: dispatch factory:
  "x" -> pkg.Foo
-/
#guard_msgs in
#eval runDispatchTest #[
  externType "Foo" (externIdent "pkg" "Foo"),
  overload "factory"
    (SpecType.ident loc (externIdent "pkg" "Foo"))
    (args := #[arg "k" (SpecType.stringLiteral loc "x")]),
  classDef "Ignored",
  func "also_ignored" int,
  typeDef "AlsoIgnored" str
]

-- Overload with no arguments produces an error.
/--
info: errors: 1
  Overloaded function 'bad' has no arguments
-/
#guard_msgs in
#eval runDispatchTest #[
  overload "bad" str
]

-- externTypeDecl produces no errors (regression test).
#guard_msgs in
#eval runFullTest #[externType "Foo" (externIdent "pkg" "Foo")]

/-! ## Nested dictionary access -/

-- Nested dictionaries retain their source type and lower through the logical
-- map at every level; the precondition text is pinned in full.
#eval do
  let kwargsTy := SpecType.typedDict loc #["Outer"] #[dict_] #[true]
  let result := signaturesToLaurel "<test>" #[
    func "f" str
      (args := #[arg "x" str])
      (kwargs := some ("kwargs", kwargsTy))
      (preconditions := #[{
        message := #[.str "nested dict"]
        formula := .intGe
          (.getIndex (.getIndex (.var "kwargs" loc) "Outer" loc) "Inner" loc)
          (.intLit 0 loc)
          loc
      }])
  ] testModule
  assertEq result.errors.size 0
  match result.program.staticProcedures with
  | proc :: _ =>
    -- A declared parameter type is also a precondition; pin only the
    -- schema and user conditions.
    let pinned := proc.preconditions.filter fun (c : Strata.Laurel.Condition) =>
      match c.summary with
      | some summary => !summary.startsWith "declared type of parameter "
      | none => true
    let preStr := String.intercalate "\n"
      (pinned.map fun (c : Strata.Laurel.Condition) =>
        toString (Strata.Laurel.formatStmtExpr c.condition))
    assertEq preStr (
      "true & (DictStrAny_keysAllowed(kwargs, " ++
      "ListStr_cons(\"Outer\", ListStr_nil())) & " ++
      "forall(py$schema_key_kwargs: string)" ++
      "{select(PySpecDict_modelOf(kwargs), py$schema_key_kwargs)} => " ++
      "PySpecDictValue..isPresent(select(" ++
      "PySpecDict_modelOf(kwargs), py$schema_key_kwargs)) ==> " ++
      "false | py$schema_key_kwargs == \"Outer\")\n" ++
      "true & PySpecDictValue..isPresent(select(" ++
      "PySpecDict_modelOf(kwargs), \"Outer\"))\n" ++
      "true & (PySpecDictValue..isPresent(select(" ++
      "PySpecDict_modelOf(kwargs), \"Outer\")) ==> " ++
      "Any..isfrom_DictStrAny(PySpecDictValue..value!(select(" ++
      "PySpecDict_modelOf(kwargs), \"Outer\"))) & " ++
      "forall(py$schema_dict_kwargs_Outer: string)" ++
      "{select(PySpecDict_modelOf(Any..as_Dict!(PySpecDictValue..value!(select(" ++
      "PySpecDict_modelOf(kwargs), \"Outer\")))), py$schema_dict_kwargs_Outer)} => " ++
      "true)\n" ++
      "Any_to_bool(PGe(PySpecDictValue..value(select(" ++
      "PySpecDict_modelOf(Any..as_Dict!(PySpecDictValue..value(select(" ++
      "PySpecDict_modelOf(kwargs), \"Outer\")))), \"Inner\")), from_int(0)))")
  | [] => throw <| IO.userError "no procedures"

/-! ## Warning kind tests -/

-- bytes, bytearray, complex now map to Any (matching PythonToLaurel)
/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" bytes]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" bytearray]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" complex_]

-- Optional patterns now map to Any without warnings
/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, float_])]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, list_])]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, dict_])]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, any])]

/--
info: procedure test_f() returns(result:UserDefined(Any))
-/
#guard_msgs in
#eval runTest
  #[func "f" (mkUnion #[none_, bytes])]

-- Precondition: placeholderExpr
/--
info: pySpecToLaurel.placeholderExpr: Placeholder expression not translatable
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .placeholder loc }])]

-- Precondition: floatLiteral
/--
info: pySpecToLaurel.floatLiteral: Float literals not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .floatLit "3.14" loc }])]

-- Precondition: isinstanceUnsupported
/--
info: pySpecToLaurel.isinstanceUnsupported: isinstance check for 'MyType' not yet supported in preconditions
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (preconditions := #[{ message := #[], formula := .isInstanceOf (.var "x" loc) "MyType" loc }])]


-- Declaration: missingMethodSelf
/--
info: pySpecToLaurel.missingMethodSelf: Method 'bad_method' has no arguments (expected 'self' as first parameter)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[.classDef {
    loc := loc, name := "C"
    methods := #[
      { loc := loc, nameLoc := loc, name := "bad_method"
        args := { args := #[], kwonly := #[] }
        returnType := str
        isOverload := false
        preconditions := #[], postconditions := #[] }
    ]
  }]

-- Declaration: non-TypedDict `**kwargs` is a fatal user-code error
/--
info: pySpecToLaurel.kwargsExpansionError: **kw must use Unpack[TypedDict], got 'builtins.str'; **kw cannot be modeled
-/
#guard_msgs in
#eval runTestWarningKinds
  #[.functionDecl {
    loc := loc, nameLoc := loc, name := "f"
    args := { args := #[], kwonly := #[],
              kwargs := some ("kw", str) }
    returnType := str
    isOverload := false
    preconditions := #[], postconditions := #[]
  }]

-- Declaration: modeled postconditions are rejected to preserve soundness
/--
info: pySpecToLaurel.unsupportedPostcondition: Modeled @ensures cannot be verified for 'test_f': result >=_int 0. A PySpec declaration is a bodyless model, so Strata cannot verify this postcondition against an implementation and will not assume it at call sites. Loading a PySpec module containing @ensures aborts analysis even if the affected function is unused. Use @admit to accept the postcondition as an unverified modeling assumption, or model the function with a real body if the property must be checked.
-/
#guard_msgs in
#eval runTestWarningKinds
  #[func "f" str
    (postconditions := #[.intGe (.var "result" loc) (.intLit 0 loc) loc])]

-- Overload: overloadNoArgs
/--
info: pySpecToLaurel.overloadNoArgs: Overloaded function 'bad' has no arguments
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str]

-- Overload: union arg type (not a singleton) → overloadArgNotStringLiteral
/--
info: pySpecToLaurel.overloadArgNotStringLiteral: Overloaded function 'bad': first argument type 'Union[Literal["a"], Literal["b"]]' is not a string literal (only string literal dispatch is currently supported)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str
    (args := #[arg "x" (mkUnion #[SpecType.stringLiteral loc "a", SpecType.stringLiteral loc "b"])])]

-- Overload: overloadArgNotStringLiteral
/--
info: pySpecToLaurel.overloadArgNotStringLiteral: Overloaded function 'bad': first argument type 'builtins.str' is not a string literal (only string literal dispatch is currently supported)
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad" str
    (args := #[arg "x" str])]

-- Overload: union return type (not a singleton) → overloadReturnNotClass
/--
info: pySpecToLaurel.overloadReturnNotClass: Overloaded function 'bad': return type 'Union[builtins.int, builtins.str]' is not a class type
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad"
    (mkUnion #[str, int])
    (args := #[arg "x" (SpecType.stringLiteral loc "a")])]

-- Overload: overloadReturnNotClass
/--
info: pySpecToLaurel.overloadReturnNotClass: Overloaded function 'bad': return type 'Literal["hello"]' is not a class type
-/
#guard_msgs in
#eval runTestWarningKinds
  #[overload "bad"
    (SpecType.stringLiteral loc "hello")
    (args := #[arg "x" (SpecType.stringLiteral loc "a")])]

/-! ## Precondition integration tests

Run `signaturesToLaurel` with a precondition and check the rendered
precondition text (via `getPreconditions`) for the expected Laurel
operations, catching wrong-operation and silently-dropped-precondition bugs. -/

/-- The first procedure's spec as text: each checked precondition as
    `assert <cond>`, each free postcondition as `assume <cond>`. -/
private def getSpecText (result : TranslationResult) : String :=
  match result.program.staticProcedures with
  | proc :: _ =>
    let pres := proc.preconditions.map fun c =>
      s!"assert {toString (Strata.Laurel.formatStmtExpr c.condition)}"
    let posts := match proc.body with
      | .Opaque postconditions _ _ =>
        postconditions.map fun c =>
          s!"assume {toString (Strata.Laurel.formatStmtExpr c.condition)}"
      | _ => []
    String.intercalate ";\n" (pres ++ posts)
  | [] => ""

/-- Render the first procedure's preconditions as `requires <cond> summary "…"`
    lines, one per `Condition`. -/
private def getPreconditions (result : TranslationResult) : String :=
  match result.program.staticProcedures with
  | proc :: _ =>
    String.intercalate "\n" (proc.preconditions.map fun c =>
      let summ := match c.summary with | some s => s!" summary \"{s}\"" | none => ""
      s!"requires {toString (Strata.Laurel.formatStmtExpr c.condition)}{summ}")
  | [] => ""

/-- Caller-visible postconditions on the first generated procedure. -/
private def getPostconditions (result : TranslationResult) : List Condition :=
  match result.program.staticProcedures with
  | proc :: _ => match proc.body with
    | .Opaque postconditions _ _ => postconditions
    | _ => []
  | [] => []

/-- A declared parameter type is a generated precondition. These tests pin
    the *user* preconditions, so drop the generated ones. -/
private def userPreconditions (result : TranslationResult) : List Condition :=
  match result.program.staticProcedures with
  | proc :: _ => proc.preconditions.filter fun c =>
      match c.summary with
      | some summary => !summary.startsWith "declared type of parameter "
      | none => true
  | [] => []

/-- `getPreconditions` text without the generated declared-parameter-type
    lines, for exact pins of the schema and user conditions. -/
private def userPreconditionText (pre : String) : String :=
  String.intercalate "\n" <|
    (pre.splitOn "\n").filter (fun l => !l.contains "declared type of parameter")

/-- True when the `@admit` predicate reached callers as a *free* postcondition:
    assumed at every call site, never checked. That is what `@admit` means, and
    for a bodiless model a free postcondition is where it has to live. -/
private def hasAdmittedPostcondition (result : TranslationResult) : Bool :=
  (getPostconditions result).any fun c =>
    c.mode == .Assume &&
      (match c.summary with
       | some summary => summary.startsWith "admitted postcondition of "
       | none => false)

/-- True when no *user* contract reached the caller-visible postconditions.
    The generated ones always do: a PySpec model is bodiless, so its declared
    return type and any module-ghost type are free postconditions rather than
    in-body assumes. Those carry generated summaries; a user contract carries
    an `admitted postcondition` summary or none at all. -/
private def noUserPostconditions (result : TranslationResult) : Bool :=
  (getPostconditions result).all fun c =>
    match c.summary with
    | some s => s.startsWith "return type of " || s.startsWith "declared type of module ghost "
    | none => false

private def formatCondition (condition : Condition) : String :=
  toString (Strata.Laurel.formatStmtExpr condition.condition)

/-- Translate a single function with preconditions. -/
private def translatePrecondResult (preconditions : Array Assertion)
    (args : Array Arg := #[]) : TranslationResult :=
  signaturesToLaurel "<test>" #[
    .functionDecl {
      loc, nameLoc := loc, name := "f"
      args := { args, kwonly := #[] }
      returnType := str, isOverload := false
      preconditions, postconditions := #[]
    }] testModule

/-- Translate a single function with preconditions and return
    `(preconditionText, errorCount)`. User `@requires` lower to caller-checked
    procedure preconditions, so the integration assertions inspect that text. -/
private def translatePrecond (preconditions : Array Assertion)
    (args : Array Arg := #[]) : String × Nat :=
  let result := translatePrecondResult preconditions args
  (getPreconditions result, result.errors.size)

-- enumMember: or and eq via `|` and `==` infix syntax
#eval do
  let (pre, errs) := translatePrecond
    #[{ message := #[], formula :=
          .enumMember (.var "x" loc) #["a", "b"] loc }]
    (args := #[arg "x" str])
  assert! errs == 0
  -- `or` renders as `|`, `eq` as `==`; would have been `<=` before fix #1
  assert! pre.contains " | "
  assert! pre.contains "=="
  assert! !pre.contains "<="

-- implies: `==>` infix syntax
#eval do
  let (pre, errs) := translatePrecond
    #[{ message := #[], formula :=
          .implies
            (.intGe (.var "x" loc) (.intLit 0 loc) loc)
            (.intGe (.var "y" loc) (.intLit 0 loc) loc)
            loc }]
    (args := #[arg "x" str, arg "y" str])
  assert! errs == 0
  -- `implies` renders as `==>`; would have been `<=` before fix #1
  assert! pre.contains "==>"

-- containsKey on kwargs checks presence in the logical map.
#eval do
  let kwargsTy := SpecType.typedDict loc #["key"] #[str] #[false]
  let result := signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := #[], kwonly := #[],
                kwargs := some ("kw", kwargsTy) }
      returnType := str, isOverload := false
      preconditions := #[{
        message := #[], formula :=
          .containsKey (.var "kw" loc) "key" loc }]
      postconditions := #[] }] testModule
  let spec := getSpecText result
  let pre := getPreconditions result
  assertEq result.errors.size 0
  assertEq spec (
    "assert true & (DictStrAny_keysAllowed(kw, ListStr_cons(\"key\", ListStr_nil())) & " ++
    "forall(py$schema_key_kw: string){select(PySpecDict_modelOf(kw), py$schema_key_kw)} => " ++
    "PySpecDictValue..isPresent(select(PySpecDict_modelOf(kw), py$schema_key_kw)) ==> " ++
    "false | py$schema_key_kw == \"key\");\n" ++
    "assert true & (PySpecDictValue..isPresent(select(PySpecDict_modelOf(kw), \"key\")) ==> " ++
    "Any..isfrom_str(PySpecDictValue..value!(select(PySpecDict_modelOf(kw), \"key\"))));\n" ++
    "assert PySpecDictValue..isPresent(select(PySpecDict_modelOf(kw), \"key\"));\n" ++
    "assume Any..isfrom_str(result)")
  assertEq pre (
    "requires true & (DictStrAny_keysAllowed(kw, " ++
    "ListStr_cons(\"key\", ListStr_nil())) & forall(py$schema_key_kw: string)" ++
    "{select(PySpecDict_modelOf(kw), py$schema_key_kw)} => " ++
    "PySpecDictValue..isPresent(select(PySpecDict_modelOf(kw), py$schema_key_kw)) ==> " ++
    "false | py$schema_key_kw == \"key\") " ++
    "summary \"'kw' must contain only declared keys\"\n" ++
    "requires true & " ++
    "(PySpecDictValue..isPresent(select(PySpecDict_modelOf(kw), \"key\")) ==> " ++
    "Any..isfrom_str(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(kw), \"key\")))) " ++
    "summary \"'kw.key' must satisfy its declared type\"\n" ++
    "requires PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(kw), \"key\")) summary \"precondition 0\"")

-- Ordinary TypedDict parameters are structurally open: declared fields retain
-- their required/type checks without an allowed-key quantifier.
#eval do
  let itemTy := SpecType.typedDict loc #["name"] #[str] #[true]
  let result := signaturesToLaurel "<test>"
    #[func "f" str (args := #[arg "item" itemTy])] testModule
  let pre := getPreconditions result
  let pre := userPreconditionText pre
  assertEq result.errors.size 0
  assertEq pre (
    "requires Any..isfrom_DictStrAny(item) & " ++
    "PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(item)), \"name\")) " ++
    "summary \"'item' must contain required key 'name'\"\n" ++
    "requires Any..isfrom_DictStrAny(item) & " ++
    "(PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(item)), \"name\")) ==> " ++
    "Any..isfrom_str(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(item)), \"name\")))) " ++
    "summary \"'item.name' must satisfy its declared type\"")

-- Equality between a dict-valued lookup (statically `Any`) and a dict-typed
-- parameter routes through extensional `PySpecAny_scalarEq`, not `PEq`.
#eval do
  let (pre, errs) := translatePrecond
    #[{ message := #[], formula :=
          .pcmp .eq
            (.getIndex (.var "Items" loc) "config" loc)
            (.var "Expected" loc)
            loc }]
    (args := #[arg "Items" (dictOf str any), arg "Expected" (dictOf str any)])
  let pre := userPreconditionText pre
  assertEq errs 0
  assertEq pre (
    "requires Any..isfrom_DictStrAny(Items) & " ++
    "forall(py$schema_Items: string)" ++
    "{select(PySpecDict_modelOf(Any..as_Dict!(Items)), py$schema_Items)} => " ++
    "true summary \"'Items' must satisfy its declared dictionary type\"\n" ++
    "requires Any..isfrom_DictStrAny(Expected) & " ++
    "forall(py$schema_Expected: string)" ++
    "{select(PySpecDict_modelOf(Any..as_Dict!(Expected)), py$schema_Expected)} => " ++
    "true summary \"'Expected' must satisfy its declared dictionary type\"\n" ++
    "requires PySpecAny_scalarEq(PySpecDictValue..value(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(Items)), \"config\")), Expected) " ++
    "summary \"precondition 0\"")

-- A dynamic dictionary subscript `d[k]` lowers through the logical map with a
-- checked string key.
#eval do
  let (pre, errs) := translatePrecond
    #[{ message := #[], formula :=
          .intGe
            (.stringLen (.getItem (.var "d" loc) (.var "k" loc) loc) loc)
            (.intLit 1 loc)
            loc }]
    (args := #[arg "d" (dictOf str str), arg "k" str])
  let pre := userPreconditionText pre
  assertEq errs 0
  assertEq pre (
    "requires Any..isfrom_DictStrAny(d) & " ++
    "forall(py$schema_d: string)" ++
    "{select(PySpecDict_modelOf(Any..as_Dict!(d)), py$schema_d)} => " ++
    "PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(d)), py$schema_d)) ==> " ++
    "Any..isfrom_str(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(d)), py$schema_d))) " ++
    "summary \"'d' must satisfy its declared dictionary type\"\n" ++
    "requires Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(" ++
    "PySpecDictValue..value(select(PySpecDict_modelOf(Any..as_Dict!(d)), " ++
    "Any..as_string(k)))))), from_int(1))) summary \"precondition 0\"")

-- Schema preconditions recurse into nested containers: a homogeneous dict
-- whose values are lists checks each list element under the value quantifier.
#eval do
  let (pre, errs) := translatePrecond #[]
    (args := #[arg "nested" (dictOf str (listOf int))])
  let pre := userPreconditionText pre
  assertEq errs 0
  assertEq pre (
    "requires Any..isfrom_DictStrAny(nested) & " ++
    "forall(py$schema_nested: string)" ++
    "{select(PySpecDict_modelOf(Any..as_Dict!(nested)), py$schema_nested)} => " ++
    "PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(nested)), py$schema_nested)) ==> " ++
    "Any..isfrom_ListAny(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(nested)), py$schema_nested))) & " ++
    "forall(py$schema_list_nested: Any)" ++
    "{List_contains(Any..as_ListAny!(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(nested)), py$schema_nested))), " ++
    "py$schema_list_nested)} => " ++
    "List_contains(Any..as_ListAny!(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(nested)), py$schema_nested))), " ++
    "py$schema_list_nested) ==> " ++
    "Any..isfrom_int(py$schema_list_nested) " ++
    "summary \"'nested' must satisfy its declared dictionary type\"")

-- Closing the top-level **kwargs dictionary must not close a nested TypedDict.
#eval do
  let innerTy := SpecType.typedDict loc #["name"] #[str] #[true]
  let kwargsTy := SpecType.typedDict loc #["item"] #[innerTy] #[true]
  let result := signaturesToLaurel "<test>" #[
    func "f" str (kwargs := some ("kw", kwargsTy))] testModule
  let pre := getPreconditions result
  assertEq result.errors.size 0
  assertEq pre (
    "requires true & (DictStrAny_keysAllowed(kw, " ++
    "ListStr_cons(\"item\", ListStr_nil())) & " ++
    "forall(py$schema_key_kw: string)" ++
    "{select(PySpecDict_modelOf(kw), py$schema_key_kw)} => " ++
    "PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(kw), py$schema_key_kw)) ==> " ++
    "false | py$schema_key_kw == \"item\") " ++
    "summary \"'kw' must contain only declared keys\"\n" ++
    "requires true & PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(kw), \"item\")) " ++
    "summary \"'kw' must contain required key 'item'\"\n" ++
    "requires true & " ++
    "(PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(kw), \"item\")) ==> " ++
    "Any..isfrom_DictStrAny(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(kw), \"item\"))) & (true & " ++
    "PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(kw), \"item\")))), \"name\")) & " ++
    "(PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(kw), \"item\")))), \"name\")) ==> " ++
    "Any..isfrom_str(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(kw), \"item\")))), \"name\")))))) " ++
    "summary \"'kw.item' must satisfy its declared type\"")

-- A TypedDict return annotation only assumes the coarse type tag: its schema
-- (required keys, field types) is not assumed at call sites without @admit,
-- matching the @ensures trust rule.
#eval do
  let resultTy := SpecType.typedDict loc #["name"] #[str] #[true]
  let result := signaturesToLaurel "<test>"
    #[func "f" resultTy] testModule
  let spec := getSpecText result
  assertEq result.errors.size 0
  assertEq spec "assume Any..isfrom_DictStrAny(result)"
  assert! !spec.contains "PySpecDict_modelOf(Any..as_Dict!(result))"

-- containsKey on a non-kwargs dict: DictStrAny_contains in a precondition
-- (would have been silently dropped before fix #2)
#eval do
  let (pre, errs) := translatePrecond
    #[{ message := #[], formula :=
          .containsKey (.var "d" loc) "mykey" loc }]
    (args := #[arg "d" str])
  assert! errs == 0
  assert! pre.contains "DictStrAny_contains"

-- A `List[TypedDict]` parameter gets its element schema enforced at call
-- sites: the schema gate covers containers, not just top-level dict atoms.
#eval do
  let itemTy := SpecType.typedDict loc #["Name"] #[str] #[true]
  let (pre, errs) := translatePrecond #[]
    (args := #[arg "Batch" (listOf itemTy)])
  assert! errs == 0
  assert! pre.contains "'Batch' must satisfy its declared dictionary type"

-- Dictionary equality is extensional rather than representation-order based.
#eval do
  let dictTy := dictOf str int
  let result := translatePrecondResult
    #[{ message := #[], formula :=
          .pcmp .eq (.var "left" loc) (.var "right" loc) loc }]
    (args := #[arg "left" dictTy, arg "right" dictTy])
  let preconditions := userPreconditions result
  assertEq result.errors.size 0
  match preconditions with
  | [leftSchema, rightSchema, equality] =>
    assertEq (formatCondition leftSchema)
      ("Any..isfrom_DictStrAny(left) & forall(py$schema_left: string)" ++
       "{select(PySpecDict_modelOf(Any..as_Dict!(left)), py$schema_left)} => " ++
       "PySpecDictValue..isPresent(select(PySpecDict_modelOf(Any..as_Dict!(left)), py$schema_left)) ==> " ++
       "Any..isfrom_int(PySpecDictValue..value!(select(" ++
       "PySpecDict_modelOf(Any..as_Dict!(left)), py$schema_left)))")
    assertEq (formatCondition rightSchema)
      ("Any..isfrom_DictStrAny(right) & forall(py$schema_right: string)" ++
       "{select(PySpecDict_modelOf(Any..as_Dict!(right)), py$schema_right)} => " ++
       "PySpecDictValue..isPresent(select(PySpecDict_modelOf(Any..as_Dict!(right)), py$schema_right)) ==> " ++
       "Any..isfrom_int(PySpecDictValue..value!(select(" ++
       "PySpecDict_modelOf(Any..as_Dict!(right)), py$schema_right)))")
    assertEq (formatCondition equality)
      "PySpecDict_scalarEq(Any..as_Dict!(left), Any..as_Dict!(right))"
  | _ =>
    throw <| IO.userError
      s!"expected two dictionary schemas and equality, got {preconditions.length}"

-- Literal-key domains are modeled as string-keyed maps: the schema lowers
-- like `Dict[str, _]` with no warning.
#eval do
  let keyType := mkUnion #[
    SpecType.stringLiteral loc "left",
    SpecType.stringLiteral loc "right"]
  let result := signaturesToLaurel "<test>"
    #[func "f" str (args := #[arg "items" (dictOf keyType int)])] testModule
  assertEq result.errors.size 0
  match result.program.staticProcedures with
  | [proc] =>
    -- A declared parameter type is also a precondition now; pin only the
    -- schema, per the `userPreconditions` convention used above.
    let pinned := proc.preconditions.filter fun (c : Strata.Laurel.Condition) =>
      match c.summary with
      | some summary => !summary.startsWith "declared type of parameter "
      | none => true
    match pinned with
    | [schema] =>
      assertEq (formatCondition schema)
        ("Any..isfrom_DictStrAny(items) & forall(py$schema_items: string)" ++
         "{select(PySpecDict_modelOf(Any..as_Dict!(items)), py$schema_items)} => " ++
         "PySpecDictValue..isPresent(select(PySpecDict_modelOf(Any..as_Dict!(items)), py$schema_items)) ==> " ++
         "Any..isfrom_int(PySpecDictValue..value!(select(" ++
         "PySpecDict_modelOf(Any..as_Dict!(items)), py$schema_items)))")
    | pres =>
      throw <| IO.userError s!"expected one schema precondition, got {pres.length}"
  | procs =>
    throw <| IO.userError s!"expected one procedure, got {procs.length}"

-- A parameter-only non-string-keyed dict never rejects the declaration: its
-- schema is skipped with a non-fatal warning. Fatal rejection is reserved for
-- conditions that actually reference the dictionary.
private def expectSchemaWarningOnly (containerTy : SpecType) : IO Unit := do
  let result := signaturesToLaurel "<test>"
    #[func "f" str (args := #[arg "data" containerTy])] testModule
  match result.errors.toList with
  | [error] =>
    assertEq error.kind Pipeline.MessageKind.dictionarySchemaWarning
    assertEq error.kind.impact.isFatal false
    assertEq result.program.staticProcedures.length 1
  | errors =>
    throw <| IO.userError
      s!"expected one schema warning, got {errors.length}"

#eval expectSchemaWarningOnly (dictOf int str)
#eval expectSchemaWarningOnly (SpecType.ident loc .typingMapping #[int, str])

-- A rejected non-TypedDict `**kwargs` is a fatal error and the procedure is
-- lowered without that input.
#eval do
  let result := signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := #[arg "x" int], kwonly := #[],
                kwargs := some ("kw", str) }
      returnType := str, isOverload := false
      preconditions := #[], postconditions := #[] }] testModule
  match result.errors.toList with
  | [error] => assertEq error.kind.impact.isFatal true
  | errors =>
    throw <| IO.userError s!"expected one kwargs error, got {errors.length}"
  match result.program.staticProcedures with
  | [proc] =>
    let names := proc.inputs.map fun (p : Laurel.Parameter) => p.name.text
    assertEq names ["x"]
  | procs =>
    throw <| IO.userError s!"expected one procedure, got {procs.length}"

/-! ## Quantifier lowering shape

Semantic coverage for quantifiers (does the formula prove/refute what the
Python means?) lives in the end-to-end suite
`StrataPythonTestExtra/AnalyzeLaurelTest.lean`, which runs PySpec fixtures
through the solver and checks pass/violation verdicts per domain.

The checks here pin only what solver verdicts cannot observe: the *shape* of
the emitted Laurel — the membership trigger `{...}`, the guard/body combiner
(`==>` for ∀ vs `&` for ∃), and binder naming/renaming. One representative
pin per shape aspect; the remaining domain combinations are covered
semantically. -/

/-- Render the user precondition produced for `formula` and require the exact
    Laurel text `expectedFormula` (with no translation errors). Only the
    `precondition N` lines are compared: a declared parameter type is also a
    precondition now, and it is pinned separately by `PySpecArgTypeTest`. -/
private def precondPins (args : Array Arg)
    (formula : Assertion) (expectedFormula : String) : Bool :=
  let (rendered, errs) := translatePrecond #[formula] (args := args)
  let userLines := (rendered.splitOn "\n").filter (·.contains "summary \"precondition ")
  errs == 0 &&
    userLines == [s!"requires {expectedFormula} summary \"precondition 0\""]

-- Canonical ∀-over-list shape: `all(len(x) >= 1 for x in xs)`. The binder is
-- Any-typed, the List_contains membership guard doubles as the trigger, and
-- the guard is combined with the body by implication.
#guard precondPins #[arg "xs" str]
  { message := #[], formula :=
      .quantifier .forall (.overList "x") (.var "xs" loc)
        (.intGe (.stringLen (.var "x" loc) loc) (.intLit 1 loc) loc) loc }
  "forall(x: Any){List_contains(Any..as_ListAny!(xs), x)} => \
     List_contains(Any..as_ListAny!(xs), x) ==> \
       Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(x))), from_int(1)))"

-- ∃ is the dual: same trigger and guard, but conjoined (`&`) with the body —
-- an implication here would make the existential vacuously witnessable.
#guard precondPins #[arg "xs" str]
  { message := #[], formula :=
      .quantifier .exists (.overList "x") (.var "xs" loc)
        (.intGe (.stringLen (.var "x" loc) loc) (.intLit 1 loc) loc) loc }
  "exists(x: Any){List_contains(Any..as_ListAny!(xs), x)} => \
     List_contains(Any..as_ListAny!(xs), x) & \
       Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(x))), from_int(1)))"

-- Dict `.values()` shape: `all(len(v) >= 1 for v in d.values())` quantifies
-- over a synthetic string key `py$v` (not the user's `v`, which is the value)
-- and binds the body occurrence of `v` to the `d[py$v]` lookup.
#guard precondPins #[arg "d" str]
  { message := #[], formula :=
      .quantifier .forall (.overDictValues "v") (.var "d" loc)
        (.intGe (.stringLen (.var "v" loc) loc) (.intLit 1 loc) loc) loc }
  "forall(py$v: string){select(\
       PySpecDict_modelOf(Any..as_Dict!(d)), py$v)} => \
     PySpecDictValue..isPresent(select(\
       PySpecDict_modelOf(Any..as_Dict!(d)), py$v)) ==> \
       Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(\
         PySpecDictValue..value!(select(\
           PySpecDict_modelOf(Any..as_Dict!(d)), py$v))))), from_int(1)))"

-- Binder/collection shadowing: in `all(len(xs) >= 1 for xs in xs)` the binder
-- is alpha-renamed to a fresh `py$quant_…` name so the membership guard still
-- reads the outer function argument `xs` instead of the binder.
-- (Semantic counterpart: `require_shadowed_nonempty` in AnalyzeLaurelTest.)
#guard precondPins #[arg "xs" str]
  { message := #[], formula :=
      .quantifier .forall (.overList "xs") (.var "xs" loc)
        (.intGe (.stringLen (.var "xs" loc) loc) (.intLit 1 loc) loc) loc }
  "forall(py$quant_0_0_xs: Any){\
       List_contains(Any..as_ListAny!(xs), py$quant_0_0_xs)} => \
     List_contains(Any..as_ListAny!(xs), py$quant_0_0_xs) ==> \
       Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(\
         py$quant_0_0_xs))), from_int(1)))"

-- A binder shadowing an outer *dict* name over a collection with unknown
-- element type must erase the outer spec type: in
-- `all(Items == Items for Items in Rows)` with an outer `Items: Dict[str, str]`
-- and an untyped `Rows`, the body equality lowers via generic `PEq` on `Any`,
-- not through the dict map model over an unchecked `as_Dict!(Items)`.
#eval do
  let (pre, errs) := translatePrecond
    #[{ message := #[], formula :=
          .quantifier .forall (.overList "Items") (.var "Rows" loc)
            (.pcmp .eq (.var "Items" loc) (.var "Items" loc) loc) loc }]
    (args := #[arg "Items" (dictOf str str),
               arg "Rows" (SpecType.ident loc .typingList #[])])
  assert! errs == 0
  assert! pre.contains "PEq(Items, Items)"

-- Nested-capture regression: the inner ∀ binds `k`, shadowing the outer dict
-- key `k`, while its body reads the outer value `v` (inlined as `d[k]`). The
-- inlined lookup must keep reading the *outer* `k`; capturing the renamed
-- inner binder would leave the formula ill-scoped.
-- (Semantic counterpart: `require_groups_nonempty` in AnalyzeLaurelTest.)
#guard precondPins #[arg "d" str]
  { message := #[], formula :=
      .quantifier .forall (.overDictItems "k" "v") (.var "d" loc)
        (.quantifier .forall (.overList "k") (.var "v" loc)
          (.intGe (.stringLen (.var "v" loc) loc) (.intLit 1 loc) loc) loc) loc }
  "forall(k: string){select(\
       PySpecDict_modelOf(Any..as_Dict!(d)), k)} => \
     PySpecDictValue..isPresent(select(\
       PySpecDict_modelOf(Any..as_Dict!(d)), k)) ==> \
       forall(py$quant_1_0_k: Any){\
           List_contains(Any..as_ListAny!(\
             PySpecDictValue..value!(select(\
               PySpecDict_modelOf(Any..as_Dict!(d)), k))), py$quant_1_0_k)} => \
         List_contains(Any..as_ListAny!(\
           PySpecDictValue..value!(select(\
             PySpecDict_modelOf(Any..as_Dict!(d)), k))), py$quant_1_0_k) ==> \
           Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(\
             PySpecDictValue..value!(select(\
               PySpecDict_modelOf(Any..as_Dict!(d)), k))))), from_int(1)))"


/-! ## Type-directed quantifier domain selection -/

-- `List[T]` / `Sequence[T]` select the list domain; dict views select their
-- respective domains, while bare `Dict`/`Mapping` selects key iteration. An
-- unsupported collection selects nothing, so quantifier translation hard-errors.
-- Each check pins the carried payload types, not just the variant: the
-- element/key/value types seed `localTypes` for the quantifier body, so a
-- domain that fired with the wrong payload would type the binder wrongly.
#guard (match (listOf str).selectQuantDomain with
        | some (.list elemTp) => elemTp == str | _ => false)
#guard (match (SpecType.ident loc .typingSequence #[int]).selectQuantDomain with
        | some (.list elemTp) => elemTp == int | _ => false)
#guard (match (SpecType.itemsView loc str int).selectQuantDomain with
        | some (.dictItems kTp vTp) => kTp == str && vTp == int | _ => false)
#guard (match (SpecType.keysView loc str int).selectQuantDomain with
        | some (.dictKeys kTp vTp) => kTp == str && vTp == int | _ => false)
#guard (match (SpecType.valuesView loc str int).selectQuantDomain with
        | some (.dictValues kTp vTp) => kTp == str && vTp == int | _ => false)
#guard (match (SpecType.ident loc .typingDict #[str, int]).selectQuantDomain with
        | some (.dictKeys kTp vTp) => kTp == str && vTp == int | _ => false)
#guard (match (SpecType.ident loc .typingMapping #[str, int]).selectQuantDomain with
        | some (.dictKeys kTp vTp) => kTp == str && vTp == int | _ => false)
-- `Set[str]` is not a supported collection: no domain, so quantifying is refused.
#guard (SpecType.ident loc (PythonIdent.ofComponent "builtins" "set") #[str])
  |>.selectQuantDomain |>.isNone

-- `dictKeyType?` reports the key type for every dict domain (so the single
-- str-key guard fires) and `none` for the list domain (which has no key).
-- The returned type is pinned to the domain's actual key type — reporting the
-- value type instead would let a non-str-keyed dict slip past the guard.
#guard (QuantDomainInfo.list str).dictKeyType?.isNone
#guard (QuantDomainInfo.dictItems str int).dictKeyType? == some str
#guard (QuantDomainInfo.dictKeys int str).dictKeyType? == some int
#guard (QuantDomainInfo.dictValues int str).dictKeyType? == some int
-- The reported key type is the actual key type, so a non-`str` key is caught.
#guard (match (QuantDomainInfo.dictKeys int str).dictKeyType? with
        | some kTp => !kTp.isStringType | none => false)

-- `isStringLikeType` accepts `str`, string-literal Literals, and their unions,
-- but rejects int literals, mixed unions with non-str idents, and empty types.
#guard str.isStringLikeType
#guard (SpecType.stringLiteral loc "JPEGQuality").isStringLikeType
#guard (SpecType.union loc str (SpecType.stringLiteral loc "a")).isStringLikeType
#guard !int.isStringLikeType
#guard !(SpecType.intLiteral loc 1).isStringLikeType
#guard !(SpecType.union loc int (SpecType.stringLiteral loc "a")).isStringLikeType
#guard !(SpecType.union loc str (SpecType.intLiteral loc 1)).isStringLikeType

/-! ## typeError warning coverage -/

private def hasTypeError (result : TranslationResult) : Bool :=
  result.errors.any fun e => e.kind == .typeError

-- Unknown identifier triggers typeError
#eval do
  let result := translatePrecondResult
    #[{ message := #[], formula := .var "unknown_name" loc }]
  assert! hasTypeError result

-- Non-Bool precondition formula (intLit returns Any, not Bool) triggers typeError
#eval do
  let result := translatePrecondResult
    #[{ message := #[], formula := .intLit 42 loc }]
  assert! hasTypeError result

/-! ## Spec structure tests

Verify the precondition + free-postcondition spec generated by
`buildSpecBody`. -/

/-- Translate a function declaration for body/postcondition tests. -/
private def translateFuncResult (args : Array Arg := #[])
    (returnType : SpecType := str)
    (preconditions : Array Assertion := #[])
    (postconditions : Array SpecExpr := #[])
    (admittedPostconditions : Array SpecExpr := #[]) : TranslationResult :=
  signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "f"
      args := { args := args, kwonly := #[] }
      returnType, isOverload := false
      preconditions, postconditions, admittedPostconditions
    }] testModule

/-- Translate a function declaration and return `(bodyString, errorCount)`. -/
private def translateFunc (args : Array Arg := #[])
    (returnType : SpecType := str)
    (preconditions : Array Assertion := #[])
    (postconditions : Array SpecExpr := #[]) : String × Nat :=
  let result := translateFuncResult args returnType preconditions postconditions
  (getSpecText result, result.errors.size)

-- No args, no preconditions: the return type is a free postcondition
#eval do
  let (spec, errs) := translateFunc
  assert! errs == 0
  assertEq spec "assume Any..isfrom_str(result)"

-- Int arg with no default: type assert (implies not-None, so no separate check)
#eval do
  let (spec, errs) := translateFunc
    (args := #[arg "x" int])
  assert! errs == 0
  assertEq spec "assert Any..isfrom_int(x);\nassume Any..isfrom_str(result)"

-- Optional bool arg (has default): type assert uses Or, no required-param check
#eval do
  let result := translatePrecondResult #[] (args := #[arg "flag" bool_ (some .none)])
  let spec := getSpecText result
  let preConds := userPreconditions result
  assert! result.errors.size == 0
  assertEq spec
    "assert Any..isfrom_None(flag) | Any..isfrom_bool(flag);\nassume Any..isfrom_str(result)"
  -- an optional param carries no required-param obligation at all
  assert! preConds.isEmpty

-- Any-typed arg with no default: the required-param check is a caller-checked
-- precondition (`!isfrom_None`) in `proc.preconditions`, not an in-body assert.
#eval do
  let result := translatePrecondResult #[] (args := #[arg "x" any])
  let preConds := userPreconditions result
  let spec := getSpecText result
  let preText := getPreconditions result
  assert! result.errors.size == 0
  -- exactly one required-param precondition, carrying the "'x' is required"
  -- summary and the `!isfrom_None(x)` obligation
  assert! preConds.length == 1
  assert! preConds.any fun (c : Strata.Laurel.Condition) => c.summary == some "'x' is required"
  assert! preText.contains "requires !Any..isfrom_None(x) summary \"'x' is required\""
  -- caller-checked means mode `.Both` (proven at call sites, assumed in callee)
  assert! preConds.all fun (c : Strata.Laurel.Condition) => c.mode == ConditionMode.Both
  -- and is NOT emitted as an in-body assert
  assert! !spec.contains "'x' is required"

-- Any-typed required param AND a user `@requires` coexist: pins the
-- `requiredParamConds ++ userPreconds` concatenation — both survive and the
-- required-param check is ordered first.
#eval do
  let pre : Assertion :=
    { message := #[.str "x in enum"]
      formula := .enumMember (.var "x" loc) #["a", "b"] loc }
  let result := translatePrecondResult #[pre] (args := #[arg "x" any])
  let preConds := userPreconditions result
  assert! result.errors.size == 0
  -- both the required-param obligation and the user precondition are present
  assert! preConds.length == 2
  -- required-param check ordered first (requiredParamConds ++ userPreconds)
  assert! (preConds.head?.bind (·.summary)) == some "'x' is required"
  -- the user precondition survives with its own summary
  assert! preConds.any fun (c : Strata.Laurel.Condition) => c.summary == some "x in enum"

-- Float return type: assume Any..isfrom_float(result)
#eval do
  let (spec, errs) := translateFunc
    (returnType := float_)
  assert! errs == 0
  assertEq spec "assume Any..isfrom_float(result)"

-- Composite return type: no assume (no tester for user-defined types)
#eval do
  let (spec, errs) := translateFunc
    (returnType := SpecType.ident loc (PythonIdent.ofComponent "mod" "Cls"))
  assert! errs == 0
  assertEq spec ""

private def isUnsupportedPostconditionError
    (error : Strata.Pipeline.PipelineMessage) (predicate : String) : Bool :=
  error.kind == .unsupportedPostcondition
    && error.kind.impact.isFatal
    && error.loc == loc
    && error.message.message.contains predicate
    && error.message.message.contains "cannot verify this postcondition against an implementation"
    && error.message.message.contains "will not assume it at call sites"
    && error.message.message.contains "Use @admit to accept the postcondition as an unverified modeling assumption"

-- A modeled postcondition is a fatal error and never becomes caller-visible.
private def t_userPostconditionRejected : Bool :=
  let postcondition := .intGe (.var "result" loc) (.intLit 0 loc) loc
  let result := translateFuncResult
    (args := #[arg "x" int])
    (postconditions := #[postcondition])
  let spec := getSpecText result
  (match result.errors.toList with
    | [error] => isUnsupportedPostconditionError error (toString postcondition)
    | _ => false)
    && noUserPostconditions result
    && !spec.contains "PGe(result, from_int(0))"
    && spec.contains "assume Any..isfrom_str(result)"

#guard t_userPostconditionRejected

-- Every modeled postcondition is rejected and none leak into the procedure.
private def t_multiplePostconditionsRejected : Bool :=
  let first := .intGe (.var "result" loc) (.intLit 0 loc) loc
  let second := .intGe (.var "result" loc) (.intLit 10 loc) loc
  let result := translateFuncResult
    (returnType := int)
    (postconditions := #[first, second])
  let spec := getSpecText result
  (match result.errors.toList with
    | [firstError, secondError] =>
        isUnsupportedPostconditionError firstError (toString first)
          && isUnsupportedPostconditionError secondError (toString second)
    | _ => false)
    && noUserPostconditions result
    && !spec.contains "PGe(result, from_int(0))"
    && !spec.contains "PGe(result, from_int(10))"
    && spec.contains "assume Any..isfrom_int(result)"

#guard t_multiplePostconditionsRejected

-- Rejection happens before expression lowering: even a non-Boolean modeled
-- postcondition receives the same fatal soundness diagnostic and is not exposed.
private def t_nonBoolPostconditionRejected : Bool :=
  let postcondition := .intLit 42 loc
  let result := translateFuncResult (postconditions := #[postcondition])
  (match result.errors.toList with
    | [error] => isUnsupportedPostconditionError error (toString postcondition)
    | _ => false)
    && noUserPostconditions result
    && (getSpecText result).contains "assume Any..isfrom_str(result)"

#guard t_nonBoolPostconditionRejected

-- Valid preconditions remain structurally available in the translation result,
-- but a modeled postcondition still makes the overall pipeline fail fatally.
private def t_preconditionAndPostconditionRejected : Bool :=
  let geZero (v : String) : SpecExpr := .intGe (.var v loc) (.intLit 0 loc) loc
  let pre : Assertion := { message := #[.str "n >= 0"], formula := geZero "n" }
  let postcondition := geZero "result"
  let result := translateFuncResult
    (args := #[arg "n" int])
    (preconditions := #[pre])
    (postconditions := #[postcondition])
  let spec := getSpecText result
  let procedurePreconditions := userPreconditions result
  (match result.errors.toList with
    | [error] => isUnsupportedPostconditionError error (toString postcondition)
    | _ => false)
    && spec.contains "assert Any..isfrom_int(n)"
    && !spec.contains "isfrom_None(n)"
    && (match procedurePreconditions with
      | [condition] =>
          condition.mode == .Both
            && condition.summary == some "n >= 0"
            && formatCondition condition == "Any_to_bool(PGe(n, from_int(0)))"
      | _ => false)
    && noUserPostconditions result
    && !spec.contains "PGe(result, from_int(0))"
    && spec.contains "assume Any..isfrom_str(result)"

#guard t_preconditionAndPostconditionRejected

/-! ## Admitted postconditions (`@admit`)

An `@admit` predicate is an explicitly acknowledged, unverified modeling
assumption. A PySpec model is bodiless, so it lowers to a *free* postcondition:
assumed at every call site, never checked -- exactly like the trusted
return-type assumption it sits beside. -/

-- @admit lowers to a free postcondition with no errors.
private def t_admittedPostconditionAssumed : Bool :=
  let admitted := .intGe (.var "result" loc) (.intLit 0 loc) loc
  let result := translateFuncResult
    (returnType := int)
    (admittedPostconditions := #[admitted])
  let spec := getSpecText result
  result.errors.isEmpty
    && hasAdmittedPostcondition result
    && spec.contains "assume Any_to_bool(PGe(result, from_int(0)))"
    && spec.contains "assume Any..isfrom_int(result)"

#guard t_admittedPostconditionAssumed

-- An @admit predicate may relate the result to a parameter: both identifiers
-- resolve inside the free postcondition.
private def t_admittedPostconditionReferencesParam : Bool :=
  let admitted := .intGe (.var "result" loc) (.var "x" loc) loc
  let result := translateFuncResult
    (args := #[arg "x" int])
    (returnType := int)
    (admittedPostconditions := #[admitted])
  let spec := getSpecText result
  result.errors.isEmpty
    && spec.contains "assume Any_to_bool(PGe(result, x))"

#guard t_admittedPostconditionReferencesParam

-- The map lowering applies uniformly inside `OLD(...)`: pre-state dictionary
-- field reads and equality use the same model as post-state ones.
#eval do
  let itemTy := SpecType.typedDict loc #["name"] #[str] #[true]
  let admitted := SpecExpr.intGe
    (.stringLen (.getIndex (.old (.var "d" loc) loc) "name" loc) loc)
    (.intLit 1 loc) loc
  let result := translateFuncResult
    (args := #[arg "d" itemTy])
    (returnType := int)
    (admittedPostconditions := #[admitted])
  let spec := getSpecText result
  assertEq result.errors.size 0
  assertEq spec (
    "assert Any..isfrom_DictStrAny(d) & PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(d)), \"name\"));\n" ++
    "assert Any..isfrom_DictStrAny(d) & (PySpecDictValue..isPresent(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(d)), \"name\")) ==> Any..isfrom_str(" ++
    "PySpecDictValue..value!(select(PySpecDict_modelOf(Any..as_Dict!(d)), \"name\"))));\n" ++
    "assert Any..isfrom_DictStrAny(d);\n" ++
    "assume Any_to_bool(PGe(from_int(Str.Length(Any..as_string!(" ++
    "PySpecDictValue..value(select(PySpecDict_modelOf(Any..as_Dict!(old(d))), " ++
    "\"name\"))))), from_int(1)));\n" ++
    "assume Any..isfrom_int(result)")

#eval do
  let dictTy := dictOf str int
  let admitted := SpecExpr.pcmp .eq (.old (.var "d" loc) loc) (.var "d" loc) loc
  let result := translateFuncResult
    (args := #[arg "d" dictTy])
    (returnType := int)
    (admittedPostconditions := #[admitted])
  let spec := getSpecText result
  assertEq result.errors.size 0
  assertEq spec (
    "assert Any..isfrom_DictStrAny(d) & forall(py$schema_d: string)" ++
    "{select(PySpecDict_modelOf(Any..as_Dict!(d)), py$schema_d)} => " ++
    "PySpecDictValue..isPresent(select(PySpecDict_modelOf(Any..as_Dict!(d)), py$schema_d)) ==> " ++
    "Any..isfrom_int(PySpecDictValue..value!(select(" ++
    "PySpecDict_modelOf(Any..as_Dict!(d)), py$schema_d)));\n" ++
    "assert Any..isfrom_DictStrAny(d);\n" ++
    "assume PySpecDict_scalarEq(Any..as_Dict!(old(d)), Any..as_Dict!(d));\n" ++
    "assume Any..isfrom_int(result)")

-- Every @admit predicate becomes a free postcondition, in order.
private def t_multipleAdmittedPostconditionsAssumed : Bool :=
  let first := .intGe (.var "result" loc) (.intLit 0 loc) loc
  let second := .intGe (.var "result" loc) (.intLit 10 loc) loc
  let result := translateFuncResult
    (returnType := int)
    (admittedPostconditions := #[first, second])
  let spec := getSpecText result
  result.errors.isEmpty
    && hasAdmittedPostcondition result
    && spec.contains "assume Any_to_bool(PGe(result, from_int(0)))"
    && spec.contains "assume Any_to_bool(PGe(result, from_int(10)))"

#guard t_multipleAdmittedPostconditionsAssumed

-- A non-Boolean @admit predicate is fatal: an acknowledged assumption must
-- not be dropped silently.
private def t_nonBoolAdmittedPostconditionRejected : Bool :=
  let admitted := .intLit 42 loc
  let result := translateFuncResult (admittedPostconditions := #[admitted])
  let spec := getSpecText result
  (match result.errors.toList with
    | [error] =>
        error.kind == .unsupportedAdmit
          && error.kind.impact.isFatal
          && error.loc == loc
          && error.message.message.contains "@admit predicate is not Bool in 'test_f'"
          && error.message.message.contains "will not be dropped silently"
    | _ => false)
    && !spec.contains "from_int(42)"
    && spec.contains "assume Any..isfrom_str(result)"

#guard t_nonBoolAdmittedPostconditionRejected

-- An @admit predicate whose translation fails (here: a placeholder) is also
-- fatal, on top of the non-fatal knownLimitation from the lowering itself.
private def t_untranslatableAdmittedPostconditionRejected : Bool :=
  let admitted := .placeholder loc
  let result := translateFuncResult (admittedPostconditions := #[admitted])
  let spec := getSpecText result
  (match result.errors.toList with
    | [limitation, error] =>
        limitation.kind == .placeholderExpr
          && !limitation.kind.impact.isFatal
          && error.kind == .unsupportedAdmit
          && error.kind.impact.isFatal
          && error.loc == loc
          && error.message.message.contains "@admit predicate of 'test_f' could not be translated"
          && error.message.message.contains "will not be dropped silently"
    | _ => false)
    && spec.contains "assume Any..isfrom_str(result)"

#guard t_untranslatableAdmittedPostconditionRejected

-- Mixed contracts: @requires stays caller-checked, @admit becomes a free
-- postcondition, and a modeled @ensures alongside them is still rejected.
private def t_mixedRequiresAdmitEnsures : Bool :=
  let geZero (v : String) : SpecExpr := .intGe (.var v loc) (.intLit 0 loc) loc
  let pre : Assertion := { message := #[.str "n >= 0"], formula := geZero "n" }
  let admitted := geZero "result"
  let postcondition := .intGe (.var "result" loc) (.intLit 10 loc) loc
  let result := translateFuncResult
    (args := #[arg "n" int])
    (preconditions := #[pre])
    (postconditions := #[postcondition])
    (admittedPostconditions := #[admitted])
  let spec := getSpecText result
  let procedurePreconditions := userPreconditions result
  (match result.errors.toList with
    | [error] => isUnsupportedPostconditionError error (toString postcondition)
    | _ => false)
    && (match procedurePreconditions with
      | [condition] => condition.summary == some "n >= 0"
      | _ => false)
    && hasAdmittedPostcondition result
    -- the admitted predicate is assumed at call sites …
    && spec.contains "PGe(result, from_int(0))"
    -- … while the rejected @ensures predicate is not
    && !spec.contains "PGe(result, from_int(10))"
    && spec.contains "assume Any..isfrom_str(result)"

#guard t_mixedRequiresAdmitEnsures

/-! ## Contracts on `@overload` stubs

No procedure is generated for a dispatch-only stub, so `@ensures` and `@admit`
on one are rejected loudly instead of silently dropped. -/

private def translateOverloadResult (postconditions : Array SpecExpr := #[])
    (admittedPostconditions : Array SpecExpr := #[]) : TranslationResult :=
  signaturesToLaurel "<test>" #[
    .functionDecl {
      loc := loc, nameLoc := loc, name := "make"
      args := { args := #[arg "kind" (SpecType.stringLiteral loc "a")], kwonly := #[] }
      returnType := pyClass "Alpha"
      isOverload := true
      preconditions := #[]
      postconditions, admittedPostconditions
    }] testModule

-- @ensures on an @overload stub is fatal; the dispatch entry is still registered.
private def t_overloadEnsuresRejected : Bool :=
  let postcondition := .intGe (.var "result" loc) (.intLit 0 loc) loc
  let result := translateOverloadResult (postconditions := #[postcondition])
  (match result.errors.toList with
    | [error] =>
        error.kind == .unsupportedPostcondition
          && error.kind.impact.isFatal
          && error.loc == loc
          && error.message.message.contains "Modeled @ensures cannot be verified for 'make'"
          && error.message.message.contains "dispatch-only declaration"
          && error.message.message.contains (toString postcondition)
    | _ => false)
    && result.overloads.contains "make"

#guard t_overloadEnsuresRejected

-- @admit on an @overload stub is fatal: no procedure is generated to carry it.
private def t_overloadAdmitRejected : Bool :=
  let admitted := .intGe (.var "result" loc) (.intLit 0 loc) loc
  let result := translateOverloadResult (admittedPostconditions := #[admitted])
  (match result.errors.toList with
    | [error] =>
        error.kind == .unsupportedAdmit
          && error.kind.impact.isFatal
          && error.loc == loc
          && error.message.message.contains "@admit is not supported on @overload stub 'make'"
          && error.message.message.contains (toString admitted)
    | _ => false)
    && result.overloads.contains "make"

#guard t_overloadAdmitRejected

/-! ## The modifies clause is one unguarded wildcard group

Strata's `Body.Opaque` carries `List ModifiesGroup`; this frontend always emits
the degenerate form — exactly one unguarded, summary-less group whose sole
target is the wildcard (`*`). The single-group wrapping is load-bearing: zero
groups would mean "unframed" downstream, while an empty-target group would mean
"nothing changes". Pinned directly because the shape is otherwise only
exercised incidentally, end to end. -/

private def isWildcardOnly (g : ModifiesGroup) : Bool :=
  match g.targets with
  | [t] => (t.val matches .All)
  | _ => false

private def firstProcGroups (result : TranslationResult) : Option (List ModifiesGroup) :=
  match result.program.staticProcedures with
  | proc :: _ =>
    match proc.body with
    | .Opaque _ _ groups => some groups
    | _ => none
  | [] => none

/--
info: groups: 1
unguarded: true, wildcard-only target: true, no summary: true
-/
#guard_msgs in
#eval do
  let result := signaturesToLaurel "<test>" #[mkFuncSig "f" (identType .builtinsInt)] testModule
  match firstProcGroups result with
  | none => IO.println "no opaque procedure found"
  | some groups =>
    IO.println s!"groups: {groups.length}"
    for g in groups do
      IO.println s!"unguarded: {g.guard.isNone}, wildcard-only target: {isWildcardOnly g}, no summary: {g.summary.isNone}"

/-! ## `classDefToLaurel` emits the `extending` list, structurally pinned.

`fmtTypeDef` drops `extending`, so a print-based test cannot see it — these `#guard`s pin it
directly through a shared `extendingOf` helper, covering the three boundary shapes of the
`cls.bases.toList.map` path: empty, single, and multiple (order-preserving). -/

private def extendingOf (name : String) (bases : Array PythonIdent)
    : Option (List Strata.Laurel.HighTypeMd) :=
  let r := signaturesToLaurel "<test>" #[.classDef { loc, name, bases, methods := #[] }] testModule
  if r.errors.size != 0 then none
  else r.program.types.findSome? fun td =>
    match td with
    | .Composite ty => if ty.name.text == s!"test_{name}" then some ty.extending else none
    | _ => none

-- A HighTypeMd base reference from its emitted (already-`toLaurelName`d) name.
private def udBase (n : String) : Strata.Laurel.HighTypeMd := ⟨.UserDefined (mkId n), unknownSource⟩

#guard extendingOf "Leaf" #[] == some []
#guard extendingOf "Derived" #[externIdent "mod" "Base"] == some [udBase "mod_Base"]
#guard extendingOf "Multi" #[externIdent "m1" "A", externIdent "m2" "B"]
       == some [udBase "m1_A", udBase "m2_B"]

-- Totality guard for `fmtHighType`'s `.TVar` arm (no SPFE path constructs a `.TVar`).
#guard fmtHighType (.TVar (mkId "T")) == "TVar(T)"

/-! ## `OLD(expr)` two-state lowering

`SpecExpr.old` is a generic structural wrapper. An admitted post-state
predicate lowers it to Laurel's `old(...)` in a free postcondition, where
`PushOldInward` can distribute it to inout state. -/

/-- Run `signaturesToLaurel` for a single admitted postcondition and print the
    error count and the full rendered spec, so `#guard_msgs` pins the complete
    Laurel output (not just a substring) at elaboration time. -/
private def runAdmittedBody (admittedPostconditions : Array SpecExpr)
    (args : Array Arg := #[]) : IO Unit := do
  let result := translateFuncResult
    (args := args)
    (returnType := identType .builtinsInt)
    (admittedPostconditions := admittedPostconditions)
  IO.println s!"errors: {result.errors.size}"
  IO.println (getSpecText result)

-- `OLD(x)` in @admit lowers to a free postcondition with `old(x)`.
/--
info: errors: 0
assert Any..isfrom_int(x);
assume Any_to_bool(PGe(old(x), x));
assume Any..isfrom_int(result)
-/
#guard_msgs in
#eval runAdmittedBody
  #[.intGe (.old (.var "x" loc) loc) (.var "x" loc) loc]
  #[mkArg "x" (identType .builtinsInt)]

-- `OLD` on an arithmetic expression wraps the whole subexpression:
-- `old(PAdd(x, x))`, not `PAdd(old(x), old(x))`.
/--
info: errors: 0
assert Any..isfrom_int(x);
assume Any_to_bool(PGe(old(PAdd(x, x)), x));
assume Any..isfrom_int(result)
-/
#guard_msgs in
#eval runAdmittedBody
  #[.intGe (.old (.add (.var "x" loc) (.var "x" loc) loc) loc) (.var "x" loc) loc]
  #[mkArg "x" (identType .builtinsInt)]

end StrataPython.Specs.ToLaurel.Tests
end
