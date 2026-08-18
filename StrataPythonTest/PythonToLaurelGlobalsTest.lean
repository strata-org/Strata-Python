/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PythonToLaurel

meta section

namespace StrataPython.ToLaurel.Tests

open Strata
open Strata.Laurel
open StrataPython.ToLaurel

private def sr : SourceRange := default

private def pyName (name : String) (ctx : expr_context SourceRange) : expr SourceRange :=
  .Name sr { val := name, ann := sr } ctx

private def loadName (name : String) : expr SourceRange :=
  pyName name (.Load sr)

private def storeName (name : String) : expr SourceRange :=
  pyName name (.Store sr)

private def intLiteral (value : Nat) : expr SourceRange :=
  .Constant sr (.ConPos sr { val := value, ann := sr }) { val := none, ann := sr }

private def assign (name : String) (value : expr SourceRange) : stmt SourceRange :=
  .Assign sr { val := #[storeName name], ann := sr } value { val := none, ann := sr }

private def assignChained (first second : String)
    (value : expr SourceRange) : stmt SourceRange :=
  .Assign sr { val := #[storeName first, storeName second], ann := sr } value
    { val := none, ann := sr }

private def annAssign (name : String) (annotation : expr SourceRange)
    (value : Option (expr SourceRange)) : stmt SourceRange :=
  .AnnAssign sr (storeName name) annotation { val := value, ann := sr }
    (.IntPos sr { val := 1, ann := sr })

private def augAssign (name : String) (value : expr SourceRange) : stmt SourceRange :=
  .AugAssign sr (storeName name) (.Add sr) value

private def emptyArguments : arguments SourceRange :=
  .mk_arguments sr
    { val := #[], ann := sr }
    { val := #[], ann := sr }
    { val := none, ann := sr }
    { val := #[], ann := sr }
    { val := #[], ann := sr }
    { val := none, ann := sr }
    { val := #[], ann := sr }

private def functionWithGlobal (functionName globalName : String) : stmt SourceRange :=
  .FunctionDef sr
    { val := functionName, ann := sr }
    emptyArguments
    { val := #[.Global sr {
        val := #[{ val := globalName, ann := sr }]
        ann := sr
      }], ann := sr }
    { val := #[], ann := sr }
    { val := none, ann := sr }
    { val := none, ann := sr }
    { val := #[], ann := sr }

private def storeAttribute (name field : String) : expr SourceRange :=
  .Attribute sr (loadName name) { val := field, ann := sr } (.Store sr)

private def loadAttribute (name field : String) : expr SourceRange :=
  .Attribute sr (loadName name) { val := field, ann := sr } (.Load sr)

private def globals : Std.HashSet String := Std.HashSet.ofList ["value"]

private def globalCtx : TranslationContext :=
  { moduleGlobals := globals, scopeGlobals := globals }

private def unsupportedGlobalCtx : TranslationContext :=
  { unsupportedModuleGlobals := globals }

private def isValueGlobalHavoc (stmts : List StmtExprMd) : Bool :=
  match stmts with
  | [{ val := .Assert { val := .Var (.Local bound), .. } (some message), .. },
     { val := .Assign [{ val := .Local target, .. }]
         { val := .Hole false (some { val := .UserDefined havocType, .. }), .. }, .. },
     { val := .Hole true none, .. }] =>
    bound.text == "$static.__strata_python_global_bound_value" &&
    message == "global 'value' is bound" &&
    target.text == "value" &&
    havocType.text == "Any"
  | _ => false

private inductive UnmodeledCallPosition
  | receiver
  | positional
  | keyword

private def havocsValueFromUnmodeledCall
    (position : UnmodeledCallPosition) (value : expr SourceRange) : Bool :=
  let call : expr SourceRange := match position with
    | .receiver =>
      .Call sr
        (.Attribute sr value { val := "mutate", ann := sr } (.Load sr))
        { val := #[], ann := sr }
        { val := #[], ann := sr }
    | .positional =>
      .Call sr (loadName "unknown")
        { val := #[value], ann := sr }
        { val := #[], ann := sr }
    | .keyword =>
      let keyword : keyword SourceRange := .mk_keyword sr
        { val := some { val := "argument", ann := sr }, ann := sr } value
      .Call sr (loadName "unknown")
        { val := #[], ann := sr }
        { val := #[keyword], ann := sr }
  match translateExpr globalCtx call with
  | .ok { val := .Block stmts _, .. } => isValueGlobalHavoc stmts
  | _ => false

private def isValueAugAssign : StmtExprMd → Bool
  | { val := .Assign targets rhs, .. } =>
    match targets, rhs with
    | [{ val := .Local target, .. }],
      { val := .StaticCall addFn [
          { val := .Var (.Local source), .. },
          { val := .StaticCall fromInt [{ val := .LiteralInt value, .. }], .. }], .. } =>
      target.text == "value" &&
      addFn.text == "PAdd" &&
      source.text == "value" &&
      fromInt.text == "from_int" &&
      value == 1
    | _, _ => false
  | _ => false

#guard
  match pythonToLaurel {} #[assign "value" (intLiteral 1)] with
  | .ok (program, _) =>
    program.staticFields.map (·.name.text) ==
      ["value", "__strata_python_global_bound_value"] &&
    program.staticFields.all fun field => !field.name.text.contains '$'
  | .error _ => false

#guard
  match translateExpr globalCtx (loadName "value") with
  | .ok { val := .Block [{ val := .Assert { val := .Var (.Local bound), .. } _, .. },
                          { val := .Var (.Local value), .. }] _, .. } =>
    bound.text == "$static.__strata_python_global_bound_value" && value.text == "value"
  | _ => false

#guard
  let implicitModuleCtx := { globalCtx with scopeGlobals := {}, scopeLocals := {} }
  match translateExpr implicitModuleCtx (loadName "value") with
  | .ok { val := .Block [
      { val := .Assert { val := .Var (.Local bound), .. } _, .. },
      { val := .Var (.Local value), .. }] _, .. } =>
    bound.text == "$static.__strata_python_global_bound_value" && value.text == "value"
  | _ => false

#guard
  match translateExpr globalCtx (loadName "value") >>= stmtExprToVar with
  | .ok { val := .Local value, .. } => value.text == "value"
  | _ => false

#guard
  match translateAssign globalCtx (storeName "value") none (intLiteral 1) unknownSource with
  | .ok (_, [
      { val := .Assign [{ val := .Declare decl, .. }]
          { val := .StaticCall initFn [], .. }, .. },
      { val := .Assign [{ val := .Local target, .. }]
          { val := .StaticCall fromInt [{ val := .LiteralInt value, .. }], .. }, .. },
      { val := .Assign [{ val := .Local bound, .. }]
          { val := .LiteralBool true, .. }, .. }], true) =>
    decl.name.text == "value" &&
    initFn.text == "from_None" &&
    target.text == "value" &&
    fromInt.text == "from_int" &&
    value == 1 &&
    bound.text == "$static.__strata_python_global_bound_value"
  | .error _ => false
  | _ => false

#guard
  let exceptionCtx := { globalCtx with maybeExceptionFunctions := ["PAdd"] }
  let rhs := expr.BinOp sr (intLiteral 1) (.Add sr) (intLiteral 2)
  match translateStmt exceptionCtx (assign "value" rhs) with
  | .ok (_, [
      _,
      { val := .Assert _ (some summary), .. },
      { val := .Assign [{ val := .Local target, .. }]
          { val := .StaticCall operation _, .. }, .. },
      { val := .Assign [{ val := .Local bound, .. }]
          { val := .LiteralBool isBound, .. }, .. }]) =>
    summary == "Check PAdd exception" &&
    target.text == "value" &&
    operation.text == "PAdd" &&
    bound.text == "$static.__strata_python_global_bound_value" &&
    isBound
  | _ => false

#guard
  match translateAssign unsupportedGlobalCtx (storeAttribute "value" "count")
      none (intLiteral 1) unknownSource with
  | .error (.unsupportedConstruct message _) =>
    message ==
      "attribute write on module variable 'value' with composite or type-alias value is not supported"
  | _ => false

#guard
  let stmt := stmt.AugAssign sr (storeAttribute "value" "count") (.Add sr) (intLiteral 1)
  match translateStmt unsupportedGlobalCtx stmt with
  | .error (.unsupportedConstruct message _) =>
    message ==
      "attribute write on module variable 'value' with composite or type-alias value is not supported"
  | _ => false

#guard
  match translateExpr unsupportedGlobalCtx (loadAttribute "value" "count") with
  | .error (.unsupportedConstruct message _) =>
    message ==
      "attribute read on module variable 'value' with composite or type-alias value is not supported"
  | _ => false

#guard
  let explicitGlobalCtx := { globalCtx with scopeLocals := globals }
  match translateExpr explicitGlobalCtx (loadName "value") with
  | .ok { val := .Block [
      { val := .Assert { val := .Var (.Local bound), .. } _, .. },
      { val := .Var (.Local value), .. }] _, .. } =>
    bound.text == "$static.__strata_python_global_bound_value" && value.text == "value"
  | _ => false

#guard
  let call := expr.Call sr (loadName "f")
    { val := #[], ann := sr } { val := #[], ann := sr }
  let stableTuple := expr.Tuple sr
    { val := #[intLiteral 1, intLiteral 2], ann := sr } (.Load sr)
  let innerTuple := expr.Tuple sr
    { val := #[intLiteral 1], ann := sr } (.Load sr)
  let nestedTuple := expr.Tuple sr
    { val := #[innerTuple, intLiteral 2], ann := sr } (.Load sr)
  let unstableTuple := expr.Tuple sr
    { val := #[intLiteral 1, call], ann := sr } (.Load sr)
  let cases : List (expr SourceRange × Bool) := [
    (intLiteral 1, true),
    (stableTuple, true),
    (nestedTuple, true),
    (unstableTuple, false),
    (loadName "captured", false)
  ]
  cases.all fun (value, expected) =>
    isCallTimeStableDefault value == expected

#guard
  let call := expr.Call sr (loadName "f")
    { val := #[], ann := sr } { val := #[], ann := sr }
  let nestedCall := expr.BinOp sr (intLiteral 1) (.Add sr) call
  let literalTree := expr.IfExp sr
    (.Constant sr (.ConTrue sr) { val := none, ann := sr })
    (intLiteral 1)
    (expr.BinOp sr (intLiteral 2) (.Add sr) (intLiteral 3))
  let cases : List (expr SourceRange × Bool) := [
    (nestedCall, true),
    (literalTree, false),
    (.Subscript sr (loadName "items") call (.Load sr), true),
    (.FormattedValue sr call (.IntNeg sr { val := 1, ann := sr })
      { val := none, ann := sr }, true),
    (.BoolOp sr (.And sr)
      { val := #[.Constant sr (.ConTrue sr) { val := none, ann := sr }, call],
        ann := sr }, true)
  ]
  cases.all fun (value, expected) =>
    containsDefinitionTimeEffect value == expected

#guard
  let localCtx := { globalCtx with
    variableTypes := [("value", PyLauType.Any)]
    scopeGlobals := {}
    scopeLocals := globals }
  match translateExpr localCtx (loadName "value") with
  | .ok { val := .Var (.Local name), .. } => name.text == "value"
  | _ => false

#guard
  let unsupported := Std.HashSet.ofList ["object"]
  let moduleCtx : TranslationContext := {
    unsupportedModuleGlobals := unsupported
    scopeLocals := unsupported
  }
  match translateExpr moduleCtx (loadName "object") with
  | .ok { val := .Var (.Local name), .. } => name.text == "object"
  | _ => false

#guard
  let functionCtx := { globalCtx with scopeGlobals := {} }
  match translateFunctionBody functionCtx []
      [augAssign "value" (intLiteral 1)] with
  | .ok ({ val := .Block [
      { val := .Assign [{ val := .Declare nullcall, .. }]
          { val := .StaticCall nullcallInit [], .. }, .. },
      { val := .Assign [{ val := .Local result, .. }]
          { val := .StaticCall resultInit [], .. }, .. },
      { val := .Assign [{ val := .Declare maybeExcept, .. }]
          { val := .StaticCall maybeExceptInit [], .. }, .. },
      { val := .Assign [{ val := .Declare localValue, .. }]
          { val := .Hole, .. }, .. },
      valueAugAssign] _, .. }, ctx) =>
    nullcall.name.text == "nullcall_ret" &&
    nullcallInit.text == "from_None" &&
    result.text == "LaurelResult" &&
    resultInit.text == "from_None" &&
    maybeExcept.name.text == "maybe_except" &&
    maybeExceptInit.text == "NoError" &&
    localValue.name.text == "value" &&
    isValueAugAssign valueAugAssign &&
    ctx.scopeLocals.toList.mergeSort == ["value"] &&
    ctx.scopeGlobals.isEmpty
  | .error _ => false
  | _ => false

#guard
  collectGlobalDeclNames [functionWithGlobal "inner" "value"] == []

#guard
  let aggregate := expr.List sr
    { val := #[loadName "value"], ann := sr } (.Load sr)
  let conditional := expr.IfExp sr
    (.Constant sr (.ConTrue sr) { val := none, ann := sr })
    (loadName "value")
    (intLiteral 0)
  let named := expr.NamedExpr sr (storeName "value") (intLiteral 1)
  let booleanAggregate := expr.BoolOp sr (.And sr)
    { val := #[.Constant sr (.ConTrue sr) { val := none, ann := sr },
              loadName "value"], ann := sr }
  let dictionaryValue := expr.Dict sr
    { val := #[.missing_expr sr], ann := sr }
    { val := #[loadName "value"], ann := sr }
  let dictionaryKey := expr.Dict sr
    { val := #[.some_expr sr (loadName "value")], ann := sr }
    { val := #[intLiteral 1], ann := sr }
  let nestedReceiverCall : expr SourceRange := .Call sr
    (.Attribute sr (loadName "value") { val := "mutate", ann := sr } (.Load sr))
    { val := #[], ann := sr } { val := #[], ann := sr }
  let subscript := expr.Subscript sr (loadName "value") (intLiteral 0) (.Load sr)
  let starred := expr.Starred sr (loadName "value") (.Load sr)
  let nestedPositionalCall : expr SourceRange := .Call sr (loadName "nested")
    { val := #[loadName "value"], ann := sr } { val := #[], ann := sr }
  let keyword : keyword SourceRange := .mk_keyword sr
    { val := some { val := "argument", ann := sr }, ann := sr }
    (loadName "value")
  let nestedKeywordCall : expr SourceRange := .Call sr (loadName "nested")
    { val := #[], ann := sr } { val := #[keyword], ann := sr }
  let cases : List (UnmodeledCallPosition × expr SourceRange) := [
    (.receiver, loadName "value"),
    (.positional, aggregate),
    (.positional, conditional),
    (.positional, named),
    (.positional, booleanAggregate),
    (.positional, dictionaryValue),
    (.positional, dictionaryKey),
    (.positional, nestedReceiverCall),
    (.positional, subscript),
    (.positional, starred),
    (.positional, nestedPositionalCall),
    (.positional, nestedKeywordCall),
    (.keyword, loadName "value")
  ]
  cases.all fun (position, value) =>
    havocsValueFromUnmodeledCall position value

#guard
  let nestedRead := expr.BinOp sr (loadName "value") (.Add sr) (intLiteral 1)
  let call : expr SourceRange := .Call sr (loadName "unknown")
    { val := #[nestedRead], ann := sr } { val := #[], ann := sr }
  match translateExpr globalCtx call with
  | .ok { val := .Block [
      { val := .Assert { val := .Var (.Local bound), .. } (some message), .. },
      { val := .Hole true none, .. }] _, .. } =>
    bound.text == "$static.__strata_python_global_bound_value" &&
    message == "global 'value' is bound"
  | _ => false

#guard
  match pythonToLaurel {} #[assign "nullcall_ret" (intLiteral 1)] with
  | .error (.unsupportedConstruct message _) =>
    message ==
      "module variable 'nullcall_ret' cannot be lowered to a Laurel static field because its name collides with a top-level definition"
  | _ => false

#guard
  match pythonToLaurel {}
      #[assign "__strata_python_global_bound_value" (intLiteral 1)] with
  | .error (.unsupportedConstruct message _) =>
    message ==
      "module variable '__strata_python_global_bound_value' cannot be lowered to a Laurel static field because its name collides with a top-level definition"
  | _ => false

-- Every spelling of a module-scope type alias is kept out of static fields, so
-- the alias is never exposed to downstream checks as an unconstrained `Any`.
#guard
  let aliasForms : List (stmt SourceRange) := [
    assign "T" (loadName "int"),
    assignChained "T" "T2" (loadName "int"),
    annAssign "T" (loadName "type") (some (loadName "int")),
    annAssign "T" (loadName "TypeAlias") (some (loadName "int")),
    annAssign "T" (loadName "TypeAlias") none
  ]
  aliasForms.all fun aliasStmt =>
    match pythonToLaurel {} #[aliasStmt] with
    | .ok (program, ctx) =>
      !(program.staticFields.map (·.name.text)).contains "T" &&
      ctx.unsupportedModuleGlobals.contains "T"
    | .error _ => false

-- Chained targets share the right-hand side, so both aliases are poisoned.
#guard
  match pythonToLaurel {} #[assignChained "T1" "T2" (loadName "int")] with
  | .ok (program, ctx) =>
    let fields := program.staticFields.map (·.name.text)
    !fields.contains "T1" && !fields.contains "T2" &&
    ctx.unsupportedModuleGlobals.contains "T1" &&
    ctx.unsupportedModuleGlobals.contains "T2"
  | .error _ => false

-- An ordinary annotated global is still lowered to a static field.
#guard
  match pythonToLaurel {} #[annAssign "value" (loadName "int") (some (intLiteral 1))] with
  | .ok (program, ctx) =>
    (program.staticFields.map (·.name.text)).contains "value" &&
    !ctx.unsupportedModuleGlobals.contains "value"
  | .error _ => false

end StrataPython.ToLaurel.Tests

end
