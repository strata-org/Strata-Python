/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataPython.UnknownSource
import StrataPython.PythonLaurelTypedExpr
public import StrataPython.Specs.Decls
public import Strata.Pipeline.Messages
import StrataPython.Specs.DDM
import Strata.Util.DecideProp
public import StrataPython.OverloadTable
import StrataPython.Specs.MessageKind

open Strata
open Strata.Laurel
open Strata.Pipeline (PipelineMessage MessageKind Phase)
open StrataPython.Laurel (SomeTypedStmtExpr TypedStmtExpr)

/-!
# PySpec to Laurel Translation

This module provides translation from PySpec signatures to Laurel declarations.

PySpec files contain type signatures extracted from Python code. This translator
converts those signatures into Laurel programs that can be verified.

## Translation Strategy

- `functionDecl`: Functions become Laurel procedures with opaque bodies
- `classDef`: Classes become composite types plus methods as procedures
- `typeDef`: Type definitions become composite type placeholders
- `externTypeDecl`: Ignored — PySpec fully qualifies imported class names
-/

namespace StrataPython

public section

private def typeTestersMap : Std.HashMap PythonIdent String :=
  .ofList [
    (.builtinsInt,       "Any..isfrom_int"),
    (.builtinsStr,       "Any..isfrom_str"),
    (.builtinsBool,      "Any..isfrom_bool"),
    (.builtinsFloat,     "Any..isfrom_float"),
    (.noneType,          "Any..isfrom_None"),
    (.builtinsBytes,     "Any..isfrom_bytes"),
    (.typingList,        "Any..isfrom_ListAny"),
    (.typingSequence,    "Any..isfrom_ListAny"),
    (.typingDict,        "Any..isfrom_DictStrAny"),
    (.typingMapping,     "Any..isfrom_DictStrAny"),
    (.builtinsException, "Any..isexception")
  ]

/-- Fully qualified Laurel name for a `PythonIdent`: module dots become
    underscores. E.g., `"mylib.sub"` / `"Foo"` → `"mylib_sub_Foo"`. -/
def PythonIdent.toLaurelName (id : PythonIdent) : String :=
  id.toString (sep := "_")

end -- public section

namespace Specs.ToLaurel

/-! ## ToLaurelM Monad -/

/-- Context for PySpec to Laurel translation. -/
structure ToLaurelContext where
  filepath : System.FilePath
  /-- Module prefix prepended to generated type and procedure names
      to avoid collisions when multiple PySpec files are combined. -/
  modulePrefix : String

/-- State for PySpec to Laurel translation. -/
structure ToLaurelState where
  errors : Array PipelineMessage := #[]
  procedures : Array Procedure := #[]
  types : Array TypeDefinition := #[]
  overloads : OverloadTable := {}
  /-- Maps unprefixed class names to prefixed names for type resolution. -/
  typeAliases : Std.HashMap String String := {}
  /-- Classes whose spec is considered exhaustive (lists all methods). -/
  exhaustiveClasses : Std.HashSet String := {}

/-- Monad for PySpec to Laurel translation. -/
abbrev ToLaurelM := ReaderT ToLaurelContext (StateM ToLaurelState)

/-- Report an error during translation. Phase is set to pySpecToLaurel since
    this monad always runs during that phase. -/
def reportError (kind : MessageKind) (loc : SourceRange) (message : String) : ToLaurelM Unit := do
  let phase := Phase.base "pySpecToLaurel"
  let e : PipelineMessage :=
    { phase, message := { fileRange := { file := .file (←read).filepath.toString, range := loc }, message, kind } }
  modify fun s => { s with errors := s.errors.push e }

def runChecked (act : ToLaurelM α) : ToLaurelM (α × Bool) := do
  let old := (←get).errors.size
  let r ← act
  let new := (←get).errors.size
  pure (r, old = new)

/-- Add a Laurel procedure to the output. -/
def pushProcedure (proc : Procedure) : ToLaurelM Unit :=
  modify fun s => { s with procedures := s.procedures.push proc }

/-- Add a Laurel type definition to the output. -/
def pushType (td : TypeDefinition) : ToLaurelM Unit :=
  modify fun s => { s with types := s.types.push td }

/-- Add an overload dispatch entry for a function. -/
def pushOverloadEntry (funcName : String) (paramName : String)
    (literalValue : String) (returnType : PythonIdent) : ToLaurelM Unit := do
  match (←get).overloads[funcName]? with
  | none =>
    modify fun s =>
      let entry : FunctionOverloads := {
        paramName := paramName
        entries := {(literalValue, returnType)}
      }
      { s with overloads := s.overloads.insert funcName entry }
  | some existing =>
    if existing.paramName != paramName then
      reportError .overloadParamNameDisagreement default
        s!"Overload entries for '{funcName}' disagree on dispatch parameter \
          name: existing '{existing.paramName}', new '{paramName}'"
    modify fun s =>
      { s with overloads := s.overloads.modify funcName fun existing =>
          { existing with entries := existing.entries.insert literalValue returnType }
      }

/-- Extract an overload dispatch entry from an `@overload` function declaration.
    Contracts are rejected first: no procedure is generated for a dispatch-only
    stub, so an `@ensures` or `@admit` on it would otherwise be silently
    dropped. -/
def extractOverloadEntry (func : FunctionDecl) : ToLaurelM Unit := do
  for postExpr in func.postconditions do
    reportError .unsupportedPostcondition postExpr.loc
      s!"Modeled @ensures cannot be verified for '{func.name}': {postExpr}. An @overload stub is a dispatch-only declaration; no procedure is generated for it, so the postcondition would be silently dropped. Attach the contract to a non-overload declaration instead."
  for admittedExpr in func.admittedPostconditions do
    reportError .unsupportedAdmit admittedExpr.loc
      s!"@admit is not supported on @overload stub '{func.name}': {admittedExpr}. No procedure body is generated for a dispatch-only declaration, so there is nowhere to assume the predicate. Attach the @admit to a non-overload declaration instead."
  let args := func.args.args
  let .isTrue _ := decideProp (args.size > 0)
    | reportError .overloadNoArgs func.loc
        s!"Overloaded function '{func.name}' has no arguments"
      return
  let firstArgType := args[0].type
  let literalValue ←
        match firstArgType.asStringLiteral with
        | some v => pure v
        | none =>
          reportError .overloadArgNotStringLiteral func.loc
            s!"Overloaded function '{func.name}': first argument \
              type '{firstArgType}' is not a \
              string literal (only string literal dispatch is \
              currently supported)"
          return
  let retType ←
        match func.returnType.asIdent with
        | some nm => pure nm
        | none =>
          reportError .overloadReturnNotClass func.loc
            s!"Overloaded function '{func.name}': return type \
              '{func.returnType}' is not a \
              class type"
          return
  pushOverloadEntry func.name args[0].name literalValue retType

/-- Prepend the module prefix to a name. -/
def prefixName (name : String) : ToLaurelM String := do
  let ctx ← read
  return ctx.modulePrefix ++ "_" ++ name

/-! ## Helper Functions -/

/-- Create a HighTypeMd with default metadata. -/
private def mkTy (ty : HighType) : HighTypeMd :=
  { val := ty, source := unknownSource }

/-- Create a UserDefined type referencing a Laurel prelude type by name. -/
private def mkUserDefined (s : String) : HighTypeMd :=
  { val := .UserDefined (mkId s), source := unknownSource }

/-! ### Laurel type constants -/

private def tyAny         : HighTypeMd := mkUserDefined "Any"
private def tyDictStrAny  : HighTypeMd := mkUserDefined "DictStrAny"

/-! ## Type Translation -/

public def builtinIdents : Std.HashSet PythonIdent :=
  .ofList [
    .builtinsBool, .builtinsBytearray, .builtinsBytes, .builtinsComplex,
    .builtinsDict, .builtinsException, .builtinsFloat, .builtinsInt,
    .builtinsStr, .noneType, .typingAny, .typingBinaryIO, .typingDict,
    .typingList
  ]

/-- Convert a SpecType to a Laurel HighTypeMd.
    Composites → `UserDefined`, everything else → `Any`. -/
def specTypeToLaurelType (ty : SpecType) : ToLaurelM HighTypeMd := do
  match ty.asIdent with
  | some nm =>
    if nm ∈ builtinIdents then
      return tyAny
    return mkTy (.UserDefined { text := nm.toLaurelName })
  | none => return tyAny

/-- Build the assertion for a single atom: type tester for idents,
    `isfrom_X(v) && as_X!(v) == literal` for literals.
    When `isUnion` is true, warns on ident atoms that lack testers.
    Always warns on TypedDict (needs a dedicated checker). -/
private def atomAssertion? (atom : SpecAtomType) (ty : SpecType)
    (value : StmtExprMd) (source : FileRange)
    (isUnion : Bool) : ToLaurelM (Option StmtExprMd) := do
  let mk (e : StmtExpr) : StmtExprMd := { val := e, source := source }
  match atom with
  | .ident nm _ =>
    match typeTestersMap[nm]? with
    | some testerName =>
      return some <| mk (.StaticCall (mkId testerName) [value])
    | none =>
      if nm != .typingAny && isUnion then
        reportError .unsupportedUnion ty.loc s!"No type tester for '{nm}' in type '{ty}'"
      return none
  | .intLiteral v =>
    let typeCheck := mk (.StaticCall (mkId "Any..isfrom_int") [value])
    let unwrap := mk (.StaticCall (mkId "Any..as_int!") [value])
    let eqCheck := mk (.StaticCall (mkId Operation.Eq.procName) [unwrap, mk (.LiteralInt v)])
    return some <| mk (.StaticCall (mkId Operation.And.procName) [typeCheck, eqCheck])
  | .stringLiteral v =>
    let typeCheck := mk (.StaticCall (mkId "Any..isfrom_str") [value])
    let unwrap := mk (.StaticCall (mkId "Any..as_string!") [value])
    let eqCheck := mk (.StaticCall (mkId Operation.Eq.procName) [unwrap, mk (.LiteralString v)])
    return some <| mk (.StaticCall (mkId Operation.And.procName) [typeCheck, eqCheck])
  | .typedDict .. =>
    return some <| mk (.StaticCall (mkId "Any..isfrom_DictStrAny") [value])

/-- Build a type-assertion expression for `value` given its declared `SpecType`.
    Returns `none` when no assertion is needed (all atoms are Any/composites).
    For union types, builds a disjunction over per-atom assertions. -/
private def typeAssertion? (ty : SpecType) (value : StmtExprMd)
    (source : FileRange) : ToLaurelM (Option StmtExprMd) := do
  let mut result : Option StmtExprMd := none
  for atom in ty.atoms do
    match atom with
    | .ident nm _ =>
      if nm = .typingAny then
        return none
    | _ => pure ()
    match ← atomAssertion? atom ty value source (ty.atoms.size > 1) with
    | some call =>
      match result with
      | none => result := some call
      | some prev =>
        result := some { val := .StaticCall (mkId Operation.Or.procName) [prev, call], source := source }
    | none => pure ()
  return result

/-! ## SpecExpr to Laurel Translation -/

/-- Create file-level source from the current pyspec filepath.
    Uses a default (zero) source range; callers with a specific location
    should use `mkSourceWithFileRange` instead. -/
private def mkFileSource : ToLaurelM FileRange := do
  let ctx ← read
  return { file := .file ctx.filepath.toString, range := default }

/-- Create source with a file range from the current pyspec file. -/
private def mkSourceWithFileRange (loc : SourceRange)
    : ToLaurelM FileRange := do
  let ctx ← read
  return { file := .file ctx.filepath.toString, range := loc }

/-- Wrap a StmtExpr with source containing a file range. -/
private def mkStmtWithLoc (e : StmtExpr) (loc : SourceRange)
    : ToLaurelM StmtExprMd := do
  let ctx ← read
  let fr : FileRange := { file := .file ctx.filepath.toString, range := loc }
  return { val := e, source := fr }

/--
Context for resolving identifiers.
-/
structure SpecExprContext where
  procName : String
  argTypes : Std.HashMap String HighType
  /-- Source-level types used to select map-native dictionary lowering. -/
  specTypes : Std.HashMap String SpecType := {}
  /-- Quantifier-bound names that resolve to a prebuilt Any-typed expression
      rather than a plain identifier. Used to inline a dict `for k, v` value
      binder as `d[k]`, so a single key quantifier suffices (avoiding a fragile
      two-binder trigger). -/
  boundValues : Std.HashMap String StmtExprMd := {}
  /-- Current quantifier nesting depth. Nested binders are alpha-renamed to
      Laurel-only names so they cannot capture identifiers embedded in an outer
      `boundValues` expression. -/
  quantifierDepth : Nat := 0

abbrev ToLaurelExprM := ReaderT SpecExprContext ToLaurelM

private def asAny (loc : SourceRange) (act : ToLaurelExprM SomeTypedStmtExpr) : ToLaurelExprM (TypedStmtExpr StrataPython.Laurel.tyAny) := do
  let ctx ← read
  let (se, success) ← runChecked <| act ctx
  if !success then
    return ⟨se.2.stmt⟩
  match se with
  | ⟨.UserDefined id, e⟩ =>
    if id.text == "Any" then pure ⟨e.stmt⟩
    else
      let pn := (← read).procName
      reportError .typeError loc s!"Expected Any-typed expression but got {repr (HighType.UserDefined id)} in '{pn}'"
      pure ⟨e.stmt⟩
  -- Box a scalar (bool/int) sub-expression into Any when used as a value.
  | ⟨.TBool, e⟩ => pure (.fromBool e)
  | ⟨.TInt, e⟩ => pure (.fromInt e)
  | ⟨tp, e⟩ =>
    let pn := (← read).procName
    reportError .typeError loc s!"Expected Any-typed expression but got {repr tp} in '{pn}'"
    pure ⟨e.stmt⟩

private def asBool (loc : SourceRange) (act : ToLaurelExprM SomeTypedStmtExpr) : ToLaurelExprM (TypedStmtExpr .TBool) := do
  let ctx ← read
  let (se, success) ← runChecked <| act ctx
  if !success then
    return ⟨se.2.stmt⟩
  match se with
  | ⟨.TBool, e⟩ => pure e
  -- Coerce an Any-typed operand (e.g. a bool param, which lowers to Any) into a
  -- bool via `Any_to_bool`, mirroring the body translator's boolean contexts.
  | ⟨.UserDefined id, e⟩ =>
    if id.text == "Any" then pure (.anyToBool ⟨e.stmt⟩)
    else
      let pn := (← read).procName
      reportError .typeError loc s!"Expected Bool-typed expression but got {repr (HighType.UserDefined id)} in '{pn}'"
      pure ⟨e.stmt⟩
  | ⟨tp, e⟩ =>
    let pn := (← read).procName
    reportError .typeError loc s!"Expected Bool-typed expression but got {repr tp} in '{pn}'"
    pure ⟨e.stmt⟩

private def asDict (loc : SourceRange) (act : ToLaurelExprM SomeTypedStmtExpr)
    : ToLaurelExprM (TypedStmtExpr StrataPython.Laurel.TypedStmtExpr.tyDictStrAny) := do
  let ctx ← read
  let (se, success) ← runChecked <| act ctx
  if !success then
    return ⟨se.2.stmt⟩
  match se with
  | ⟨.UserDefined id, e⟩ =>
    if id.text == "DictStrAny" then
      pure ⟨e.stmt⟩
    else if id.text == "Any" then
      pure (TypedStmtExpr.anyAsDict ⟨e.stmt⟩)
    else
      let pn := (← read).procName
      reportError .loweringTypeError loc
        s!"Expected dictionary expression but got {repr (HighType.UserDefined id)} in '{pn}'"
      pure ⟨e.stmt⟩
  | ⟨tp, e⟩ =>
    let pn := (← read).procName
    reportError .loweringTypeError loc s!"Expected dictionary expression but got {repr tp} in '{pn}'"
    pure ⟨e.stmt⟩

-- A dictionary operand boxed as `Any`: the bare `DictStrAny` of `**kwargs`
-- boxes via `from_DictStrAny`; `Any`-represented dictionaries pass through.
private def asDictAny (loc : SourceRange) (act : ToLaurelExprM SomeTypedStmtExpr)
    : ToLaurelExprM (TypedStmtExpr StrataPython.Laurel.tyAny) := do
  let ctx ← read
  let (se, success) ← runChecked <| act ctx
  if !success then
    return ⟨se.2.stmt⟩
  match se with
  | ⟨.UserDefined id, e⟩ =>
    if id.text == "DictStrAny" then
      pure (.ofStmt (.StaticCall (mkId "from_DictStrAny") [e.stmt]) e.stmt.source)
    else if id.text == "Any" then
      pure ⟨e.stmt⟩
    else
      let pn := (← read).procName
      reportError .loweringTypeError loc
        s!"Expected dictionary expression but got {repr (HighType.UserDefined id)} in '{pn}'"
      pure ⟨e.stmt⟩
  | ⟨tp, e⟩ =>
    let pn := (← read).procName
    reportError .loweringTypeError loc s!"Expected dictionary expression but got {repr tp} in '{pn}'"
    pure ⟨e.stmt⟩

private inductive SpecDictKind where
  | homogeneous (valueType : SpecType)
  | typedDict

private def specDictKind? (tp : SpecType) : Option SpecDictKind :=
  if let some (keyType, valueType) := tp.extractDictKeyValueTypes then
    if keyType.isStringType then some (.homogeneous valueType) else none
  else if tp.asIdent == some .builtinsDict ||
      tp.asIdent == some .typingDict ||
      tp.asIdent == some .typingMapping then
    some (.homogeneous (.ident tp.loc .typingAny))
  else
    if tp.isTypedDict then some .typedDict else none

private partial def specTypeOf? : SpecExpr → ToLaurelExprM (Option SpecType)
  | .var name _ => do return (← read).specTypes[name]?
  | .old inner _ => specTypeOf? inner
  | .getIndex subject field _ => do
    let some subjectType ← specTypeOf? subject | return none
    if let some fieldType := subjectType.lookupTypedDictField field then
      return some fieldType
    match specDictKind? subjectType with
    | some (.homogeneous valueType) => return some valueType
    | _ => return none
  | .getItem subject _ _ => do
    let some subjectType ← specTypeOf? subject | return none
    match specDictKind? subjectType with
    | some (.homogeneous valueType) => return some valueType
    | _ => return none
  | _ => return none

private def specDictKindOf? (e : SpecExpr) : ToLaurelExprM (Option SpecDictKind) := do
  return (← specTypeOf? e).bind specDictKind?

private def dictModelOf (dict : TypedStmtExpr StrataPython.Laurel.TypedStmtExpr.tyDictStrAny)
    (source : FileRange) :
    TypedStmtExpr StrataPython.Laurel.TypedStmtExpr.tyPySpecDictMap :=
  TypedStmtExpr.pySpecDictModelOf dict source

private def dictSelect
    (dict : TypedStmtExpr StrataPython.Laurel.TypedStmtExpr.tyDictStrAny)
    (key : TypedStmtExpr .TString) (source : FileRange) :
    TypedStmtExpr StrataPython.Laurel.TypedStmtExpr.tyPySpecDictValue :=
  TypedStmtExpr.pySpecDictSelect (dictModelOf dict source) key source

private def dictScalarEq
    (left right : TypedStmtExpr StrataPython.Laurel.TypedStmtExpr.tyDictStrAny)
    (source : FileRange) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "PySpecDict_scalarEq")
    [left.stmt, right.stmt]) source

private def anyScalarEq
    (left right : TypedStmtExpr StrataPython.Laurel.tyAny)
    (source : FileRange) : TypedStmtExpr .TBool :=
  .ofStmt (.StaticCall (mkId "PySpecAny_scalarEq")
    [left.stmt, right.stmt]) source

/-- Look up an identifier's type from the SpecExprContext and create a typed identifier.
    Reports a typeError if the name is not found in argTypes. -/
private def lookupIdentifier (name : String) (loc : SourceRange) (source : FileRange)
    : ToLaurelExprM SomeTypedStmtExpr := do
  let ctx ← read
  if let some stmt := ctx.boundValues[name]? then
    return .mkSome (⟨stmt⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  match ctx.argTypes[name]? with
  | some tp => return .mkSome <| .identifier name tp source
  | none =>
    reportError .typeError loc s!"Unknown identifier '{name}' in '{ctx.procName}'"
    return default

/-- Laurel prelude function realizing each abstract `PCmpOp`. This is the single
    place that maps the backend-agnostic PySpec operator onto a prelude name. -/
def pcmpPreludeName : PCmpOp → String
  | .lt => "PLt"
  | .le => "PLe"
  | .gt => "PGt"
  | .ge => "PGe"
  | .eq => "PEq"
  | .ne => "PNEq"
  | .isIn => "PIn"
  | .notIn => "PNotIn"

/-- Translate a SpecExpr to a typed Laurel expression (`SomeTypedStmtExpr`).
    Returns `default` (a `Hole`) for unsupported expressions; callers use
    `runChecked` to detect whether errors were reported during translation.
    Uses Core prelude function names (Any_len, DictStrAny_contains, etc.)
    which are resolved after the Core prelude is prepended. -/
def specExprToLaurel (e : SpecExpr) (source : FileRange)
  : ToLaurelExprM SomeTypedStmtExpr :=
  -- Use per-node source range when available, falling back to the
  -- nearest ancestor's source for nodes with default (empty) locations.
  -- This is intentional: the parent's location is a closer approximation
  -- than the function-level source for nodes without their own location.
  let nodeSource (loc : SourceRange) : ToLaurelM FileRange := do
    if loc == default then
      pure source
    else do
      let fr : FileRange := { file := .file (← read).filepath.toString, range := loc }
      pure fr
  match e with
  | .placeholder loc => do
    reportError .placeholderExpr loc "Placeholder expression not translatable"
    return default
  | .var name loc => do
    let src ← nodeSource loc
    lookupIdentifier name loc src
  | .old inner loc => do
    let src ← nodeSource loc
    let ⟨tp, e⟩ ← specExprToLaurel inner src
    return ⟨tp, .old e⟩
  -- Scalar literals box into `Any`: `from{Int,Bool,None}` build the prelude
  -- `from_int`/`from_bool`/`from_None` calls, and `mkSome` packages the result
  -- as a `SomeTypedStmtExpr` (its `HighType` paired with the typed expression).
  | .intLit v loc => do
    let src ← nodeSource loc
    return .mkSome <| .fromInt (.literalInt v src)
  | .boolLit b loc => do
    let src ← nodeSource loc
    return .mkSome <| .fromBool (.literalBool b src)
  | .noneLit loc => do
    let src ← nodeSource loc
    return .mkSome <| .fromNone src
  | .floatLit _ loc => do
    reportError .floatLiteral loc "Float literals not yet supported in preconditions"
    return default
  | .getIndex subject field loc => do
    if (← specDictKindOf? subject).isSome then do
      let src ← nodeSource loc
      let dict ← asDict loc <| specExprToLaurel subject src
      let selected := dictSelect dict (.literalString field src) src
      return .mkSome <| TypedStmtExpr.pySpecDictValueChecked selected src
    else do
      let src ← nodeSource loc
      let s ← asAny loc <| specExprToLaurel subject src
      let from_str := TypedStmtExpr.fromStr (.literalString field src) src
      return .mkSome <| .anyGet s from_str src
  | .getItem subject key loc => do
    let src ← nodeSource loc
    let dict ← asDict loc <| specExprToLaurel subject src
    let keyAny ← asAny loc <| specExprToLaurel key src
    let selected := dictSelect dict (keyAny.anyAsStringChecked src) src
    return .mkSome <| TypedStmtExpr.pySpecDictValueChecked selected src
  | .isInstanceOf _ typeName loc => do
    reportError .isinstanceUnsupported loc s!"isinstance check for '{typeName}' not yet supported in preconditions"
    return default
  | .stringLen subject loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    return .mkSome <| .fromInt (.strLength (.anyAsString s))
  | .intGe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    -- `>=` -> runtime `Any_to_bool(PGe(..))`, matching the body translator.
    let cmp : StmtExprMd := { val := .StaticCall (mkId "PGe") [s.stmt, b.stmt], source := src }
    return .mkSome (⟨{ val := .StaticCall (mkId "Any_to_bool") [cmp], source := src }⟩ : TypedStmtExpr .TBool)
  | .intLe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    let cmp : StmtExprMd := { val := .StaticCall (mkId "PLe") [s.stmt, b.stmt], source := src }
    return .mkSome (⟨{ val := .StaticCall (mkId "Any_to_bool") [cmp], source := src }⟩ : TypedStmtExpr .TBool)
  | .pcmp op lhs rhs loc => do
    let src ← nodeSource loc
    let lhsDictKind ← specDictKindOf? lhs
    let rhsDictKind ← specDictKindOf? rhs
    if (op == .eq || op == .ne) && lhsDictKind.isSome && rhsDictKind.isSome then
      let l ← asDict loc <| specExprToLaurel lhs src
      let r ← asDict loc <| specExprToLaurel rhs src
      let eq := dictScalarEq l r src
      if op == .eq then
        return .mkSome eq
      return .mkSome <| TypedStmtExpr.not eq src
    else if (op == .eq || op == .ne) && (lhsDictKind.isSome || rhsDictKind.isSome) then
      -- One statically-dict side: `PySpecAny_scalarEq` stays extensional when
      -- the other operand is a dict at runtime, unlike order-sensitive `PEq`.
      let l ← if lhsDictKind.isSome then asDictAny loc <| specExprToLaurel lhs src
              else asAny loc <| specExprToLaurel lhs src
      let r ← if rhsDictKind.isSome then asDictAny loc <| specExprToLaurel rhs src
              else asAny loc <| specExprToLaurel rhs src
      let eq := anyScalarEq l r src
      if op == .eq then
        return .mkSome eq
      return .mkSome <| TypedStmtExpr.not eq src
    else
      let l ← asAny loc <| specExprToLaurel lhs src
      let r ← asAny loc <| specExprToLaurel rhs src
      let cmp : StmtExprMd := { val := .StaticCall (mkId (pcmpPreludeName op)) [l.stmt, r.stmt], source := src }
      return .mkSome (⟨{ val := .StaticCall (mkId "Any_to_bool") [cmp], source := src }⟩ : TypedStmtExpr .TBool)
  | .add lhs rhs loc => do
    -- Addition -> runtime `PAdd` over Any operands.
    let src ← nodeSource loc
    let l ← asAny loc <| specExprToLaurel lhs src
    let r ← asAny loc <| specExprToLaurel rhs src
    let addExpr : StmtExprMd := { val := .StaticCall (mkId "PAdd") [l.stmt, r.stmt], source := src }
    return .mkSome (⟨addExpr⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  | .sub lhs rhs loc => do
    let src ← nodeSource loc
    let l ← asAny loc <| specExprToLaurel lhs src
    let r ← asAny loc <| specExprToLaurel rhs src
    let subExpr : StmtExprMd := { val := .StaticCall (mkId "PSub") [l.stmt, r.stmt], source := src }
    return .mkSome (⟨subExpr⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  | .mul lhs rhs loc => do
    let src ← nodeSource loc
    let l ← asAny loc <| specExprToLaurel lhs src
    let r ← asAny loc <| specExprToLaurel rhs src
    let mulExpr : StmtExprMd := { val := .StaticCall (mkId "PMul") [l.stmt, r.stmt], source := src }
    return .mkSome (⟨mulExpr⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  | .floorDiv lhs rhs loc => do
    let src ← nodeSource loc
    let l ← asAny loc <| specExprToLaurel lhs src
    let r ← asAny loc <| specExprToLaurel rhs src
    let e : StmtExprMd := { val := .StaticCall (mkId "PFloorDiv") [l.stmt, r.stmt], source := src }
    return .mkSome (⟨e⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  | .mod lhs rhs loc => do
    let src ← nodeSource loc
    let l ← asAny loc <| specExprToLaurel lhs src
    let r ← asAny loc <| specExprToLaurel rhs src
    let e : StmtExprMd := { val := .StaticCall (mkId "PMod") [l.stmt, r.stmt], source := src }
    return .mkSome (⟨e⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  | .pow lhs rhs loc => do
    -- Exponentiation -> runtime `PPow` over Any operands.
    let src ← nodeSource loc
    let l ← asAny loc <| specExprToLaurel lhs src
    let r ← asAny loc <| specExprToLaurel rhs src
    let e : StmtExprMd := { val := .StaticCall (mkId "PPow") [l.stmt, r.stmt], source := src }
    return .mkSome (⟨e⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  | .neg operand loc => do
    -- Unary minus -> runtime `PNeg` over an Any operand.
    let src ← nodeSource loc
    let o ← asAny loc <| specExprToLaurel operand src
    let e : StmtExprMd := { val := .StaticCall (mkId "PNeg") [o.stmt], source := src }
    return .mkSome (⟨e⟩ : TypedStmtExpr StrataPython.Laurel.tyAny)
  | .floatGe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    return .mkSome <| .realGeq (.anyAsFloat s) (.anyAsFloat b)
  | .floatLe subject bound loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let b ← asAny loc <| specExprToLaurel bound src
    return .mkSome <| .realLeq (.anyAsFloat s) (.anyAsFloat b)
  | .not inner loc => do
    let src ← nodeSource loc
    let i ← asBool loc <| specExprToLaurel inner src
    return .mkSome <| .not i
  | .and lhs rhs loc => do
    let src ← nodeSource loc
    let l ← asBool loc <| specExprToLaurel lhs src
    let r ← asBool loc <| specExprToLaurel rhs src
    return .mkSome <| .and l r
  | .or lhs rhs loc => do
    let src ← nodeSource loc
    let l ← asBool loc <| specExprToLaurel lhs src
    let r ← asBool loc <| specExprToLaurel rhs src
    return .mkSome <| .or l r
  | .implies cond body loc => do
    let src ← nodeSource loc
    let c ← asBool loc <| specExprToLaurel cond src
    let b ← asBool loc <| specExprToLaurel body src
    return .mkSome <| .implies c b
  | .enumMember subject values loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let sStr := s.anyAsString
    return .mkSome <|
      values.foldl (init := .literalBool false) fun acc v =>
        .or acc (.stringEq sStr (.literalString v src))
  | .containsKey container key loc => do
    let src ← nodeSource loc
    if (← specDictKindOf? container).isSome then do
      let dict ← asDict loc <| specExprToLaurel container src
      let selected := dictSelect dict (.literalString key src) src
      return .mkSome <| TypedStmtExpr.pySpecDictIsPresent selected src
    else do
      let c ← asAny loc <| specExprToLaurel container src
      return .mkSome <| .dictStrAnyContains (c.anyAsDict) (.literalString key)
  | .regexMatch subject pattern loc => do
    let src ← nodeSource loc
    let s ← asAny loc <| specExprToLaurel subject src
    let sStr := .anyAsString s
    return .mkSome <| .reSearchBool (.literalString pattern) sStr
  | .quantifier quant domain collection body loc => do
    -- The domain supplies the binder, membership guard, trigger, and body
    -- environment. QuantKind determines how the guard combines with the body.
    let src ← nodeSource loc
    let ctx ← read
    -- Keep top-level names readable unless that name occurs in the collection:
    -- `for xs in xs` must retain the outer `xs` in the membership expression.
    -- Nested binders always use Laurel-only names, as compiler-generated
    -- temporaries elsewhere do, so they cannot capture identifiers embedded in
    -- an outer prebuilt value such as d[k].
    let freshBinderName (name : String) : String :=
      if ctx.quantifierDepth == 0 && !collection.mentionsVar name then name
      else s!"{pythonGeneratedPrefix}quant_{ctx.quantifierDepth}_{loc.start.byteIdx}_{name}"
    let (param, guard, trigger, bodyEnv) ←
      match domain with
      | .overList varName =>
        let collExpr ← asAny loc <| specExprToLaurel collection src
        let actualName := freshBinderName varName
        let elemVar := TypedStmtExpr.identifier actualName StrataPython.Laurel.tyAny src
        let membership := collExpr.anyAsList.listContains elemVar src
        let elemType := (← specTypeOf? collection).bind (·.extractElementType)
        let param : Parameter :=
          { name := mkId actualName, type := { val := StrataPython.Laurel.tyAny, source := src } }
        let bodyEnv := fun (c : SpecExprContext) => { c with
          argTypes := c.argTypes.insert varName StrataPython.Laurel.tyAny
          specTypes := match elemType with
            | some tp => c.specTypes.insert varName tp
            | none => c.specTypes
          boundValues := if actualName == varName
            then c.boundValues.erase varName
            else c.boundValues.insert varName elemVar.stmt
          quantifierDepth := c.quantifierDepth + 1 }
        pure (param, membership, membership.stmt, bodyEnv)
      | .overDictItems keyVar valVar =>
        let dict ← asDict loc <| specExprToLaurel collection src
        let valueType := match (← specDictKindOf? collection) with
          | some (.homogeneous tp) => some tp
          | _ => none
        let actualKey := freshBinderName keyVar
        let keyStr := TypedStmtExpr.identifier actualKey .TString src
        let selected := dictSelect dict keyStr src
        let membership := TypedStmtExpr.pySpecDictIsPresent selected src
        let valueLookup := TypedStmtExpr.pySpecDictValueUnchecked selected src
        let keyBoxed := keyStr.fromStr src
        let param : Parameter :=
          { name := mkId actualKey, type := { val := .TString, source := src } }
        let bodyEnv := fun (c : SpecExprContext) => { c with
          argTypes := c.argTypes.insert keyVar StrataPython.Laurel.tyAny
            |>.insert valVar StrataPython.Laurel.tyAny
          specTypes := match valueType with
            | some tp => c.specTypes
                |>.insert keyVar (.ident loc .builtinsStr)
                |>.insert valVar tp
            | none => c.specTypes.insert keyVar (.ident loc .builtinsStr)
          boundValues := c.boundValues
            |>.insert keyVar keyBoxed.stmt
            |>.insert valVar valueLookup.stmt
          quantifierDepth := c.quantifierDepth + 1 }
        pure (param, membership, selected.stmt, bodyEnv)
      | .overDictKeys keyVar =>
        let dict ← asDict loc <| specExprToLaurel collection src
        let actualKey := freshBinderName keyVar
        let keyStr := TypedStmtExpr.identifier actualKey .TString src
        let selected := dictSelect dict keyStr src
        let membership := TypedStmtExpr.pySpecDictIsPresent selected src
        let keyBoxed := keyStr.fromStr src
        let param : Parameter :=
          { name := mkId actualKey, type := { val := .TString, source := src } }
        let bodyEnv := fun (c : SpecExprContext) => { c with
          argTypes := c.argTypes.insert keyVar StrataPython.Laurel.tyAny
          specTypes := c.specTypes.insert keyVar (.ident loc .builtinsStr)
          boundValues := c.boundValues.insert keyVar keyBoxed.stmt
          quantifierDepth := c.quantifierDepth + 1 }
        pure (param, membership, selected.stmt, bodyEnv)
      | .overDictValues valVar =>
        let dict ← asDict loc <| specExprToLaurel collection src
        let valueType := match (← specDictKindOf? collection) with
          | some (.homogeneous tp) => some tp
          | _ => none
        let keyName := if ctx.quantifierDepth == 0 then pythonGeneratedPrefix ++ valVar
          else s!"{pythonGeneratedPrefix}quant_{ctx.quantifierDepth}_{loc.start.byteIdx}_key"
        let keyStr := TypedStmtExpr.identifier keyName .TString src
        let selected := dictSelect dict keyStr src
        let membership := TypedStmtExpr.pySpecDictIsPresent selected src
        let valueLookup := TypedStmtExpr.pySpecDictValueUnchecked selected src
        let param : Parameter :=
          { name := mkId keyName, type := { val := .TString, source := src } }
        let bodyEnv := fun (c : SpecExprContext) => { c with
          argTypes := c.argTypes.insert valVar StrataPython.Laurel.tyAny
          specTypes := match valueType with
            | some tp => c.specTypes.insert valVar tp
            | none => c.specTypes
          boundValues := c.boundValues.insert valVar valueLookup.stmt
          quantifierDepth := c.quantifierDepth + 1 }
        pure (param, membership, selected.stmt, bodyEnv)
    let bodyBool ← withReader bodyEnv <| asBool loc <| specExprToLaurel body src
    return .mkSome <|
      match quant with
      | .forall =>
        TypedStmtExpr.forallTrigger param trigger (guard.implies bodyBool) src
      | .exists =>
        -- See README.md "Spec quantifiers" for the user-visible limitation of
        -- membership-triggered existential preconditions.
        TypedStmtExpr.existsTrigger param trigger (guard.and bodyBool) src

private def formatAssertionMessage (msg : Array MessagePart) : String :=
  let parts := msg.map fun
    | .str s => s
    | .expr e => toString e
  String.join parts.toList

/-- Structured PySpec assertion messages. Rendered to string before storing
    in metadata so that rewording is centralized. -/
inductive SpecAssertMsg where
  | requiredParam (param : String)
  | userAssertion (text : String)
  | unnamed (index : Nat)

/-- Render a structured assertion message to a human-readable string. -/
def SpecAssertMsg.render : SpecAssertMsg → String
  | .requiredParam param => s!"'{param}' is required"
  | .userAssertion text  => text
  | .unnamed index       => s!"precondition {index}"

/-- Build an opaque procedure body with havoc and type/required-param
    assertions. Modeled `@ensures` postconditions are rejected for now:
    generated PySpec procedures have no implementation against which Strata can
    prove an `@ensures`, so silently exposing one to callers would be unsound.
    `@admit` postconditions — explicitly acknowledged as unverified modeling
    assumptions — are lowered as in-body `assume`s, like the trusted
    return-type assumption; an `@admit` that cannot be lowered is fatal.
    Returns the required-param not-None checks as caller-checked `Condition`s
    for `funcDeclToLaurel` to merge into the preconditions. -/
def buildSpecBody (allArgs : Array Arg)
    (postconditions : Array SpecExpr)
    (admittedPostconditions : Array SpecExpr)
    (returnType : SpecType)
    (source : FileRange)
    (ctx : SpecExprContext)
    : ToLaurelM (Body × List Condition) := do
  let fileSource ← mkFileSource
  let mut stmts : Array StmtExprMd := #[]
  let mut requiredParamConds : List Condition := []
  -- 1. Havoc the result: result := Hole(nondet)
  let holeExpr : StmtExprMd := { val := .Hole (deterministic := false), source := source }
  let resultId : AstNode Variable := { val := Variable.Local (mkId "result"), source := source }
  let assignStmt ← mkStmtWithLoc (.Assign [resultId] holeExpr) default
  stmts := stmts.push assignStmt
  -- 2. Type constraints stay in-body (caller-checking them would reject
  --    gradually-typed Any callers); only a no-default param's not-None
  --    check becomes a caller-checked precondition.
  for arg in allArgs do
    let paramId : StmtExprMd := { val := .Var $ Variable.Local (mkId arg.name), source := source }
    match ← typeAssertion? arg.type paramId source with
    | some assertion =>
      if arg.default.isSome then
        let noneCheck : StmtExprMd := { val := .StaticCall (mkId "Any..isfrom_None") [paramId], source := source }
        let orExpr : StmtExprMd := { val := .StaticCall (mkId Operation.Or.procName) [noneCheck, assertion], source := source }
        let assertStmt ← mkStmtWithLoc (.Assert orExpr none) default
        stmts := stmts.push assertStmt
      else
        let assertStmt ← mkStmtWithLoc (.Assert assertion none) default
        stmts := stmts.push assertStmt
    | none =>
      if arg.default.isNone then
        let cond : TypedStmtExpr _ := .not (.anyIsfromNone (.identifier arg.name StrataPython.Laurel.tyAny))
        let msg := SpecAssertMsg.requiredParam arg.name |>.render
        requiredParamConds := requiredParamConds ++
          [{ condition := cond.stmt, summary := some msg }]
  -- 3. Reject modeled `@ensures`. A PySpec declaration has no implementation
  --    to verify the predicate against, so it must not enter caller reasoning
  --    silently; `@admit` is the explicit opt-in for that assumption.
  for postExpr in postconditions do
    reportError .unsupportedPostcondition postExpr.loc
      s!"Modeled @ensures cannot be verified for '{ctx.procName}': {postExpr}. A PySpec declaration is a bodyless model, so Strata cannot verify this postcondition against an implementation and will not assume it at call sites. Loading a PySpec module containing @ensures aborts analysis even if the affected function is unused. Use @admit to accept the postcondition as an unverified modeling assumption, or model the function with a real body if the property must be checked."
  -- 4. Assume `@admit` postconditions in-body. The decorator is the author's
  --    acknowledgment that the predicate is an unverified assumption the
  --    verification depends on, so it joins the trusted return-type assume —
  --    and one that cannot be lowered must not be dropped silently.
  for admittedExpr in admittedPostconditions do
    let (⟨condType, condExpr⟩, success) ← runChecked <| specExprToLaurel admittedExpr source ctx
    if success then
      if let .TBool := condType then
        let assumeStmt ← mkStmtWithLoc (.Assume condExpr.stmt) default
        stmts := stmts.push assumeStmt
      else
        reportError .unsupportedAdmit admittedExpr.loc
          s!"@admit predicate is not Bool in '{ctx.procName}': {admittedExpr}. The verification depends on this acknowledged assumption, so it will not be dropped silently. Fix the predicate to be a boolean expression."
    else
      reportError .unsupportedAdmit admittedExpr.loc
        s!"@admit predicate of '{ctx.procName}' could not be translated: {admittedExpr}. The verification depends on this acknowledged assumption, so it will not be dropped silently. Rewrite the predicate using supported constructs."
  -- 5. Keep the return type postcondition in-body. Exposing inferred return
  --    types to callers is a separate semantic change from user contracts.
  -- NOTE. Skip NoneType: generated stubs currently declare `-> None` even for methods
  -- that return values. Assuming isfrom_None would make callers unreachable.
  if returnType.asIdent != some .noneType then
    let resultRef : StmtExprMd := { val := .Var $ Variable.Local (mkId "result"), source := source }
    if let some retAssertion ← typeAssertion? returnType resultRef source then
      let assumeStmt ← mkStmtWithLoc (.Assume retAssertion) default
      stmts := stmts.push assumeStmt
  let body := {
      val := .Block stmts.toList none,
      source := fileSource
  }
  return (.Opaque [] (some body) (ModifiesGroup.wildcard unknownSource), requiredParamConds)

/-- Lower user `@requires` preconditions into caller-checked Laurel
    `Condition`s (default `ConditionMode.Both`: proven at each call site,
    assumed inside the callee). -/
def buildPreconditionConds
    (preconditions : Array Assertion)
    (source : FileRange)
    (ctx : SpecExprContext)
    : ToLaurelM (List Condition) := do
  let mut conds : List Condition := []
  let mut idx := 0
  for assertion in preconditions do
    let formattedMsg := formatAssertionMessage assertion.message
    let msg := if formattedMsg.isEmpty
      then SpecAssertMsg.unnamed idx |>.render
      else SpecAssertMsg.userAssertion formattedMsg |>.render
    let (⟨condType, condExpr⟩, success) ← runChecked <| specExprToLaurel assertion.formula source ctx
    if success then
      if let .TBool := condType then
        conds := conds ++ [{ condition := condExpr.stmt, summary := some msg }]
      else
        reportError .typeError default
          s!"Precondition expression is not Bool in '{ctx.procName}' (skipping): {msg}"
    idx := idx + 1
  return conds

private def andAll (conditions : List (TypedStmtExpr .TBool))
    (source : FileRange) : TypedStmtExpr .TBool :=
  conditions.foldl (·.and · source) (.literalBool true source)

private def orAll (conditions : List (TypedStmtExpr .TBool))
    (source : FileRange) : TypedStmtExpr .TBool :=
  conditions.foldl (·.or · source) (.literalBool false source)

private def singletonSpecType (loc : SourceRange) : SpecAtomType → SpecType
  | .ident name args => .ident loc name args
  | .intLiteral value => .intLiteral loc value
  | .stringLiteral value => .stringLiteral loc value
  | .typedDict fields fieldTypes required =>
    .typedDict loc fields fieldTypes required

private inductive TypedDictSchemaMode where
  | openKeys
  | closedKeys
  deriving BEq

private def stringListExpr (values : List String)
    (source : FileRange) : StmtExprMd :=
  values.foldr
    (fun value tail => {
      val := .StaticCall (mkId "ListStr_cons")
        [{ val := .LiteralString value, source }, tail]
      source })
    { val := .StaticCall (mkId "ListStr_nil") [], source }

private partial def schemaValueAssertion? (typedDictMode : TypedDictSchemaMode)
    (path : String) (tp : SpecType)
    (value : StmtExprMd) (source : FileRange)
    : ToLaurelM (Option StmtExprMd) := do
  let hasAny := tp.atoms.any fun
    | .ident name _ => name == .typingAny
    | _ => false
  if hasAny then
    return none
  if tp.atoms.size > 1 && tp.hasContainerAtom then
    let mut arms : List (TypedStmtExpr .TBool) := []
    for atom in tp.atoms do
      let atomType := singletonSpecType tp.loc atom
      match ← schemaValueAssertion? typedDictMode path atomType value source with
      | some condition =>
        arms := arms ++ [(⟨condition⟩ : TypedStmtExpr .TBool)]
      | none => return none
    return some (orAll arms source).stmt
  if let some kind := specDictKind? tp then
    let anyValue : TypedStmtExpr StrataPython.Laurel.tyAny := ⟨value⟩
    let isDict := anyValue.anyIsfromDict source
    let dict := anyValue.anyAsDict source
    let model := dictModelOf dict source
    let binderPath := (path.replace "." "_").replace "[]" "_list"
    let schema ←
      match kind with
      | .homogeneous valueType => do
        let keyName := s!"{pythonGeneratedPrefix}schema_dict_{binderPath}"
        let key := TypedStmtExpr.identifier keyName .TString source
        let selected := TypedStmtExpr.pySpecDictSelect model key source
        let present := TypedStmtExpr.pySpecDictIsPresent selected source
        let nestedValue := TypedStmtExpr.pySpecDictValueUnchecked selected source
        let nestedCondition ←
          schemaValueAssertion? .openKeys s!"{path}.value"
            valueType nestedValue.stmt source
        let body := match nestedCondition with
          | some condition =>
            present.implies (⟨condition⟩ : TypedStmtExpr .TBool) source
          | none => .literalBool true source
        let param : Parameter :=
          { name := mkId keyName, type := { val := .TString, source } }
        pure <| TypedStmtExpr.forallTrigger param selected.stmt body source
      | .typedDict => do
        let fields := tp.asTypedDict.getD #[]
        let mut conditions : List (TypedStmtExpr .TBool) := []
        if typedDictMode == .closedKeys then
          -- Keep the map universal as the logical contract. The equivalent
          -- structural check gives concrete dictionaries a finite solver witness.
          let allowedKeys := stringListExpr (fields.toList.map (·.name)) source
          conditions := conditions ++ [
            TypedStmtExpr.ofStmt
              (.StaticCall (mkId "DictStrAny_keysAllowed")
                [dict.stmt, allowedKeys]) source]
          let keyName := s!"{pythonGeneratedPrefix}schema_dict_key_{binderPath}"
          let key := TypedStmtExpr.identifier keyName .TString source
          let selected := TypedStmtExpr.pySpecDictSelect model key source
          let present := TypedStmtExpr.pySpecDictIsPresent selected source
          let allowed := fields.foldl
            (init := TypedStmtExpr.literalBool false source) fun acc field =>
              acc.or (key.stringEq (.literalString field.name source) source) source
          let keyParam : Parameter :=
            { name := mkId keyName, type := { val := .TString, source } }
          conditions := conditions ++ [
            TypedStmtExpr.forallTrigger keyParam selected.stmt
              (present.implies allowed source) source]
        for field in fields do
          let fieldKey := TypedStmtExpr.literalString field.name source
          let selected := TypedStmtExpr.pySpecDictSelect model fieldKey source
          let present := TypedStmtExpr.pySpecDictIsPresent selected source
          if field.required then
            conditions := conditions ++ [present]
          let nestedValue := TypedStmtExpr.pySpecDictValueUnchecked selected source
          if let some condition ← schemaValueAssertion? .openKeys
              s!"{path}.{field.name}" field.type nestedValue.stmt source then
            conditions := conditions ++
              [present.implies (⟨condition⟩ : TypedStmtExpr .TBool) source]
        pure <| andAll conditions source
    return some (isDict.and schema source).stmt
  if let some elemType := tp.extractElementType then
    let listValue : TypedStmtExpr StrataPython.Laurel.tyAny := ⟨value⟩
    let isList : TypedStmtExpr .TBool :=
      .ofStmt (.StaticCall (mkId "Any..isfrom_ListAny") [value]) source
    let list := listValue.anyAsList source
    let binderPath := (path.replace "." "_").replace "[]" "_list"
    let elemName := s!"{pythonGeneratedPrefix}schema_list_{binderPath}"
    let elem := TypedStmtExpr.identifier elemName StrataPython.Laurel.tyAny source
    let contains := TypedStmtExpr.listContains list elem source
    let elemCondition ← schemaValueAssertion? .openKeys
      s!"{path}[]" elemType elem.stmt source
    let body := match elemCondition with
      | some condition =>
        contains.implies (⟨condition⟩ : TypedStmtExpr .TBool) source
      | none => .literalBool true source
    let param : Parameter :=
      { name := mkId elemName, type := { val := StrataPython.Laurel.tyAny, source } }
    let allElements := TypedStmtExpr.forallTrigger param contains.stmt body source
    return some (isList.and allElements source).stmt
  if tp.hasContainerAtom then
    reportError .dictionarySchemaWarning tp.loc
      s!"Container type '{tp}' cannot be modeled (dictionaries require string keys); the schema of '{path}' is not enforced"
    return none
  let hasUnsupportedAtom := tp.atoms.any fun
    | .ident name _ => typeTestersMap[name]?.isNone
    | .intLiteral _ | .stringLiteral _ => false
    | .typedDict .. => true
  if hasUnsupportedAtom then
    return none
  let assertion ← typeAssertion? tp value source
  return assertion

/-- Caller-visible schema for a dictionary-typed parameter. Runtime values stay
    in `DictStrAny`; these conditions inspect only their logical map view.
    TypedDict schemas are split per aspect so a violated obligation names the
    offending field. -/
private def dictSchemaConditions (arg : Arg) (rawDictInput : Bool)
    (typedDictMode : TypedDictSchemaMode) (source : FileRange)
    : ToLaurelM (List Condition) := do
  if (specDictKind? arg.type).isNone then
    if rawDictInput || !arg.type.hasDictionaryAtom then
      return []
    let value :=
      TypedStmtExpr.identifier arg.name StrataPython.Laurel.tyAny source
    let some condition ←
        schemaValueAssertion? typedDictMode arg.name arg.type value.stmt source
      | return []
    return [{
      condition
      summary := some s!"'{arg.name}' must satisfy its declared dictionary type" }]
  let some kind := specDictKind? arg.type
    | return []
  let (dict, tagCondition) :=
    if rawDictInput then
      (TypedStmtExpr.identifier arg.name
          StrataPython.Laurel.TypedStmtExpr.tyDictStrAny source,
        TypedStmtExpr.literalBool true source)
    else
      let value := TypedStmtExpr.identifier arg.name StrataPython.Laurel.tyAny source
      (value.anyAsDict source, value.anyIsfromDict source)
  let model := dictModelOf dict source
  let mkCondition (aspect : TypedStmtExpr .TBool) (summary : String) : Condition :=
    let condition := tagCondition.and aspect source
    let condition :=
      if arg.default.isSome && !rawDictInput then
        let value := TypedStmtExpr.identifier arg.name StrataPython.Laurel.tyAny source
        value.anyIsfromNone source |>.or condition source
      else condition
    { condition := condition.stmt, summary := some summary }
  match kind with
  | .homogeneous valueType =>
    let keyName := s!"{pythonGeneratedPrefix}schema_{arg.name}"
    let key := TypedStmtExpr.identifier keyName .TString source
    let selected := TypedStmtExpr.pySpecDictSelect model key source
    let present := TypedStmtExpr.pySpecDictIsPresent selected source
    let value := TypedStmtExpr.pySpecDictValueUnchecked selected source
    let valueCondition ←
      schemaValueAssertion? .openKeys arg.name valueType value.stmt source
    let body := match valueCondition with
      | some condition =>
        present.implies
          (⟨condition⟩ : TypedStmtExpr .TBool) source
      | none => .literalBool true source
    let param : Parameter :=
      { name := mkId keyName, type := { val := .TString, source := source } }
    let schema := TypedStmtExpr.forallTrigger param selected.stmt body source
    return [mkCondition schema
      s!"'{arg.name}' must satisfy its declared dictionary type"]
  | .typedDict =>
    let mut conditions : List Condition := []
    let fields := arg.type.asTypedDict.getD #[]
    if typedDictMode == .closedKeys then
      let allowedKeys := stringListExpr (fields.toList.map (·.name)) source
      let structural : TypedStmtExpr .TBool :=
        TypedStmtExpr.ofStmt
          (.StaticCall (mkId "DictStrAny_keysAllowed")
            [dict.stmt, allowedKeys]) source
      let keyName := s!"{pythonGeneratedPrefix}schema_key_{arg.name}"
      let key := TypedStmtExpr.identifier keyName .TString source
      let selected := TypedStmtExpr.pySpecDictSelect model key source
      let present := TypedStmtExpr.pySpecDictIsPresent selected source
      let allowed := fields.foldl (init := TypedStmtExpr.literalBool false source)
        fun acc field =>
          acc.or (key.stringEq (.literalString field.name source) source) source
      let keyBody := present.implies allowed source
      let keyParam : Parameter :=
        { name := mkId keyName, type := { val := .TString, source := source } }
      let universal := TypedStmtExpr.forallTrigger keyParam selected.stmt keyBody source
      conditions := conditions ++ [
        mkCondition (structural.and universal source)
          s!"'{arg.name}' must contain only declared keys"]
    for field in fields do
      let key := TypedStmtExpr.literalString field.name source
      let selected := TypedStmtExpr.pySpecDictSelect model key source
      let present := TypedStmtExpr.pySpecDictIsPresent selected source
      if field.required then
        conditions := conditions ++ [
          mkCondition present
            s!"'{arg.name}' must contain required key '{field.name}'"]
      let value := TypedStmtExpr.pySpecDictValueUnchecked selected source
      let valueCondition ←
        schemaValueAssertion? .openKeys s!"{arg.name}.{field.name}"
          field.type value.stmt source
      if let some valueCondition := valueCondition then
        conditions := conditions ++ [
          mkCondition (present.implies (⟨valueCondition⟩ : TypedStmtExpr .TBool) source)
            s!"'{arg.name}.{field.name}' must satisfy its declared type"]
    return conditions

private def buildDictSchemaConds (args : Array Arg)
    (kwargs : Option (String × SpecType)) (source : FileRange)
    : ToLaurelM (List Condition) := do
  let mut conditions : List Condition := []
  for arg in args do
    conditions := conditions ++ (← dictSchemaConditions arg false .openKeys source)
  if let some (name, tp) := kwargs then
    let arg : Arg := { name, type := tp }
    conditions := conditions ++ (← dictSchemaConditions arg true .closedKeys source)
  return conditions

private def addReturnSchemaAssume (body : Body)
    (conditions : List Condition) : Body :=
  match body, conditions with
  | _, [] => body
  | .Opaque postconditions (some implementation) modifies, conditions =>
    let assumeStmts : List StmtExprMd := conditions.map fun c =>
      { val := .Assume c.condition, source := c.condition.source }
    let implementation := match implementation.val with
      | .Block statements label =>
        { implementation with val := .Block (statements ++ assumeStmts) label }
      | _ =>
        { implementation with val := .Block (implementation :: assumeStmts) none }
    .Opaque postconditions (some implementation) modifies
  | _, _ => body

/-! ## Declaration Translation -/

/-- Convert a function declaration to a Laurel Procedure.
    `**kwargs: Unpack[TypedDict]` is passed as one `DictStrAny` input; its
    schema is expressed as a map condition on the logical dictionary model.
    When `isMethod` is true, the first positional arg (`self`) is stripped. -/
def funcDeclToLaurel (procName : String) (func : FunctionDecl)
    (isMethod : Bool := false) : ToLaurelM Procedure := do
  if isMethod && func.args.args.size == 0 then
    reportError .missingMethodSelf default
      s!"Method '{func.name}' has no arguments (expected 'self' as first parameter)"
  let posArgs := if isMethod then func.args.args.extract 1 func.args.args.size
                 else func.args.args
  let kwargs ← match func.args.kwargs with
    | some (name, tp) =>
      if tp.isTypedDict then
        pure (some (name, tp))
      else do
        reportError .kwargsExpansionError tp.loc
          s!"**{name} must use Unpack[TypedDict], got '{tp}'; **{name} is dropped from the model"
        pure none
    | none => pure none
  let allArgs := posArgs ++ func.args.kwonly
  let explicitInputs ← allArgs.mapM fun a => do
    let ty ← specTypeToLaurelType a.type
    return ({ name := a.name, type := ty } : Parameter)
  let inputs := match kwargs with
    | some (name, _) =>
      explicitInputs.push {
        name := name
        type := mkUserDefined "DictStrAny" }
    | none => explicitInputs
  let outputs : List Parameter := [{ name := "result", type := tyAny }]
  let argTypes : Std.HashMap String HighType :=
    inputs.foldl (init := ({} : Std.HashMap String HighType).insert "result" StrataPython.Laurel.tyAny) fun m p =>
      m.insert p.name.text p.type.val
  let specTypes := allArgs.foldl
    (init := ({} : Std.HashMap String SpecType).insert "result" func.returnType)
    fun m a => m.insert a.name a.type
  let specTypes := match kwargs with
    | some (name, tp) => specTypes.insert name tp
    | none => specTypes
  let specCtx : SpecExprContext := { procName, argTypes, specTypes }
  let (body, requiredParamConds) ← buildSpecBody allArgs func.postconditions
    func.admittedPostconditions func.returnType unknownSource specCtx
  let userPreconds ← buildPreconditionConds func.preconditions unknownSource specCtx
  let dictSchemaConds ← buildDictSchemaConds allArgs kwargs unknownSource
  let returnSchema ← dictSchemaConditions
    { name := "result", type := func.returnType } false .openKeys unknownSource
  let body := addReturnSchemaAssume body returnSchema
  let src ← mkSourceWithFileRange func.loc
  return {
    name := { text := procName, source := src }
    inputs := inputs.toList
    outputs := outputs
    preconditions := dictSchemaConds ++ requiredParamConds ++ userPreconds
    decreases := none
    body := body
  }

/-- Convert a class definition to Laurel types and procedures. -/
def classDefToLaurel (cls : ClassDef) : ToLaurelM Unit := do
  let prefixedName ← prefixName cls.name
  -- Register alias from unprefixed to prefixed name for type resolution
  if prefixedName != cls.name then
    modify fun s => { s with typeAliases := s.typeAliases.insert cls.name prefixedName }
  if cls.exhaustive then
    modify fun s => { s with exhaustiveClasses := s.exhaustiveClasses.insert prefixedName }
  let laurelFields ← cls.fields.toList.mapM fun f => do
    let ty ← specTypeToLaurelType f.type
    pure { name := f.name, isMutable := true, type := ty : Laurel.Field }
  -- `extending` holds `HighTypeMd` (a composite may extend a generic parent `Base<T>`);
  -- a Python base class is a plain nominal parent, so wrap each prefixed base as `.UserDefined`.
  let prefixedBases := cls.bases.toList.map fun cd =>
    (⟨.UserDefined (mkId cd.toLaurelName), unknownSource⟩ : Laurel.HighTypeMd)
  pushType (.Composite {
    name := prefixedName
    extending := prefixedBases
    fields := laurelFields
    instanceProcedures := []
  })
  for method in cls.methods do
    let proc ← funcDeclToLaurel (prefixedName ++ "@" ++ method.name) method (isMethod := true)
    pushProcedure proc
  for sub in cls.subclasses do
    classDefToLaurel sub
decreasing_by
  · cases cls
    decreasing_tactic

/-- Convert a type definition to a Laurel composite type placeholder. -/
def typeDefToLaurel (td : TypeDef) : ToLaurelM Unit := do
  let prefixedName ← prefixName td.name
  pushType (.Composite {
    name := prefixedName
    extending := []
    fields := []
    instanceProcedures := []
  })

/-- Convert a single PySpec signature to Laurel declarations. -/
def signatureToLaurel (sig : Signature) : ToLaurelM Unit :=
  match sig with
  | .externTypeDecl .. =>
    -- No Laurel output needed: PySpec fully qualifies imported class names,
    -- so the local-name → PythonIdent mapping is not required here.
    pure ()
  | .typeDef td =>
    typeDefToLaurel td
  | .functionDecl func => do
    if func.isOverload then
      extractOverloadEntry func
    else do
      let procName ← prefixName func.name
      let proc ← funcDeclToLaurel procName func
      pushProcedure proc
  | .classDef cls => classDefToLaurel cls

/-- Result of translating PySpec signatures to Laurel. -/
public structure TranslationResult where
  program : Laurel.Program
  errors : Array PipelineMessage
  overloads : OverloadTable
  /-- Maps unprefixed class names to prefixed names for type resolution. -/
  typeAliases : Std.HashMap String String := {}
  /-- Classes whose spec is considered exhaustive (lists all methods). -/
  exhaustiveClasses : Std.HashSet String := {}

/-- Run the translation and return a Laurel Program, dispatch table,
    and any errors. -/
public def signaturesToLaurel (filepath : System.FilePath) (sigs : Array Signature)
    (moduleName : ModuleName)
    : TranslationResult :=
  let ctx : ToLaurelContext := {
    filepath,
    modulePrefix := moduleName.toString (sep := "_")
  }
  let ((), state) := (sigs.forM signatureToLaurel).run ctx |>.run {}
  let pgm : Laurel.Program := {
    staticProcedures := state.procedures.toList
    staticFields := []
    types := state.types.toList
    constants := []
  }
  { program := pgm
    errors := state.errors
    overloads := state.overloads
    typeAliases := state.typeAliases
    exhaustiveClasses := state.exhaustiveClasses }

/-- Extract only the overload dispatch table from PySpec signatures.
    Processes `@overload` function declarations, ignoring classDef,
    typeDef, externTypeDecl, and non-overload functions. -/
public def extractOverloads (filepath : System.FilePath) (sigs : Array Signature)
    : OverloadTable × Array PipelineMessage :=
  let ctx : ToLaurelContext := { filepath, modulePrefix := "" }
  let action := sigs.forM fun sig =>
    match sig with
    | .functionDecl func =>
      if func.isOverload then extractOverloadEntry func
      else pure ()
    | _ => pure ()
  let ((), state) := action.run ctx |>.run {}
  (state.overloads, state.errors)


end StrataPython.Specs.ToLaurel
