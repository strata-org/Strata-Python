/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public section
namespace Strata.Pipeline.MessageKind

-- PySpec parsing phase
def pySpecReadError : MessageKind :=
  { category := "readError", impact := .configurationError }
def pySpecParsingError : MessageKind :=
  { category := "error", impact := .internalError }
def pySpecParsingWarning : MessageKind :=
  { category := "warning", impact := .knownLimitation }

-- Overload dispatch errors (in PySpec-to-Laurel phase)
def overloadNoArgs : MessageKind :=
  { category := "overloadNoArgs", impact := .internalError }
def overloadReturnNotClass : MessageKind :=
  { category := "overloadReturnNotClass", impact := .internalError }
def overloadParamNameDisagreement : MessageKind :=
  { category := "overloadParamNameDisagreement", impact := .internalError }
def overloadArgNotStringLiteral : MessageKind :=
  { category := "overloadArgNotStringLiteral", impact := .internalError }

-- Overload resolution phase
def overloadResolveWarning : MessageKind :=
  { category := "resolveWarning", impact := .internalWarning }

-- PySpec.ToLaurel internal warnings/errors
def missingMethodSelf : MessageKind :=
  { category := "missingMethodSelf", impact := .internalWarning }
/-- A violated invariant between source-type selection and Laurel expression
    lowering. This indicates a translator defect, not invalid user code. -/
def loweringTypeError : MessageKind :=
  { category := "loweringTypeError", impact := .internalError }
def typeError : MessageKind :=
  { category := "typeError", impact := .internalWarning }
/-- A dictionary type the map model cannot express (e.g. non-string keys):
    the schema condition is skipped; conditions referencing such a dictionary
    are rejected separately at condition translation. -/
def dictionarySchemaWarning : MessageKind :=
  { category := "dictionarySchemaWarning", impact := .userCodeWarning }
/-- A `**kwargs` parameter without `Unpack[TypedDict]` cannot be modeled.
    Fatal: the parameter would be dropped from the model, so a `@requires`
    mentioning it would fail to lower and silently weaken the contract —
    the same silent-weakening `unsupportedPostcondition` is fatal to avoid. -/
def kwargsExpansionError : MessageKind :=
  { category := "kwargsExpansionError", impact := .userCodeError }

-- Type translation warnings
def unsupportedUnion : MessageKind :=
  { category := "unsupportedUnion", impact := .knownLimitation }

-- Contract errors
/-- PySpec models do not provide an implementation against which Strata can
    prove an `@ensures`, so the unsupported contract is rejected rather than
    silently assumed in caller verification conditions. Postconditions that
    are deliberately unverified modeling assumptions can be acknowledged
    explicitly with `@admit` instead — the same division as Dafny's verified
    `ensures` versus `{:extern}`/`{:axiom}` assumptions. -/
def unsupportedPostcondition : MessageKind :=
  { category := "unsupportedPostcondition", impact := .userCodeError }

/-- An `@admit` predicate that cannot be lowered to a Laurel assumption.
    Fatal: silently dropping an acknowledged assumption would resurface as a
    confusing verification failure far from the broken decorator. -/
def unsupportedAdmit : MessageKind :=
  { category := "unsupportedAdmit", impact := .userCodeError }

-- Precondition warnings
def placeholderExpr : MessageKind :=
  { category := "placeholderExpr", impact := .knownLimitation }
def floatLiteral : MessageKind :=
  { category := "floatLiteral", impact := .knownLimitation }
def isinstanceUnsupported : MessageKind :=
  { category := "isinstanceUnsupported", impact := .knownLimitation }
/-- An `assert` whose formula could not be translated, so the assertion was
    dropped from the generated contract. Kept as its own kind so consumers can
    detect it structurally instead of matching the user-facing message text. -/
def pySpecDroppedAssertion : MessageKind :=
  { category := "droppedAssertion", impact := .knownLimitation }

-- PySpec-to-Laurel assembly phase
def functionSignatureError : MessageKind :=
  { category := "functionSignatureError", impact := .internalError }
def typeNameCollision : MessageKind :=
  { category := "typeNameCollision", impact := .internalError }
def procedureNameCollision : MessageKind :=
  { category := "procedureNameCollision", impact := .internalError }
/-- Two PySpec inputs produce the same canonical module-ghost name. -/
def ghostNameCollision : MessageKind :=
  { category := "ghostNameCollision", impact := .userCodeError }
/-- A parameter shadows a module ghost the contract references. -/
def ghostShadowedByParam : MessageKind :=
  { category := "ghostShadowedByParam", impact := .userCodeError }
/-- A module ghost's initializer could not be translated. -/
def ghostInitializerError : MessageKind :=
  { category := "ghostInitializerError", impact := .userCodeError }
/-- `OLD` over a module ghost not listed in `@modifies`. -/
def ghostOldWithoutModifies : MessageKind :=
  { category := "ghostOldWithoutModifies", impact := .userCodeError }

-- Module resolution phase
def invalidModuleName : MessageKind :=
  { category := "invalidModuleName", impact := .configurationError }
def missingPySpecModule : MessageKind :=
  { category := "missingPySpecModule", impact := .configurationError }

end Strata.Pipeline.MessageKind
end
