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
def typeError : MessageKind :=
  { category := "typeError", impact := .internalWarning }
def kwargsExpansionError : MessageKind :=
  { category := "kwargsExpansionError", impact := .internalWarning }

-- Type translation warnings
def unsupportedUnion : MessageKind :=
  { category := "unsupportedUnion", impact := .knownLimitation }

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

-- Module resolution phase
def invalidModuleName : MessageKind :=
  { category := "invalidModuleName", impact := .configurationError }
def missingPySpecModule : MessageKind :=
  { category := "missingPySpecModule", impact := .configurationError }

end Strata.Pipeline.MessageKind
end
