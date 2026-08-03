/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.Translation

meta section

namespace StrataPython.PythonTypeToHighTypeTest

open Strata (SourceRange)
open Strata.Laurel (HighType)
open StrataPython.Resolution (PythonType)
open StrataPython.Translation (pythonTypeToHighType)

/-! Compile-time coverage for `pythonTypeToHighType`, the total pure function that
    maps a Python type annotation to a Laurel `HighType`. It has ~15 name cases plus
    subscript/binop/alias arms; these `#guard`s pin the builtin mappings, the
    alias-resolution path (`MyInt = int`), and the unknown-name fallthrough. -/

/-- Build a bare `.Name` type annotation (`x: <n>`) the way `translateModule` does. -/
private def name (n : String) : PythonType :=
  .Name SourceRange.none ⟨SourceRange.none, n⟩ (.Load SourceRange.none)

/-- Build a subscripted annotation head (`<n>[...]`); the element is irrelevant to
    the arms under test, so reuse a `.Name` as the (ignored) index. -/
private def subscript (n : String) : PythonType :=
  .Subscript SourceRange.none (.Name SourceRange.none ⟨SourceRange.none, n⟩ (.Load SourceRange.none))
    (.Name SourceRange.none ⟨SourceRange.none, "int"⟩ (.Load SourceRange.none)) (.Load SourceRange.none)

-- Primitive builtins map to Core primitive HighTypes.
#guard pythonTypeToHighType {} (name "int") == HighType.TInt
#guard pythonTypeToHighType {} (name "bool") == HighType.TBool
#guard pythonTypeToHighType {} (name "str") == HighType.TString
-- Python `float` is a real (one domain with float literals), not `float64`.
#guard pythonTypeToHighType {} (name "float") == HighType.TReal
#guard pythonTypeToHighType {} (name "None") == HighType.TVoid

-- Dynamic / boxed forms collapse to the named gradual composites.
#guard pythonTypeToHighType {} (name "Any") == HighType.UserDefined { text := "Any" }
#guard pythonTypeToHighType {} (name "object") == HighType.UserDefined { text := "Any" }
#guard pythonTypeToHighType {} (name "bytes") == HighType.UserDefined { text := "Any" }
#guard pythonTypeToHighType {} (name "dict") == HighType.UserDefined { text := "DictStrAny" }
#guard pythonTypeToHighType {} (name "list") == HighType.UserDefined { text := "ListAny" }
#guard pythonTypeToHighType {} (name "set") == HighType.UserDefined { text := "ListAny" }

-- Subscripted collections match their bare forms (so a bare annotation and a literal unify).
#guard pythonTypeToHighType {} (subscript "dict") == HighType.UserDefined { text := "DictStrAny" }
#guard pythonTypeToHighType {} (subscript "list") == HighType.UserDefined { text := "ListAny" }
#guard pythonTypeToHighType {} (subscript "Optional") == HighType.UserDefined { text := "Any" }

-- An unknown bare name with no alias becomes a phantom `UserDefined` of that name.
#guard pythonTypeToHighType {} (name "MyClass") == HighType.UserDefined { text := "MyClass", uniqueId := none }

-- Alias resolution: a module-level `MyInt = int` alias resolves the name to the aliased
-- type rather than a phantom composite. This is the path class fields now share with
-- parameters/locals (`translateClass` threads `typeAliases`).
private def withAlias : Std.HashMap String HighType := ({} : Std.HashMap String HighType).insert "MyInt" HighType.TInt
#guard pythonTypeToHighType withAlias (name "MyInt") == HighType.TInt
-- A name absent from the alias map still falls through to the phantom composite.
#guard pythonTypeToHighType withAlias (name "Other") == HighType.UserDefined { text := "Other", uniqueId := none }

end StrataPython.PythonTypeToHighTypeTest
end
