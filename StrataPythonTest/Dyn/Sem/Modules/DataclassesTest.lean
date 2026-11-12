/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Dataclasses
public import StrataPythonTest.Dyn.Sem.Modules.TypingTest
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Modules.Dataclasses
meta import StrataPythonTest.Dyn.Sem.Modules.TypingTest

set_option autoImplicit false

/-!
# The model of `dataclasses`

Each model's class holds every name of CPython's `vars()` of its class or stops with a gap on it,
the classes of all the models are all the classes outside `builtins` that their objects reach, and
the module binds only names that CPython's `vars(dataclasses)` has.
-/

namespace StrataPython.Dyn.Sem.Modules.DataclassesTest

open StrataPython.Dyn.Sem
open StrataPython.Dyn.Sem.Modules.TypesTest (namesAgree)

/-- The model's classes of `dataclasses`, by CPython's `module.qualname`. -/
def dcSpecs : List (String × ClassSpec) :=
  [("dataclasses.Field", fieldSpec), ("dataclasses.FrozenInstanceError", frozenErrorSpec),
    ("dataclasses._DataclassParams", paramsSpec), ("dataclasses._FIELD_BASE", fieldBaseSpec),
    ("dataclasses._HAS_DEFAULT_FACTORY_CLASS", hasFactorySpec),
    ("dataclasses._MISSING_TYPE", missingTypeSpec)]

#guard dcSpecs.all fun (key, spec) => namesAgree spec key
-- The models' objects reach no other class outside `builtins`.
#guard (classNames.map (·.1)).mergeSort (· ≤ ·) ==
  ((TypingTest.specs ++ dcSpecs).map (·.1)).mergeSort (· ≤ ·)
#guard dataclassesAttrNames.all ((moduleNames.lookup "dataclasses").get!.contains ·)

end StrataPython.Dyn.Sem.Modules.DataclassesTest
