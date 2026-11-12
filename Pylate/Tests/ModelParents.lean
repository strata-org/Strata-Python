/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Pylate.Syntax.ClassTable
import StrataPython.Dyn.Sem.Modules.Dataclasses

/-!
The exception classes that the semantics models outside `builtins` have the parents that PyLate's
`builtinExcParent` gives them: `dataclasses.FrozenInstanceError` is an `AttributeError`.
-/

#guard Pylate.builtinExcParent.lookup "FrozenInstanceError" ==
  some StrataPython.Dyn.Sem.Modules.frozenErrorBase.info.name
