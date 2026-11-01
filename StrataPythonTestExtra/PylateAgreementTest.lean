/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Not a `module` file: PyLate's files are plain files, which a `module` file can't import.
import Pylate.Syntax.ClassTable
import StrataPython.Dyn.Sem.Generated.Types

/-! # PyLate's exception classes are the semantics' built-in exception classes

Each class of PyLate's exception hierarchy (`Pylate.builtinExcParent`) is a built-in exception
class of the Python semantics, with the same parent as its only base. `FrozenInstanceError`
comes from `dataclasses`, not from the builtins, so this test leaves it out.
-/

open StrataPython.Dyn.Sem

/-- The pairs of PyLate's table that the semantics' table doesn't have, with the reason. -/
def mismatches : List String :=
  Pylate.builtinExcParent.filterMap fun (cls, parent) =>
    if cls == "FrozenInstanceError" then none
    else match Builtin.ofName? cls, Builtin.ofName? parent with
      | some c, some p =>
        let info := c.info
        if info.kind != .type then some s!"{cls} is not a type"
        else if info.bases != #[p] then some s!"{cls}'s bases are not ({parent},)"
        else none
      | none, _ => some s!"{cls} is not a built-in of the semantics"
      | _, none => some s!"{parent} is not a built-in of the semantics"

/-- info: [] -/
#guard_msgs in
#eval mismatches

-- PyLate's table has 31 classes, so a class added to it or removed from it shows here.
#guard Pylate.builtinExcParent.length == 31
