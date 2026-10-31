/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Base
public import StrataPython.Dyn.Env
public import StrataPython.Dyn.Sem.Value

set_option autoImplicit false

/-!
# The Lean types of Python's IR types

`py.Value` is `Value`; `py.Completion` is the datatype that `#dyn_types` derives,
`Py.Completion.Val`; a comprehension's accumulator (`py.ListAcc`, `py.SetAcc`, `py.DictAcc`) is
its object in the store.
-/

namespace StrataPython.Dyn.Sem

attribute [dyn_type Py.Value] Value

/-- The list that a list comprehension builds, while it builds it: its object in the store. -/
public structure ListAcc where
  obj : Value
  deriving Repr, Inhabited

/-- The set that a set comprehension builds: as `ListAcc`. -/
public structure SetAcc where
  obj : Value
  deriving Repr, Inhabited

/-- The dict that a dict comprehension builds: as `ListAcc`. -/
public structure DictAcc where
  obj : Value
  deriving Repr, Inhabited

attribute [dyn_type Py.ListAcc] ListAcc
attribute [dyn_type Py.SetAcc] SetAcc
attribute [dyn_type Py.DictAcc] DictAcc

#dyn_types Py

end StrataPython.Dyn.Sem
