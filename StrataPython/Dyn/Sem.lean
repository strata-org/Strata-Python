/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Generated.Types
public import StrataPython.Dyn.Sem.Value
public import StrataPython.Dyn.Sem.Hash
public import StrataPython.Dyn.Sem.HashProps
public import StrataPython.Dyn.Sem.Index
public import StrataPython.Dyn.Sem.IndexProps
public import StrataPython.Dyn.Sem.Dict
public import StrataPython.Dyn.Sem.DictProps
public import StrataPython.Dyn.Sem.Set
public import StrataPython.Dyn.Sem.SetProps
public import StrataPython.Dyn.Sem.Mro
public import StrataPython.Dyn.Sem.MroProps
public import StrataPython.Dyn.Sem.Unicode
public import StrataPython.Dyn.Sem.Format

/-!
# The Python semantics

Python's values, their hashes, the tables of dicts and sets, C3, the formatting of ints, floats
and strs, and the Unicode tables, for the rules of the `py` operations.
-/
