/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Generated.Types
public import StrataPython.Dyn.Sem.Value
public import StrataPython.Dyn.Sem.ValueProps
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
public import StrataPython.Dyn.Sem.Arith
public import StrataPython.Dyn.Sem.Store
public import StrataPython.Dyn.Sem.StoreProps
public import StrataPython.Dyn.Sem.World
public import StrataPython.Dyn.Sem.WorldProps
public import StrataPython.Dyn.Sem.Dom
public import StrataPython.Dyn.Sem.Basics
public import StrataPython.Dyn.Sem.BasicsProps
public import StrataPython.Dyn.Sem.Exceptions
public import StrataPython.Dyn.Sem.Monad
public import StrataPython.Dyn.Sem.Assembly
public import StrataPython.Dyn.Sem.ConcreteProps
public import StrataPython.Dyn.Sem.RuleOK
public import StrataPython.Dyn.Sem.RuleOKProps
public import StrataPython.Dyn.Sem.RuleTheorems
public import StrataPython.Dyn.Sem.PyTypes
public import StrataPython.Dyn.Sem.Proto.Values
public import StrataPython.Dyn.Sem.Imm
public import StrataPython.Dyn.Sem.ImmProps
public import StrataPython.Dyn.Sem.MonadProps
public import StrataPython.Dyn.Sem.DictLookup
public import StrataPython.Dyn.Sem.Rules.Comprehensions
public import StrataPython.Dyn.Sem.Rules.Values
public import StrataPython.Dyn.Sem.Rules.Ops
public import StrataPython.Dyn.Sem.Proto.Ops
public import StrataPython.Dyn.Sem.Proto.Containers
public import StrataPython.Dyn.Sem.Proto.Iter
public import StrataPython.Dyn.Sem.Proto.Mapping
public import StrataPython.Dyn.Sem.Proto.Calls
public import StrataPython.Dyn.Sem.Rules.Containers
public import StrataPython.Dyn.Sem.Rules.Globals
public import StrataPython.Dyn.Sem.Rules.Closures
public import StrataPython.Dyn.Sem.Rules.Calls
public import StrataPython.Dyn.Sem.Rules.Attrs
public import StrataPython.Dyn.Sem.Proto.Repr
public import StrataPython.Dyn.Sem.Rules.Strings
public import StrataPython.Dyn.Sem.Rules.GlobalsProps
public import StrataPython.Dyn.Sem.Table
public import StrataPython.Dyn.Sem.Library.Unicode
public import StrataPython.Dyn.Sem.Library.Str
public import StrataPython.Dyn.Sem.Library.Numbers
public import StrataPython.Dyn.Sem.Library.Codecs
public import StrataPython.Dyn.Sem.Library.FormatString
public import StrataPython.Dyn.Sem.Library.Sum
public import StrataPython.Dyn.Sem.Library.SumProps
public import StrataPython.Dyn.Sem.Library.SortProps
public import StrataPython.Dyn.Sem.Library.Iterables
public import StrataPython.Dyn.Sem.Library.Iterators
public import StrataPython.Dyn.Sem.Library.Functions
public import StrataPython.Dyn.Sem.Library.Constructors
public import StrataPython.Dyn.Sem.Library.Collections
public import StrataPython.Dyn.Sem.Library.Machines
public import StrataPython.Dyn.Sem.Contracts.LocationsProps

/-!
# The Python semantics

Python's values, their hashes, the tables of dicts and sets, C3, the formatting of ints, floats
and strs, the Unicode tables, and the arithmetic of ints, bools and floats with the indices of a
slice; the objects and the world; the record of primitives and the rule monad `PyM`, with their
proofs; the rules of the `py` operations, and their table `PySem`, with the theorems that each
rule stays within its declared effect and reaches only the cells and closures it is given, and that
the table is certified (`PySem.certified`).
-/
