/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Generated.Types
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Generated.Types

set_option autoImplicit false

/-!
# The built-in constants

Spot checks of `Generated/Types.lean` against CPython 3.12.15.
-/

namespace StrataPython.Dyn.Sem.BuiltinTest

open StrataPython.Dyn.Sem

-- An alias names the same constant, as `IOError is OSError` is `True`.
#guard Builtin.ofName? "IOError" == some .OSError
#guard Builtin.ofName? "EnvironmentError" == some .OSError
#guard Builtin.ofName? "len" == some .len
-- The immediates of `dir(builtins)` are not constants, nor is a name `builtins` lacks.
#guard Builtin.ofName? "None" == none
#guard Builtin.ofName? "True" == none
#guard Builtin.ofName? "__debug__" == none
#guard Builtin.ofName? "__name__" == none
#guard Builtin.ofName? "__doc__" == none
#guard Builtin.ofName? "nonexistent" == none

-- Kinds.
#guard Builtin.len.info.kind == .function
#guard Builtin.int.info.kind == .type
#guard Builtin.exit.info.kind == .other

-- The types that values have outside `builtins`, with CPython's names.
#guard Builtin.«str_ascii_iterator».info.tpName == "str_ascii_iterator"
#guard Builtin.«longrange_iterator».info.name == "longrange_iterator"
#guard Builtin.«method-wrapper».info.tpName == "method-wrapper"
#guard Builtin.«_frozen_importlib.ModuleSpec».info.tpName == "ModuleSpec"
#guard Builtin.«_frozen_importlib.ModuleSpec».info.name == "ModuleSpec"
#guard Builtin.«_frozen_importlib.ModuleSpec».info.module == "_frozen_importlib"
#guard Builtin.NoneType.info.tpName == "NoneType"
#guard Builtin.ellipsis.info.tpName == "ellipsis"
#guard Builtin.method.info.tpName == "method"
#guard Builtin.cell.info.tpName == "cell"
#guard Builtin.«_sitebuiltins.Quitter».info.name == "Quitter"

-- What each constant's hash depends on.
#guard Builtin.int.info.hash == .addr
#guard Builtin.len.info.hash == .other
#guard Builtin.exit.info.hash == .addr
#guard Builtin.«__spec__».info.hash == .unhashable

-- The values of the names of `dir(builtins)` that are strs.
#guard (Builtin.strNames.lookup "__name__") == some "builtins"
#guard (Builtin.strNames.lookup "__package__") == some ""
#guard ((Builtin.strNames.lookup "__doc__").map (·.startsWith "Built-in functions")) == some true
#guard Builtin.strNames.length == 3

-- MROs.
#guard Builtin.bool.info.mro == #[.bool, .int, .object]
#guard Builtin.KeyError.info.mro == #[.KeyError, .LookupError, .Exception, .BaseException, .object]

-- Solid bases decide layout conflicts: `class C(list, dict)` and `class C(list, ValueError)` raise,
-- `class C(OSError, ValueError)` doesn't.
#guard Builtin.list.info.solidBase == .list
#guard Builtin.dict.info.solidBase == .dict
#guard Builtin.ValueError.info.solidBase == .BaseException
#guard Builtin.OSError.info.solidBase == .OSError
#guard Builtin.KeyError.info.solidBase == .BaseException
#guard Builtin.AttributeError.info.solidBase == .AttributeError
#guard Builtin.StopIteration.info.solidBase == .StopIteration
#guard Builtin.bool.info.solidBase == .int

-- Every constant appears once in `allConstants`.
#guard Builtin.allConstants.size == 186
#guard (Builtin.allConstants.toList.eraseDups).length == Builtin.allConstants.size

end StrataPython.Dyn.Sem.BuiltinTest
