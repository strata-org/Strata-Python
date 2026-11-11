/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Typing
public import StrataPythonTest.Dyn.Sem.Modules.TypesTest
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Modules.Typing
meta import StrataPythonTest.Dyn.Sem.Modules.TypesTest

set_option autoImplicit false

/-!
# The model of `typing`

Each model's class holds every name of CPython's `vars()` of its class or stops with a gap on it,
the classes are all the classes outside `builtins` that the models' objects reach, and the module
binds only names that CPython's `vars(typing)` has. The builtins check knows the starting value of
every name of the builtins dict, and `ForwardRef`'s check accepts exactly the dotted names.
-/

namespace StrataPython.Dyn.Sem.Modules.TypingTest

open StrataPython.Dyn.Sem
open StrataPython.Dyn.Sem.Modules.TypesTest (namesAgree)

/-- The model's classes, by CPython's `module.qualname`. -/
def specs : List (String × ClassSpec) :=
  [("collections._tuplegetter", tupleGetterSpec), ("types.GenericAlias", gaSpec),
    ("types.UnionType", unionSpec), ("typing.Any", anySpec),
    ("typing.ForwardRef", forwardRefSpec), ("typing.NamedTuple", namedTupleSpec),
    ("typing.NamedTupleMeta", namedTupleMetaSpec), ("typing.TypedDict", typedDictSpec),
    ("typing._AnyMeta", anyMetaSpec),
    ("typing._BaseGenericAlias", baseGenericAliasSpec), ("typing._Final", finalSpec),
    ("typing._GenericAlias", genericAliasSpec), ("typing._NotIterable", notIterableSpec),
    ("typing._SpecialForm", specialFormSpec), ("typing._SpecialGenericAlias", specialGenericAliasSpec),
    ("typing._TupleType", tupleTypeSpec), ("typing._TypedDictMeta", typedDictMetaSpec),
    ("typing._UnionGenericAlias", unionGenericAliasSpec)]

#guard specs.all fun (key, spec) => namesAgree spec key
-- The models' objects reach no other class outside `builtins`.
#guard classNames.map (·.1) == specs.map (·.1)
#guard typingAttrNames.all ((moduleNames.lookup "typing").get!.contains ·)

-- Every name of the builtins dict has a known starting value, so `import typing` can pass its check.
#guard Builtin.dictNames.all fun n => (builtinOriginal? (V := Unit) n).isSome

#guard dottedName? "Node" == some true
#guard dottedName? "a.b_1" == some true
#guard dottedName? "match" == some true
#guard dottedName? "1 +" == some false
#guard dottedName? "a." == some false
#guard dottedName? "None" == some false
#guard dottedName? "x.class" == some false
#guard dottedName? "é" == none

end StrataPython.Dyn.Sem.Modules.TypingTest
