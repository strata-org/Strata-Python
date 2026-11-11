/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Types
public import StrataPython.Dyn.Sem.Modules.Names
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Modules.Types
meta import StrataPython.Dyn.Sem.Modules.Names

set_option autoImplicit false

/-!
# The models of `types.GenericAlias` and `types.UnionType`

Each model's class holds every name of CPython's `vars()` of its class, or stops with a gap on it.
`ga_hash` is the `^` of the hashes of the origin and of the arguments, as 64-bit words; the model
stops with a gap when it gives -1, where CPython's `hash()` raises `SystemError`.
-/

namespace StrataPython.Dyn.Sem.Modules.TypesTest

open StrataPython.Dyn.Sem

/-- Whether the class `spec` describes holds every name of `vars()` of CPython's class `key` or
stops with a gap on it, and holds no other name. It may stop with a gap on another name, whose
lookup would go on to a base where CPython behaves otherwise (`UnionType` has no `__new__`, and
CPython refuses to make one). -/
def namesAgree (spec : ClassSpec) (key : String) : Bool :=
  match classNames.lookup key with
  | some names =>
    names.all spec.names.contains && spec.entries.all (names.contains ·.name)
  | none => false

#guard namesAgree gaSpec "types.GenericAlias"
#guard namesAgree unionSpec "types.UnionType"
#guard !(classNames.lookup "types.UnionType").get!.contains "__new__" && unionSpec.gapped.contains "__new__"
-- The models' objects reach no other class outside `builtins`.
#guard classNames.map (·.1) == ["types.GenericAlias", "types.UnionType"]

#guard gaHash (.exact 5) (.exact 3) == .exact 6
-- -1 comes out of two hashes that are not -1, and the body stops with a gap on it.
#guard gaHash (.exact (-2)) (.exact 1) == .exact (-1)
#guard gaHash (.exact 0) (.exact (-1)) == .exact (-1)
#guard gaHash (.exact (-(2 ^ 63))) (.exact 1) == .exact (-(2 ^ 63) + 1)
-- A part that the model knows only symbolically keeps the result symbolic.
#guard gaHash (.symbolic (HashSrc.const .int)) (.exact 1) ==
  .symbolic (HashSrc.combine "GenericAlias.__hash__" [.symbolic (HashSrc.const .int), .exact 1])

end StrataPython.Dyn.Sem.Modules.TypesTest
