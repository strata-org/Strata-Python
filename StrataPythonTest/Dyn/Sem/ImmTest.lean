/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Imm
meta import StrataPython.Dyn.Sem.Imm

set_option autoImplicit false

/-!
# Immediates and `storeAddrFree`

`storeAddrFree` is `false` for a store object's address, nested or not, and for a freeable
built-in constant; `true` for the sources of values that CPython never frees; and `false` for a
code that no constructor of `HashSrc` makes.  `Value.toImm?` gives no immediate for an object,
an unassigned value, or a symbolic hash value that names an object.
-/

namespace StrataPython.Dyn.Sem.ImmTest

open StrataPython.Dyn.Sem

/-- A symbolic hash of the source `s`. -/
def sym (s : HashSrc) : Hash := .symbolic s

-- A store object's address, alone and inside each of the four combining sources.
#guard !(HashSrc.addr 3).storeAddrFree
#guard !(HashSrc.tuple [.exact 1, sym (.addr 3)]).storeAddrFree
#guard !(HashSrc.frozenset [sym (.buffer [97]), sym (.addr 3)]).storeAddrFree
#guard !(HashSrc.combine "K" [sym (.addr 3)]).storeAddrFree
#guard !(HashSrc.reduced (.addr 3)).storeAddrFree
#guard !(HashSrc.tuple [sym (.tuple [sym (.reduced (.addr 3))])]).storeAddrFree

-- A freeable built-in constant counts as a store address; `int` doesn't.
#guard !(HashSrc.const .exit).storeAddrFree
#guard !(HashSrc.tuple [sym (.const .license)]).storeAddrFree
#guard (HashSrc.const .int).storeAddrFree

-- The sources that pass.
#guard (HashSrc.buffer [1, 2, 3]).storeAddrFree
#guard (HashSrc.singleton true).storeAddrFree
#guard (HashSrc.builtinFn .len).storeAddrFree
#guard (HashSrc.descr .str "upper").storeAddrFree
#guard (HashSrc.frozenset [sym (.const .int), sym (.const .str)]).storeAddrFree
#guard (HashSrc.combine "list[int]" [sym (.const .list), sym (.const .int)]).storeAddrFree
#guard (HashSrc.reduced (.tuple [.exact 5, sym (.buffer [97])])).storeAddrFree
-- A static method's hash holds a descriptor's address, which is never freed.
#guard (HashSrc.combine "<staticmethod>" [sym (.descr .str "maketrans")]).storeAddrFree

-- Codes that no constructor makes fail closed.
#guard !(HashSrc.mk []).storeAddrFree
#guard !(HashSrc.mk [42, 1]).storeAddrFree
#guard !(HashSrc.mk [3, 1, 5, 1, 9]).storeAddrFree
#guard !(HashSrc.mk [9]).storeAddrFree
#guard !(HashSrc.mk [7, 5]).storeAddrFree
#guard !(HashSrc.mk [0, 300]).storeAddrFree
#guard !(HashSrc.mk [2, 100000]).storeAddrFree
#guard !(HashSrc.mk [3, 5]).storeAddrFree
#guard !(HashSrc.mk [6, 6, 0]).storeAddrFree

-- What `Value.toImm?` gives.
#guard (Value.obj 3).toImm?.isNone
#guard (Value.undef "x").toImm?.isNone
#guard (Value.symHash (.addr 3)).toImm?.isNone
#guard (Value.symHash (.buffer [97])).toImm?.isSome
#guard ((Imm.tuple #[Value.int 1]).toValue.toImm?.map Imm.toValue) == some (.tuple #[.int 1])

end StrataPython.Dyn.Sem.ImmTest
