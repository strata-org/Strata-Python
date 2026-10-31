/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.DictLookup
import StrataPython.Dyn.Sem.World
meta import StrataPython.Dyn.Sem.DictLookup
meta import StrataPython.Dyn.Sem.World

set_option autoImplicit false

/-!
# Equality of keys, structural equality, and the `builtins` dict

* `pyEqImm` against CPython 3.12.15: `{(1,): 'a', (True,): 'b'}` is `{(1,): 'b'}`,
  `{range(0, 3, 2): 'a', range(0, 4, 2): 'b'}` is `{range(0, 3, 2): 'b'}`,
  `{range(0): 'a', range(5, 5): 'b'}` is `{range(0, 0): 'b'}`, and
  `{(1, 2): 'a', (1, 3): 'b'}` keeps both keys.
* `Value.beq`, the structural equality, on each kind.
* The `builtins` dict holds every name of `vars(builtins)`, in its order.
-/

namespace StrataPython.Dyn.Sem.ValuesTest

open StrataPython.Dyn.Sem

#guard pyEqImm (.tuple #[.int 1]) (.tuple #[.bool true]) == some true
#guard pyEqImm (.tuple #[.int 1, .int 2]) (.tuple #[.int 1, .int 3]) == some false
#guard pyEqImm (.tuple #[.int 1]) (.tuple #[.int 1, .int 2]) == some false
#guard pyEqImm (.range 0 3 2) (.range 0 4 2) == some true
#guard pyEqImm (.range 0 0 1) (.range 5 5 1) == some true
#guard pyEqImm (.range 0 1 1) (.range 0 1 7) == some true
#guard pyEqImm (.range 0 3 1) (.range 0 3 2) == some false
#guard pyEqImm (.slice (.int 1) (.int 2) .none) (.slice (.bool true) (.int 2) .none) == some true
#guard pyEqImm (.ofFloat 0.0) (.ofFloat (-0.0)) == some true
#guard pyEqImm (.ofString "a") (.bytes #[97]) == some false
#guard pyEqImm .none .none == some true
-- What the model doesn't decide yet: a NaN, an int against a float, a symbolic hash.
#guard pyEqImm (.ofFloat (0.0 / 0.0)) (.ofFloat (0.0 / 0.0)) == none
#guard pyEqImm (.int 1) (.ofFloat 1.0) == none
#guard pyEqImm (.symHash (HashSrc.buffer [97])) (.int 1) == none

-- Structural equality: floats by their bits, members in order.
#guard Value.beq (.ofFloat 0.0) (.ofFloat (-0.0)) == false
#guard Value.beq (.tuple #[.int 1, .ofString "a"]) (.tuple #[.int 1, .ofString "a"])
#guard !Value.beq (.tuple #[.int 1]) (.tuple #[.bool true])
#guard Value.beq (.slice .none (.int 2) .none) (.slice .none (.int 2) .none)
#guard Value.beq (.bound (.int 1) .int "__add__" .slotWrapper)
  (.bound (.int 1) .int "__add__" .slotWrapper)
#guard !Value.beq (.method (.obj 1) (.int 1)) (.method (.obj 1) (.int 2))
#guard !Value.beq (.obj 1) (.int 1)

/-- The names of the `builtins` dict, in order. -/
def builtinsNames : List String :=
  builtinsDict.live.toList.map fun (e, _) => match e.key with
    | .str s => s.s
    | _ => "?"

#guard builtinsNames.length == 157
#guard builtinsNames.take 6 ==
  ["__name__", "__doc__", "__package__", "__loader__", "__spec__", "__build_class__"]
#guard builtinsDict.live.all fun (_, v) => !(v matches .undef _)

end StrataPython.Dyn.Sem.ValuesTest
