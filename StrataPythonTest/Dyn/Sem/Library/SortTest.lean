/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Sort
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Library.Sort

set_option autoImplicit false

/-!
# The fast path of `list.sort` sorts as CPython's port does

When every key is a number or every key is a `str`, `list.sort` sorts with `fastSort`
(`List.mergeSort`) instead of the port of CPython's sort. `SortProps` proves that `fastSort` is
a stable sort by `FastKey.le`. A deterministic stream of random key lists checks that it gives
the same order as the port with `FastKey.lt`, on numbers with ties written two ways
(`fin 2 0` and `fin 1 1`), infinities, and on `str`s.
-/

namespace StrataPython.Dyn.Sem.Library.SortTest

open StrataPython.Dyn.Sem.Library
open Strata.Dyn.Util

/-- The port needs a default item, which it never returns. -/
private instance : Inhabited FastKey := ⟨.inf false⟩

/-- A pseudo-random stream (an LCG). -/
private def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A numeric key from the random number `r`: an infinity, or `m * 2 ^ e` for small `m` and `e`,
so that equal values written two ways are frequent. -/
private def numKey (r : Nat) : FastKey :=
  match r % 9 with
  | 0 => .inf true
  | 1 => .inf false
  | _ => .fin ((r / 16 % 9 : Nat) - 4 : Int) ((r / 256 % 5 : Nat) - 2 : Int)

/-- A `str` key from the random number `r`, over a small alphabet. -/
private def strKey (r : Nat) : FastKey :=
  .str (String.ofList ((List.range (r % 4)).map fun i => "abé".toList.getD (r / (3 ^ i) % 3) 'a'))

/-- `n` keys from seed `s`, made by `key`, paired with their positions. -/
private def randomKeys (key : Nat → FastKey) (s n : Nat) : List (Nat × FastKey) :=
  ((List.range n).foldl (fun (acc : List (Nat × FastKey) × Nat) i =>
      let s' := next acc.2
      ((i, key (s' / 65536)) :: acc.1, s')) ([], s)).1.reverse

/-- The positions in the order of the port with `FastKey.lt`. -/
private def portOrder (xs : List (Nat × FastKey)) : List Nat :=
  (Id.run (Sort.sort (m := Id) (ε := Unit) (fun a b => pure (.ok (FastKey.lt a.2 b.2)))
    xs.toArray)).1.toList.map (·.1)

/-- The seeds and sizes where the fast path and the port give different orders. -/
private def mismatches (key : Nat → FastKey) : List (Nat × Nat) :=
  (List.range 30).flatMap fun s =>
    [0, 1, 2, 7, 33, 64, 65, 130, 300].filterMap fun n =>
      let xs := randomKeys key (s + 1) n
      if portOrder xs == (fastSort xs).map (·.1) then none else some (s, n)

#guard mismatches numKey == []
#guard mismatches strKey == []

end StrataPython.Dyn.Sem.Library.SortTest
