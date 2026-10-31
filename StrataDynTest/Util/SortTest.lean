/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Util.Sort
public import StrataDynTest.Util.SortCases
meta import StrataDyn.Util.Sort
meta import StrataDynTest.Util.SortCases

set_option autoImplicit false

/-! # CPython's list sort

`SortCases.cases` holds CPython 3.12's runs of `list.sort` on test lists, with every comparison
that CPython made. The port must make the same comparisons, in the same order, and leave the list
in the same order, also when a comparison fails part way. -/

namespace Strata.Dyn.Util.SortTest

open Strata.Dyn.Util

/-- The comparison of a case: answers by the case's mode (see `gen_sort_cases.py`), logs the
indices, and fails on the `fail`-th comparison. -/
private def logLt (values : Array Int) (mode : Nat) (fail : Option Nat) (i j : Nat) :
    StateM (Array Nat) (Except Unit Bool) := do
  let log ← get
  let c := log.size / 2
  if fail == some c then return .error ()
  set (log.push i |>.push j)
  let lt := values.getD i 0 < values.getD j 0
  return .ok <| match mode with
    | 1 => (7 * i + 13 * j + c) % 3 == 0
    | 2 => if (7 * i + 13 * j + c) % 11 == 0 then !lt else lt
    | _ => lt

/-- The port's run of a case, failing at `fail`: its log, the final order, and whether it
failed. -/
private def runCase (c : SortCases.Case) (fail : Option Nat) : Array Nat × Array Nat × Bool :=
  let values := SortCases.ints c.values
  let ((final, err), log) :=
    (Sort.sort (logLt values c.mode fail) (Array.range values.size)).run #[]
  (log, final, err.isSome)

/-- The names of the cases where the port differs from CPython, with the failure point. -/
private def mismatches : List (String × Option Nat) :=
  SortCases.cases.toList.flatMap fun c =>
    let expected := SortCases.nats c.log
    let (log, final, failed) := runCase c none
    let whole := if log == expected && final == SortCases.nats c.final && !failed then []
      else [(c.name, none)]
    whole ++ c.fails.toList.filterMap fun (f, ffinal) =>
      let (log, final, failed) := runCase c (some f)
      if log == expected.extract 0 (2 * f) && final == SortCases.nats ffinal && failed then none
      else some (c.name, some f)

#guard SortCases.cases.size == 42
#guard (SortCases.cases.foldl (fun n c => n + c.fails.size) 0) == 39
#guard mismatches == []

/-! ## Equal to a stable sort when the order is consistent

On a strict weak order, every stable sort gives the same result. A deterministic stream of random
lists checks the port against `List.mergeSort`, which is stable. -/

/-- A pseudo-random stream (an LCG). -/
private def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A list of `n` keys below `k`, paired with their index, from seed `s`. -/
private def randomList (s n k : Nat) : List (Nat × Nat) :=
  ((List.range n).foldl (fun (acc : List (Nat × Nat) × Nat) i =>
      let s' := next acc.2
      ((s' / 65536 % k, i) :: acc.1, s')) ([], s)).1.reverse

private def portSort (xs : List (Nat × Nat)) : List (Nat × Nat) :=
  (Id.run (Sort.sort (m := Id) (ε := Unit) (fun a b => pure (.ok (a.1 < b.1))) xs.toArray)).1.toList

/-- The seeds and sizes where the port differs from `List.mergeSort`. -/
private def stableMismatches : List (Nat × Nat) :=
  (List.range 40).flatMap fun s =>
    [0, 1, 2, 5, 31, 63, 64, 65, 127, 200, 513].filterMap fun n =>
      let xs := randomList (s + 1) n (if s % 2 == 0 then 4 else 1000)
      if portSort xs == xs.mergeSort (fun a b => a.1 ≤ b.1) then none else some (s, n)

#guard stableMismatches == []

/-! ## The pieces -/

#guard Sort.minRun 63 == 63
#guard Sort.minRun 64 == 32
#guard Sort.minRun 65 == 33
#guard Sort.minRun 2112 == 33
-- `powerloop` of the runs `[0, 32)` and `[32, 64)` of 100 items: the midpoints 16 and 48 have
-- the binary fractions 0.0010… and 0.0111…, which share 1 leading digit.
#guard Sort.powerLoop 0 32 32 100 == 2

/-! ## A monad in a higher universe

The sort also runs in a monad from `Type` to `Type 1`. The items and the error stay in `Type`, but
each computation is in `Type 1`. This happens when a computation takes a type as an argument. -/

/-- A monad from `Type` to `Type 1`: each computation takes a type as an argument. -/
private structure M1 (α : Type) : Type 1 where
  run : Type → α

private instance : Monad M1 where
  pure a := ⟨fun _ => a⟩
  bind x f := ⟨fun t => (f (x.run t)).run t⟩

#guard ((Sort.sort (m := M1) (ε := String) (fun (x y : Nat) => pure (.ok (decide (x < y))))
  #[3, 1, 2, 1]).run Nat).1 == #[1, 1, 2, 3]

end Strata.Dyn.Util.SortTest
