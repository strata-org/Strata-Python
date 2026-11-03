/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Sum
public import StrataPythonTest.Dyn.Sem.Library.SumCases
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Library.Sum
meta import StrataPythonTest.Dyn.Sem.Library.SumCases

set_option autoImplicit false

/-!
# The numeric core of `sum`

`SumCases.cases` holds CPython 3.12's `sum` of ints, bools, floats and instances of subclasses of
`int` and `float` that don't override anything. The loop below runs `Sum.step` on them, adds an
item with `+` as `Arith.binary` gives it when `step` says so, and must give CPython's result.
-/

namespace StrataPython.Dyn.Sem.Library.SumTest

open StrataPython.Dyn.Sem.Arith
open StrataPython.Dyn.Sem.Format (Failure)
open StrataPython.Dyn.Sem.Library.Sum

/-- A value of the cases: its number, and whether its type is a subclass. -/
private def value (tok : String) : Num × Bool :=
  match tok.splitOn ":" with
  | ["i", v] => (.int v.toInt!, false)
  | ["I", v] => (.int v.toInt!, true)
  | ["b", v] => (.bool (v == "1"), false)
  | ["f", v] => (.float v.toNat!.toUInt64, false)
  | ["F", v] => (.float v.toNat!.toUInt64, true)
  | _ => (.int 0, false)

/-- How `sum` tells the item apart. -/
private def itemOf : Num × Bool → Item
  | (.int i, sub) => .int i !sub
  | (.bool b, _) => .int (if b then 1 else 0) true
  | (.float bits, false) => .float bits
  | (.float _, true) => .other

/-- How `sum` tells the start apart. -/
private def startOf : String → Start Num
  | "-" => .none
  | "s" => .rejected .str
  | "y" => .rejected .bytes
  | "a" => .rejected .bytearray
  | tok =>
    match value tok with
    | (.int i, false) => .int i (.int i)
    | (.float bits, false) => .float bits
    | (n, _) => .other n

/-- A result, written as the cases write CPython's. -/
private def showResult : Except Failure Num → String
  | .ok (.int i) => s!"i{i}"
  | .ok (.bool b) => s!"b{if b then 1 else 0}"
  | .ok (.float bits) => if isNaN bits then "fnan" else s!"f{bits}"
  | .error (.raise cls msg) => s!"E{cls}: {msg}"
  | .error (.notModelled what) => s!"N{what}"

/-- A total as a number. -/
private def totalValue : Total Num → Num
  | .int i => .int i
  | .float bits => .float bits
  | .obj n => n

/-- `sum` of the items, from the state `s`. -/
private def loop : State Num → List (Num × Bool) → Except Failure Num
  | s, [] => .ok (totalValue (finish s))
  | s, x :: xs =>
    match step s (itemOf x) with
    | .next s => loop s xs
    | .add t => do
      -- An instance of a subclass adds as its value; the result's type is `int` or `float`.
      let r ← (binary .add (totalValue t) x.1).getD (.error (.notModelled "no slot"))
      let bits := match r with
        | .float bits => some bits
        | _ => none
      loop (afterAdd s r bits) xs

private def run (start items : String) : String :=
  let items := (items.splitOn " ").filter (· != "") |>.map value
  showResult do
    let s ← init (startOf start)
    loop s items

private def mismatches : List (String × String) :=
  SumCases.cases.toList.filterMap fun (s, xs, r) =>
    if run s xs == r then none else some (s, xs)

#guard SumCases.cases.size == 1528
#guard mismatches == []

/-! ## The phases -/

/-- Results compared by their contents, for the guards below. -/
private instance {α : Type} [BEq α] : BEq (Except Failure α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

-- An int item that doesn't fit in a C `long`, or whose sum doesn't, ends the int phase.
#guard step (α := Nat) (.int 0) (.int (2 ^ 63) true) == .add (.int 0)
#guard step (α := Nat) (.int 1) (.int (2 ^ 63 - 1) true) == .add (.int 1)
#guard step (α := Nat) (.int (-1)) (.int (-2 ^ 63) true) == .add (.int (-1))
#guard step (α := Nat) (.int (-1)) (.int (2 ^ 63 - 1) true) == .next (.int (2 ^ 63 - 2))
-- An instance of a subclass of `int` ends the int phase, but not the float phase.
#guard step (α := Nat) (.int 0) (.int 1 false) == .add (.int 0)
#guard step (α := Nat) (.float one zero) (.int 1 false) == .next (.float two zero)
-- The generic phase adds every item to its total object.
#guard step (.generic 7) (.int 1 true) == .add (.obj 7)
-- After the int phase, the sum goes on in the float phase only if the total is then a float,
-- and otherwise in the generic phase, with the add's result `r` (here 5) as its total.
#guard afterAdd (.int 0) 5 (some one) == .float one zero
#guard afterAdd (.int 0) 5 none == .generic 5
#guard afterAdd (.float one zero) 5 (some one) == .generic 5
#guard init (.int (2 ^ 63) 9) == .ok (.generic 9)
#guard init (α := Nat) (.int (2 ^ 63 - 1) 9) == .ok (.int (2 ^ 63 - 1))
#guard init (.other 9) == .ok (.generic 9)
#guard finish (.generic 9) == .obj 9

end StrataPython.Dyn.Sem.Library.SumTest
