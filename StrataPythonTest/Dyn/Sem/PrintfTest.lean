/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Printf
public import StrataPython.Dyn.Sem.Concrete
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Proto.Printf
meta import StrataPython.Dyn.Sem.Concrete

set_option autoImplicit false

/-!
# The pure helpers of `repr` and printf-style `%`

Each expected text is what CPython 3.12 gives: `bytes` and `ascii` reprs, the digits of an
integer conversion (`pfLongText`), its padding (`pfPad`), and what the `repr` guard finds
(`reprEntryOf`).
-/

namespace StrataPython.Dyn.Sem.PrintfTest

open StrataPython.Dyn.Sem Proto

-- `repr` of a `bytes`: the quote, and the escapes of a backslash, the quote, `\t` and other bytes.
#guard Format.bytesRepr #[97, 39, 34, 0, 255, 92, 9] == "b'a\\'\"\\x00\\xff\\\\\\t'"
#guard Format.bytesRepr "it's".toUTF8.data == "b\"it's\""
-- `ascii`: `\x`, `\u` and `\U` escapes by the code point.
#guard Format.asciiEscape "'aé€😀'" == "'a\\xe9\\u20ac\\U0001f600'"

/-- A unit's text, as `pfFormat` makes it for an `int` conversion: the digits, then the padding. -/
def longUnit (a : PfArg) (n : Int) : Option String :=
  match pfLongText n a.alt a.prec a.ch with
  | .ok cs => some (String.ofList (pfPad { a with sign := true } cs))
  | .error _ => none

#guard longUnit { ch := 'd', ljust := true, zero := true, width := 5 } 3 == some "3    "
#guard longUnit { ch := 'd', plus := true, zero := true, width := 5 } 3 == some "+0003"
#guard longUnit { ch := 'd', zero := true, width := 5 } (-3) == some "-0003"
#guard longUnit { ch := 'd', blank := true, width := 5 } 3 == some "    3"
#guard longUnit { ch := 'x', alt := true, zero := true, width := 8 } 255 == some "0x0000ff"
#guard longUnit { ch := 'o', alt := true, ljust := true, width := 8 } 8 == some "0o10    "
#guard longUnit { ch := 'd', prec := 3 } (-7) == some "-007"
#guard longUnit { ch := 'X', alt := true } 255 == some "0XFF"
#guard longUnit { ch := 'x' } (-255) == some "-ff"
#guard longUnit { ch := 'x', alt := true } (-255) == some "-0xff"
#guard longUnit { ch := 'x', prec := 5 } 255 == some "000ff"
-- A string conversion's padding: right-justified, or left with `-`.
#guard String.ofList (pfPad { ch := 's', width := 5 } "ab".toList) == "   ab"
#guard String.ofList (pfPad { ch := 's', ljust := true, width := 5 } "ab".toList) == "ab   "

-- The `repr` guard: an object is found by its id; a tuple is `unknown` when a tuple with the same
-- items is in the guard, and fresh when only other tuples are.
#guard Prim.reprEntryOf { active := #[.obj 3] } (.obj 3) == .hit
#guard Prim.reprEntryOf { active := #[.obj 3] } (.obj 4) == .fresh
#guard Prim.reprEntryOf { active := #[Prim.reprKeyOf (.tuple #[.obj 3])] } (Prim.reprKeyOf (.tuple #[.obj 3])) == .unknown
#guard Prim.reprEntryOf { active := #[Prim.reprKeyOf (.tuple #[.obj 3])] } (Prim.reprKeyOf (.tuple #[.obj 4])) == .fresh
#guard Prim.reprEntryOf { active := #[Prim.reprKeyOf (.tuple #[.int 1])] } (.obj 1) == .fresh
-- A tuple inside an active tuple holds fewer values, so it is fresh at once.
#guard (Value.tuple #[.int 0, .tuple #[.int 0, .none]]).nodes == 5
#guard Prim.reprEntryOf { active := #[Prim.reprKeyOf (.tuple #[.int 0, .tuple #[.int 0, .none]])] }
  (Prim.reprKeyOf (.tuple #[.int 0, .none])) == .fresh

end StrataPython.Dyn.Sem.PrintfTest
