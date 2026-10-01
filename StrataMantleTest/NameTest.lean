/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.NameProps
meta import StrataMantle.Name

set_option autoImplicit false

/-! # `Name` ordering, in the kernel and in compiled code

Checks that `Name.cmpStr` gives the same results under `decide` and in compiled code, on
prefixes, digits and multi-byte code points. -/

namespace StrataMantleTest.NameTest

open Strata.Mantle

def py (s : String) : Name := .str (.str .base "py") s

/-! Kernel: `decide` reduces the byte-wise body. -/

example : Name.cmpStr "ab" "abx" = .lt := by decide
example : Name.cmpStr "abx" "ab" = .gt := by decide
example : Name.cmpStr "ab" "ab" = .eq := by decide
example : Name.cmpStr "" "a" = .lt := by decide
example : Name.cmpStr "op137" "op14" = .lt := by decide
example : Name.cmpStr "Z" "a" = .lt := by decide
example : Name.cmpStr "a" "é" = .lt := by decide
example : Name.cmpStr "é" "ê" = .lt := by decide
example : Name.cmpStr "ÿ" "Ā" = .lt := by decide      -- U+00FF vs U+0100: 2-byte, lead differs
example : Name.cmpStr "\uFFFF" "𐀀" = .lt := by decide  -- U+FFFF vs U+10000: 3-byte vs 4-byte

example : compare (py "a") (py "b") = .lt := by decide
example : compare (py "b") (.str (py "a") "z") = .gt := by decide
example : compare (py "a") (.num (py "a") 0) = .lt := by decide

/-! Compiled code: `@[csimp]` runs `String.compare`, and gives the same answers. -/

def cases : List (String × String) :=
  [("ab", "abx"), ("abx", "ab"), ("ab", "ab"), ("", "a"), ("op137", "op14"), ("Z", "a"),
   ("a", "é"), ("é", "ê"), ("ÿ", "Ā"), ("\uFFFF", "𐀀")]

/-- info: [lt, gt, eq, lt, lt, lt, lt, lt, lt, lt] -/
#guard_msgs in
#eval IO.println (cases.map fun (a, b) =>
  match Name.cmpStr a b with | .lt => "lt" | .eq => "eq" | .gt => "gt")

/-! The order is lawful. -/

example : Std.TransOrd Name := inferInstance
example : Std.LawfulEqOrd Name := inferInstance

end StrataMantleTest.NameTest
