/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Util.NameMap

set_option autoImplicit false

/-! # A 2-3 tree keyed by `Nat`, and maps of names

Checks, by `decide +kernel`, that the kernel reduces `NatTree23`, `NameMap` and `NameSet`, and
that `Name.key` separates names that differ in where a segment ends or in a segment's kind.
-/

namespace Strata.Mantle.Util.NatTree23Test

/-! ## The tree

Forty keys in an order that splits nodes at every level, each mapped to its square. -/

private def ks : List Nat :=
  [17, 3, 29, 8, 1, 22, 35, 11, 6, 39, 14, 26, 2, 31, 19, 9, 37, 5, 24, 12,
   0, 33, 16, 28, 7, 21, 38, 10, 4, 30, 15, 25, 13, 36, 18, 27, 20, 34, 23, 32]

private def entries : List (Nat × Nat) := ks.map fun k => (k, k * k)

private def t : Option (NatTree23 Nat) := NatTree23.ofArray? entries.toArray

/-- Forty distinct keys: the build succeeds. -/
example : t.isSome = true := by decide +kernel

/-- Every key is found, with the value it was given. -/
example : (t.map fun u => entries.all fun p => u.find? p.1 == some p.2) = some true := by
  decide +kernel

/-- No other key is found. -/
example : (t.map fun u => [40, 41, 100].any fun k => (u.find? k).isSome) = some false := by
  decide +kernel

/-- The keys increase from left to right, which is what `find?` searches by. -/
example : (t.map fun u => decide u.Ordered) = some true := by decide +kernel

/-- The tree holds forty entries. -/
example : (t.map fun u => u.entries.length) = some 40 := by decide +kernel

/-- The reversed list gives the same lookups. -/
example : ((NatTree23.ofArray? entries.reverse.toArray).map fun u =>
    entries.all fun p => u.find? p.1 == some p.2) = some true := by decide +kernel

/-- One repeated key, and the build fails: the duplicate check is the build. -/
example : (NatTree23.ofArray? (entries ++ [(23, 0)]).toArray).isSome = false := by
  decide +kernel

/-- A key repeated inside the list, not just appended. -/
example : (NatTree23.ofArray? #[(1, 'a'), (2, 'b'), (1, 'c')]).isSome = false := by
  decide +kernel

/-- An empty array builds the empty tree, which finds nothing. -/
example : ((NatTree23.ofArray? (#[] : Array (Nat × Nat))).map fun u => (u.find? 0).isSome) =
    some false := by decide +kernel

/-! ## `Name.key`

The markers `256` and `257` are what keep one segment's digits from running into the next, so
names that differ only in where a segment ends have different keys. -/

example : (Name.key (.str (.str .base "ab") "c") == Name.key (.str (.str .base "a") "bc")) =
    false := by decide +kernel

example : (Name.key (.str (.str .base "a") "b") == Name.key (.str .base "ab")) = false := by
  decide +kernel

/-- A numeric segment and the string of the same digits are different names. -/
example : (Name.key (.num .base 12) == Name.key (.str .base "12")) = false := by decide +kernel

/-- An empty outer segment is not no segment. -/
example : (Name.key (.str (.str .base "a") "") == Name.key (.str .base "a")) = false := by
  decide +kernel

/-- Equal names have equal keys, deep ones included. -/
example : (Name.key (.num (.str (.str .base "pkg") "mod") 7) ==
    Name.key (.num (.str (.str .base "pkg") "mod") 7)) = true := by decide +kernel

/-! ## Maps and sets of names -/

private def nms : List Name :=
  [.str .base "a", .str (.str .base "a") "b", .num .base 3, .num (.str .base "a") 3,
   .str (.str (.str .base "pkg") "mod") "f", .base]

private def s : Option NameSet := NameSet.of? nms.toArray

/-- Six distinct names: the set is built, and holds them all. -/
example : (s.map fun u => nms.all u.contains) = some true := by decide +kernel

/-- A name it was not given is not in it, however near. -/
example : (s.map fun u => [Name.str .base "b", .num .base 4, .str (.str .base "a") "c"].any
    u.contains) = some false := by decide +kernel

/-- A repeated name, and the build fails. -/
example : (NameSet.of? (nms ++ [Name.num (.str .base "a") 3]).toArray).isSome = false := by
  decide +kernel

/-- A map returns the value at a name. -/
private def nm : Option (NameMap Nat) :=
  NameMap.ofArray? #[(.str .base "a", 1), (.num .base 3, 2), (.base, 3)]

example : (nm.map fun u => u.find? (.num .base 3)) = some (some 2) := by decide +kernel

example : (nm.map fun u => u.find? .base) = some (some 3) := by decide +kernel

example : (nm.map fun u => u.find? (.str .base "b")) = some none := by decide +kernel

end Strata.Mantle.Util.NatTree23Test
