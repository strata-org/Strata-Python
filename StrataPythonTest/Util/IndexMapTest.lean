/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Util.IndexMap
meta import StrataPython.Util.IndexMap

set_option autoImplicit false

/-! # `IndexMap`: lookup by key, iteration in insertion order

The map is a hash index over two arrays, so nothing here reduces in the kernel: the
behaviour is pinned with `#guard` in compiled code, and the lemmas are exercised as the
rewrites a client would use them for. -/

namespace StrataPython.Util.IndexMapTest

open Strata

private def m₀ : IndexMap String Nat := ∅
private def m₁ : IndexMap String Nat := (m₀.insert "b" 1).insert "a" 2
private def m₂ : IndexMap String Nat := (m₁.insert "c" 3).insert "b" 10

/-! ## Iteration order is insertion order, not hash order -/

#guard m₁.keys == #["b", "a"]
#guard m₁.vals == #[1, 2]
#guard m₁.size == 2

/-! Overwriting a key replaces its value in place: the order does not move. -/

#guard m₂.keys == #["b", "a", "c"]
#guard m₂.vals == #[10, 2, 3]
#guard m₂.toArray == #[("b", 10), ("a", 2), ("c", 3)]

/-! ## Lookup -/

#guard m₂["b"]? == some 10
#guard m₂["c"]? == some 3
#guard m₂["z"]? == none
#guard m₀["a"]? == none
#guard m₂.idxOf? "a" == some 1
#guard m₂.idxOf? "z" == none
#guard m₂.contains "c" && !m₂.contains "z"
#guard m₂.getD "z" 7 == 7
#guard m₂.get! "a" == 2

/-! ## `ofArray`: the last value for a key wins, at the key's first position -/

private def ofA : IndexMap String Nat := .ofArray #[("x", 1), ("y", 2), ("x", 3)]

#guard ofA.keys == #["x", "y"]
#guard ofA["x"]? == some 3

/-! ## `BEq` ignores the order of insertion -/

#guard (m₀.insert "p" 1 |>.insert "q" 2) == (m₀.insert "q" 2 |>.insert "p" 1)
#guard !((m₀.insert "p" 1) == (m₀.insert "p" 2))

/-! ## The lemmas, as rewrites

What a client proves about a map is stated through `keys`, `vals` and `[·]?`. -/

example : (m₀.insert "a" 1)["a"]? = some 1 := by simp

example (m : IndexMap String Nat) (k : String) (h : ¬ k ∈ m) (v : Nat) :
    (m.insert k v).keys = m.keys.push k ∧ (m.insert k v).vals = m.vals.push v :=
  ⟨IndexMap.keys_insert_of_not_mem v h, IndexMap.vals_insert_of_not_mem v h⟩

example (m : IndexMap String Nat) (k : String) (h : k ∈ m) (v : Nat) :
    (m.insert k v).keys = m.keys :=
  IndexMap.keys_insert_of_mem v h

/-- A member's total lookup agrees with `[·]?`. -/
example (m : IndexMap String Nat) (k : String) (v : Nat) (h : m[k]? = some v) :
    m[k]'(IndexMap.mem_of_getElem?_eq_some h) = v :=
  IndexMap.getElem_eq_of_getElem?_eq_some _ h

/-- Keys never repeat, which is what makes a position a key's address. -/
example (m : IndexMap String Nat) : m.keys.toList.Nodup := IndexMap.keys_nodup m

/-- The key at a position is found at that position. -/
example (m : IndexMap String Nat) (i : Nat) (h : i < m.keys.size) :
    m.idxOf? m.keys[i] = some i :=
  IndexMap.idxOf?_getElem_keys m i h

end StrataPython.Util.IndexMapTest
