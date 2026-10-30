/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDDM.AST

set_option autoImplicit false

/-!
# Termination of recursion on a DDM AST

The scope pass and the translator recurse on parts of AST nodes.  A DDM node wraps its array,
option and string fields in an `Ann`, so a recursive call on `body.val` needs the size of
`body.val` below the size of `body`, which Lean's default termination tactic does not see.

* `sizeOf_ann` gives the size of an `Ann`, and `sizeOf_sourceRange` that of a source range,
  which every node has;
* `sizeOf_snd_lt`, `sizeOf_toList_lt` and `sizeOf_zip_le` bound the sizes of values that
  helpers compute from parts of a node;
* `ast_decreasing` proves the size goal of such a call.  In the namespace
  `StrataPython.Dyn`, it extends `decreasing_trivial`, so a definition there with
  `termination_by sizeOf e` needs no `decreasing_by`.

Nothing here is about Python: any front end whose AST comes from a DDM dialect can use it.
-/

namespace StrataPython.Dyn

public section

/-- The size of an annotated value: one more than its annotation's and its value's. -/
theorem sizeOf_ann {B α : Type} [SizeOf B] [SizeOf α] (a : StrataDDM.Ann B α) :
    sizeOf a = 1 + sizeOf a.ann + sizeOf a.val := by
  cases a; simp

/-- The size of a source range: its two positions, and one for each of its three
structures. -/
theorem sizeOf_sourceRange (sr : StrataDDM.SourceRange) :
    sizeOf sr = 3 + sr.start.byteIdx + sr.stop.byteIdx := by
  rcases sr with ⟨⟨_⟩, ⟨_⟩⟩; simp; omega

/-- The second component of a pair is smaller than the pair. -/
theorem sizeOf_snd_lt {α β : Type} [SizeOf α] [SizeOf β] (p : α × β) :
    sizeOf p.2 < sizeOf p := by
  cases p; simp; omega

/-- The list of an array's elements is smaller than the array. -/
theorem sizeOf_toList_lt {α : Type} [SizeOf α] (a : Array α) : sizeOf a.toList < sizeOf a := by
  cases a; simp

/-- Zipping two lists gives a list no larger than the two together. -/
private theorem sizeOf_list_zip_le {α β : Type} [SizeOf α] [SizeOf β] (xs : List α) (ys : List β) :
    sizeOf (xs.zip ys) ≤ sizeOf xs + sizeOf ys := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys => have hle := ih ys; simp; omega

/-- Zipping two arrays gives an array no larger than the two together. -/
theorem sizeOf_zip_le {α β : Type} [SizeOf α] [SizeOf β] (xs : Array α) (ys : Array β) :
    sizeOf (xs.zip ys) ≤ sizeOf xs + sizeOf ys := by
  rcases xs with ⟨xs⟩; rcases ys with ⟨ys⟩
  have hle := sizeOf_list_zip_le xs ys
  rw [List.zip_toArray]; simp; omega

end -- public section

/-- Prove `sizeOf x < sizeOf y` for a recursive call on part of an AST node: take the
hypothesis `x ∈ xs` that Lean adds for a call inside `for`, `mapM` or `flatMap` over `xs`, if
there is one, unfold the sizes of `Ann` fields and source ranges (and, if that is not enough,
of constructors), then use `omega`. -/
syntax "ast_decreasing" : tactic

macro_rules
  | `(tactic| ast_decreasing) => `(tactic| (
    try have hmem := Array.sizeOf_lt_of_mem ‹_ ∈ _›
    first
      | (simp (config := { failIfUnchanged := false }) only
          [StrataPython.Dyn.sizeOf_ann, StrataPython.Dyn.sizeOf_sourceRange] at *; omega)
      | (simp (config := { failIfUnchanged := false })
          [StrataPython.Dyn.sizeOf_ann, StrataPython.Dyn.sizeOf_sourceRange] at *
         omega)))

scoped macro_rules | `(tactic| decreasing_trivial) => `(tactic| ast_decreasing)

end StrataPython.Dyn
