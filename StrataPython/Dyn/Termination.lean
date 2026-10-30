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

* `sizeOf_ann` gives the size of an `Ann`;
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

end -- public section

/-- Prove `sizeOf x < sizeOf y` for a recursive call on part of an AST node: take the
hypothesis `x ∈ xs` that Lean adds for a call inside `for`, `mapM` or `flatMap` over `xs`, if
there is one, unfold the sizes of `Ann` fields (and, if that is not enough, of constructors),
then use `omega`. -/
syntax "ast_decreasing" : tactic

macro_rules
  | `(tactic| ast_decreasing) => `(tactic| (
    try have hmem := Array.sizeOf_lt_of_mem ‹_ ∈ _›
    first
      | (simp (config := { failIfUnchanged := false }) only [StrataPython.Dyn.sizeOf_ann]
          at *; omega)
      | (simp (config := { failIfUnchanged := false }) [StrataPython.Dyn.sizeOf_ann] at *
         omega)))

scoped macro_rules | `(tactic| decreasing_trivial) => `(tactic| ast_decreasing)

end StrataPython.Dyn
