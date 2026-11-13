/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Old parts

An `OLD(e)` in a post-state clause of a PySpec model or in a loop invariant reads `e` in the state
at the function's entry. The part read there is the largest subexpression around an `OLD` that
reads no state outside its `OLD`s (`docs/PythonToDyn.md` §12.4): `len(OLD(xs)) == len(xs) + 1`
reads `len(xs)` at entry, and `OLD(xs) == xs` reads only `xs` there.

`OldSyntax` is what a syntax gives for this rule, and `hasOld`, `readsOnlyOld`, `unOld` and
`splitOld` state the rule once, for every syntax that has an instance. The class is
syntax-neutral; its instances are PySpec's clause expressions (`PySpec/Clause.lean`) and the
Python expressions of loop invariants (`Markers.lean`).
-/

namespace StrataPython.Dyn

public section

/-- What the old-part rule needs from a syntax `α`. -/
class OldSyntax (α : Type) [SizeOf α] where
  /-- `some e` if the node is `OLD(e)`. -/
  oldArg? : α → Option α
  /-- `OLD(e)`, for the result of a split. -/
  mkOld : α → α
  /-- Whether the node may become an old part, for example not a slice. Only `splitOld` reads
  it. -/
  wrappable : α → Bool
  /-- Whether the node itself reads state, not counting its children: a parameter, a name, a
  quantifier's binder, a call's result. -/
  readsState : α → Bool
  /-- The children that the rule looks into. -/
  children : α → List α
  children_lt : ∀ e c, c ∈ children e → sizeOf c < sizeOf e
  oldArg_lt : ∀ e a, oldArg? e = some a → sizeOf a < sizeOf e
  /-- The node with each child replaced. -/
  mapChildren : (e : α) → ((c : α) → c ∈ children e → α) → α
  /-- Rebuilding replaces exactly the children that the rule looks into, in order. -/
  children_mapChildren : ∀ e (f : (c : α) → c ∈ children e → α),
    children (mapChildren e f) = (children e).attach.map fun ⟨c, h⟩ => f c h

namespace OldSplit

variable {α : Type} [SizeOf α] [OldSyntax α]
open OldSyntax

/-- Whether `e` holds an `OLD`. -/
@[expose] def hasOld (e : α) : Bool :=
  (oldArg? e).isSome || (children e).attach.any fun ⟨c, _⟩ => hasOld c
termination_by sizeOf e
decreasing_by exact children_lt e c ‹_›

/-- Whether `e` reads no state outside its `OLD`s, so that the whole of `e` can be read at
entry. -/
@[expose] def readsOnlyOld (e : α) : Bool :=
  if (oldArg? e).isSome then true
  else !readsState e && (children e).attach.all fun ⟨c, _⟩ => readsOnlyOld c
termination_by sizeOf e
decreasing_by exact children_lt e c ‹_›

/-- `e` with every `OLD` removed: the expression inside an old region. -/
@[expose] def unOld (e : α) : α :=
  match _h : oldArg? e with
  | some a => unOld a
  | none => mapChildren e fun c _ => unOld c
termination_by sizeOf e
decreasing_by
  · exact oldArg_lt e a _h
  · exact children_lt e c ‹_›

/-- `e` with each old part `x` written `OLD(x')`, where `x'` is `x` without its `OLD`s: each
largest subexpression that may become an old part, holds an `OLD` and reads no state outside its
`OLD`s. -/
@[expose] def splitOld (e : α) : α :=
  if wrappable e && hasOld e && readsOnlyOld e then mkOld (unOld e) else
  match oldArg? e with
  | some a => mkOld (unOld a)
  | none => mapChildren e fun c _ => splitOld c
termination_by sizeOf e
decreasing_by exact children_lt e c ‹_›

end OldSplit

end -- public section

end StrataPython.Dyn
