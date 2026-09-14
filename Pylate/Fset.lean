/-
Finite sets, held as duplicate-free lists and computed through hash sets.

Strata carries no mathlib, so the `Finset` and `→₀` types of LEAN_SPEC.md
section 3 are replaced by lists with set-theoretic order and join. No canonical
form is kept: the order is `∀ a ∈ s, a ∈ t`, which is insensitive to duplication
and ordering, and the fixpoint tests use the order, never structural equality.

The *representation* stays a list, because a value's tags and locations are
iterated, mapped, and pattern-matched all over the interpreter. What changed is
the set operations. Every one of them used a linear membership scan, so `union`
was O(|s| x |t|), and that was the interpreter's dominant cost: a list of 560
tuple literals gives one value 560 locations, and joining it costs ~313k list
steps every time -- once per line snapshot over a 4116-line file.

Each operation now builds a hash set of the side it tests against and streams the
other side past it, which is O(|s| + |t|) and yields the same elements in the
same order. Order is preserved deliberately: it reaches rendered output, so a
reordering would drift every golden without changing a single fact.
-/
import Std.Data.HashSet

set_option linter.unusedSectionVars false

namespace Pylate

open Std

abbrev Fset (A : Type) := List A

namespace Fset

variable {A : Type} [DecidableEq A]

def insert (a : A) (s : Fset A) : Fset A :=
  if a ∈ s then s else a :: s

section Fast
variable {A : Type} [BEq A] [Hashable A]

/-- Elements of `s` not already in `t`, prepended in order. Matches the old
    `s.foldr insert t` on duplicate-free inputs, which every `Fset` is, and the
    accumulator is tracked so a duplicated input still yields a set. -/
def union (s t : Fset A) : Fset A := Id.run do
  let mut seen := HashSet.ofList t
  let mut out := t
  for a in s.reverse do
    if !seen.contains a then
      seen := seen.insert a
      out := a :: out
  return out

def inter (s t : Fset A) : Fset A :=
  let keep := HashSet.ofList t
  s.filter (fun a => keep.contains a)

def diff (s t : Fset A) : Fset A :=
  let drop := HashSet.ofList t
  s.filter (fun a => !drop.contains a)

def subset (s t : Fset A) : Bool :=
  let have' := HashSet.ofList t
  s.all (fun a => have'.contains a)

end Fast

/-- The set-theoretic order. All lattice reasoning happens here. -/
def Sub (s t : Fset A) : Prop := ∀ a, a ∈ s → a ∈ t

theorem Sub.refl (s : Fset A) : Sub s s := fun _ h => h

theorem Sub.trans {s t u : Fset A} (h₁ : Sub s t) (h₂ : Sub t u) : Sub s u :=
  fun a h => h₂ a (h₁ a h)

/-- `Sub` is the lattice order every soundness proof reasons with. It quantifies
    over membership, so it says nothing about how a union is computed and holds
    for any representation. -/
theorem mem_filter' {p : A → Bool} {a : A} {s : Fset A} :
    a ∈ s.filter p ↔ a ∈ s ∧ p a = true := List.mem_filter

theorem filter_sub {p : A → Bool} {s : Fset A} : Sub (s.filter p) s :=
  fun _ h => (List.mem_filter.mp h).1

end Fset
end Pylate
