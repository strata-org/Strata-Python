/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Sem

set_option autoImplicit false

/-!
# A rule's obligation, at the rule's own types

A rule is a trusted Lean function that returns a `Sem ε E α` tree.  A proof about a rule, a
certificate that it respects the heap's typing or an analysis's transfer, states what the tree
may do and proves it of the tree, at the rule's own Lean types.  This file states what "the
tree satisfies a spec" means, once for every such proof:

* a `Spec G ε E` says, for a *ghost state* `g : G` (a typing of the heap, an abstract heap, a
  footprint), which requests the rule may make, which answers it may be given, which worlds the
  machine may hold and which exits the rule may take; `Ext` says how the ghost state grows
  between a request and its answer;
* `Spec.Sat V Q g t`: every request that `t` makes is allowed, and every leaf that `t` reaches
  under allowed answers returns a value `Q` holds of, or takes an allowed exit, or faults.

The statement is over `Sem ε E α` for an arbitrary `ε` and `E`, the rule's own generic
parameters, so a lemma about a rule is proved with the rule's capabilities, not at the machine's
tags.  `sat_bind` takes a goal through a `do` block, `Sat.bind` composes lemmas about helpers,
and `Sat.mono` weakens a postcondition.

A rule's lemma assumes what its regions promise, rely-guarantee: `RegionSpec`, with the `Sat`
lemma of running a region, `RegionSpec.sat`.  `Exec/CertModel.lean` is one choice of `G` and
`Spec`, a typing of the heap.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-- What a proof about a rule may assume of the machine, and what it requires of the rule, at a
ghost state of type `G`: how the ghost state grows, which requests are allowed and which answers
they may get, which worlds are possible, and which exits are allowed. -/
structure Spec (G : Type) (ε : Eff) (E : Type) where
  /-- The ghost state may grow from the first to the second while a request is served. -/
  Ext : G → G → Prop
  /-- The rule may make this request in this ghost state. -/
  Pre : G → ε.I → Prop
  /-- The machine may answer the request with this value, in this ghost state. -/
  Post : G → (i : ε.I) → ε.O i → Prop
  /-- The machine may hold this world in this ghost state. -/
  World : G → ε.W → Prop
  /-- The rule may take this exit in this ghost state. -/
  Exit : G → E → Prop

section
variable {G : Type} {ε : Eff} {E α β : Type} (V : Spec G ε E)

mutual
/-- **The tree `t` satisfies the spec `V`, with postcondition `Q`, from ghost state `g`**: every
request is allowed, every leaf reached under allowed answers returns a value `Q` holds of or
takes an allowed exit, and every world update keeps the world possible.  A fault is allowed:
a spec says nothing of faults.  A choice may be any number, so every one is covered. -/
def Spec.Sat (Q : G → α → Prop) : G → Sem ε E α → Prop
  | g, .ret a => Q g a
  | g, .stop (.jump e) => V.Exit g e
  | _, .stop (.fault _) => True
  | g, .choose k => ∀ c, Spec.Sat Q g (k c)
  | g, .vis i k => V.Pre g i ∧ ∀ g₁, V.Ext g g₁ → ∀ o, V.Post g₁ i o → Spec.Sat Q g₁ (k o)
  | g, .update f => ∀ w, V.World g w → Spec.SatAfter Q g (f w)

/-- An update's new world is possible, and its continuation satisfies the spec. -/
def Spec.SatAfter (Q : G → α → Prop) : G → ε.W × Sem ε E α → Prop
  | g, (w, k) => V.World g w ∧ Spec.Sat Q g k
end

variable {V}

/-- A leaf that returns satisfies the spec when the postcondition holds of its value. -/
@[simp] theorem Spec.sat_ret {Q : G → α → Prop} {g : G} {a : α} :
    V.Sat Q g (.ret a) ↔ Q g a := by
  rw [Spec.Sat]

/-- A jump satisfies the spec when its exit is allowed. -/
@[simp] theorem Spec.sat_jump {Q : G → α → Prop} {g : G} {e : E} :
    V.Sat Q g (.stop (.jump e)) ↔ V.Exit g e := by
  rw [Spec.Sat]

/-- A fault satisfies every spec. -/
@[simp] theorem Spec.sat_fault {Q : G → α → Prop} {g : G} {f : Fault} :
    V.Sat Q g (.stop (.fault f)) := by
  rw [Spec.Sat]
  trivial

/-- A request satisfies the spec when it is allowed, and its continuation does on every allowed
answer, at every grown ghost state. -/
@[simp] theorem Spec.sat_vis {Q : G → α → Prop} {g : G} {i : ε.I} {k : ε.O i → Sem ε E α} :
    V.Sat Q g (.vis i k) ↔
      V.Pre g i ∧ ∀ g₁, V.Ext g g₁ → ∀ o, V.Post g₁ i o → V.Sat Q g₁ (k o) := by
  rw [Spec.Sat]

/-- A choice satisfies the spec when every continuation does. -/
@[simp] theorem Spec.sat_choose {Q : G → α → Prop} {g : G} {k : Nat → Sem ε E α} :
    V.Sat Q g (.choose k) ↔ ∀ c, V.Sat Q g (k c) := by
  rw [Spec.Sat]

/-- A world update satisfies the spec when, from every possible world, it leads to a possible
world and a continuation that satisfies the spec. -/
@[simp] theorem Spec.sat_update {Q : G → α → Prop} {g : G} {f : ε.W → ε.W × Sem ε E α} :
    V.Sat Q g (.update f) ↔ ∀ w, V.World g w → V.World g (f w).1 ∧ V.Sat Q g (f w).2 := by
  rw [Spec.Sat]
  exact forall_congr' fun w => forall_congr' fun _ => by
    obtain ⟨w₁, k⟩ := f w
    rw [Spec.SatAfter]

/-- **A postcondition may be weakened.** -/
theorem Spec.Sat.mono {Q Q₁ : G → α → Prop} (hQ : ∀ g a, Q g a → Q₁ g a) {t : Sem ε E α}
    {g : G} (h : V.Sat Q g t) : V.Sat Q₁ g t :=
  Sem.rec (motive_1 := fun t => ∀ g, V.Sat Q g t → V.Sat Q₁ g t)
    (motive_2 := fun p => ∀ g, V.SatAfter Q g p → V.SatAfter Q₁ g p)
    (fun a g h => Spec.sat_ret.mpr (hQ g a (Spec.sat_ret.mp h)))
    (fun s _ h => by
      cases s with
      | jump e => exact Spec.sat_jump.mpr (Spec.sat_jump.mp h)
      | fault f => exact Spec.sat_fault)
    (fun _ ih g h => Spec.sat_choose.mpr fun c => ih c g (Spec.sat_choose.mp h c))
    (fun _ _ ih g h =>
      have h := Spec.sat_vis.mp h
      Spec.sat_vis.mpr ⟨h.1, fun g₁ he o ho => ih o g₁ (h.2 g₁ he o ho)⟩)
    (fun _ ih g h => by
      rw [Spec.Sat] at h ⊢
      exact fun w hw => ih w g (h w hw))
    (fun _ _ ih g h => by
      rw [Spec.SatAfter] at h ⊢
      exact ⟨h.1, ih g h.2⟩)
    t g h

end

/-! ## What a region promises -/

section
variable {G : Type} {ε : Eff} {E : Type} (V : Spec G ε E)

/-- **What a region promises**: running it on arguments that `P` holds of is an allowed
request, and its answer, at every grown ghost state, is a value `R` holds of. -/
structure RegionSpec {ts : List Type} {α : Type} (r : Region ε ts α) (P : G → Payload ts → Prop)
    (R : G → α → Prop) : Prop where
  req : ∀ g a, P g a → V.Pre g (r.req a)
  ans : ∀ g a o, V.Post g (r.req a) o → R g (r.ans a o)

variable {V}

/-- Running a region satisfies the spec when its arguments meet the region's precondition and
every answer the region promises meets the postcondition. -/
theorem RegionSpec.sat {ts : List Type} {α : Type} {r : Region ε ts α}
    {P : G → Payload ts → Prop} {R : G → α → Prop} (hr : RegionSpec V r P R) {a : Payload ts}
    {g : G} (ha : P g a) {Q : G → α → Prop} (hQ : ∀ g₁, V.Ext g g₁ → ∀ x, R g₁ x → Q g₁ x) :
    V.Sat Q g (runRegion r a) :=
  Spec.sat_vis.mpr ⟨hr.req g a ha, fun g₁ he o ho => Spec.sat_ret.mpr (hQ g₁ he _ (hr.ans g₁ a o ho))⟩

end

section
variable {G : Type} {ε : Eff} {E α β : Type} {V : Spec G ε E}

/-- `pure a` satisfies the spec when the postcondition holds of `a`. -/
@[simp] theorem Spec.sat_pure {Q : G → α → Prop} {g : G} {a : α} :
    V.Sat Q g (pure a : Sem ε E α) ↔ Q g a :=
  Spec.sat_ret

/-- A tree that branches on `c` satisfies the spec when each branch does where it is taken. -/
@[simp] theorem Spec.sat_ite {Q : G → α → Prop} {g : G} {c : Prop} [Decidable c]
    {a b : Sem ε E α} : V.Sat Q g (if c then a else b) ↔ (c → V.Sat Q g a) ∧ (¬c → V.Sat Q g b) := by
  by_cases h : c
  · simp only [h, ↓reduceIte, true_implies, not_true_eq_false, false_implies, and_true]
  · simp only [h, ↓reduceIte, false_implies, not_false_eq_true, true_implies, true_and]

/-- **`x >>= f` satisfies the spec exactly when `x` does, with the postcondition "`f` on the
value does"**: the simp lemma that takes a `Sat` goal through a `do` block. -/
@[simp] theorem Spec.sat_bind {Q : G → β → Prop} {x : Sem ε E α} {f : α → Sem ε E β} {g : G} :
    V.Sat Q g (x >>= f) ↔ V.Sat (fun g a => V.Sat Q g (f a)) g x :=
  Sem.rec (motive_1 := fun x => ∀ g, V.Sat Q g (x.bind f) ↔
      V.Sat (fun g a => V.Sat Q g (f a)) g x)
    (motive_2 := fun p => ∀ g, V.SatAfter Q g (Sem.bindAfter p f) ↔
      V.SatAfter (fun g a => V.Sat Q g (f a)) g p)
    (fun a g => (Spec.sat_ret (Q := fun g a => V.Sat Q g (f a)) (g := g) (a := a)).symm)
    (fun s _ => by
      cases s with
      | jump e => exact Spec.sat_jump.trans Spec.sat_jump.symm
      | fault f => exact iff_of_true Spec.sat_fault Spec.sat_fault)
    (fun _ ih _ => Spec.sat_choose.trans
      ((forall_congr' fun c => ih c _).trans Spec.sat_choose.symm))
    (fun _ _ ih _ => Spec.sat_vis.trans (Iff.trans
      (and_congr_right fun _ => forall_congr' fun g₁ => forall_congr' fun _ =>
        forall_congr' fun o => forall_congr' fun _ => ih o g₁) Spec.sat_vis.symm))
    (fun u ih g => by
      show V.Sat Q g (.update fun w => Sem.bindAfter (u w) f) ↔ _
      rw [Spec.Sat, Spec.Sat]
      exact forall_congr' fun w => forall_congr' fun _ => ih w g)
    (fun _ _ ih _ => by
      rw [Spec.SatAfter, Spec.SatAfter]
      exact and_congr_right fun _ => ih _)
    x g

/-- **Lemmas about helpers compose**: if `x` satisfies the spec with the postcondition "the rest
of the rule, `f` on the value, satisfies the spec", then `x` followed by `f` satisfies it. -/
theorem Spec.Sat.bind {Q : G → β → Prop} {x : Sem ε E α} {f : α → Sem ε E β} {g : G}
    (h : V.Sat (fun g a => V.Sat Q g (f a)) g x) : V.Sat Q g (x.bind f) :=
  Spec.sat_bind.mpr h

end

end

end Strata.Dyn.Exec
