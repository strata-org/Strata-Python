/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Machine
public import StrataDyn.Exec.CertModel
public import StrataDyn.Exec.Frame

set_option autoImplicit false

/-!
# Facts relating a source frame to a target frame

The simulation of ref-to-reg relates a frame of the source, where
promoted cells live on the heap, to a frame of the target, where their contents live in values.
What it knows at a point of the code is a list of *facts*, each about one source value or cell and
at most one target value:

* `eq u v`: the target's value `u` is the source's value `v`;
* `cell u c`: the target's value `u` is the content of the source's promoted cell `c`;
* `prom c`: the source's value `c` is a promoted cell.

A promoted cell's location is in the set `P` of promoted locations, which the simulation keeps as
ghost state; the source and target heaps agree off `P` (`HeapRel`).  `Sound` is what a frame's
facts say, together with the distinctness of the promoted cells' locations.

`bindSite_param` says which value each parameter of a block is bound to.
-/

namespace Strata.Dyn.RefToRegSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-! ## Binding a block's parameters -/

/-- Binding distinct parameters to as many values binds the `k`-th to the `k`-th value. -/
theorem bindSite_param :
    ∀ (env : Array (Dyn M.interp)) {ts : List Ty} (ps : Exec.Ctx) (ds : List (Dyn M.interp))
      (xs : Args M.interp ts) (h : ∀ p ∈ ps, p.1 < env.size), (ps.map (·.1)).Nodup →
      ds.length + ts.length = ps.length → ∀ (k : Nat) (hk : k < ps.length),
      (bindSite env ps ds xs h)[(ps[k]'hk).1]? = (ds ++ Args.toList xs)[k]?
  | env, _, (p, _) :: ps, d :: ds, xs, h, hn, hl, k, hk => by
    rw [bindSite]
    have hn₁ := (List.nodup_cons.mp hn)
    cases k with
    | zero =>
      show (bindSite _ ps ds xs _)[p]? = _
      rw [bindSite_other _ ps ds xs _ hn₁.1]
      simp
    | succ k =>
      have := bindSite_param (env.set p d (h (p, _) List.mem_cons_self)) ps ds xs (fits_set h d)
        hn₁.2 (by simp at hl ⊢; omega) k (Nat.lt_of_succ_lt_succ hk)
      simpa using this
  | env, _, (p, _) :: ps, [], .cons x xs, h, hn, hl, k, hk => by
    rw [bindSite]
    have hn₁ := (List.nodup_cons.mp hn)
    cases k with
    | zero =>
      show (bindSite _ ps [] xs _)[p]? = _
      rw [bindSite_other _ ps [] xs _ hn₁.1]
      simp [Args.toList]
    | succ k =>
      have := bindSite_param (env.set p ⟨_, x⟩ (h (p, _) List.mem_cons_self)) ps [] xs
        (fits_set h _)
        hn₁.2 (by simp at hl ⊢; omega) k (Nat.lt_of_succ_lt_succ hk)
      simpa [Args.toList] using this
  | _, _, [], _, _, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | _, _, (_, _) :: _, [], .nil, _, _, hl, _, _ => by simp at hl

/-! ## The source's typing off the promoted cells -/

/-- The typing of `heap` without the locations `P`: each other cell at its value's tag, and each
captures cell at its values' tags.  A value of the source that is valid in it holds no
promoted cell. -/
def typOff (heap : Heap M) (P : List Nat) : Typing where
  cell l := if l ∈ P then none else (heap.cells[l]?).map (·.1)
  caps k := (heap.caps[k]?).map (·.map (·.1))

/-- A promoted location is not in the typing off `P`. -/
theorem typOff_none {heap : Heap M} {P : List Nat} {l : Nat} (hl : l ∈ P) :
    (typOff heap P).cell l = none := by
  unfold typOff
  simp only [hl, ↓reduceIte]

/-- A cell valid off `P` is not in `P`, and holds a value of its tag. -/
theorem typOff_valid {heap : Heap M} {P : List Nat} {l : Nat} {t : Ty} :
    (typOff heap P).Valid l t ↔ l ∉ P ∧ ∃ h : l < heap.cells.size, (heap.cells[l]'h).1 = t := by
  unfold typOff Typing.Valid
  by_cases hl : l ∈ P
  · simp [hl]
  · simp only [hl, ↓reduceIte, not_false_eq_true, true_and, Option.map_eq_some_iff,
      Array.getElem?_eq_some_iff]
    exact ⟨fun ⟨_, ⟨h, rfl⟩, ht⟩ => ⟨h, ht⟩, fun ⟨h, ht⟩ => ⟨_, ⟨h, rfl⟩, ht⟩⟩

/-- A valid location is one of the heap's. -/
theorem typOff_valid_lt {heap : Heap M} {P : List Nat} {l : Nat} {t : Ty}
    (h : (typOff heap P).Valid l t) : l < heap.cells.size :=
  (typOff_valid.mp h).2.1

/-- Off `P`, the typing is the heap's: two heaps that agree off `P` and have the same captures
type alike. -/
theorem typOff_congr {heap heap₁ : Heap M} {P : List Nat}
    (h : ∀ l, l ∉ P → heap₁.cells[l]? = heap.cells[l]?) (hc : heap₁.caps = heap.caps) :
    typOff heap₁ P = typOff heap P := by
  unfold typOff
  congr 1
  · funext l
    by_cases hl : l ∈ P
    · simp [hl]
    · simp [hl, h l hl]
  · rw [hc]

/-- A new cell, promoted or not, extends the typing off `P`. -/
theorem typOff_push {heap : Heap M} {P P₁ : List Nat} (d : Dyn M.interp)
    (hP : P₁ = heap.cells.size :: P ∨ P₁ = P) :
    (typOff heap P).Extends (typOff (heap.push d) P₁) := by
  refine ⟨fun l t h => ?_, fun k ts h => h⟩
  obtain ⟨hlP, hlt, ht⟩ := typOff_valid.mp h
  refine typOff_valid.mpr ⟨?_, by simp only [Heap.push, Array.size_push]; omega, ?_⟩
  · rcases hP with rfl | rfl
    · intro hm
      rcases List.mem_cons.mp hm with e | hm
      · omega
      · exact hlP hm
    · exact hlP
  · simp only [Heap.push, Array.getElem_push_lt hlt, ht]

/-- Writing a value of a cell's tag keeps the typing off `P`. -/
theorem typOff_set {heap : Heap M} {P : List Nat} {l : Nat} {d : Dyn M.interp}
    (hl : l < heap.cells.size) (hd : d.1 = (heap.cells[l]'hl).1) :
    typOff (heap.set l d hl) P = typOff heap P := by
  unfold typOff
  congr 1
  funext l₁
  by_cases hl₁ : l₁ ∈ P
  · simp [hl₁]
  · simp only [hl₁, ↓reduceIte, Heap.set]
    by_cases he : l = l₁
    · subst he
      simp [hd, Array.getElem?_eq_getElem hl]
    · rw [Array.getElem?_set_ne _ he]

/-- Updating a cell's contents keeps its tag, so the typing off `P`. -/
theorem typOff_modify {heap : Heap M} {P : List Nat} {l : Nat} {t : Ty}
    {g : M.interp t → M.interp t} : typOff (heap.modify l t g) P = typOff heap P := by
  unfold typOff
  congr 1
  funext l₁
  by_cases hl₁ : l₁ ∈ P
  · simp [hl₁]
  · simp only [hl₁, ↓reduceIte, Heap.modify, Array.getElem?_modify]
    by_cases he : l = l₁
    · subst he
      cases heap.cells[l]? with
      | none => simp
      | some d =>
        by_cases h : d.1 = t
        · simp [h]
        · simp [h]
    · simp [he]

/-- A new captures cell extends the typing off `P`. -/
theorem typOff_capture {heap : Heap M} {P : List Nat} (ds : List (Dyn M.interp)) :
    (typOff heap P).Extends (typOff (heap.capture ds) P) := by
  refine ⟨fun l t h => h, fun k ts h => ?_⟩
  simp only [typOff, Heap.capture, Option.map_eq_some_iff] at h ⊢
  obtain ⟨cs, hcs, rfl⟩ := h
  exact ⟨cs, by rw [Array.getElem?_push, ite_eq_right (fun he => by
    have := (Array.getElem?_eq_some_iff.mp hcs).1; omega)]; exact hcs, rfl⟩

/-- The captures cell a new closure names is valid in the heap that made it. -/
theorem typOff_capture_valid {heap : Heap M} {P : List Nat} (ds : List (Dyn M.interp)) :
    (typOff (heap.capture ds) P).CapValid (heap.caps.size + 1) :=
  .inr ⟨ds.map (·.1), by
    simp only [typOff, Heap.capture, Nat.add_sub_cancel, Array.getElem?_push_size, Option.map_some]⟩

/-! ## Facts -/


/-- A fact about a source frame and a target frame. -/
inductive Fact where
  /-- The target's value `u` is the source's value `v`. -/
  | eq (u v : Nat)
  /-- The target's value `u` is the content of the source's promoted cell `c`. -/
  | cell (u c : Nat)
  /-- The source's value `c` is a promoted cell. -/
  | prom (c : Nat)
  deriving DecidableEq, Repr

namespace Fact

/-- The source value a fact is about. -/
def src : Fact → Nat
  | eq _ v | cell _ v | prom v => v

/-- The target value a fact is about, if any. -/
def tgt? : Fact → Option Nat
  | eq u _ | cell u _ => some u
  | prom _ => none

/-- The promoted cell a fact is about, if any. -/
def prom? : Fact → Option Nat
  | cell _ c | prom c => some c
  | eq .. => none

/-- Whether the fact is a content of the cell `c`. -/
def isCellOf (c : Nat) : Fact → Bool
  | cell _ c₁ => c₁ == c
  | _ => false

end Fact

/-- The facts that survive a new binding of the source's value `d`. -/
def dropSrc (d : Nat) (F : List Fact) : List Fact := F.filter (·.src != d)

/-- The facts that survive a new binding of the target's value `d`. -/
def dropTgt (d : Nat) (F : List Fact) : List Fact := F.filter (·.tgt? != some d)

/-- The facts that survive a write of the source's cell `c`. -/
def dropCell (c : Nat) (F : List Fact) : List Fact := F.filter (!·.isCellOf c)

/-- The facts after an instruction that binds `d` in both frames. -/
def after (d : Nat) (F : List Fact) : List Fact := .eq d d :: dropTgt d (dropSrc d F)

/-- What survives a new binding of the source's `d`. -/
theorem mem_dropSrc {d : Nat} {F : List Fact} {φ : Fact} : φ ∈ dropSrc d F ↔ φ ∈ F ∧ φ.src ≠ d := by
  simp [dropSrc]

/-- What survives a new binding of the target's `d`. -/
theorem mem_dropTgt {d : Nat} {F : List Fact} {φ : Fact} :
    φ ∈ dropTgt d F ↔ φ ∈ F ∧ φ.tgt? ≠ some d := by
  simp [dropTgt]

/-- What survives a write of the source's cell `c`. -/
theorem mem_dropCell {c : Nat} {F : List Fact} {φ : Fact} :
    φ ∈ dropCell c F ↔ φ ∈ F ∧ φ.isCellOf c = false := by
  simp [dropCell]

/-- The source's value `c` is a ref to location `l`. -/
def RefAt (env : Array (Dyn M.interp)) (c l : Nat) : Prop :=
  ∃ t x, env[c]? = some ⟨Ty.ref t, x⟩ ∧ M.locOf x = l

/-- A ref is at one location. -/
theorem RefAt.unique {env : Array (Dyn M.interp)} {c l l₁ : Nat} (h : RefAt env c l)
    (h₁ : RefAt env c l₁) : l = l₁ := by
  obtain ⟨t, x, he, rfl⟩ := h
  obtain ⟨t₁, x₁, he₁, rfl⟩ := h₁
  rw [he] at he₁
  cases he₁
  rfl

variable (A : Accounts M)

/-- What a fact says, with the accounts `A`, the promoted locations `P`, the source's store
`env` and heap `heap`, and the target's store `env₁`.  A value an `eq` fact names is valid off
`P`, so it holds no promoted cell: a cell it names is not promoted. -/
def Fact.Holds (P : List Nat) (env env₁ : Array (Dyn M.interp)) (heap : Heap M) : Fact → Prop
  | eq u v => ∃ d, env[v]? = some d ∧ env₁[u]? = some d ∧ A.DynOK (typOff heap P) d
  | cell u c => ∃ l d, RefAt env c l ∧ l ∈ P ∧ heap.cells[l]? = some d ∧ env₁[u]? = some d
  | prom c => ∃ l, RefAt env c l ∧ l ∈ P ∧ l < heap.cells.size

/-- The facts `F` hold, and distinct promoted cells among them are at distinct locations. -/
structure Sound (P : List Nat) (F : List Fact) (env env₁ : Array (Dyn M.interp)) (heap : Heap M) :
    Prop where
  holds : ∀ φ ∈ F, φ.Holds A P env env₁ heap
  distinct : ∀ φ ∈ F, ∀ ψ ∈ F, ∀ c c₁ l, φ.prom? = some c → ψ.prom? = some c₁ → c ≠ c₁ →
    RefAt env c l → ¬ RefAt env c₁ l

/-- The source's heap `heap` and the target's `heap₁` agree off the promoted locations `P`, which
are locations of the heap, and have the same cells' count and captures. -/
structure HeapRel (P : List Nat) (heap heap₁ : Heap M) : Prop where
  size : heap₁.cells.size = heap.cells.size
  agree : ∀ l, l ∉ P → heap₁.cells[l]? = heap.cells[l]?
  bound : ∀ l ∈ P, l < heap.cells.size
  caps : heap₁.caps = heap.caps

/-- Everything the source's heap holds is valid off `P`: each cell's value, promoted or not, and
each captured value. -/
structure HeapInv (P : List Nat) (heap : Heap M) : Prop where
  cells : ∀ (l : Nat) (d : Dyn M.interp), heap.cells[l]? = some d → A.DynOK (typOff heap P) d
  caps : ∀ (k : Nat) (ds : List (Dyn M.interp)), heap.caps[k]? = some ds →
    ∀ d ∈ ds, A.DynOK (typOff heap P) d

variable {A}

/-- A fact still holds when what it reads is unchanged, the heap grows, the promoted locations
grow, and the typing off them extends. -/
theorem Fact.Holds.congr {P P₂ : List Nat} {env env₂ env₁ env₃ : Array (Dyn M.interp)}
    {heap heap₂ : Heap M} {φ : Fact} (h : φ.Holds A P env env₁ heap)
    (hs : env₂[φ.src]? = env[φ.src]?) (ht : ∀ u, φ.tgt? = some u → env₃[u]? = env₁[u]?)
    (hsz : heap.cells.size ≤ heap₂.cells.size) (hP : ∀ l ∈ P, l ∈ P₂)
    (hT : (typOff heap P).Extends (typOff heap₂ P₂))
    (hc : ∀ u c l, φ = .cell u c → RefAt env c l → heap₂.cells[l]? = heap.cells[l]?) :
    φ.Holds A P₂ env₂ env₃ heap₂ := by
  have hr : ∀ l, RefAt env φ.src l → RefAt env₂ φ.src l := fun l ⟨t, x, he, hl⟩ =>
    ⟨t, x, hs.trans he, hl⟩
  cases φ with
  | eq u v =>
    obtain ⟨d, h₁, h₂, h₃⟩ := h
    exact ⟨d, hs.trans h₁, (ht u rfl).trans h₂, Typing.AllValid.mono hT h₃⟩
  | cell u c =>
    obtain ⟨l, d, h₁, h₂, h₃, h₄⟩ := h
    exact ⟨l, d, hr l h₁, hP l h₂, (hc u c l rfl h₁).trans h₃, (ht u rfl).trans h₄⟩
  | prom c =>
    obtain ⟨l, h₁, h₂, h₃⟩ := h
    exact ⟨l, hr l h₁, hP l h₂, Nat.lt_of_lt_of_le h₃ hsz⟩

/-- The location of a promoted cell that a fact mentions is a location of the heap. -/
theorem Fact.Holds.prom_lt {P : List Nat} {env env₁ : Array (Dyn M.interp)} {heap : Heap M}
    {φ : Fact} {c l : Nat} (h : φ.Holds A P env env₁ heap) (hc : φ.prom? = some c)
    (hl : RefAt env c l) : l < heap.cells.size ∧ l ∈ P := by
  cases φ with
  | cell u c₁ =>
    cases hc
    obtain ⟨l₁, d, h₁, h₂, h₃, -⟩ := h
    obtain rfl := h₁.unique hl
    exact ⟨(Array.getElem?_eq_some_iff.mp h₃).1, h₂⟩
  | prom c₁ =>
    cases hc
    obtain ⟨l₁, h₁, h₂, h₃⟩ := h
    obtain rfl := h₁.unique hl
    exact ⟨h₃, h₂⟩
  | eq _ _ => exact nomatch hc

/-- A fact's promoted cell is the source value it is about. -/
theorem Fact.src_of_prom? : ∀ {φ : Fact} {c : Nat}, φ.prom? = some c → φ.src = c
  | .cell _ _, _, rfl => rfl
  | .prom _, _, rfl => rfl

/-- Facts that are among sound facts, and whose reads are unchanged, are sound. -/
theorem Sound.congr {P P₂ : List Nat} {F F₂ : List Fact}
    {env env₂ env₁ env₃ : Array (Dyn M.interp)} {heap heap₂ : Heap M}
    (h : Sound A P F env env₁ heap) (hF : ∀ φ ∈ F₂, φ ∈ F)
    (hs : ∀ φ ∈ F₂, env₂[φ.src]? = env[φ.src]?)
    (ht : ∀ φ ∈ F₂, ∀ u, φ.tgt? = some u → env₃[u]? = env₁[u]?)
    (hsz : heap.cells.size ≤ heap₂.cells.size) (hP : ∀ l ∈ P, l ∈ P₂)
    (hT : (typOff heap P).Extends (typOff heap₂ P₂))
    (hc : ∀ φ ∈ F₂, ∀ u c l, φ = .cell u c → RefAt env c l → heap₂.cells[l]? = heap.cells[l]?) :
    Sound A P₂ F₂ env₂ env₃ heap₂ where
  holds φ hφ := (h.holds φ (hF φ hφ)).congr (hs φ hφ) (ht φ hφ) hsz hP hT (hc φ hφ)
  distinct φ hφ ψ hψ c c₁ l hc₀ hc₁ hne hl hl₁ := by
    have e₀ := hs φ hφ
    have e₁ := hs ψ hψ
    rw [Fact.src_of_prom? hc₀] at e₀
    rw [Fact.src_of_prom? hc₁] at e₁
    obtain ⟨t, x, he, hx⟩ := hl
    obtain ⟨t₁, x₁, he₁, hx₁⟩ := hl₁
    exact h.distinct φ (hF φ hφ) ψ (hF ψ hψ) c c₁ l hc₀ hc₁ hne ⟨t, x, e₀ ▸ he, hx⟩
      ⟨t₁, x₁, e₁ ▸ he₁, hx₁⟩

/-- A sound list's sublist is sound. -/
theorem Sound.sub {P : List Nat} {F F₁ : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) (hF : ∀ φ ∈ F₁, φ ∈ F) :
    Sound A P F₁ env env₁ heap :=
  h.congr hF (fun _ _ => rfl) (fun _ _ _ _ => rfl) (Nat.le_refl _) (fun _ h => h)
    (Typing.Extends.refl _) (fun _ _ _ _ _ _ _ => rfl)

/-- Adding a fact that holds and promotes no cell keeps a list sound. -/
theorem Sound.cons {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} {φ : Fact} (h : Sound A P F env env₁ heap) (hφ : φ.Holds A P env env₁ heap)
    (hp : φ.prom? = none) : Sound A P (φ :: F) env env₁ heap where
  holds ψ hψ := by
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact h.holds ψ hψ
  distinct ψ hψ χ hχ c c₁ l h₀ h₁ := by
    rcases List.mem_cons.mp hψ with rfl | hψ
    · rw [hp] at h₀; exact nomatch h₀
    rcases List.mem_cons.mp hχ with rfl | hχ
    · rw [hp] at h₁; exact nomatch h₁
    exact h.distinct ψ hψ χ hχ c c₁ l h₀ h₁

/-- Binding the source's value `d` and the target's value `d` to the same valid value, with the
heap unchanged, keeps the facts that do not mention them, and adds `eq d d`. -/
theorem Sound.bind {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)} {heap : Heap M}
    (h : Sound A P F env env₁ heap) {d : Nat} (x : Dyn M.interp)
    (hx : A.DynOK (typOff heap P) x) (hd : d < env.size)
    (hd₁ : d < env₁.size) : Sound A P (after d F) (env.set d x hd) (env₁.set d x hd₁) heap := by
  have h₀ : Sound A P (dropTgt d (dropSrc d F)) (env.set d x hd) (env₁.set d x hd₁) heap := by
    refine h.congr (fun φ hφ => (mem_dropSrc.mp (mem_dropTgt.mp hφ).1).1) (fun φ hφ => ?_)
      (fun φ hφ u hu => ?_) (Nat.le_refl _) (fun _ h => h) (Typing.Extends.refl _)
      (fun _ _ _ _ _ _ _ => rfl)
    · exact Array.getElem?_set_ne _ (Ne.symm (mem_dropSrc.mp (mem_dropTgt.mp hφ).1).2)
    · refine Array.getElem?_set_ne _ fun he => (mem_dropTgt.mp hφ).2 ?_
      rw [hu, he]
  refine h₀.cons ⟨x, ?_, ?_, hx⟩ rfl
  · simp
  · simp

/-- The heap relation, with a heap that grows by the same cell in both. -/
theorem HeapRel.push {P : List Nat} {heap heap₁ : Heap M} (h : HeapRel P heap heap₁)
    (x : Dyn M.interp) : HeapRel P (heap.push x) (heap₁.push x) where
  size := by simp [Heap.push, h.size]
  agree l hl := by
    simp only [Heap.push, Array.getElem?_push, h.size, h.agree l hl]
  bound l hl := by simp only [Heap.push, Array.size_push]; exact Nat.lt_succ_of_lt (h.bound l hl)
  caps := h.caps

end

end Strata.Dyn.RefToRegSound
