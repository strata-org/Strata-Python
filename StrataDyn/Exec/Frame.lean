/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Trace
public import StrataDyn.Exec.Run
public import StrataDyn.Exec.CertModel

set_option autoImplicit false

/-!
# Reachability, and the frame theorem

A run of a certified model reaches the heap only through refs and closures it holds.  So the
cells that nothing it holds reaches are left alone.  This file says so for runs that do not end
as well as for those that do.

* `Reachable A heap roots p`: the location `p` is reached from the locations `roots`, through
  the contents of the cells and the captures cells reached, as the accounts `A` say where a
  value's refs are.  `ReachesCell` forgets a cell's tag.  The lemmas say how a change of the heap
  changes what is reached: a new cell is reached only through a ref to it (`reachable_push`) and
  keeps what was reached (`Reachable.push`); a write, an update or a new captures cell adds only
  what the value written holds (`reachable_update`, `reachable_set`, `reachable_modify`,
  `reachable_capture`); heaps that agree on what is reached reach alike (`Reachable.of_agree`);
  and reachability is monotone in its roots and transitive (`Reachable.mono`,
  `Reachable.trans`).
* `reachTyping A heap roots`: the typing of the cells and captures cells reached, at their
  contents' tags.  When every ref reached names a cell of its tag (`WellTagged`), it types the
  heap, everything it types holds only what it types (`HeapOK`), and every root is valid in it.
  Roots valid in any typing of the heap are well tagged (`Accounts.HeapOK.wellTagged`).
* `Inv A P heap₀ T s`: the invariant of a run.  The typing `T` types the heap, misses the
  locations `P`, and every value the state holds is valid in it: the frames' stores,
  the world, the pending transition's value, tree or state, and each paused rule resumes on
  valid answers.  Every frame runs certified code.  And the cells at `P` hold what they held in
  `heap₀`, which the heap extends.
* `step_inv`: a step of a module with certified rules keeps the invariant, at an extension of
  the typing.  `inv_always` reads it over every run.
* **The frame theorem**, `frame`: from a state where the invariant holds, at every configuration of
  the run, ended or not, the cells at `P` are unchanged, and the heap only grows, so every cell the
  run allocates is not at `P` (`frame_fresh`).  `frame_startCore` starts it from a function's entry
  on arguments from which, with the world, no location of `P` is reachable.

A proof about a run that writes some cells itself, such as a simulation, uses the parts of the
invariant on its own: `HeapOK` at a typing that leaves those cells out, and `HeapFrame`, a change
of the heap at cells valid in that typing, which keeps every other cell.  The generic lemmas of
such proofs are here as well: payloads as lists, valid operands (`Accounts.FnOK.applyFn`),
`AgainOK`, `ResumeOK` and the run invariant's facts about `refNew`, `refSet` and `callCode`.
-/

namespace Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-! ## Reachability -/

section
variable (A : Accounts M) (heap : Heap M) (roots : List Loc)

/-- **Reachability.** The location `p` is reached from `roots` in `heap`: it is a root, or one of
the refs held by the contents of a cell reached, or by what a captures cell reached holds.  A
cell is reached whatever the tag its ref gives it. -/
inductive Reachable : Loc → Prop where
  | root {p : Loc} : p ∈ roots → Reachable p
  | cell {l : Nat} {t : Ty} {d : Dyn M.interp} {p : Loc} : Reachable (.cell l t) →
      heap.cells[l]? = some d → p ∈ A.acct d.1 d.2 → Reachable p
  | caps {k : Nat} {ds : List (Dyn M.interp)} {d : Dyn M.interp} {p : Loc} : Reachable (.caps k) →
      heap.captures? k = some ds → d ∈ ds → p ∈ A.acct d.1 d.2 → Reachable p

/-- Location `l`'s cell is reached from `roots`, at some tag. -/
def ReachesCell (l : Nat) : Prop := ∃ t, Reachable A heap roots (.cell l t)

/-- Every ref reached names a cell of the heap that holds a value of its tag, and every closure
reached names a captures cell of the heap. -/
structure WellTagged : Prop where
  cell : ∀ l t, Reachable A heap roots (.cell l t) →
    ∃ h : l < heap.cells.size, (heap.cells[l]'h).1 = t
  caps : ∀ k, Reachable A heap roots (.caps k) → ∃ ds, heap.captures? k = some ds

open Classical in
/-- **The typing of what is reached**: each cell reached, at its contents' tag, and each
captures cell reached, at its values' tags. -/
noncomputable def reachTyping : Typing where
  cell l := if ReachesCell A heap roots l then (heap.cells[l]?).map (·.1) else none
  caps k := if Reachable A heap roots (.caps (k + 1)) then (heap.caps[k]?).map (·.map (·.1))
    else none

end

section
variable {A : Accounts M} {heap heap₁ : Heap M} {roots roots₁ : List Loc}

/-- **Monotonicity in the roots.** More roots reach more. -/
theorem Reachable.mono (hr : ∀ p ∈ roots, p ∈ roots₁) {p : Loc}
    (h : Reachable A heap roots p) : Reachable A heap roots₁ p := by
  induction h with
  | root hp => exact .root (hr _ hp)
  | cell _ hd hp ih => exact .cell ih hd hp
  | caps _ hd hm hp ih => exact .caps ih hd hm hp

/-- **Transitivity.** What is reached from roots that are themselves reached is reached. -/
theorem Reachable.trans (hr : ∀ p ∈ roots₁, Reachable A heap roots p) {p : Loc}
    (h : Reachable A heap roots₁ p) : Reachable A heap roots p := by
  induction h with
  | root hp => exact hr _ hp
  | cell _ hd hp ih => exact .cell ih hd hp
  | caps _ hd hm hp ih => exact .caps ih hd hm hp

/-- **Heaps that agree on what is reached reach alike.** If every cell and captures cell that
`heap₁` reaches from `roots` holds in `heap` what it holds in `heap₁`, then `heap` reaches it
too. -/
theorem Reachable.of_agree
    (hc : ∀ l t, Reachable A heap₁ roots (.cell l t) → heap₁.cells[l]? = heap.cells[l]?)
    (hk : ∀ k, Reachable A heap₁ roots (.caps k) → heap₁.captures? k = heap.captures? k)
    {p : Loc} (h : Reachable A heap₁ roots p) : Reachable A heap roots p := by
  induction h with
  | root hp => exact .root hp
  | cell hr hd hp ih => exact .cell ih ((hc _ _ hr).symm.trans hd) hp
  | caps hr hd hm hp ih => exact .caps ih ((hk _ hr).symm.trans hd) hm hp

/-- A new cell's contents are reached only through a ref to the new location. -/
theorem reachable_push (d : Dyn M.interp)
    (hn : ∀ t, ¬ Reachable A heap roots (.cell heap.cells.size t)) {p : Loc}
    (h : Reachable A (heap.push d) roots p) : Reachable A heap roots p := by
  induction h with
  | root hp => exact .root hp
  | @cell l t d₁ _ _ hd hp ih =>
    refine .cell ih ?_ hp
    have hl : l ≠ heap.cells.size := fun e => hn t (e ▸ ih)
    simp only [Heap.push, Array.getElem?_push, hl, ↓reduceIte] at hd
    exact hd
  | caps _ hd hm hp ih => exact .caps ih hd hm hp

/-- The old heap's reach is kept by a new cell. -/
theorem Reachable.push (d : Dyn M.interp) {p : Loc} (h : Reachable A heap roots p) :
    Reachable A (heap.push d) roots p := by
  induction h with
  | root hp => exact .root hp
  | @cell l _ _ _ _ hd hp ih =>
    refine .cell ih ?_ hp
    simp only [Heap.push, Array.getElem?_push]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.ne_of_lt (Array.getElem?_eq_some_iff.mp hd).1))]
    exact hd
  | caps _ hd hm hp ih => exact .caps ih hd hm hp

/-- The refs held by the contents of location `l`, if it is a cell of the heap. -/
def cellRefs (A : Accounts M) (heap : Heap M) (l : Nat) : List Loc :=
  match heap.cells[l]? with
  | some d => A.acct d.1 d.2
  | none => []

/-- **A change of one cell adds only what it writes.**  If `heap₁` is `heap` but at location
`l`, with the same captures cells, what `heap₁` reaches from `roots` is reached in `heap` from
`roots` and the refs of `heap₁`'s contents at `l`. -/
theorem reachable_update {l : Nat} (hc : ∀ l₁, l₁ ≠ l → heap₁.cells[l₁]? = heap.cells[l₁]?)
    (hk : heap₁.caps = heap.caps) {p : Loc} (h : Reachable A heap₁ roots p) :
    Reachable A heap (roots ++ cellRefs A heap₁ l) p := by
  induction h with
  | root hp => exact .root (List.mem_append_left _ hp)
  | @cell l₁ _ d₁ _ _ hd hp ih =>
    by_cases he : l₁ = l
    · subst he
      refine .root (List.mem_append_right _ ?_)
      unfold cellRefs
      rw [hd]
      exact hp
    · rw [hc l₁ he] at hd
      exact .cell ih hd hp
  | caps _ hd hm hp ih =>
    refine .caps ih ?_ hm hp
    unfold Heap.captures? at hd ⊢
    rw [← hk]
    exact hd

/-- **A write adds only what it writes.**  After writing `d` at location `l`, what is reached
from `roots` is reached before from `roots` and `d`'s refs. -/
theorem reachable_set {l : Nat} {d : Dyn M.interp} (hl : l < heap.cells.size) {p : Loc}
    (h : Reachable A (heap.set l d hl) roots p) :
    Reachable A heap (roots ++ A.acct d.1 d.2) p := by
  have h₁ := reachable_update (heap := heap) (heap₁ := heap.set l d hl) (l := l)
    (fun l₁ he => by simp only [Heap.set]; exact Array.getElem?_set_ne _ (Ne.symm he)) rfl h
  unfold cellRefs at h₁
  simp only [Heap.set, Array.getElem?_set_self] at h₁
  exact h₁

/-- A write of a value whose refs are reached reaches nothing new. -/
theorem reachable_set_sub {l : Nat} {d : Dyn M.interp} (hl : l < heap.cells.size)
    (hd : ∀ p ∈ A.acct d.1 d.2, Reachable A heap roots p) {p : Loc}
    (h : Reachable A (heap.set l d hl) roots p) : Reachable A heap roots p :=
  Reachable.trans (fun q hq => (List.mem_append.mp hq).elim (fun h => .root h) (hd q))
    (reachable_set hl h)

/-- **An update adds only what it writes**: what is reached after updating location `l` is
reached before from `roots` and the refs of the value written. -/
theorem reachable_modify {l : Nat} {t : Ty} {g : M.interp t → M.interp t} {p : Loc}
    (h : Reachable A (heap.modify l t g) roots p) :
    Reachable A heap (roots ++ cellRefs A (heap.modify l t g) l) p :=
  reachable_update (heap := heap) (heap₁ := heap.modify l t g) (l := l) (fun l₁ he => by
    simp only [Heap.modify, Array.getElem?_modify]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm he))]) rfl h

/-- **A new captures cell adds only what it captures.** -/
theorem reachable_capture (ds : List (Dyn M.interp)) {p : Loc}
    (h : Reachable A (heap.capture ds) roots p) :
    Reachable A heap (roots ++ ds.flatMap fun d => A.acct d.1 d.2) p := by
  induction h with
  | root hp => exact .root (List.mem_append_left _ hp)
  | cell _ hd hp ih => exact .cell ih hd hp
  | @caps k ds₁ d _ _ hd hm hp ih =>
    unfold Heap.captures? at hd
    split at hd
    · cases hd; exact nomatch hm
    · simp only [Heap.capture, Array.getElem?_push] at hd
      split at hd
      · cases hd
        exact .root (List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hm, hp⟩))
      · refine .caps ih ?_ hm hp
        unfold Heap.captures?
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by assumption))]
        exact hd

end

/-! ## The typing of what is reached -/

/-- **A typing of the heap whose contents stay inside it**: each cell of `T` is a cell of
`heap` at its contents' tag, and its contents are valid in `T`; each captures cell of `T` is
one of `heap`, and what it holds is valid in `T`. -/
structure Accounts.HeapOK (A : Accounts M) (T : Typing) (heap : Heap M) : Prop where
  cell : ∀ l t, T.cell l = some t →
    ∃ h : l < heap.cells.size, (heap.cells[l]'h).1 = t ∧ A.DynOK T (heap.cells[l]'h)
  caps : ∀ k ts, T.caps k = some ts → ∃ ds, heap.caps[k]? = some ds ∧ ∀ d ∈ ds, A.DynOK T d

section
variable {A : Accounts M} {heap : Heap M} {roots : List Loc}

/-- A cell is in the typing of what is reached exactly when it is reached and is a cell of the
heap, at its contents' tag. -/
theorem reachTyping_cell {l : Nat} {t : Ty} :
    (reachTyping A heap roots).cell l = some t ↔
      ReachesCell A heap roots l ∧ ∃ h : l < heap.cells.size, (heap.cells[l]'h).1 = t := by
  unfold reachTyping
  by_cases hr : ReachesCell A heap roots l
  · simp only [hr, ↓reduceIte, true_and, Option.map_eq_some_iff, Array.getElem?_eq_some_iff]
    exact ⟨fun ⟨_, ⟨h, rfl⟩, ht⟩ => ⟨h, ht⟩, fun ⟨h, ht⟩ => ⟨_, ⟨h, rfl⟩, ht⟩⟩
  · simp only [hr, ↓reduceIte, reduceCtorEq, false_and]

/-- A captures cell in the typing of what is reached is reached, and is one of the heap's. -/
theorem reachTyping_caps {k : Nat} {ts : List Ty} (h : (reachTyping A heap roots).caps k = some ts) :
    Reachable A heap roots (.caps (k + 1)) ∧ ∃ ds, heap.caps[k]? = some ds := by
  unfold reachTyping at h
  by_cases hr : Reachable A heap roots (.caps (k + 1))
  · simp only [hr, ↓reduceIte, Option.map_eq_some_iff] at h
    obtain ⟨ds, hds, -⟩ := h
    exact ⟨hr, ds, hds⟩
  · simp only [hr, ↓reduceIte, reduceCtorEq] at h

/-- **Everything reached is valid** in the typing of what is reached, when every ref reached
names a cell of its tag. -/
theorem WellTagged.valid (hw : WellTagged A heap roots) {p : Loc} (h : Reachable A heap roots p) :
    (reachTyping A heap roots).LocValid p := by
  cases p with
  | cell l t => exact reachTyping_cell.mpr ⟨⟨t, h⟩, hw.cell l t h⟩
  | caps k =>
    by_cases hk : k = 0
    · exact .inl hk
    · obtain ⟨ds, hds⟩ := hw.caps k h
      unfold Heap.captures? at hds
      rw [ite_eq_right_of_eq_false _ _ (eq_false hk)] at hds
      refine .inr ⟨ds.map (·.1), ?_⟩
      unfold reachTyping
      have e : k - 1 + 1 = k := by omega
      simp only [e, h, ↓reduceIte, hds, Option.map_some]

/-- **The roots are valid** in the typing of what is reached. -/
theorem WellTagged.rootsValid (hw : WellTagged A heap roots) : (reachTyping A heap roots).AllValid roots :=
  fun _ hp => hw.valid (.root hp)

/-- **The typing of what is reached types the heap, and what it types holds only what it types.** -/
theorem WellTagged.heapOK (hw : WellTagged A heap roots) : A.HeapOK (reachTyping A heap roots) heap where
  cell l t h := by
    obtain ⟨⟨t₁, hr⟩, hl, ht⟩ := reachTyping_cell.mp h
    exact ⟨hl, ht, fun p hp => hw.valid (.cell hr (Array.getElem?_eq_getElem hl) hp)⟩
  caps k ts h := by
    obtain ⟨hr, ds, hds⟩ := reachTyping_caps h
    refine ⟨ds, hds, fun d hd p hp => hw.valid (.caps hr ?_ hd hp)⟩
    unfold Heap.captures?
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.succ_ne_zero k))]
    exact hds

/-- A cell that is not reached is not in the typing of what is reached. -/
theorem reachTyping_none {l : Nat} (h : ¬ ReachesCell A heap roots l) :
    (reachTyping A heap roots).cell l = none := by
  unfold reachTyping
  simp only [h, ↓reduceIte]

end

/-! ## Valid values in stores and payloads -/

/-- A payload's values, each with its tag. -/
def Args.toList {I : Ty → Type} : {ts : List Ty} → Args I ts → List (Dyn I)
  | _, .nil => []
  | _, .cons x xs => ⟨_, x⟩ :: Args.toList xs

/-- A payload has a value per tag. -/
theorem Args.length_toList {I : Ty → Type} : ∀ {ts : List Ty} (xs : Args I ts),
    (Args.toList xs).length = ts.length
  | _, .nil => rfl
  | _, .cons _ xs => congrArg (· + 1) (Args.length_toList xs)

namespace Accounts

variable (A : Accounts M)

/-- Every value of the store `env` is valid in `T`. -/
def EnvOK (T : Typing) (env : Array (Dyn M.interp)) : Prop := ∀ d ∈ env, A.DynOK T d

variable {A}

/-- A valid payload's values are valid. -/
theorem argsOK_toList {S : Typing} : ∀ {ts : List Ty} {xs : Args M.interp ts},
    A.ArgsOK S xs → ∀ d ∈ Args.toList xs, A.DynOK S d
  | _, .nil, _, _, hd => nomatch hd
  | _, .cons _ _, h, _, hd => by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h.1
    · exact argsOK_toList h.2 _ hd

/-- A valid value, at its tag, is valid. -/
theorem dynOK_at {S : Typing} {v : Dyn M.interp} (hv : A.DynOK S v) {t : Ty} (h : v.1 = t) :
    A.ValOK S t (v.at h) := by
  obtain ⟨t₀, x⟩ := v
  cases h
  exact hv

/-- The value of a slot at its tag is valid when the slot's value is. -/
theorem valOK_getT {S : Typing} {env : Array (Dyn M.interp)} {v : Nat} {t : Ty}
    (h : HasTy env v t) (hd : A.DynOK S (env[v]'h.1)) : A.ValOK S t (getT env v t h) := by
  have e := sigma_cast (env[v]'h.1) (h.2 h.1)
  unfold Accounts.DynOK at hd
  rw [← e] at hd
  exact hd

/-- The value the machine reads from a cell is valid when the cell's contents are. -/
theorem valOK_valueAt {S : Typing} {heap : Heap M} {l : Nat} {t : Ty}
    (hl : l < heap.cells.size) (ht : (heap.cells[l]'hl).1 = t) (hd : A.DynOK S (heap.cells[l]'hl)) :
    A.ValOK S t (heap.valueAt hl ht) := by
  have e := sigma_cast (heap.cells[l]'hl) ht
  unfold Accounts.DynOK at hd
  rw [← e] at hd
  exact hd

/-- **Operands that are valid.** `P` holds of `f` applied to operands whose values are valid in
`S`, when `f` is `FnOK` at `S`. -/
theorem FnOK.applyFn {S : Typing} {R : Type} {P : R → Prop} {env : Array (Dyn M.interp)} :
    ∀ {ts : List Ty} {f : Fn M.interp R ts} {vs : List Nat} (h : Typed env vs ts),
      (∀ v ∈ vs, ∀ d, env[v]? = some d → A.DynOK S d) → A.FnOK S P ts f →
      P (Exec.applyFn env ts f vs h)
  | [], _, [], _, _, hf => hf
  | t₀ :: t₁ :: ts, f, v₀ :: v₁ :: vs, h, hv, hf => by
    have h₀ := hv v₀ List.mem_cons_self _ (Array.getElem?_eq_getElem h.1.1)
    have h₁ := hv v₁ (List.mem_cons_of_mem _ List.mem_cons_self) _
      (Array.getElem?_eq_getElem h.2.1.1)
    exact FnOK.applyFn h.2.2 (fun w hw => hv w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hw)))
      (hf _ (valOK_getT h.1 h₀) _ (valOK_getT h.2.1 h₁))
  | [_], _, [v], h, hv, hf => by
    have h₀ := hv v List.mem_cons_self _ (Array.getElem?_eq_getElem h.1.1)
    exact hf _ (valOK_getT h.1 h₀)
  | [_], _, _ :: _ :: _, h, _, _ => h.2.elim
  | _ :: _ :: _, _, [_], h, _, _ => h.2.elim
  | [], _, _ :: _, h, _, _ => h.elim
  | _ :: _, _, [], h, _, _ => h.elim

/-- Operands of a valid store are valid. -/
theorem EnvOK.applyFn {S : Typing} {R : Type} {P : R → Prop} {env : Array (Dyn M.interp)}
    (he : A.EnvOK S env) {ts : List Ty} {f : Fn M.interp R ts} {vs : List Nat}
    (h : Typed env vs ts) (hf : A.FnOK S P ts f) : P (Exec.applyFn env ts f vs h) :=
  FnOK.applyFn h (fun _ _ d hd => he d (Array.mem_of_getElem? hd)) hf

/-- A valid store stays valid in an extension. -/
theorem EnvOK.mono {S S₁ : Typing} (h : S.Extends S₁) {env : Array (Dyn M.interp)}
    (he : A.EnvOK S env) : A.EnvOK S₁ env :=
  fun d hd => Typing.AllValid.mono h (he d hd)

/-- A slot of a valid store holds a valid value. -/
theorem EnvOK.get {S : Typing} {env : Array (Dyn M.interp)} (he : A.EnvOK S env) {v : Nat}
    (h : v < env.size) : A.DynOK S (env[v]'h) :=
  he _ (Array.getElem_mem h)

/-- An operand of a valid store, at its tag, is valid. -/
theorem EnvOK.getT {S : Typing} {env : Array (Dyn M.interp)} (he : A.EnvOK S env) {v : Nat}
    {t : Ty} (h : HasTy env v t) : A.ValOK S t (getT env v t h) :=
  valOK_getT h (he.get h.1)

/-- Setting a slot of a valid store to a valid value keeps it valid. -/
theorem EnvOK.set {S : Typing} {env : Array (Dyn M.interp)} (he : A.EnvOK S env) {v : Nat}
    (h : v < env.size) {d : Dyn M.interp} (hd : A.DynOK S d) : A.EnvOK S (env.set v d h) :=
  fun d₁ hm => (Array.mem_or_eq_of_mem_set hm).elim (he d₁) fun e => e ▸ hd

/-- The values of some slots of a valid store are valid. -/
theorem EnvOK.lookupAll {S : Typing} {env : Array (Dyn M.interp)} (he : A.EnvOK S env) :
    ∀ {vs : List Nat} (h : AllBound env vs), ∀ d ∈ Exec.lookupAll env vs h, A.DynOK S d
  | [], _, _, hd => nomatch hd
  | _ :: _, h, d, hd => by
    rcases List.mem_cons.mp hd with rfl | hd
    · exact he.get h.1
    · exact EnvOK.lookupAll he h.2 d hd

/-- Binding a site's parameters to valid values keeps a valid store valid. -/
theorem EnvOK.bindSite {S : Typing} :
    ∀ {env : Array (Dyn M.interp)} {ts : List Ty} (ps : Ctx) (ds : List (Dyn M.interp))
      (xs : Args M.interp ts) (h : ∀ p ∈ ps, p.1 < env.size), A.EnvOK S env →
      (∀ d ∈ ds, A.DynOK S d) → (∀ d ∈ Args.toList xs, A.DynOK S d) →
      A.EnvOK S (Exec.bindSite env ps ds xs h)
  | _, _, [], _, _, _, he, _, _ => he
  | _, _, (_, _) :: ps, d :: ds, xs, h, he, hd, hx =>
    EnvOK.bindSite ps ds xs (fits_set h d) (he.set _ (hd d List.mem_cons_self))
      (fun d₁ hm => hd d₁ (List.mem_cons_of_mem _ hm)) hx
  | _, _, (_, _) :: ps, [], .cons _ xs, h, he, _, hx =>
    EnvOK.bindSite ps [] xs (fits_set h _) (he.set _ (hx _ List.mem_cons_self))
      (fun _ hm => nomatch hm) (fun d₁ hm => hx d₁ (List.mem_cons_of_mem _ hm))
  | _, _, (_, _) :: _, [], .nil, _, he, _, _ => he

/-- A fresh store holds the unit value only, which holds no ref. -/
theorem envOK_freshStore (S : Typing) (n : Nat) : A.EnvOK S (freshStore M n) := by
  intro d hd
  obtain ⟨-, rfl⟩ := Array.mem_replicate.mp hd
  unfold Accounts.DynOK Accounts.ValOK
  rw [A.unit]
  exact Typing.allValid_nil _

end Accounts

/-- The one value passed to a body's exit is the arguments' and the payload's. -/
theorem single_spec {r : Ty} :
    ∀ (ds : List (Dyn M.interp)) {ts : List Ty} (xs : Args M.interp ts)
      (h : ds.map (·.1) ++ ts = [r]), ds ++ Args.toList xs = [single ds xs h]
  | [_], _, .nil, _ => rfl
  | [], _, .cons _ .nil, _ => rfl
  | [], _, .nil, h => absurd h (by simp)
  | [], _, .cons _ (.cons _ _), h => absurd h (by simp)
  | [_], _, .cons _ _, h => absurd h (by simp)
  | _ :: _ :: _, _, _, h => absurd h (by simp)

/-! ## Facts of the run invariant about instructions -/

section
variable {m : LModule M} {B : Ty} {s : Core M}

/-- A `refNew`'s value has the tag of the cell's contents, by the run invariant. -/
theorem CoreOK.refNew_tag (h : CoreOK m B s) {dst : Nat} {t : Ty} {v : Nat}
    {code : List (LInsn M)} (hc : s.top.code = .refNew dst t v :: code) :
    HasTy s.top.env v t := by
  obtain ⟨Γ, r, hA, hr⟩ := h.ctx hc
  exact hA.hasTy (insnTy_refNew.mp hr).1

/-- A `callCode`'s arguments have the tags of the call, by the run invariant. -/
theorem CoreOK.callCode_args (h : CoreOK m B s) {dst : Nat} {ts : List Ty} {r : Ty} {f : Nat}
    {args : List Nat} {code : List (LInsn M)} (hc : s.top.code = .callCode dst ts r f args :: code)
    (hb : AllBound s.top.env args) : (lookupAll s.top.env args hb).map (·.1) = ts := by
  obtain ⟨Γ, r₁, hA, hr⟩ := h.ctx hc
  have := hA.lookupAll (insnTy_callCode.mp hr).2.1 hb
  rwa [List.append_nil] at this

/-- A `refSet`'s value has the tag of the cell's contents, by the run invariant. -/
theorem CoreOK.refSet_tag (h : CoreOK m B s) {dst : Nat} {t : Ty} {c v : Nat}
    {code : List (LInsn M)} (hc : s.top.code = .refSet dst t c v :: code) :
    HasTy s.top.env v t := by
  obtain ⟨Γ, r, hA, hr⟩ := h.ctx hc
  exact hA.hasTy (insnTy_refSet.mp hr).2.1

end

/-! ## Rules that run again and rules that resume -/

variable (A : Accounts M) in
/-- The rule of operation `i` respects every typing from every valid state, when it runs again
on valid operands. -/
def AgainOK (i : Inst M) : Prop :=
  ∀ S, A.FnOK S (fun k => ∀ st, A.StOK i.rerun.key S st →
    A.TreeOK (A.StOK i.rerun.key) S i.ret (k st)) i.rerun.ts i.rerun.tree

variable (A : Accounts M) in
/-- A paused rule resumes, from typing `S` or any extension, on any valid answer, with a tree
that respects the typing. -/
def ResumeOK (S : Typing) (p : Pending M) : Prop :=
  ∀ S₁, S.Extends S₁ → ∀ o : M.interp p.ret, A.ValOK S₁ p.ret o →
    A.TreeOK (A.StOK p.inst.rerun.key) S₁ p.inst.ret (p.k o)

/-- A paused rule resumes as well from an extension of the typing. -/
theorem ResumeOK.mono {A : Accounts M} {S S₁ : Typing} {p : Pending M} (h : ResumeOK A S p)
    (he : S.Extends S₁) : ResumeOK A S₁ p :=
  fun S₂ he₂ o ho => h S₂ (he.trans he₂) o ho

/-! ## How the heap changes -/

/-- **The heap changes only at cells valid in `T`**: it grows, and every other cell it had
holds what it held. -/
structure HeapFrame (T : Typing) (heap heap₁ : Heap M) : Prop where
  size : heap.cells.size ≤ heap₁.cells.size
  keep : ∀ l, l < heap.cells.size → T.cell l = none → heap₁.cells[l]? = heap.cells[l]?

namespace HeapFrame

variable {T : Typing} {heap : Heap M}

/-- Nothing changes. -/
theorem refl (T : Typing) (heap : Heap M) : HeapFrame T heap heap :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

/-- A new cell changes no cell. -/
theorem push (d : Dyn M.interp) : HeapFrame T heap (heap.push d) :=
  ⟨by simp only [Heap.push, Array.size_push]; omega, fun l hl _ => by
    simp only [Heap.push, Array.getElem?_push]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.ne_of_lt hl))]⟩

/-- A write at a cell valid in `T` changes no other cell. -/
theorem set {l : Nat} {t : Ty} (hl : l < heap.cells.size) (ht : T.cell l = some t)
    (d : Dyn M.interp) : HeapFrame T heap (heap.set l d hl) :=
  ⟨by simp only [Heap.set, Array.size_set]; omega, fun l₁ _ h₁ => by
    simp only [Heap.set]
    exact Array.getElem?_set_ne _ fun e => by rw [e] at ht; rw [ht] at h₁; exact nomatch h₁⟩

/-- An update at a cell valid in `T` changes no other cell. -/
theorem modify {l : Nat} {t : Ty} (ht : T.cell l = some t) (g : M.interp t → M.interp t) :
    HeapFrame T heap (heap.modify l t g) :=
  ⟨by simp only [Heap.modify, Array.size_modify]; omega, fun l₁ _ h₁ => by
    simp only [Heap.modify, Array.getElem?_modify]
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun e => by
      rw [e] at ht; rw [ht] at h₁; exact nomatch h₁)]⟩

/-- A new captures cell changes no cell. -/
theorem capture (ds : List (Dyn M.interp)) : HeapFrame T heap (heap.capture ds) :=
  ⟨Nat.le_refl _, fun _ _ _ => rfl⟩

end HeapFrame

/-- **The cells at `P` hold what they held in `heap₀`, and the heap extends `heap₀`.** -/
structure Kept (P : Nat → Prop) (heap₀ heap : Heap M) : Prop where
  size : heap₀.cells.size ≤ heap.cells.size
  cells : ∀ l, P l → heap.cells[l]? = heap₀.cells[l]?

/-- A heap that changes only at cells valid in a typing that misses `P` keeps `P`'s cells, when
`P` is a set of `heap₀`'s locations. -/
theorem Kept.frame {P : Nat → Prop} {heap₀ heap heap₁ : Heap M} {T : Typing}
    (hP : ∀ l, P l → l < heap₀.cells.size) (hk : Kept P heap₀ heap)
    (hav : ∀ l, P l → T.cell l = none) (hf : HeapFrame T heap heap₁) : Kept P heap₀ heap₁ :=
  ⟨Nat.le_trans hk.size hf.size, fun l hl =>
    (hf.keep l (Nat.lt_of_lt_of_le (hP l hl) hk.size) (hav l hl)).trans (hk.cells l hl)⟩

/-- Every heap keeps its own cells. -/
theorem Kept.refl (P : Nat → Prop) (heap : Heap M) : Kept P heap heap :=
  ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-! ## Typings that grow with the heap -/

/-- `T` with location `l` at tag `t`. -/
def Typing.addCell (T : Typing) (l : Nat) (t : Ty) : Typing :=
  { T with cell := fun l₁ => if l₁ = l then some t else T.cell l₁ }

/-- `T` with captures cell `k` at the tags `ts`. -/
def Typing.addCaps (T : Typing) (k : Nat) (ts : List Ty) : Typing :=
  { T with caps := fun k₁ => if k₁ = k then some ts else T.caps k₁ }

/-- Adding a location that `T` does not type extends `T`. -/
theorem Typing.extends_addCell {T : Typing} {l : Nat} (hl : T.cell l = none) (t : Ty) :
    T.Extends (T.addCell l t) :=
  ⟨fun l₁ t₁ h => by
    show (if l₁ = l then some t else T.cell l₁) = some t₁
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun e => by rw [e] at h; rw [hl] at h; exact nomatch h)]
    exact h, fun _ _ h => h⟩

/-- Adding a captures cell that `T` does not type extends `T`. -/
theorem Typing.extends_addCaps {T : Typing} {k : Nat} (hk : T.caps k = none) (ts : List Ty) :
    T.Extends (T.addCaps k ts) :=
  ⟨fun _ _ h => h, fun k₁ ts₁ h => by
    show (if k₁ = k then some ts else T.caps k₁) = some ts₁
    rw [ite_eq_right_of_eq_false _ _ (eq_false fun e => by rw [e] at h; rw [hk] at h; exact nomatch h)]
    exact h⟩

namespace Accounts.HeapOK

variable {A : Accounts M} {T : Typing} {heap : Heap M}

/-- A location of a heap typing is a location of the heap. -/
theorem lt (h : A.HeapOK T heap) {l : Nat} {t : Ty} (hl : T.cell l = some t) :
    l < heap.cells.size :=
  (h.cell l t hl).1

/-- The new location is not in a typing of the heap. -/
theorem none_size (h : A.HeapOK T heap) : T.cell heap.cells.size = none := by
  cases hc : T.cell heap.cells.size with
  | none => rfl
  | some t => exact absurd (h.lt hc) (Nat.lt_irrefl _)

/-- The new captures cell is not in a typing of the heap. -/
theorem caps_none_size (h : A.HeapOK T heap) : T.caps heap.caps.size = none := by
  cases hc : T.caps heap.caps.size with
  | none => rfl
  | some ts =>
    obtain ⟨ds, hds, -⟩ := h.caps _ ts hc
    exact absurd hds (by rw [Array.getElem?_eq_none (Nat.le_refl _)]; exact fun h => nomatch h)

/-- A cell valid in the typing holds valid contents. -/
theorem cellOK (h : A.HeapOK T heap) {l : Nat} {t : Ty} (hl : T.Valid l t) :
    ∃ h₁ : l < heap.cells.size, (heap.cells[l]'h₁).1 = t ∧ A.DynOK T (heap.cells[l]'h₁) :=
  h.cell l t hl

/-- What a valid closure captured is valid. -/
theorem captures (h : A.HeapOK T heap) {captured : Nat} (hc : T.CapValid captured)
    {caps : List (Dyn M.interp)} (hk : heap.captures? captured = some caps) :
    ∀ d ∈ caps, A.DynOK T d := by
  unfold Heap.captures? at hk
  split at hk
  · cases hk; exact fun _ hd => nomatch hd
  · rcases hc with hc | ⟨ts, hts⟩
    · contradiction
    · obtain ⟨ds, hds, hv⟩ := h.caps _ ts hts
      rw [hds] at hk
      cases hk
      exact hv

/-- What a typing of the heap makes valid reaches only what it makes valid. -/
theorem valid_of_reachable {roots : List Loc} (hH : A.HeapOK T heap) (hr : T.AllValid roots)
    {p : Loc} (h : Reachable A heap roots p) : T.LocValid p := by
  induction h with
  | root hp => exact hr _ hp
  | @cell l _ d _ _ hd hp ih =>
    obtain ⟨hl, -, hok⟩ := hH.cellOK ih
    obtain rfl : heap.cells[l]'hl = d :=
      Option.some.inj ((Array.getElem?_eq_getElem hl).symm.trans hd)
    exact hok _ hp
  | caps _ hd hm hp ih => exact hH.captures ih hd _ hm _ hp

/-- **Roots valid in a typing of the heap are well tagged**: every ref they reach names a cell of
its tag, and every closure they reach a captures cell. -/
theorem wellTagged {roots : List Loc} (hH : A.HeapOK T heap) (hr : T.AllValid roots) :
    WellTagged A heap roots where
  cell l t h :=
    let ⟨hl, ht, _⟩ := hH.cellOK (hH.valid_of_reachable hr h)
    ⟨hl, ht⟩
  caps k h := by
    unfold Heap.captures?
    rcases hH.valid_of_reachable hr h with hk | ⟨ts, hts⟩
    · exact ⟨[], by rw [ite_eq_left_iff.mpr fun h => absurd hk h]⟩
    · by_cases hk : k = 0
      · exact ⟨[], by rw [ite_eq_left_iff.mpr fun h => absurd hk h]⟩
      · obtain ⟨ds, hds, -⟩ := hH.caps _ ts hts
        exact ⟨ds, by rw [ite_eq_right_of_eq_false _ _ (eq_false hk)]; exact hds⟩

/-- A typing grows by extension when everything it typed is kept. -/
theorem mono {T₁ : Typing} {heap₁ : Heap M} (h : A.HeapOK T heap) (he : T.Extends T₁)
    (hc : ∀ l t, T₁.cell l = some t → T.cell l = some t ∧ heap₁.cells[l]? = heap.cells[l]? ∨
      ∃ h₁ : l < heap₁.cells.size, (heap₁.cells[l]'h₁).1 = t ∧ A.DynOK T₁ (heap₁.cells[l]'h₁))
    (hk : ∀ k ts, T₁.caps k = some ts → T.caps k = some ts ∧ heap₁.caps[k]? = heap.caps[k]? ∨
      ∃ ds, heap₁.caps[k]? = some ds ∧ ∀ d ∈ ds, A.DynOK T₁ d) :
    A.HeapOK T₁ heap₁ where
  cell l t hl := by
    rcases hc l t hl with ⟨h₀, he₀⟩ | h₁
    · obtain ⟨hlt, ht, hd⟩ := h.cell l t h₀
      have e : heap₁.cells[l]? = some (heap.cells[l]'hlt) := he₀.trans (Array.getElem?_eq_getElem hlt)
      obtain ⟨hlt₁, e₁⟩ := Array.getElem?_eq_some_iff.mp e
      exact ⟨hlt₁, by rw [e₁]; exact ht, by rw [e₁]; exact Typing.AllValid.mono he hd⟩
    · exact h₁
  caps k ts hk₁ := by
    rcases hk k ts hk₁ with ⟨h₀, he₀⟩ | h₁
    · obtain ⟨ds, hds, hv⟩ := h.caps k ts h₀
      exact ⟨ds, he₀.trans hds, fun d hd => Typing.AllValid.mono he (hv d hd)⟩
    · exact h₁

/-- **A new cell of a valid value** is typed at its tag. -/
theorem push (h : A.HeapOK T heap) {d : Dyn M.interp} (hd : A.DynOK T d) :
    A.HeapOK (T.addCell heap.cells.size d.1) (heap.push d) := by
  have he := Typing.extends_addCell h.none_size d.1
  refine h.mono he (fun l t hl => ?_) (fun k ts hk => .inl ⟨hk, rfl⟩)
  change (if l = heap.cells.size then some d.1 else T.cell l) = some t at hl
  by_cases e : l = heap.cells.size
  · rw [ite_eq_left_of_eq_true _ _ (eq_true e)] at hl
    cases hl
    subst e
    refine .inr ⟨by simp [Heap.push], by simp [Heap.push], ?_⟩
    simp only [Heap.push, Array.getElem_push_eq]
    exact Typing.AllValid.mono he hd
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e)] at hl
    refine .inl ⟨hl, ?_⟩
    simp only [Heap.push, Array.getElem?_push]
    rw [ite_eq_right_of_eq_false _ _ (eq_false e)]

/-- **A write of a valid value of a cell's tag** keeps the heap typed. -/
theorem set (h : A.HeapOK T heap) {l : Nat} (hl : l < heap.cells.size) {d : Dyn M.interp}
    (ht : d.1 = (heap.cells[l]'hl).1) (hd : A.DynOK T d) : A.HeapOK T (heap.set l d hl) := by
  refine h.mono (Typing.Extends.refl _) (fun l₁ t hl₁ => ?_) (fun k ts hk => .inl ⟨hk, rfl⟩)
  by_cases e : l = l₁
  · subst e
    obtain ⟨_, ht₁, -⟩ := h.cell l t hl₁
    refine .inr ⟨by simp [Heap.set]; exact hl, ?_, ?_⟩
    · simp only [Heap.set, Array.getElem_set_self]
      exact ht.trans ht₁
    · simp only [Heap.set, Array.getElem_set_self]
      exact hd
  · refine .inl ⟨hl₁, ?_⟩
    simp only [Heap.set]
    exact Array.getElem?_set_ne _ e

/-- **An update that keeps valid values valid**, at a cell of its tag, keeps the heap typed. -/
theorem modify (h : A.HeapOK T heap) {l : Nat} {t : Ty} {g : M.interp t → M.interp t}
    (hg : ∀ x, A.ValOK T t x → A.ValOK T t (g x)) : A.HeapOK T (heap.modify l t g) := by
  refine h.mono (Typing.Extends.refl _) (fun l₁ t₁ hl₁ => ?_) (fun k ts hk => .inl ⟨hk, rfl⟩)
  by_cases e : l = l₁
  · subst e
    obtain ⟨hlt, ht₁, hd⟩ := h.cell l t₁ hl₁
    have hlt₁ : l < (heap.modify l t g).cells.size := by simp [Heap.modify]; exact hlt
    refine .inr ⟨hlt₁, ?_⟩
    have e₁ : (heap.modify l t g).cells[l]'hlt₁ =
        (if h : (heap.cells[l]'hlt).1 = t then ⟨t, g (cast (congrArg M.interp h) (heap.cells[l]'hlt).2)⟩
          else heap.cells[l]'hlt) := by
      simp only [Heap.modify, Array.getElem_modify_self]
    rw [e₁]
    by_cases htt : (heap.cells[l]'hlt).1 = t
    · rw [dite_eq_left_of_eq_true (eq_true htt)]
      refine ⟨htt.symm.trans ht₁, hg _ ?_⟩
      have e₂ := sigma_cast (heap.cells[l]'hlt) htt
      unfold Accounts.DynOK at hd
      rw [← e₂] at hd
      exact hd
    · rw [dite_eq_right_of_eq_false (eq_false htt)]
      exact ⟨ht₁, hd⟩
  · refine .inl ⟨hl₁, ?_⟩
    simp only [Heap.modify, Array.getElem?_modify]
    rw [ite_eq_right_of_eq_false _ _ (eq_false e)]

/-- **A new captures cell of valid values** is typed at their tags. -/
theorem capture (h : A.HeapOK T heap) {ds : List (Dyn M.interp)} (hd : ∀ d ∈ ds, A.DynOK T d) :
    A.HeapOK (T.addCaps heap.caps.size (ds.map (·.1))) (heap.capture ds) := by
  have he := Typing.extends_addCaps h.caps_none_size (ds.map (·.1))
  refine h.mono he (fun l t hl => .inl ⟨hl, rfl⟩) (fun k ts hk => ?_)
  change (if k = heap.caps.size then some (ds.map (·.1)) else T.caps k) = some ts at hk
  by_cases e : k = heap.caps.size
  · subst e
    exact .inr ⟨ds, by simp [Heap.capture], fun d hm => Typing.AllValid.mono he (hd d hm)⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false e)] at hk
    refine .inl ⟨hk, ?_⟩
    simp only [Heap.capture, Array.getElem?_push]
    rw [ite_eq_right_of_eq_false _ _ (eq_false e)]

end Accounts.HeapOK

/-! ## The run invariant -/

namespace Accounts

variable (A : Accounts M)

/-- **A frame of a run**: its store is valid in `T`, and its body, its rest of a block and its
terminator are certified. -/
structure FrameInv (T : Typing) (f : Frame M) : Prop where
  env : A.EnvOK T f.env
  body : f.func.All A.InsnOK A.TermOK
  code : ∀ i ∈ f.code, A.InsnOK i
  term : A.TermOK f.term

/-- **A waiting frame of a run**: its frame is one, and a paused rule runs again from valid
states and resumes on valid answers. -/
def WaitInv (T : Typing) : Wait M → Prop
  | .rule f p => A.FrameInv T f ∧ AgainOK A p.inst ∧ ResumeOK A T p
  | .call f _ _ => A.FrameInv T f

/-- **A pending transition of a run**: the frame it leads to is one, a value it leaves with is
valid, and a rule's tree respects `T`, or its state is valid. -/
def ModeInv (T : Typing) (c : Core M) : Mode M → Prop
  | .exec => A.FrameInv T c.top
  | .jump to => A.FrameInv T to
  | .call g w => A.FrameInv T g ∧ A.WaitInv T w
  | .ret v => A.DynOK T v
  | .request i t => A.FrameInv T c.top ∧ AgainOK A i ∧ A.TreeOK (A.StOK i.rerun.key) T i.ret t
  | .again r => A.FrameInv T c.top ∧ AgainOK A r.inst ∧ A.StOK r.inst.rerun.key T r.st
  | .done _ => True

/-- **The frames and the data of a run**: `T` types the heap and misses `P`, the world and the
waiting frames are valid in it, and the cells at `P` hold what they held in `heap₀`. -/
structure CoreInv (P : Nat → Prop) (heap₀ : Heap M) (T : Typing) (c : Core M) : Prop where
  heap : A.HeapOK T c.heap
  avoid : ∀ l, P l → T.cell l = none
  world : T.AllValid (A.world c.world)
  conts : ∀ w ∈ c.conts, A.WaitInv T w
  kept : Kept P heap₀ c.heap

/-- **The invariant of a run** that keeps the cells at `P` as `heap₀` has them, at the typing
`T`. -/
def Inv (P : Nat → Prop) (heap₀ : Heap M) (T : Typing) (s : State M) : Prop :=
  A.CoreInv P heap₀ T s.core ∧ A.ModeInv T s.core s.mode

/-- A step keeps the invariant at an extension of `T`, or ends with the cells at `P` kept. -/
def StepInv {m : LModule M} {B : Ty} (P : Nat → Prop) (heap₀ : Heap M) (T : Typing) :
    StepR m B → Prop
  | .next _ s _ => ∃ T₁, T.Extends T₁ ∧ A.Inv P heap₀ T₁ s
  | .final _ heap _ _ => Kept P heap₀ heap

/-- Where a transfer leads is valid: a frame of the run, or a valid value. -/
def NextInv (T : Typing) : Next M → Prop
  | .frame g => A.FrameInv T g
  | .leave v => A.DynOK T v

variable {A}

/-- A frame of a run is one at an extension of the typing. -/
theorem FrameInv.mono {T T₁ : Typing} (he : T.Extends T₁) {f : Frame M} (h : A.FrameInv T f) :
    A.FrameInv T₁ f :=
  ⟨h.env.mono he, h.body, h.code, h.term⟩

/-- A waiting frame of a run is one at an extension of the typing. -/
theorem WaitInv.mono {T T₁ : Typing} (he : T.Extends T₁) : ∀ {w : Wait M}, A.WaitInv T w →
    A.WaitInv T₁ w
  | .rule _ _, ⟨hf, hag, hr⟩ => ⟨hf.mono he, hag, hr.mono he⟩
  | .call _ _ _, hf => FrameInv.mono he hf

/-- A step that keeps the invariant at an extension of an extension keeps it at an extension. -/
theorem StepInv.trans {m : LModule M} {B : Ty} {P : Nat → Prop} {heap₀ : Heap M}
    {T T₁ : Typing} (he : T.Extends T₁) : ∀ {r : StepR m B}, A.StepInv P heap₀ T₁ r →
      A.StepInv P heap₀ T r
  | .next _ _ _, ⟨T₂, he₂, h⟩ => ⟨T₂, he.trans he₂, h⟩
  | .final _ _ _ _, h => h

/-- The frame that runs a block of a certified body, in a valid store with valid parameters, is
a frame of the run. -/
theorem FrameInv.entry {T : Typing} {g : LBody M} {b : LBlock M} (hg : g.All A.InsnOK A.TermOK)
    (hb : b ∈ g.blocks) {env : Array (Dyn M.interp)} (he : A.EnvOK T env) {ts : List Ty}
    {ds : List (Dyn M.interp)} (hds : ∀ d ∈ ds, A.DynOK T d) {xs : Args M.interp ts}
    (hxs : ∀ d ∈ Args.toList xs, A.DynOK T d) {hle : g.slots ≤ env.size} {hp : ParamsFit g b} :
    A.FrameInv T (Frame.entry g b env ds xs hle hp) :=
  ⟨EnvOK.bindSite _ _ _ _ he hds hxs, hg, (hg b hb).1, (hg b hb).2⟩

/-- A region's frame, on valid arguments, in a frame of the run, is a frame of the run. -/
theorem FrameInv.regionStart {m : LModule M} (hR : m.RulesOK A) {T : Typing} {f : Frame M}
    (hf : A.FrameInv T f) {k : Nat} {hk : k < m.regions.size}
    {hb : 0 < (m.regions[k]'hk).blocks.size} {hs : (m.regions[k]'hk).slots ≤ f.func.slots}
    {hp : ParamsFit (m.regions[k]'hk) ((m.regions[k]'hk).blocks[0]'hb)} {ts : List Ty}
    (args : Args M.interp ts) (hargs : ∀ d ∈ Args.toList args, A.DynOK T d) :
    A.FrameInv T (Exec.regionStart m f k hk hb hs hp args) := by
  unfold Exec.regionStart
  exact FrameInv.entry (hR.2 _ (Array.getElem_mem hk)) (Array.getElem_mem hb) hf.env
    (fun _ hd => absurd hd List.not_mem_nil) hargs

/-- A function's frame, on valid arguments, is a frame of the run. -/
theorem FrameInv.callFrame {m : LModule M} (hR : m.RulesOK A) (hwf : WF m) {T : Typing}
    {i : Nat} {hi : i < m.funcs.size} {ds : List (Dyn M.interp)} (hds : ∀ d ∈ ds, A.DynOK T d)
    {ts : List Ty} (xs : Args M.interp ts) (hxs : ∀ d ∈ Args.toList xs, A.DynOK T d) :
    A.FrameInv T (Exec.callFrame hwf i hi ds xs) := by
  unfold Exec.callFrame
  exact FrameInv.entry (hR.1 _ (Array.getElem_mem hi)) (Array.getElem_mem _)
    (A.envOK_freshStore T _) hds hxs

/-- Binding a valid value in a frame of the run keeps it one. -/
theorem FrameInv.bind {T : Typing} {f : Frame M} (h : A.FrameInv T f) {v : Nat}
    {d : Dyn M.interp} (hd : A.DynOK T d) (hv : v < f.func.slots) : A.FrameInv T (f.bind v d hv) :=
  ⟨h.env.set (Nat.lt_of_lt_of_le hv f.fits) hd, h.body, h.code, h.term⟩

/-- **A transfer** along a site of a frame of the run, with a valid payload, leads to a frame of
the run or leaves with a valid value. -/
theorem FrameInv.take {T : Typing} {f : Frame M} (hf : A.FrameInv T f) :
    ∀ (s : LSite) {ts : List Ty} (xs : Args M.interp ts) (h : CanTake f s ts),
      (∀ d ∈ Args.toList xs, A.DynOK T d) → A.NextInv T (take f s xs h)
  | ⟨.block i, args⟩, _, xs, h, hx => by
    have hb := Array.getElem_mem (xs := f.func.blocks) h.2.1
    exact ⟨EnvOK.bindSite _ _ _ _ hf.env (hf.env.lookupAll _) hx, hf.body, (hf.body _ hb).1,
      (hf.body _ hb).2⟩
  | ⟨.exit, args⟩, _, xs, h, hx => by
    have hm : single (lookupAll f.env args h.1) xs h.2 ∈ lookupAll f.env args h.1 ++ Args.toList xs := by
      rw [single_spec]
      exact List.mem_cons_self
    rcases List.mem_append.mp hm with hm | hm
    · exact hf.env.lookupAll h.1 _ hm
    · exact hx _ hm

/-- **An exit** of a frame of the run, with a valid payload, leads to a frame of the run or
leaves with a valid value. -/
theorem FrameInv.exitTo {T : Typing} {f : Frame M} (hf : A.FrameInv T f) :
    ∀ {ps : List (List Ty)} (ss : List LSite) (e : Exit M.interp ps) (h : SitesOK f ss ps),
      A.ExitOK T e → A.NextInv T (Exec.exitTo f ss e h)
  | _, s :: _, .here xs, _, he => hf.take s xs _ (argsOK_toList he)
  | _, _ :: ss, .there e, _, he => hf.exitTo ss e _ he
  | _, [], .here _, h, _ => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)
  | _, [], .there _, h, _ => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)

/-- The frames and data of a run, with another top frame. -/
theorem CoreInv.withTop {P : Nat → Prop} {heap₀ : Heap M} {T : Typing} {c : Core M}
    (h : A.CoreInv P heap₀ T c) (f : Frame M) : A.CoreInv P heap₀ T { c with top := f } :=
  ⟨h.heap, h.avoid, h.world, h.conts, h.kept⟩

/-- The frames and data of a run, with a waiting frame fewer. -/
theorem CoreInv.tail {P : Nat → Prop} {heap₀ : Heap M} {T : Typing} {top : Frame M}
    {w : Wait M} {cs : List (Wait M)} {heap : Heap M} {world : M.W}
    (h : A.CoreInv P heap₀ T ⟨top, w :: cs, heap, world⟩) (f : Frame M) :
    A.CoreInv P heap₀ T ⟨f, cs, heap, world⟩ :=
  ⟨h.heap, h.avoid, h.world, fun w₁ hw => h.conts w₁ (List.mem_cons_of_mem _ hw), h.kept⟩

/-- **The frames and data of a run after a change of the heap** that keeps it typed, at an
extension that misses `P`, and changes only cells valid in the old typing. -/
theorem CoreInv.heapStep {P : Nat → Prop} {heap₀ : Heap M} {T T₁ : Typing} {c : Core M}
    (hP : ∀ l, P l → l < heap₀.cells.size) (h : A.CoreInv P heap₀ T c) (he : T.Extends T₁)
    {heap₁ : Heap M} (hH : A.HeapOK T₁ heap₁) (hav : ∀ l, P l → T₁.cell l = none)
    (hf : HeapFrame T c.heap heap₁) : A.CoreInv P heap₀ T₁ { c with heap := heap₁ } :=
  ⟨hH, hav, Typing.AllValid.mono he h.world, fun w hw => (h.conts w hw).mono he,
    h.kept.frame hP h.avoid hf⟩

/-- A new location misses `P`, a set of `heap₀`'s locations. -/
theorem CoreInv.avoid_addCell {P : Nat → Prop} {heap₀ : Heap M} {T : Typing} {c : Core M}
    (hP : ∀ l, P l → l < heap₀.cells.size) (h : A.CoreInv P heap₀ T c) (t : Ty) :
    ∀ l, P l → (T.addCell c.heap.cells.size t).cell l = none := fun l hl => by
  show (if l = c.heap.cells.size then some t else T.cell l) = none
  rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.ne_of_lt
    (Nat.lt_of_lt_of_le (hP l hl) h.kept.size)))]
  exact h.avoid l hl

end Accounts

/-! ## A step keeps the invariant -/

section
variable {A : Accounts M} {m : LModule M} (hwf : WF m) (oracle : Nat → Nat) {B : Ty}
  (hR : m.RulesOK A) {P : Nat → Prop} {heap₀ : Heap M} (hP : ∀ l, P l → l < heap₀.cells.size)

/-- Stopping with a fault keeps the cells at `P`. -/
theorem faultStep_inv {T : Typing} {c : Core M} (hC : A.CoreInv P heap₀ T c) (f : Fault)
    (drawn : Nat) : A.StepInv P heap₀ T (faultStep (m := m) (B := B) c f drawn) :=
  ⟨T, .refl _, hC, trivial⟩

/-- A transfer to a frame of the run, or out with a valid value, keeps the invariant. -/
theorem transfer_inv {T : Typing} {c : Core M} {n : Next M} (hn : NextOK m c.top n)
    (hK : ContsOK m B c.top.func.ret c.conts) {drawn : Nat} {ev : Event}
    (hC : A.CoreInv P heap₀ T c) (hN : A.NextInv T n) :
    A.StepInv P heap₀ T (transfer c n hn hK drawn ev) := by
  cases n with
  | frame g => exact ⟨T, .refl _, hC, hN⟩
  | leave v => exact ⟨T, .refl _, hC, hN⟩

include hR in
/-- **A rule's tree, continued**: a tree that respects `T`, of a rule that runs again from valid
states, in a frame of the run, keeps the invariant. -/
theorem settle_inv {T : Typing} {c : Core M} {i : Inst M} (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) {drawn : Nat} {ev : Event}
    (hC : A.CoreInv P heap₀ T c) (hf : A.FrameInv T c.top) (hag : AgainOK A i) (t : i.Tree)
    (ht : A.TreeOK (A.StOK i.rerun.key) T i.ret t) :
    A.StepInv P heap₀ T (settle hwf c i hi hK drawn ev t) := by
  cases t with
  | ret a =>
    obtain ⟨op, pc, dst, ret, ps, rs, regs, succs, rerun⟩ := i
    cases ret with
    | none => exact nomatch a
    | some r =>
      simp only [settle]
      exact ⟨T, .refl _, hC.withTop _, hf.bind (d := resDyn (some r) a) (A.treeOK_ret.mp ht) (hi.dst_lt a)⟩
  | stop s =>
    cases s with
    | jump o =>
      cases o with
      | exit e =>
        simp only [settle]
        exact transfer_inv _ _ hC (hf.exitTo i.succs e hi.sitesOK (A.treeOK_jump.mp ht))
      | again st =>
        simp only [settle]
        exact ⟨T, .refl _, hC, hf, hag, A.treeOK_jump.mp ht⟩
    | fault f =>
      simp only [settle]
      exact faultStep_inv hC f drawn
  | choose k =>
    simp only [settle]
    exact ⟨T, .refl _, hC, hf, hag, ht⟩
  | update f =>
    simp only [settle]
    exact ⟨T, .refl _, hC, hf, hag, ht⟩
  | vis q k =>
    have hsat := A.treeOK_vis.mp ht
    cases q with
    | region j args =>
      simp only [settle, visitRegion]
      refine ⟨T, .refl _, hC, ?_, hf, hag, fun S₁ he o ho => hsat.2 S₁ he o ho⟩
      exact Accounts.FrameInv.regionStart hR hf args (Accounts.argsOK_toList hsat.1)
    | call sig idx captured args =>
      simp only [settle, visitCall]
      by_cases hc : ∃ caps, m.CallOK c.heap idx captured sig.1 sig.2 caps
      · obtain ⟨caps, hco⟩ := hc
        rw [LModule.callee_pos hco]
        refine ⟨T, .refl _, hC, ?_, hf, hag, fun S₁ he o ho => hsat.2 S₁ he o ho⟩
        exact Accounts.FrameInv.callFrame hR hwf (hC.heap.captures hsat.1.1 hco.2.1) _
          (Accounts.argsOK_toList hsat.1.2)
      · rw [LModule.callee_neg (fun caps h => hc ⟨caps, h⟩)]
        exact faultStep_inv hC _ drawn
    | new _ _ =>
      simp only [settle]
      exact ⟨T, .refl _, hC, hf, hag, ht⟩
    | get _ _ =>
      simp only [settle]
      exact ⟨T, .refl _, hC, hf, hag, ht⟩
    | set _ _ _ =>
      simp only [settle]
      exact ⟨T, .refl _, hC, hf, hag, ht⟩
    | modify _ _ _ =>
      simp only [settle]
      exact ⟨T, .refl _, hC, hf, hag, ht⟩
    | bind _ _ _ _ _ =>
      simp only [settle]
      exact ⟨T, .refl _, hC, hf, hag, ht⟩

include hR hP in
/-- **Answering a rule's world or cell request**: a tree that respects `T` asks only for cells
valid in `T`, so the machine changes no cell at `P`, and the typing grows by what the answer
makes. -/
theorem serve_inv {T : Typing} {c : Core M} {i : Inst M} (t : i.Tree)
    (h : InstOK m c.top i ∧ ContsOK m B c.top.func.ret c.conts) {drawn : Nat}
    (hC : A.CoreInv P heap₀ T c) (hf : A.FrameInv T c.top) (hag : AgainOK A i)
    (ht : A.TreeOK (A.StOK i.rerun.key) T i.ret t) :
    A.StepInv P heap₀ T (serve hwf oracle c i t h drawn) := by
  cases t with
  | choose k =>
    simp only [serve]
    exact settle_inv hwf hR _ _ hC hf hag _ (A.treeOK_choose.mp ht _)
  | update f =>
    obtain ⟨top, conts, heap, w⟩ := c
    have hu := (A.treeOK_update.mp ht) w hC.world
    simp only [serve]
    exact settle_inv hwf hR (c := ⟨top, conts, heap, (f w).1⟩) _ _
      ⟨hC.heap, hC.avoid, hu.1, hC.conts, hC.kept⟩ hf hag _ hu.2
  | ret a =>
    simp only [serve]
    exact settle_inv hwf hR _ _ hC hf hag _ ht
  | stop s =>
    simp only [serve]
    exact settle_inv hwf hR _ _ hC hf hag _ ht
  | vis q k =>
    have hsat := A.treeOK_vis.mp ht
    cases q with
    | region j args =>
      simp only [serve]
      exact settle_inv hwf hR _ _ hC hf hag _ ht
    | call sig idx captured args =>
      simp only [serve]
      exact settle_inv hwf hR _ _ hC hf hag _ ht
    | new ty v =>
      simp only [serve]
      have he := Typing.extends_addCell hC.heap.none_size ty
      have hval : (T.addCell c.heap.cells.size ty).Valid c.heap.cells.size ty := by
        show (if c.heap.cells.size = c.heap.cells.size then some ty else _) = some ty
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      refine Accounts.StepInv.trans he (settle_inv hwf hR (c := { c with heap := c.heap.push ⟨ty, v⟩ }) _ _
        (hC.heapStep hP he (hC.heap.push (d := ⟨ty, v⟩) hsat.1) (hC.avoid_addCell hP ty) (HeapFrame.push _))
        (hf.mono he) hag _ (hsat.2 _ he _ hval))
    | get ty l =>
      obtain ⟨hl, htl, hd⟩ := hC.heap.cellOK hsat.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      simp only [serve]
      rw [Heap.cell_pos hh]
      exact settle_inv hwf hR _ _ hC hf hag _
        (hsat.2 _ (Typing.Extends.refl _) _ (Accounts.valOK_valueAt hh.lt hh.code hd))
    | set ty l v =>
      obtain ⟨hl, htl, -⟩ := hC.heap.cellOK hsat.1.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      simp only [serve]
      rw [Heap.cell_pos hh]
      exact settle_inv hwf hR (c := { c with heap := c.heap.set l ⟨ty, v⟩ hh.lt }) _ _
        (hC.heapStep hP (.refl _) (hC.heap.set hh.lt hh.code.symm hsat.1.2) hC.avoid
          (HeapFrame.set hh.lt hsat.1.1 _))
        hf hag _ (hsat.2 _ (Typing.Extends.refl _) () trivial)
    | modify ty l g =>
      obtain ⟨hl, htl, -⟩ := hC.heap.cellOK hsat.1.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      simp only [serve]
      rw [Heap.cell_pos hh, Heap.modifyAt_eq]
      exact settle_inv hwf hR (c := { c with heap := c.heap.modify l ty g }) _ _
        (hC.heapStep hP (.refl _) (hC.heap.modify hsat.1.2) hC.avoid
          (HeapFrame.modify hsat.1.1 _))
        hf hag _ (hsat.2 _ (Typing.Extends.refl _) () trivial)
    | bind ty v sig idx captured =>
      simp only [serve]
      by_cases hc : ∃ caps, m.CallOK c.heap idx captured (ty :: sig.1) sig.2 caps
      · obtain ⟨caps, hco⟩ := hc
        rw [LModule.callee_pos hco]
        have hds : ∀ d ∈ caps ++ [(⟨ty, v⟩ : Dyn M.interp)], A.DynOK T d := by
          intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hC.heap.captures hsat.1.1 hco.2.1 d hd
          · rw [List.mem_singleton.mp hd]; exact hsat.1.2
        have he := Typing.extends_addCaps hC.heap.caps_none_size ((caps ++ [(⟨ty, v⟩ : Dyn M.interp)]).map (·.1))
        have hval : (T.addCaps c.heap.caps.size ((caps ++ [(⟨ty, v⟩ : Dyn M.interp)]).map (·.1))).CapValid
            (c.heap.caps.size + 1) := by
          refine .inr ⟨(caps ++ [(⟨ty, v⟩ : Dyn M.interp)]).map (·.1), ?_⟩
          show (if c.heap.caps.size + 1 - 1 = c.heap.caps.size then some _ else _) = _
          rw [ite_eq_left_of_eq_true _ _ (eq_true (Nat.add_sub_cancel _ _))]
        exact Accounts.StepInv.trans he (settle_inv hwf hR
          (c := { c with heap := c.heap.capture (caps ++ [(⟨ty, v⟩ : Dyn M.interp)]) }) _ _
          (hC.heapStep hP he (hC.heap.capture hds) hC.avoid (HeapFrame.capture _))
          (hf.mono he) hag _ (hsat.2 _ he _ hval))
      · rw [LModule.callee_neg (fun caps h => hc ⟨caps, h⟩)]
        exact faultStep_inv hC _ drawn


/-- A ref valid in `T` names a cell valid in `T` at its contents' tag. -/
theorem Accounts.valid_of_ref {A : Accounts M} {T : Typing} {t : Ty} {x : M.interp (Ty.ref t)}
    (h : A.ValOK T (Ty.ref t) x) : T.Valid (M.locOf x) t := by
  unfold Accounts.ValOK at h
  rw [A.ref] at h
  exact Typing.allValid_singleton.mp h

/-- A closure valid in `T` names a captures cell valid in `T`. -/
theorem Accounts.capValid_of_fn {A : Accounts M} {T : Typing} {ts : List Ty} {r : Ty}
    {x : M.interp (Ty.fn ts r)} (h : A.ValOK T (Ty.fn ts r) x) : T.CapValid (M.fnOf x).captured := by
  unfold Accounts.ValOK at h
  rw [A.fn] at h
  exact Typing.capValid_of_allValid h

include hR hP in
/-- **Running an instruction or a terminator** of a frame of the run keeps the invariant. -/
theorem exec_inv {T : Typing} {c : Core M} (h : CoreOK m B c) {drawn : Nat}
    (hC : A.CoreInv P heap₀ T c) (hf : A.FrameInv T c.top) :
    A.StepInv P heap₀ T (exec hwf c h drawn) := by
  obtain ⟨⟨func, code, term, env, blk, pc, fits⟩, conts, heap, world⟩ := c
  cases code with
  | nil =>
    cases term with
    | case ts ps f args succs =>
      simp only [exec, execCode, execTerm]
      exact transfer_inv _ _ hC (hf.exitTo succs _ _ (hf.env.applyFn _ (hf.term T)))
    | sem op rs ps re f regs succs =>
      simp only [exec, execCode, execTerm]
      exact settle_inv hwf hR _ _ hC hf (by exact hf.term.2) _ (by exact hf.env.applyFn _ (hf.term.1 T))
  | cons i code =>
    have hi : A.InsnOK i := hf.code i List.mem_cons_self
    have hcode : ∀ i₁ ∈ code, A.InsnOK i₁ := fun i₁ hm => hf.code i₁ (List.mem_cons_of_mem _ hm)
    cases i with
    | const dst v =>
      simp only [exec, execCode, Core.next]
      refine ⟨T, .refl _, hC.withTop _,
        hf.env.set (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) ?_, hf.body, hcode, hf.term⟩
      unfold Accounts.DynOK Accounts.ValOK
      rw [show A.acct v.1 v.2 = [] from hi]
      exact Typing.allValid_nil _
    | pure dst ts r f args =>
      simp only [exec, execCode, Core.next]
      exact ⟨T, .refl _, hC.withTop _, hf.env.set (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)
        (hf.env.applyFn (h.ready rfl) (hi T)), hf.body, hcode, hf.term⟩
    | sem op dst rs r ps re f regs succs =>
      simp only [exec, execCode]
      exact settle_inv hwf hR _ _ (hC.withTop _) (by exact ⟨hf.env, hf.body, hcode, hf.term⟩)
        (by exact hi.2) _ (by exact hf.env.applyFn _ (hi.1 T))
    | refNew dst t v =>
      simp only [exec, execCode, Core.refNew, Core.next]
      have hv : v < env.size := h.ready rfl
      have htag : (getD env v hv).1 = t := (CoreOK.refNew_tag h rfl).2 hv
      have hx : A.DynOK T (getD env v hv) := hf.env.get hv
      have he := Typing.extends_addCell hC.heap.none_size (getD env v hv).1
      have hnew : A.DynOK (T.addCell heap.cells.size (getD env v hv).1)
          ⟨Ty.ref t, M.cellAt t heap.cells.size⟩ := by
        unfold Accounts.DynOK Accounts.ValOK
        rw [A.ref, M.locOf_cellAt]
        refine Typing.allValid_singleton.mpr ?_
        show (if heap.cells.size = heap.cells.size then some _ else _) = some t
        rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), htag]
      have hC₁ := hC.heapStep hP he (hC.heap.push hx) (hC.avoid_addCell hP _) (HeapFrame.push _)
      exact ⟨_, he, hC₁.withTop _,
        (hf.env.mono he).set (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) hnew, hf.body, hcode, hf.term⟩
    | refGet dst t x =>
      simp only [exec, execCode, Core.cellLoc]
      have hl := Accounts.valid_of_ref (Accounts.EnvOK.getT hf.env (h.ready rfl))
      by_cases hh : heap.Holds (M.locOf (getT env x (Ty.ref t) (h.ready rfl))) t
      · rw [Heap.cell_pos hh]
        simp only [Core.refGet, Core.next]
        obtain ⟨_, _, hd⟩ := hC.heap.cellOK hl
        exact ⟨T, .refl _, hC.withTop _, hf.env.set (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) hd,
          hf.body, hcode, hf.term⟩
      · rw [Heap.cell_neg hh]
        exact faultStep_inv hC _ drawn
    | refSet dst t x v =>
      simp only [exec, execCode, Core.cellLoc]
      have hl := Accounts.valid_of_ref (Accounts.EnvOK.getT hf.env (h.ready rfl).1)
      by_cases hh : heap.Holds (M.locOf (getT env x (Ty.ref t) (h.ready rfl).1)) t
      · rw [Heap.cell_pos hh]
        simp only [Core.refSet, Core.next]
        have hv : v < env.size := (h.ready rfl).2
        have htag : (getD env v hv).1 =
            (heap.cells[M.locOf (getT env x (Ty.ref t) (h.ready rfl).1)]'hh.lt).1 :=
          ((CoreOK.refSet_tag h rfl).2 hv).trans hh.code.symm
        have hC₁ := hC.heapStep hP (.refl _) (hC.heap.set hh.lt htag (hf.env.get hv)) hC.avoid
          (HeapFrame.set hh.lt hl _)
        have hunit : A.DynOK T ⟨M.unit, M.unitVal⟩ := by
          unfold Accounts.DynOK Accounts.ValOK
          rw [A.unit]
          exact Typing.allValid_nil _
        exact ⟨T, .refl _, hC₁.withTop _,
          hf.env.set (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) hunit, hf.body, hcode, hf.term⟩
      · rw [Heap.cell_neg hh]
        exact faultStep_inv hC _ drawn
    | callCode dst ts r fn args =>
      simp only [exec, execCode]
      have hr : HasTy env fn (Ty.fn ts r) ∧ AllBound env args := h.ready rfl
      have hcap := Accounts.capValid_of_fn (Accounts.EnvOK.getT hf.env hr.1)
      by_cases hc : ∃ caps, m.CallOK heap (M.fnOf (getT env fn (Ty.fn ts r) hr.1)).idx
          (M.fnOf (getT env fn (Ty.fn ts r) hr.1)).captured ts r caps
      · obtain ⟨caps, hco⟩ := hc
        rw [LModule.callee_pos hco]
        have hds : ∀ d ∈ appendCaps caps (lookupAll env args hr.2), A.DynOK T d := by
          intro d hd
          rw [appendCaps_eq] at hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hC.heap.captures hcap hco.2.1 d hd
          · exact hf.env.lookupAll hr.2 d hd
        exact ⟨T, .refl _, hC, Accounts.FrameInv.callFrame hR hwf hds _ (fun _ hd => nomatch hd),
          hf.env, hf.body, hcode, hf.term⟩
      · rw [LModule.callee_neg (fun caps h => hc ⟨caps, h⟩)]
        exact faultStep_inv hC _ drawn

include hR in
/-- **Leaving a body** with a valid value keeps the invariant. -/
theorem leave_inv {T : Typing} {c : Core M} {v : Dyn M.interp} (h : LeftOK m B c v) {drawn : Nat}
    (hC : A.CoreInv P heap₀ T c) (hv : A.DynOK T v) :
    A.StepInv P heap₀ T (leave hwf c v h drawn) := by
  obtain ⟨top, conts, heap, world⟩ := c
  cases conts with
  | nil =>
    simp only [leave, leaveTo]
    exact ⟨T, .refl _, hC, trivial⟩
  | cons w cs =>
    have hw := hC.conts w List.mem_cons_self
    cases w with
    | rule f p =>
      simp only [leave, leaveTo]
      obtain ⟨hfi, hag, hres⟩ := hw
      exact settle_inv hwf hR _ _ (hC.tail f) hfi hag _
        (hres T (.refl _) _ (Accounts.dynOK_at hv _))
    | call f dst r =>
      simp only [leave, leaveTo]
      exact ⟨T, .refl _, hC.tail _, hw.bind hv (LeftOK.call_dst h rfl)⟩

include hR hP in
/-- **A step keeps the invariant**, at an extension of the typing: a step of a module whose
rules are certified changes no cell at `P`, and a run that ends keeps them. -/
theorem step_inv {s : State M} (h : StateOK m B s) {T : Typing} (hs : A.Inv P heap₀ T s) :
    A.StepInv P heap₀ T (step hwf oracle s h) := by
  obtain ⟨⟨top, conts, heap, world⟩, mode, drawn, ⟨⟩⟩ := s
  obtain ⟨hC, hm⟩ := hs
  cases mode with
  | exec => exact exec_inv hwf hR hP h hC hm
  | jump to =>
    simp only [step]
    exact ⟨T, .refl _, hC.withTop _, hm⟩
  | call callee w =>
    simp only [step]
    refine ⟨T, .refl _, ⟨hC.heap, hC.avoid, hC.world, fun w₁ hw₁ => ?_, hC.kept⟩, hm.1⟩
    rcases List.mem_cons.mp hw₁ with rfl | hw₁
    · exact hm.2
    · exact hC.conts w₁ hw₁
  | ret v => exact leave_inv hwf hR h hC hm
  | request i t => exact serve_inv hwf oracle hR hP t h hC hm.1 hm.2.1 hm.2.2
  | again r =>
    simp only [step, Inst.again]
    exact settle_inv hwf hR _ _ hC hm.1 hm.2.1 _ (hm.1.env.applyFn _ (hm.2.1 T) _ hm.2.2)
  | done r =>
    simp only [step]
    exact hC.kept

end

/-! ## The frame theorem -/

section
variable {A : Accounts M} {m : LModule M} {hwf : WF m} {B : Ty}
  {P : Nat → Prop} {heap₀ : Heap M}

/-- **The invariant holds at every configuration of every run**, at an extension of the typing
it starts at, and a run that ends keeps the cells at `P`. -/
theorem inv_always (hR : m.RulesOK A) (hP : ∀ l, P l → l < heap₀.cells.size) {s : State M}
    {h : StateOK m B s} {T : Typing} (hs : A.Inv P heap₀ T s) (r : RunFrom hwf s h) (n : Nat) :
    (r.cfg n).Sat (fun c => ∃ T₁, T.Extends T₁ ∧ A.Inv P heap₀ T₁ c.1)
      (fun f => Kept P heap₀ f.snapshot.heap) := by
  refine always (P := fun s => ∃ T₁, T.Extends T₁ ∧ A.Inv P heap₀ T₁ s) ?_ r ⟨T, .refl _, hs⟩ n
  rintro o s₁ h₁ ⟨T₁, he, hi⟩
  have hst := step_inv hwf o hR hP h₁ hi
  revert hst
  cases step hwf o s₁ h₁ with
  | next e s₂ h₂ =>
    rintro ⟨T₂, he₂, hi₂⟩
    exact ⟨T₂, he.trans he₂, hi₂⟩
  | final r hp w d => exact id

/-- **The frame theorem.**  A run of a module whose rules are certified, from a state
where the invariant holds for a set `P` of locations of `heap₀`, leaves the cells at `P` as
`heap₀` has them, at every configuration of every run and at its end if it ends, and only grows
the heap. -/
theorem frame (hR : m.RulesOK A) (hP : ∀ l, P l → l < heap₀.cells.size) {s : State M}
    {h : StateOK m B s} {T : Typing} (hs : A.Inv P heap₀ T s) (r : RunFrom hwf s h) (n : Nat) :
    (r.cfg n).Sat (fun c => Kept P heap₀ c.1.core.heap)
      (fun f => Kept P heap₀ f.snapshot.heap) := by
  have h₁ := inv_always hR hP hs r n
  revert h₁
  cases r.cfg n with
  | running c =>
    rintro ⟨_, _, hi⟩
    exact hi.1.kept
  | ended f => exact id

/-- **Allocation is fresh.**  A cell that a run allocates, at or past the end of `heap₀`, is not
at `P`, a set of `heap₀`'s locations. -/
theorem frame_fresh (hP : ∀ l, P l → l < heap₀.cells.size) {l : Nat}
    (hl : heap₀.cells.size ≤ l) : ¬ P l :=
  fun h => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (hP l h) hl)

/-- The refs a function starts with: its arguments' and the world's. -/
def startRoots (A : Accounts M) (args : List (Dyn M.interp)) (w : M.W) : List Loc :=
  args.flatMap (fun d => A.acct d.1 d.2) ++ A.world w

/-- **A function's start satisfies the invariant** at any typing that types the snapshot's heap
and misses `P`, in which the world's refs and the arguments are valid. -/
theorem inv_startCore_of (hR : m.RulesOK A) {i : Nat} {args : List (Dyn M.interp)}
    {snap : Snapshot M} {c : Core M} {hc : CoreOK m B c}
    (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩) {T : Typing} (hH : A.HeapOK T snap.heap)
    (hP : ∀ l, P l → T.cell l = none) (hw : T.AllValid (A.world snap.world))
    (hargs : ∀ d ∈ args, A.DynOK T d) :
    A.Inv P snap.heap T ⟨c, .exec, 0, ()⟩ := by
  obtain ⟨fn, b, hf, hb, rfl⟩ := startCore_entry hst
  refine ⟨⟨hH, hP, hw, fun _ hm => absurd hm List.not_mem_nil, Kept.refl _ _⟩, ?_⟩
  exact Accounts.FrameInv.entry (g := fn) (b := b) (hle := fresh_fits fn)
    (hp := hwf.fits_of_getElem? hf hb) (hR.1 _ (Array.mem_of_getElem? hf))
    (Array.mem_of_getElem? hb) (A.envOK_freshStore _ _) hargs
    (fun _ hd => absurd hd List.not_mem_nil)

/-- **A function's start satisfies the invariant**, at the typing of what its arguments and the
world reach, for any set `P` of locations that they do not reach, when every ref they reach
names a cell of its tag. -/
theorem inv_startCore (hR : m.RulesOK A) {i : Nat} {args : List (Dyn M.interp)}
    {snap : Snapshot M} {c : Core M} {hc : CoreOK m B c}
    (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩)
    (hw : WellTagged A snap.heap (startRoots A args snap.world))
    (hu : ∀ l, P l → ¬ ReachesCell A snap.heap (startRoots A args snap.world) l) :
    A.Inv P snap.heap (reachTyping A snap.heap (startRoots A args snap.world))
      ⟨c, .exec, 0, ()⟩ :=
  inv_startCore_of hR hst hw.heapOK (fun l hl => reachTyping_none (hu l hl))
    (fun p hp => hw.rootsValid p (List.mem_append_right _ hp))
    (fun d hd p hp => hw.rootsValid p (List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, hp⟩)))

/-- **The frame theorem from a function's start.**  A run of a function of a module whose rules are
certified, on arguments from which, with the world, no location of `P` is reachable in the
snapshot's heap, leaves the cells at `P` unchanged at every configuration of every run and at its
end if it ends. -/
theorem frame_startCore (hR : m.RulesOK A) {i : Nat} {args : List (Dyn M.interp)}
    {snap : Snapshot M} {c : Core M} {hc : CoreOK m B c}
    (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩)
    (hw : WellTagged A snap.heap (startRoots A args snap.world))
    (hP : ∀ l, P l → l < snap.heap.cells.size)
    (hu : ∀ l, P l → ¬ ReachesCell A snap.heap (startRoots A args snap.world) l)
    (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc) (n : Nat) :
    (r.cfg n).Sat (fun c => Kept P snap.heap c.1.core.heap)
      (fun f => Kept P snap.heap f.snapshot.heap) :=
  frame hR hP (inv_startCore hR hst hw hu) r n

end

end

end Strata.Dyn.Exec
