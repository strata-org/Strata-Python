/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.Edge
public import StrataDyn.Exec.SameSigs
public import StrataDyn.Exec.Trace

set_option autoImplicit false

/-!
# The simulation of a certified promotion

`Rel` relates a state of the source module to one of the target:

* the same choices drawn and the same world;
* heaps that agree off the promoted locations `P` (`HeapRel`), and a source heap and world whose
  every value is valid off `P` (`HeapInv`), so they hold no promoted cell;
* pending transitions that correspond (`ModeRel`), and waiting frames that correspond frame by
  frame (`StackRel`), each with the facts that hold of it;
* no frame above a waiting frame may write a promoted cell whose content the waiting frame holds
  (`Disjoint`).

A source state that has ended with a wrong result (`Wrong`, a bad cell) corresponds to any
target state.

A rule's tree is the same in the source and the target, on the same operands.  It satisfies the
machine's spec at the typing off `P` (`Accounts.TreeOK`), so every cell it asks for is off `P`,
where the heaps agree: the machine answers it alike in both.

The step diagram of a pair of steps is the machine's (`Exec.Diagram`): a source step is matched
by a target step and then silent target steps, or by none with a smaller measure.  A promotion
needs no silent step.  Each source step is matched by one target step, except a removed `refGet`
or `refSet` of a promoted cell, which the target does not take: the source's code gets shorter,
the measure (`measure`).

The key theorem is `step_good`, the step diagram: from corresponding states, a source step is
matched by a target step and then silent steps to states that correspond, or by none with a
smaller measure, and a source that has ended has a wrong result or the target has ended alike.
It rests on `exec_good`, for running an instruction or a terminator; `settle_lock` and
`serve_lock`, for a rule's tree and its requests to the machine; and `leave_good`, for leaving a
body.  The cases of a rule's tree and of a call check, in the source and the target at once, are
those of the eliminators of `Exec/SameSigs.lean`.
-/

namespace Strata.Dyn.RefToRegSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-- A source result the target may improve on: a bad cell, which only a removed `refGet` or
`refSet` of a promoted cell can give where the target does not fault. -/
def Wrong (r : Result M.interp) : Prop := ∃ l, r = .fault (.badCell l)

variable (A : Accounts M) (X : CertEnv M)

/-- The rule of the source's operation `i`, running in `f` with facts `F`, and of the target's
version of it, with the operands `args₁` and the edges `succs₁`, running in `f₁`: the operands
and edges are certified, its regions start from `F`, which holds no content of a cell `Wr` they
may write, its tree from a state respects every typing, and the frames' code continues, when the
rule returns, from the facts after `i`. -/
def PendOK (P : List Nat) (heap : Heap M) (F : List Fact) (f f₁ : Frame M) (i : Inst M)
    (succs₁ : List LSite) (args₁ : List Nat) : Prop :=
  ∃ E Wr, BodyOK X f.func f₁.func E ∧
    Sound A P F f.env f₁.env heap ∧ WrOK F Wr ∧ (∀ u c, Fact.cell u c ∈ F → c ∉ Wr) ∧
    ArgsEq F args₁ i.rerun.args ∧ All₂ (SiteOK E f.func f₁.func F) i.succs succs₁ ∧
    (∀ k ∈ i.regs, RegionOK X (regFacts Wr F) k) ∧ AgainOK A i ∧
    ∀ r, i.ret = some r → CodeOK X E f.func f₁.func (after i.dst F) f.code f.term f₁.code f₁.term

/-- A source frame waiting for a body and a target frame waiting for one correspond, with the
facts `F` of the waiting frame: a paused rule, the target's operation being its version of the
source's and resuming alike, or the caller of a `callCode`. -/
inductive WaitRel (P : List Nat) (heap : Heap M) (F : List Fact) : Wait M → Wait M → Prop
  | rule {f f₁ : Frame M} {i : Inst M} {pc₁ : Nat} {succs₁ : List LSite} {args₁ : List Nat}
      {req req₁ : MReq M.interp i.rs} {r : Ty} {k : M.interp r → i.Tree} :
      PendOK A X P heap F f f₁ i succs₁ args₁ → ResumeOK A (typOff heap P) ⟨i, req, r, k⟩ →
      WaitRel P heap F (.rule f ⟨i, req, r, k⟩)
        (.rule f₁ ⟨mkInst i pc₁ succs₁ args₁, req₁, r, k⟩)
  | call {f f₁ : Frame M} {dst : Nat} {r : Ty} {E : Nat → List Fact} :
      BodyOK X f.func f₁.func E →
      CodeOK X E f.func f₁.func (after dst F) f.code f.term f₁.code f₁.term →
      Sound A P F f.env f₁.env heap → WaitRel P heap F (.call f dst r) (.call f₁ dst r)

/-- The waiting frames correspond, frame by frame, with the facts `Fs`. -/
inductive StackRel (P : List Nat) (heap : Heap M) :
    List (List Fact) → List (Wait M) → List (Wait M) → Prop
  | nil : StackRel P heap [] [] []
  | cons {F : List Fact} {Fs : List (List Fact)} {w w₁ : Wait M} {ws ws₁ : List (Wait M)} :
      WaitRel A X P heap F w w₁ → StackRel P heap Fs ws ws₁ →
      StackRel P heap (F :: Fs) (w :: ws) (w₁ :: ws₁)

/-- The waiting frames' stores with their facts. -/
def stackFacts : List (List Fact) → List (Wait M) → List (Array (Dyn M.interp) × List Fact)
  | F :: Fs, w :: ws => (w.frame.env, F) :: stackFacts Fs ws
  | _, _ => []

/-- No frame of the list may write a promoted cell whose content a frame after it holds. -/
def Disjoint : List (Array (Dyn M.interp) × List Fact) → Prop
  | [] => True
  | (env, F) :: rest => (∀ l, promLocs env F l → ∀ q ∈ rest, ¬ cellLocs q.1 q.2 l) ∧ Disjoint rest

/-- The source's pending transition and the target's correspond, with the frames whose stores
and facts `L` lists, the frames running or about to run: the same transition, a rule's operation
in the target being its version of the source's; or the source has ended with a wrong result,
whatever the target's transition. -/
inductive ModeRel (P : List Nat) (heap : Heap M) (c c₁ : Core M) :
    List (Array (Dyn M.interp) × List Fact) → Mode M → Mode M → Prop
  | exec {F : List Fact} : FrameOK A X P heap F c.top c₁.top →
      ModeRel P heap c c₁ [(c.top.env, F)] .exec .exec
  | jump {F : List Fact} {to to₁ : Frame M} : FrameOK A X P heap F to to₁ →
      ModeRel P heap c c₁ [(to.env, F)] (.jump to) (.jump to₁)
  | call {F Fw : List Fact} {g g₁ : Frame M} {w w₁ : Wait M} : FrameOK A X P heap F g g₁ →
      WaitRel A X P heap Fw w w₁ →
      ModeRel P heap c c₁ [(g.env, F), (w.frame.env, Fw)] (.call g w) (.call g₁ w₁)
  | ret {v : Dyn M.interp} : A.DynOK (typOff heap P) v → ModeRel P heap c c₁ [] (.ret v) (.ret v)
  | request {F : List Fact} {i : Inst M} {pc₁ : Nat} {succs₁ : List LSite} {args₁ : List Nat}
      (t : i.Tree) : PendOK A X P heap F c.top c₁.top i succs₁ args₁ →
      A.TreeOK (A.StOK i.rerun.key) (typOff heap P) i.ret t →
      ModeRel P heap c c₁ [(c.top.env, F)] (.request i t)
        (.request (mkInst i pc₁ succs₁ args₁) t)
  | again {F : List Fact} {i : Inst M} {pc₁ : Nat} {succs₁ : List LSite} {args₁ : List Nat}
      (st : i.St) : PendOK A X P heap F c.top c₁.top i succs₁ args₁ →
      A.StOK i.rerun.key (typOff heap P) st →
      ModeRel P heap c c₁ [(c.top.env, F)] (.again ⟨i, st⟩)
        (.again ⟨mkInst i pc₁ succs₁ args₁, st⟩)
  | done (r : Result M.interp) : ModeRel P heap c c₁ [] (.done r) (.done r)
  | wrong {r : Result M.interp} {mode₁ : Mode M} : Wrong r → ModeRel P heap c c₁ [] (.done r) mode₁

/-- A source state and a target state that correspond. -/
def Rel (s s₁ : State M) : Prop :=
  s₁.drawn = s.drawn ∧ s₁.core.world = s.core.world ∧
    ∃ P L Fs, HeapRel P s.core.heap s₁.core.heap ∧ HeapInv A P s.core.heap ∧
      (typOff s.core.heap P).AllValid (A.world s.core.world) ∧
      ModeRel A X P s.core.heap s.core s₁.core L s.mode s₁.mode ∧
      StackRel A X P s.core.heap Fs s.core.conts s₁.core.conts ∧
      Disjoint (L ++ stackFacts Fs s.core.conts)

/-! ## Facts across a change of the heap -/

/-- The source's heap and promoted locations change from `heap`, `P` to `heap₁`, `P₁`: the heap
grows, the promoted locations grow, the typing off them extends, and no promoted cell changes but
those `W` names. -/
structure HeapStep (P P₁ : List Nat) (heap heap₁ : Heap M) (W : Nat → Prop) : Prop where
  size : heap.cells.size ≤ heap₁.cells.size
  prom : ∀ l ∈ P, l ∈ P₁
  typ : (typOff heap P).Extends (typOff heap₁ P₁)
  keep : ∀ l ∈ P, ¬ W l → heap₁.cells[l]? = heap.cells[l]?

/-- **The frame of a step off the promoted cells.**  A change of the heap that changes only cells
valid in the typing off `P` (`Exec.HeapFrame`, which every rule's cell request and every
machine access of a cell that is not promoted makes) keeps every promoted cell. -/
theorem HeapStep.of_frame {P : List Nat} {heap heap₁ : Heap M} {W : Nat → Prop}
    (hb : ∀ l ∈ P, l < heap.cells.size) (hT : (typOff heap P).Extends (typOff heap₁ P))
    (hf : HeapFrame (typOff heap P) heap heap₁) : HeapStep P P heap heap₁ W :=
  ⟨hf.size, fun _ h => h, hT, fun l hl _ => hf.keep l (hb l hl) (typOff_none hl)⟩

/-- Nothing changes. -/
theorem HeapStep.refl (P : List Nat) (heap : Heap M) (W : Nat → Prop) : HeapStep P P heap heap W :=
  ⟨Nat.le_refl _, fun _ h => h, Typing.Extends.refl _, fun _ _ _ => rfl⟩

variable {A X}

/-- Facts whose contents are not of a changed cell still hold after a change of the heap. -/
theorem Sound.step {P P₁ : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap heap₁ : Heap M} {W : Nat → Prop} (hS : Sound A P F env env₁ heap)
    (hst : HeapStep P P₁ heap heap₁ W) (hw : ∀ l, cellLocs env F l → ¬ W l) :
    Sound A P₁ F env env₁ heap₁ :=
  hS.congr (fun _ h => h) (fun _ _ => rfl) (fun _ _ _ _ => rfl) hst.size hst.prom hst.typ
    fun φ hφ u c l he hr => by
      subst he
      obtain ⟨l₁, d, hr₁, hP, -, -⟩ := hS.holds _ hφ
      obtain rfl := hr₁.unique hr
      exact hst.keep l₁ hP (hw l₁ ⟨u, c, hφ, hr⟩)

/-- A paused rule's facts still hold after a change of the heap that keeps its cells. -/
theorem PendOK.step {P P₁ : List Nat} {F : List Fact} {heap heap₁ : Heap M} {W : Nat → Prop}
    {f f₁ : Frame M} {i : Inst M} {succs₁ : List LSite} {args₁ : List Nat}
    (h : PendOK A X P heap F f f₁ i succs₁ args₁) (hst : HeapStep P P₁ heap heap₁ W)
    (hw : ∀ l, cellLocs f.env F l → ¬ W l) : PendOK A X P₁ heap₁ F f f₁ i succs₁ args₁ := by
  obtain ⟨E, Wr, hB, hS, hrest⟩ := h
  exact ⟨E, Wr, hB, hS.step hst hw, hrest⟩

/-- A waiting frame's correspondence survives a change of the heap that keeps its cells. -/
theorem WaitRel.step {P P₁ : List Nat} {F : List Fact} {heap heap₁ : Heap M} {W : Nat → Prop}
    {w w₁ : Wait M} (h : WaitRel A X P heap F w w₁) (hst : HeapStep P P₁ heap heap₁ W)
    (hw : ∀ l, cellLocs w.frame.env F l → ¬ W l) : WaitRel A X P₁ heap₁ F w w₁ := by
  cases h with
  | rule hp hres => exact .rule (hp.step hst hw) (hres.mono hst.typ)
  | call hB hc hS => exact .call hB hc (hS.step hst hw)

/-- The waiting frames' correspondence survives a change of the heap that keeps their cells. -/
theorem StackRel.step {P P₁ : List Nat} {heap heap₁ : Heap M} {W : Nat → Prop}
    (hst : HeapStep P P₁ heap heap₁ W) {Fs : List (List Fact)} {ws ws₁ : List (Wait M)}
    (h : StackRel A X P heap Fs ws ws₁)
    (hq : ∀ q ∈ stackFacts Fs ws, ∀ l, cellLocs q.1 q.2 l → ¬ W l) :
    StackRel A X P₁ heap₁ Fs ws ws₁ := by
  induction h with
  | nil => exact .nil
  | cons hw _ ih =>
    exact .cons (hw.step hst (hq _ List.mem_cons_self))
      (ih fun q hm => hq q (List.mem_cons_of_mem _ hm))

/-- A change of the heap that leaves the promoted cells alone keeps every waiting frame. -/
theorem StackRel.stepOff {P P₁ : List Nat} {heap heap₁ : Heap M}
    (hst : HeapStep P P₁ heap heap₁ (fun _ => False)) {Fs : List (List Fact)}
    {ws ws₁ : List (Wait M)} (h : StackRel A X P heap Fs ws ws₁) :
    StackRel A X P₁ heap₁ Fs ws ws₁ :=
  h.step hst fun _ _ _ _ h => h

/-- The frames of a list after a frame that `Disjoint` keeps apart hold no content of a cell
the first frame may write. -/
theorem Disjoint.head {env : Array (Dyn M.interp)} {F : List Fact}
    {rest : List (Array (Dyn M.interp) × List Fact)} (h : Disjoint ((env, F) :: rest)) :
    ∀ l, promLocs env F l → ∀ q ∈ rest, ¬ cellLocs q.1 q.2 l :=
  h.1

/-- A frame that may write fewer cells keeps a list disjoint. -/
theorem Disjoint.sub {env env₁ : Array (Dyn M.interp)} {F F₁ : List Fact}
    {rest : List (Array (Dyn M.interp) × List Fact)} (h : Disjoint ((env, F) :: rest))
    (hs : ∀ l, promLocs env₁ F₁ l → promLocs env F l) : Disjoint ((env₁, F₁) :: rest) :=
  ⟨fun l hl => h.1 l (hs l hl), h.2⟩

/-! ## Facts across one instruction -/

/-- Binding the source's value `d` alone keeps the facts that do not mention it. -/
theorem Sound.bindSrc {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {d : Nat} (x : Dyn M.interp)
    (hd : d < env.size) : Sound A P (dropSrc d F) (env.set d x hd) env₁ heap :=
  h.congr (fun _ hφ => (mem_dropSrc.mp hφ).1)
    (fun _ hφ => Array.getElem?_set_ne _ (Ne.symm (mem_dropSrc.mp hφ).2))
    (fun _ _ _ _ => rfl) (Nat.le_refl _) (fun _ h => h) (Typing.Extends.refl _)
    (fun _ _ _ _ _ _ _ => rfl)

/-- Binding the source's value `d` to a valid value and the target's value `d` to a value equal to
it, with the heap unchanged, keeps the facts that do not mention them, and adds `eq d d`. -/
theorem Sound.bind' {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {d : Nat} {x x₁ : Dyn M.interp} (hx : x₁ = x)
    (hv : A.DynOK (typOff heap P) x) (hd : d < env.size) (hd₁ : d < env₁.size) :
    Sound A P (after d F) (env.set d x hd) (env₁.set d x₁ hd₁) heap := by
  subst hx
  exact h.bind _ hv hd hd₁

/-- Adding a fact about a promoted cell `c` whose location no other promoted cell of the list
has keeps a list sound. -/
theorem Sound.cons_prom {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} {φ : Fact} {c : Nat} (h : Sound A P F env env₁ heap)
    (hφ : φ.Holds A P env env₁ heap) (hp : φ.prom? = some c)
    (hd : ∀ ψ ∈ F, ∀ c₁ l, ψ.prom? = some c₁ → c₁ ≠ c → RefAt env c l → ¬ RefAt env c₁ l) :
    Sound A P (φ :: F) env env₁ heap where
  holds ψ hψ := by
    rcases List.mem_cons.mp hψ with rfl | hψ
    · exact hφ
    · exact h.holds ψ hψ
  distinct ψ hψ χ hχ c₀ c₁ l h₀ h₁ hne hl hl₁ := by
    rcases List.mem_cons.mp hψ with e₀ | hψ₁ <;> rcases List.mem_cons.mp hχ with e₁ | hχ₁
    · subst e₀ e₁
      rw [hp] at h₀ h₁
      cases h₀
      cases h₁
      exact hne rfl
    · subst e₀
      rw [hp] at h₀
      cases h₀
      exact hd χ hχ₁ c₁ l h₁ (Ne.symm hne) hl hl₁
    · subst e₁
      rw [hp] at h₁
      cases h₁
      exact hd ψ hψ₁ c₀ l h₀ hne hl₁ hl
    · exact h.distinct ψ hψ₁ χ hχ₁ c₀ c₁ l h₀ h₁ hne hl hl₁

/-- Adding a fact about a promoted cell that the list already has keeps a list sound. -/
theorem Sound.cons_same {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} {φ : Fact} {c : Nat} (h : Sound A P F env env₁ heap)
    (hφ : φ.Holds A P env env₁ heap) (hp : φ.prom? = some c) {ψ : Fact} (hψ : ψ ∈ F)
    (hψc : ψ.prom? = some c) : Sound A P (φ :: F) env env₁ heap :=
  h.cons_prom hφ hp fun χ hχ c₁ l h₁ hne hl hl₁ =>
    h.distinct ψ hψ χ hχ c c₁ l hψc h₁ (Ne.symm hne) hl hl₁

/-- The heaps grow by a cell each, at a new promoted location. -/
theorem HeapRel.pushProm {P : List Nat} {heap heap₁ : Heap M} (h : HeapRel P heap heap₁)
    (x x₁ : Dyn M.interp) : HeapRel (heap.cells.size :: P) (heap.push x) (heap₁.push x₁) where
  size := by simp [Heap.push, h.size]
  agree l hl := by
    have hne : l ≠ heap.cells.size := fun e => hl (e ▸ List.mem_cons_self)
    have hlP : l ∉ P := fun hm => hl (List.mem_cons_of_mem _ hm)
    simp only [Heap.push, Array.getElem?_push, h.size, hne, ↓reduceIte, h.agree l hlP]
  bound l hl := by
    simp only [Heap.push, Array.size_push]
    rcases List.mem_cons.mp hl with rfl | hl
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (h.bound l hl)
  caps := h.caps

/-- The heap relation, with a source heap and a target heap that each grow by a cell, the target's
equal to the source's. -/
theorem HeapRel.push' {P : List Nat} {heap heap₁ : Heap M} (h : HeapRel P heap heap₁)
    {x x₁ : Dyn M.interp} (hx : x₁ = x) : HeapRel P (heap.push x) (heap₁.push x₁) := by
  subst hx
  exact h.push _

/-- The heaps' cells at one location set to one value. -/
theorem HeapRel.set {P : List Nat} {heap heap₁ : Heap M} (hH : HeapRel P heap heap₁) {l : Nat}
    (hl : l < heap.cells.size) (hl₁ : l < heap₁.cells.size) (x : Dyn M.interp) :
    HeapRel P (heap.set l x hl) (heap₁.set l x hl₁) where
  size := by simp [Heap.set, hH.size]
  agree l₁ hl₂ := by
    simp only [Heap.set, Array.getElem?_set, hH.agree l₁ hl₂]
  bound l₁ hl₂ := by
    simp only [Heap.set, Array.size_set]
    exact hH.bound l₁ hl₂
  caps := hH.caps

/-- At a location that is not promoted, the heaps hold the same tag. -/
theorem HeapRel.holds_iff {P : List Nat} {heap heap₁ : Heap M} (hH : HeapRel P heap heap₁)
    {l : Nat} (hl : l ∉ P) (t : Ty) : heap₁.Holds l t ↔ heap.Holds l t := by
  have he := hH.agree l hl
  constructor
  · intro ⟨h₁, h₂⟩
    have hl₀ : l < heap.cells.size := hH.size ▸ h₁
    refine ⟨hl₀, ?_⟩
    rw [Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem hl₀] at he
    rw [← Option.some.inj he]
    exact h₂
  · intro ⟨h₁, h₂⟩
    have hl₀ : l < heap₁.cells.size := hH.size ▸ h₁
    refine ⟨hl₀, ?_⟩
    rw [Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem hl₀] at he
    rw [Option.some.inj he]
    exact h₂

/-- At a location that is not promoted, the heaps hold the same value. -/
theorem HeapRel.get_eq {P : List Nat} {heap heap₁ : Heap M} (hH : HeapRel P heap heap₁)
    {l : Nat} (hl : l ∉ P) (h : l < heap.cells.size) (h₁ : l < heap₁.cells.size) :
    heap₁.cells[l]'h₁ = heap.cells[l]'h := by
  have he := hH.agree l hl
  rw [Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem h] at he
  exact Option.some.inj he

/-- The heap relation, with the source's and the target's cells at one location set to values that
are equal. -/
theorem HeapRel.set' {P : List Nat} {heap heap₁ : Heap M} (hH : HeapRel P heap heap₁) {l : Nat}
    (hl : l < heap.cells.size) (hl₁ : l < heap₁.cells.size) {x x₁ : Dyn M.interp} (hx : x₁ = x) :
    HeapRel P (heap.set l x hl) (heap₁.set l x₁ hl₁) := by
  subst hx
  exact hH.set hl hl₁ _

/-- The location the machine reads for a cell is the one its ref names. -/
theorem locOf_getT {env : Array (Dyn M.interp)} {c l : Nat} {t : Ty} (hr : RefAt env c l)
    (h : HasTy env c (Ty.ref t)) : M.locOf (getT env c (Ty.ref t) h) = l := by
  obtain ⟨t₁, x, he, rfl⟩ := hr
  have hd : env[c]'h.1 = ⟨Ty.ref t₁, x⟩ := by
    rw [Array.getElem?_eq_getElem h.1] at he
    exact Option.some.inj he
  have ht : Ty.ref t₁ = Ty.ref t := (congrArg Sigma.fst hd).symm.trans (h.2 h.1)
  obtain rfl : t₁ = t := List.head_eq_of_cons_eq (Ty.app.inj ht).2
  have key : ∀ (d : Dyn M.interp) (e : d.1 = Ty.ref t₁), d = ⟨Ty.ref t₁, x⟩ →
      cast (congrArg M.interp e) d.2 = x := by
    intro d e hd₀
    subst hd₀
    rfl
  exact congrArg M.locOf (key _ (h.2 h.1) hd)

/-- Two slots that hold the same ref name the same location. -/
theorem locOf_getT_congr {env env₁ : Array (Dyn M.interp)} {c c₁ : Nat} {t : Ty}
    (h : HasTy env c (Ty.ref t)) (h₁ : HasTy env₁ c₁ (Ty.ref t)) (he : env₁[c₁]? = env[c]?) :
    M.locOf (getT env₁ c₁ (Ty.ref t) h₁) = M.locOf (getT env c (Ty.ref t) h) := by
  rw [getT_congr h h₁ he]

/-- A slot bound at a ref's tag holds a ref to the location the machine reads. -/
theorem refAt_getT {env : Array (Dyn M.interp)} {c : Nat} {t : Ty} (h : HasTy env c (Ty.ref t)) :
    RefAt env c (M.locOf (getT env c (Ty.ref t) h)) := by
  refine ⟨t, getT env c (Ty.ref t) h, ?_, rfl⟩
  rw [Array.getElem?_eq_getElem h.1]
  exact congrArg some (sigma_cast _ (h.2 h.1)).symm

/-- An `eq` fact gives the same lookup on both sides. -/
theorem Sound.eq_get {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {u v : Nat} (hm : Fact.eq u v ∈ F) :
    env₁[u]? = env[v]? := by
  obtain ⟨d, h₂, h₃, -⟩ := h.holds _ hm
  exact h₃.trans h₂.symm

/-- Target operands that `ArgsEq` certifies hold the source operands' values. -/
theorem Sound.args_get {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {args₁ args : List Nat}
    (ha : ArgsEq F args₁ args) : All₂ (fun v₁ v => env₁[v₁]? = env[v]?) args₁ args :=
  ha.imp fun _ _ hm => h.eq_get hm

/-- A value an `eq` fact names is valid off the promoted cells. -/
theorem Sound.eq_ok {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {u v : Nat} (hm : Fact.eq u v ∈ F) :
    ∀ d, env[v]? = some d → A.DynOK (typOff heap P) d := by
  intro d hd
  obtain ⟨d₀, h₂, -, h₄⟩ := h.holds _ hm
  rw [hd] at h₂
  cases h₂
  exact h₄

/-- Source operands that `ArgsEq` names are valid off the promoted cells. -/
theorem Sound.args_ok {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {args₁ args : List Nat}
    (ha : ArgsEq F args₁ args) : ∀ v ∈ args, ∀ d, env[v]? = some d → A.DynOK (typOff heap P) d := by
  induction ha with
  | nil => intro v hv; exact nomatch hv
  | cons hm _ ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.eq_ok hm
    · exact ih v hv

/-! ## The heap's values, valid off the promoted cells -/

/-- Values valid in a typing stay valid in an extension. -/
theorem HeapInv.mono {P P₁ : List Nat} {heap heap₁ : Heap M} (h : HeapInv A P heap)
    (hT : (typOff heap P).Extends (typOff heap₁ P₁))
    (hc : ∀ (l : Nat) (d : Dyn M.interp), heap₁.cells[l]? = some d →
      heap.cells[l]? = some d ∨ A.DynOK (typOff heap₁ P₁) d)
    (hk : ∀ (k : Nat) (ds : List (Dyn M.interp)), heap₁.caps[k]? = some ds →
      heap.caps[k]? = some ds ∨ ∀ d ∈ ds, A.DynOK (typOff heap₁ P₁) d) :
    HeapInv A P₁ heap₁ where
  cells l d hd := (hc l d hd).elim (fun h₀ => Typing.AllValid.mono hT (h.cells l d h₀)) id
  caps k ds hd := (hk k ds hd).elim (fun h₀ d hm => Typing.AllValid.mono hT (h.caps k ds h₀ d hm))
    id

/-- **The source's heap invariant is the frame invariant's**, at the typing off `P`: that
typing types the heap, and what it types holds only what it types (`Exec.Accounts.HeapOK`). -/
theorem HeapInv.heapOK {P : List Nat} {heap : Heap M} (h : HeapInv A P heap) :
    A.HeapOK (typOff heap P) heap where
  cell l t hl := by
    obtain ⟨-, hlt, ht⟩ := typOff_valid.mp hl
    exact ⟨hlt, ht, h.cells l _ (Array.getElem?_eq_getElem hlt)⟩
  caps k ts hk := by
    obtain ⟨ds, hds, -⟩ := Option.map_eq_some_iff.mp hk
    exact ⟨ds, hds, h.caps k ds hds⟩

/-- A new cell of a valid value keeps the heap's values valid. -/
theorem HeapInv.push {P P₁ : List Nat} {heap : Heap M} (h : HeapInv A P heap) (d : Dyn M.interp)
    (hP : P₁ = heap.cells.size :: P ∨ P₁ = P) (hd : A.DynOK (typOff heap P) d) :
    HeapInv A P₁ (heap.push d) :=
  h.mono (typOff_push d hP) (fun l d₁ h₁ => by
      simp only [Heap.push, Array.getElem?_push] at h₁
      split at h₁
      · cases h₁; exact .inr (Typing.AllValid.mono (typOff_push d hP) hd)
      · exact .inl h₁)
    fun _ _ h₁ => .inl h₁

/-- Writing a valid value of a cell's tag keeps the heap's values valid. -/
theorem HeapInv.set {P : List Nat} {heap : Heap M} (h : HeapInv A P heap) {l : Nat}
    {d : Dyn M.interp} (hl : l < heap.cells.size) (ht : d.1 = (heap.cells[l]'hl).1)
    (hd : A.DynOK (typOff heap P) d) : HeapInv A P (heap.set l d hl) := by
  have e := typOff_set (P := P) hl ht
  refine h.mono (by rw [e]; exact Typing.Extends.refl _) (fun l₁ d₁ h₁ => ?_) fun _ _ h₁ => .inl h₁
  simp only [Heap.set, Array.getElem?_set] at h₁
  split at h₁
  · cases h₁; exact .inr (by rw [e]; exact hd)
  · exact .inl h₁

/-- A new captures cell of valid values keeps the heap's values valid. -/
theorem HeapInv.capture {P : List Nat} {heap : Heap M} (h : HeapInv A P heap)
    (ds : List (Dyn M.interp)) (hd : ∀ d ∈ ds, A.DynOK (typOff heap P) d) :
    HeapInv A P (heap.capture ds) :=
  h.mono (typOff_capture ds) (fun _ _ h₁ => .inl h₁) fun k ds₁ h₁ => by
    simp only [Heap.capture, Array.getElem?_push] at h₁
    split at h₁
    · cases h₁
      exact .inr fun d hm => Typing.AllValid.mono (typOff_capture ds) (hd d hm)
    · exact .inl h₁

/-- Updating a cell by a function that keeps valid values valid keeps the heap's values
valid. -/
theorem HeapInv.modify {P : List Nat} {heap : Heap M} (h : HeapInv A P heap) {l : Nat} {t : Ty}
    {g : M.interp t → M.interp t}
    (hg : ∀ x, A.ValOK (typOff heap P) t x → A.ValOK (typOff heap P) t (g x)) :
    HeapInv A P (heap.modify l t g) := by
  have e : typOff (heap.modify l t g) P = typOff heap P := typOff_modify
  refine h.mono (by rw [e]; exact Typing.Extends.refl _) (fun l₁ d₁ h₁ => ?_) fun _ _ h₁ => .inl h₁
  simp only [Heap.modify, Array.getElem?_modify] at h₁
  split at h₁
  · obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h₁
    by_cases ht : d.1 = t
    · subst ht
      rw [dite_eq_left rfl, e]
      exact .inr (hg _ (h.cells _ _ hd))
    · rw [dite_eq_right ht]
      exact .inl hd
  · exact .inl h₁

/-- Both heaps updated alike at a location off the promoted cells still agree. -/
theorem HeapRel.modify {P : List Nat} {heap heap₁ : Heap M} (hH : HeapRel P heap heap₁) {l : Nat}
    (hl : l ∉ P) (t : Ty) (g : M.interp t → M.interp t) :
    HeapRel P (heap.modify l t g) (heap₁.modify l t g) where
  size := by simp [Heap.modify, hH.size]
  agree l₁ hl₁ := by
    simp only [Heap.modify, Array.getElem?_modify]
    split
    · rename_i he; subst he; rw [hH.agree _ hl]
    · exact hH.agree l₁ hl₁
  bound l₁ hl₁ := by simp only [Heap.modify, Array.size_modify]; exact hH.bound l₁ hl₁
  caps := hH.caps

/-- Both heaps with the same new captures cell still agree. -/
theorem HeapRel.capture {P : List Nat} {heap heap₁ : Heap M} (hH : HeapRel P heap heap₁)
    (ds : List (Dyn M.interp)) : HeapRel P (heap.capture ds) (heap₁.capture ds) where
  size := hH.size
  agree := hH.agree
  bound := hH.bound
  caps := by simp [Heap.capture, hH.caps]

/-- A cell whose content facts name is a location of the heap. -/
theorem Sound.cellLocs_lt {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (hS : Sound A P F env env₁ heap) {l : Nat} (hl : cellLocs env F l) :
    l < heap.cells.size ∧ l ∈ P := by
  obtain ⟨u, c, hm, hr⟩ := hl
  obtain ⟨l₁, d, hr₁, hP, hd, -⟩ := hS.holds _ hm
  obtain rfl := hr₁.unique hr
  exact ⟨(Array.getElem?_eq_some_iff.mp hd).1, hP⟩

/-- Rebinding the source's `d` keeps the cells the other facts may write. -/
theorem promLocs_dropSrc {env : Array (Dyn M.interp)} {F : List Fact} {d : Nat} {x : Dyn M.interp}
    {hd : d < env.size} {l : Nat} (h : promLocs (env.set d x hd) (dropSrc d F) l) :
    promLocs env F l := by
  obtain ⟨c, hm, t, y, hy, hl⟩ := h
  obtain ⟨hm₁, hc⟩ := mem_dropSrc.mp hm
  exact ⟨c, hm₁, t, y, (Array.getElem?_set_ne _ (Ne.symm hc)).symm.trans hy, hl⟩

/-- An instruction that binds `d` keeps the cells the facts may write. -/
theorem promLocs_after {env : Array (Dyn M.interp)} {F : List Fact} {d : Nat} {x : Dyn M.interp}
    {hd : d < env.size} {l : Nat} (h : promLocs (env.set d x hd) (after d F) l) :
    promLocs env F l := by
  obtain ⟨c, hm, hr⟩ := h
  rcases List.mem_cons.mp hm with e | hm
  · exact nomatch e
  · exact promLocs_dropSrc ⟨c, (mem_dropTgt.mp hm).1, hr⟩

/-- Facts without some contents may write the same cells. -/
theorem promLocs_dropCells {env : Array (Dyn M.interp)} {F : List Fact} {Wr : List Nat} {l : Nat}
    (h : promLocs env (dropCells Wr F) l) : promLocs env F l := by
  obtain ⟨c, hm, hr⟩ := h
  exact ⟨c, (List.mem_filter.mp hm).1, hr⟩

/-- Facts without some contents hold the contents of no other cells. -/
theorem cellLocs_dropCells {env : Array (Dyn M.interp)} {F : List Fact} {Wr : List Nat} {l : Nat}
    (h : cellLocs env (dropCells Wr F) l) : cellLocs env F l := by
  obtain ⟨u, c, hm, hr⟩ := h
  exact ⟨u, c, (List.mem_filter.mp hm).1, hr⟩

/-! ## Entering a body -/

/-- The entry frames of a region pair, in stores whose facts `F` hold, on one valid payload,
satisfy the entry facts their parameters' binding establishes, and promote no cell `F` does
not. -/
theorem region_frameOK {P : List Nat} {heap : Heap M} {F : List Fact}
    {env env₁ : Array (Dyn M.interp)} (hS : Sound A P F env env₁ heap) {g g₁ : LBody M}
    {b b₁ : LBlock M} {E : Nat → List Fact} (hB : BodyOK X g g₁ E) (hb : g.blocks[0]? = some b)
    (hb₁ : g₁.blocks[0]? = some b₁) {ts : List Ty} (xs : Args M.interp ts)
    (hxs : ∀ d ∈ Args.toList xs, A.DynOK (typOff heap P) d)
    (hn : (b.params.map (·.1)).Nodup) (hn₁ : (b₁.params.map (·.1)).Nodup)
    (hl : ts.length = b.params.length) (hl₁ : ts.length = b₁.params.length)
    (hE : ∀ φ ∈ E 0, Established F b.params b₁.params [] [] φ)
    (hle : g.slots ≤ env.size) (hle₁ : g₁.slots ≤ env₁.size) (hp : ParamsFit g b)
    (hp₁ : ParamsFit g₁ b₁) :
    FrameOK A X P heap (E 0) (Frame.entry g b env [] xs hle hp)
      (Frame.entry g₁ b₁ env₁ [] xs hle₁ hp₁) ∧
      ∀ l, promLocs (Frame.entry g b env [] xs hle hp).env (E 0) l → promLocs env F l := by
  obtain ⟨h0, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨h0₁, rfl⟩ := Array.getElem?_eq_some_iff.mp hb₁
  obtain ⟨hj₁, hcode⟩ := hB 0 h0
  obtain ⟨hS₁, hsub⟩ := established_sound A hS xs hxs (args := []) (args₁ := []) trivial trivial _ _
    hn hn₁ (by rw [List.length_nil, Nat.zero_add]; exact hl)
    (by rw [List.length_nil, Nat.zero_add]; exact hl₁) hE
  exact ⟨⟨E, hB, hcode, hS₁⟩, hsub⟩

/-- The entry frames of a certified function pair, in fresh stores, on the same valid values,
satisfy the entry facts, which promote no cell. -/
theorem start_frameOK {P : List Nat} {heap : Heap M} {fn fn₁ : LBody M} {b b₁ : LBlock M}
    {E : Nat → List Fact} (hB : BodyOK X fn fn₁ E)
    (hst : StartOK (paramsOf fn 0) (paramsOf fn₁ 0) (E 0))
    (hb : fn.blocks[0]? = some b) (hb₁ : fn₁.blocks[0]? = some b₁) {ds : List (Dyn M.interp)}
    {ts : List Ty} (xs : Args M.interp ts)
    (hds : ∀ d ∈ ds ++ Args.toList xs, A.DynOK (typOff heap P) d)
    (hl : ds.length + ts.length = b.params.length) (hl₁ : ds.length + ts.length = b₁.params.length)
    {env env₁ : Array (Dyn M.interp)} (hle : fn.slots ≤ env.size) (hle₁ : fn₁.slots ≤ env₁.size)
    (hp : ParamsFit fn b) (hp₁ : ParamsFit fn₁ b₁) :
    FrameOK A X P heap (E 0) (Frame.entry fn b env ds xs hle hp)
      (Frame.entry fn₁ b₁ env₁ ds xs hle₁ hp₁) ∧
      ∀ l, ¬ promLocs (Frame.entry fn b env ds xs hle hp).env (E 0) l := by
  obtain ⟨h0, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨h0₁, rfl⟩ := Array.getElem?_eq_some_iff.mp hb₁
  obtain ⟨hj₁, hcode⟩ := hB 0 h0
  have hps : paramsOf fn 0 = (fn.blocks[0]'h0).params := by
    rw [paramsOf, Array.getElem?_eq_getElem h0, Option.map_some, Option.getD_some]
  have hps₁ : paramsOf fn₁ 0 = (fn₁.blocks[0]'h0₁).params := by
    rw [paramsOf, Array.getElem?_eq_getElem h0₁, Option.map_some, Option.getD_some]
  rw [hps, hps₁] at hst
  obtain ⟨-, hn, hn₁, hE⟩ := hst
  refine ⟨⟨E, hB, hcode, ?_, ?_⟩, ?_⟩
  · intro φ hφ
    obtain ⟨k, hk, hk₁, rfl⟩ := hE φ hφ
    have e := bindSite_param env _ ds xs (fun p hp₂ => Nat.lt_of_lt_of_le (hp p hp₂) hle) hn hl k hk
    have e₁ := bindSite_param env₁ _ ds xs (fun p hp₂ => Nat.lt_of_lt_of_le (hp₁ p hp₂) hle₁) hn₁
      hl₁ k hk₁
    have hka : k < (ds ++ Args.toList xs).length := by
      rw [List.length_append, Args.length_toList]; omega
    exact ⟨_, e.trans (List.getElem?_eq_getElem hka), e₁.trans (List.getElem?_eq_getElem hka),
      hds _ (List.getElem_mem hka)⟩
  · intro φ hφ _ _ _ _ _ h₀
    obtain ⟨k, hk, hk₁, rfl⟩ := hE φ hφ
    exact nomatch h₀
  · rintro l ⟨c, hc, -⟩
    obtain ⟨k, hk, hk₁, he⟩ := hE _ hc
    exact nomatch he

/-! ## Steps that correspond -/

/-- The measure: a state about to run an instruction has its block's rest's length, plus
one; any other has none. -/
def measure (s : State M) : Nat :=
  match s.mode with
  | .exec => s.core.top.code.length + 1
  | _ => 0

section
variable (A X) {B B₁ : Ty}

/-- What corresponds between two cores, besides their pending transitions: the world, the
heaps, the source's values off `P`, and the waiting frames. -/
structure CoreRel (P : List Nat) (Fs : List (List Fact)) (c c₁ : Core M) : Prop where
  world : c₁.world = c.world
  heap : HeapRel P c.heap c₁.heap
  inv : HeapInv A P c.heap
  wok : (typOff c.heap P).AllValid (A.world c.world)
  stack : StackRel A X P c.heap Fs c.conts c₁.conts

/-- Corresponding cores, pending transitions and frames, with the same choices drawn. -/
theorem Rel.of {P : List Nat} {Fs : List (List Fact)} {c c₁ : Core M}
    {L : List (Array (Dyn M.interp) × List Fact)} {mode mode₁ : Mode M} {drawn : Nat}
    (hC : CoreRel A X P Fs c c₁) (hm : ModeRel A X P c.heap c c₁ L mode mode₁)
    (hD : Disjoint (L ++ stackFacts Fs c.conts)) :
    Rel A X ⟨c, mode, drawn, ()⟩ ⟨c₁, mode₁, drawn, ()⟩ :=
  ⟨rfl, hC.world, P, L, Fs, hC.heap, hC.inv, hC.wok, hm, hC.stack, hD⟩

variable {A X} (hwf₁ : WF X.m₁) (oracle : Nat → Nat)

/-- Cores that correspond still do with other top frames. -/
theorem CoreRel.withTop {P : List Nat} {Fs : List (List Fact)} {c c₁ : Core M}
    (hC : CoreRel A X P Fs c c₁) (f f₁ : Frame M) :
    CoreRel A X P Fs { c with top := f } { c₁ with top := f₁ } :=
  ⟨hC.world, hC.heap, hC.inv, hC.wok, hC.stack⟩

/-- Transfers that `NextRel` relates lead to states that correspond. -/
theorem transfer_lock {s s₁ : State M} {P : List Nat} {Fs : List (List Fact)} {F : List Fact}
    {c c₁ : Core M} {n n₁ : Next M} (hn : NextOK X.m c.top n)
    (hK : ContsOK X.m B c.top.func.ret c.conts)
    (hn₁ : NextOK X.m₁ c₁.top n₁) (hK₁ : ContsOK X.m₁ B₁ c₁.top.func.ret c₁.conts) {drawn : Nat}
    {ev ev₁ : Event} (hC : CoreRel A X P Fs c c₁)
    (hD : Disjoint ((c.top.env, F) :: stackFacts Fs c.conts))
    (hr : NextRel A X P c.heap c.top.env F n n₁) :
    Diagram hwf₁ oracle (Rel A X) measure Wrong s s₁ (transfer c n hn hK drawn ev)
      (transfer c₁ n₁ hn₁ hK₁ drawn ev₁) := by
  cases n with
  | frame g =>
    cases n₁ with
    | frame g₁ =>
      obtain ⟨F₁, hF, hsub⟩ := hr
      exact .next (Rel.of A X hC (.jump hF) (hD.sub hsub))
    | leave _ => exact hr.elim
  | leave v =>
    cases n₁ with
    | frame _ => exact hr.elim
    | leave v₁ =>
      obtain ⟨rfl, hv⟩ := hr
      exact .next (Rel.of A X hC (.ret hv) hD.2)

end

/-! ## Calls -/

section

/-- The promoted cells of a region's facts are the ones it may write, promoted by its
operation's facts. -/
theorem mem_regFacts_prom {Wr : List Nat} {F : List Fact} {c : Nat}
    (h : Fact.prom c ∈ regFacts Wr F) : c ∈ Wr ∧ Fact.prom c ∈ F := by
  simp only [regFacts, dropCells, List.mem_filter] at h
  exact ⟨List.contains_iff_mem.mp h.2, h.1.1⟩

/-- A function's parameters' tags are its entry block's. -/
theorem WF.params_entry {m : LModule M} (hwf : WF m) {i : Nat} (hi : i < m.funcs.size) :
    (m.funcs[i]'hi).params =
      ((m.funcs[i]'hi).blocks[0]'(hwf.entry (Array.getElem_mem hi))).paramTys := by
  obtain ⟨⟨b, hb, -, hps, -⟩, -⟩ := hwf.func (Array.getElem_mem hi)
  rw [hps, Option.some.inj ((Array.getElem?_eq_getElem _).symm.trans hb)]

variable (hok : ModOK X)
include hok

/-- A certified promotion keeps every function's name, parameters' tags and result tag. -/
private theorem ModOK.sameSigs : SameSigs X.m X.m₁ where
  size := hok.funcs_size
  sig i hi _ :=
    let ⟨_, _, _, _, hn, hps, hrt⟩ := hok.funcs i hi
    ⟨hn, hps, hrt⟩

/-- A call of function `idx` on valid values starts frames that correspond, with facts that
promote no cell. -/
theorem callFrame_ok (hwf : WF X.m) (hwf₁ : WF X.m₁) {P : List Nat} {heap : Heap M}
    {idx idx₁ : Nat} (hl : idx < X.m.funcs.size) (hl₁ : idx₁ < X.m₁.funcs.size) (hi : idx = idx₁)
    {ds ds₁ : List (Dyn M.interp)} (hds₁ : ds = ds₁) {ts : List Ty} (xs : Args M.interp ts)
    (hds : ∀ d ∈ ds ++ Args.toList xs, A.DynOK (typOff heap P) d)
    (hp : (X.m.funcs[idx]'hl).params = ds.map (·.1) ++ ts) :
    ∃ F₀, FrameOK A X P heap F₀ (callFrame hwf idx hl ds xs) (callFrame hwf₁ idx₁ hl₁ ds₁ xs) ∧
      ∀ l, ¬ promLocs (callFrame hwf idx hl ds xs).env F₀ l := by
  subst hi hds₁
  obtain ⟨hl₂, E, hB, hst, -, hps, -⟩ := hok.funcs idx hl
  have h0 := hwf.entry (Array.getElem_mem hl)
  have h0₁ := hwf₁.entry (Array.getElem_mem hl₁)
  have e := (WF.params_entry hwf hl).symm.trans hp
  have e₁ := (WF.params_entry hwf₁ hl₁).symm.trans (hps.trans hp)
  have hlen : ds.length + ts.length = ((X.m.funcs[idx]'hl).blocks[0]'h0).params.length := by
    have := congrArg List.length e
    simp only [LBlock.paramTys, List.length_map, List.length_append] at this
    omega
  have hlen₁ : ds.length + ts.length = ((X.m₁.funcs[idx]'hl₁).blocks[0]'h0₁).params.length := by
    have := congrArg List.length e₁
    simp only [LBlock.paramTys, List.length_map, List.length_append] at this
    omega
  exact ⟨E 0, start_frameOK hB hst (Array.getElem?_eq_getElem h0) (Array.getElem?_eq_getElem h0₁)
    xs hds hlen hlen₁ (fresh_fits _) (fresh_fits _) (WF.entryFits hwf (Array.getElem_mem hl) h0)
    (WF.entryFits hwf₁ (Array.getElem_mem hl₁) h0₁)⟩

end

/-! ## A rule's tree, continued -/

section
variable {B B₁ : Ty} (hwf : WF X.m) (hwf₁ : WF X.m₁) (hok : ModOK X) (oracle : Nat → Nat)

/-- The parameters of a body's block, as `paramsOf` gives them. -/
theorem paramsOf_eq {g : LBody M} {j : Nat} (hj : j < g.blocks.size) :
    paramsOf g j = (g.blocks[j]'hj).params := by
  rw [paramsOf, Array.getElem?_eq_getElem hj, Option.map_some, Option.getD_some]

/-- A region's entry block takes as many parameters as its signature's. -/
theorem InstOK.region_params {m : LModule M} {f : Frame M} {i : Inst M} (h : InstOK m f i)
    (j : Fin i.rs.length) :
    (i.rs.get j).1.length =
      ((m.regions[i.region j h.length]'(h.region_lt j)).blocks[0]'
        (h.region_entry j)).params.length := by
  obtain ⟨_, _, hc⟩ := h.region_ok j
  obtain ⟨g, b, hg, hb, hps, -⟩ := checkRegion_eq_ok.mp hc
  obtain rfl : m.regions[i.region j h.length]'(h.region_lt j) = g :=
    Option.some.inj ((Array.getElem?_eq_getElem (h.region_lt j)).symm.trans hg)
  obtain rfl : (m.regions[i.region j h.length]'(h.region_lt j)).blocks[0]'(h.region_entry j) = b :=
    Option.some.inj ((Array.getElem?_eq_getElem (h.region_entry j)).symm.trans hb)
  rw [← hps, LBlock.paramTys, List.length_map]

/-- What a closure captured is valid off the promoted cells. -/
theorem HeapInv.captures {P : List Nat} {heap : Heap M} (h : HeapInv A P heap) {captured : Nat}
    {caps : List (Dyn M.interp)} (hc : heap.captures? captured = some caps) :
    ∀ d ∈ caps, A.DynOK (typOff heap P) d := by
  unfold Heap.captures? at hc
  split at hc
  · cases hc; intro d hd; exact nomatch hd
  · exact h.caps _ _ hc

include hok in
/-- The region frames that a request of region `kk` starts, in frames whose facts hold, on one
valid payload, correspond, with the region's entry facts, which promote no cell but those the
region may write. -/
theorem regionStart_ok {P : List Nat} {heap : Heap M} {F : List Fact} {Wr : List Nat}
    {f f₁ : Frame M} (hS : Sound A P F f.env f₁.env heap) {kk : Nat}
    (hR : RegionOK X (regFacts Wr F) kk) (hk : kk < X.m.regions.size)
    (hb : 0 < (X.m.regions[kk]'hk).blocks.size) (hs : (X.m.regions[kk]'hk).slots ≤ f.func.slots)
    (hp : ParamsFit (X.m.regions[kk]'hk) ((X.m.regions[kk]'hk).blocks[0]'hb))
    (hk₁ : kk < X.m₁.regions.size) (hb₁ : 0 < (X.m₁.regions[kk]'hk₁).blocks.size)
    (hs₁ : (X.m₁.regions[kk]'hk₁).slots ≤ f₁.func.slots)
    (hp₁ : ParamsFit (X.m₁.regions[kk]'hk₁) ((X.m₁.regions[kk]'hk₁).blocks[0]'hb₁))
    {ts : List Ty} (args : Args M.interp ts)
    (hargs : ∀ d ∈ Args.toList args, A.DynOK (typOff heap P) d)
    (hl : ts.length = ((X.m.regions[kk]'hk).blocks[0]'hb).params.length)
    (hl₁ : ts.length = ((X.m₁.regions[kk]'hk₁).blocks[0]'hb₁).params.length) :
    FrameOK A X P heap (X.ER kk 0) (regionStart X.m f kk hk hb hs hp args)
        (regionStart X.m₁ f₁ kk hk₁ hb₁ hs₁ hp₁ args) ∧
      ∀ l, promLocs (regionStart X.m f kk hk hb hs hp args).env (X.ER kk 0) l →
        promLocs f.env (regFacts Wr F) l := by
  obtain ⟨g, g₁, hg, hg₁, hn, hn₁, hE⟩ := hR
  obtain rfl : X.m.regions[kk]'hk = g :=
    Option.some.inj ((Array.getElem?_eq_getElem hk).symm.trans hg)
  obtain rfl : X.m₁.regions[kk]'hk₁ = g₁ :=
    Option.some.inj ((Array.getElem?_eq_getElem hk₁).symm.trans hg₁)
  obtain ⟨_, hBr⟩ := hok.regions kk hk
  rw [paramsOf_eq hb] at hn hE
  rw [paramsOf_eq hb₁] at hn₁ hE
  exact region_frameOK (hS.sub fun φ hφ => (List.mem_filter.mp (List.mem_filter.mp hφ).1).1) hBr
    (Array.getElem?_eq_getElem hb) (Array.getElem?_eq_getElem hb₁) args hargs hn hn₁ hl hl₁ hE
    (Nat.le_trans hs f.fits) (Nat.le_trans hs₁ f₁.fits) hp hp₁

include hok in
/-- **A rule's tree, continued alike**: in frames whose facts hold, a tree that respects the
typing off `P` leads, in the source and in the target, to states that correspond. -/
theorem settle_lock {s s₁ : State M} {P : List Nat} {Fs : List (List Fact)} {F : List Fact}
    {c c₁ : Core M} {i : Inst M} {pc₁ : Nat} {succs₁ : List LSite} {args₁ : List Nat}
    (hi : InstOK X.m c.top i) (hK : ContsOK X.m B c.top.func.ret c.conts)
    (hi₁ : InstOK X.m₁ c₁.top (mkInst i pc₁ succs₁ args₁))
    (hK₁ : ContsOK X.m₁ B₁ c₁.top.func.ret c₁.conts)
    {drawn : Nat} {ev ev₁ : Event} (hC : CoreRel A X P Fs c c₁)
    (hD : Disjoint ((c.top.env, F) :: stackFacts Fs c.conts))
    (hp : PendOK A X P c.heap F c.top c₁.top i succs₁ args₁) {t t₁ : i.Tree} (he : t₁ = t)
    (ht : A.TreeOK (A.StOK i.rerun.key) (typOff c.heap P) i.ret t) :
    Diagram hwf₁ oracle (Rel A X) measure Wrong s s₁ (settle hwf c i hi hK drawn ev t)
      (settle hwf₁ c₁ (mkInst i pc₁ succs₁ args₁) hi₁ hK₁ drawn ev₁ t₁) := by
  have hp₀ := hp
  obtain ⟨E, Wr, hB, hS, hWr, hWc, hargs, hsites, hregs, hag, hnext⟩ := hp
  subst he
  refine hok.sameSigs.settle_rec₂ hC.heap.caps
    (P := fun t r r₁ => A.TreeOK (A.StOK i.rerun.key) (typOff c.heap P) i.ret t →
      Diagram hwf₁ oracle (Rel A X) measure Wrong s s₁ r r₁)
    (fun a ht => ?_) (fun e ht => ?_) (fun st ht => ?_) (fun _ _ _ => ?_)
    (fun j args k ht => ?_) (fun sig idx captured args k caps hco hco₁ ht => ?_)
    (fun _ ht => ?_) _ ht
  · obtain ⟨op, pc, dst, ret, ps, rs, regs, succs, rerun⟩ := i
    cases ret with
    | none => exact nomatch a
    | some r =>
      refine .next (Rel.of A X (hC.withTop _ _) (.exec (F := after dst F) ⟨E, hB, hnext r rfl, ?_⟩)
        (hD.sub fun l h => promLocs_after (by simp only [Frame.bind] at h; exact h)))
      have hv : A.ResOK (typOff c.heap P) (some r) a := A.treeOK_ret.mp ht
      simp only [Frame.bind]
      exact hS.bind (resDyn (some r) a) hv _ _
  · exact transfer_lock hwf₁ oracle _ _ _ _ hC hD
      (exitTo_rel A X hB hS e (A.treeOK_jump.mp ht) _ _ hsites)
  · exact .next (Rel.of A X hC (.again st hp₀ (A.treeOK_jump.mp ht)) hD)
  · exact .next (Rel.of A X hC (.done _) hD.2)
  · have hsat := A.treeOK_vis.mp ht
    obtain ⟨hfr, hsub⟩ := regionStart_ok hok hS (hregs _ (List.getElem_mem _)) (hi.region_lt j)
      (hi.region_entry j) (hi.region_fits j).1 (hi.region_fits j).2 (hi₁.region_lt j)
      (hi₁.region_entry j) (hi₁.region_fits j).1 (hi₁.region_fits j).2 args
      (Accounts.argsOK_toList hsat.1) (InstOK.region_params hi j) (InstOK.region_params hi₁ j)
    refine .next (Rel.of A X hC
      (.call hfr (.rule hp₀ fun S₁ he o ho => hsat.2 S₁ he o ho))
      ⟨fun l hl q hq => ?_, hD⟩)
    obtain ⟨c₀, hc₀, hr₀⟩ := hsub l hl
    obtain ⟨hcW, hcF⟩ := mem_regFacts_prom hc₀
    rcases List.mem_cons.mp hq with rfl | hq
    · rintro ⟨u, c₂, hc₂, hr₂⟩
      exact hS.distinct _ hcF _ hc₂ c₀ c₂ l rfl rfl (fun e => hWc u c₂ hc₂ (e ▸ hcW)) hr₀ hr₂
    · exact hD.head l ⟨c₀, hcF, hr₀⟩ q hq
  · have hsat := A.treeOK_vis.mp ht
    have hv : ∀ d ∈ caps ++ Args.toList (Args.ofPayload sig.1 args),
        A.DynOK (typOff c.heap P) d := by
      intro d hd
      rcases List.mem_append.mp hd with hd | hd
      · exact hC.inv.captures hco.2.1 d hd
      · exact Accounts.argsOK_toList hsat.1.2 d hd
    obtain ⟨F₀, hfr, hnp⟩ := callFrame_ok hok hwf hwf₁ hco.1 hco₁.1 rfl rfl _ hv hco.2.2.1
    exact .next (Rel.of A X hC
      (.call hfr (.rule hp₀ fun S₁ he o ho => hsat.2 S₁ he o ho))
      ⟨fun l hl => (hnp l hl).elim, hD⟩)
  · exact .next (Rel.of A X hC (.request _ hp₀ ht) hD)

end

section
variable {B B₁ : Ty} (hwf : WF X.m) (hwf₁ : WF X.m₁) (hok : ModOK X) (oracle : Nat → Nat)

/-- The value the machine reads from a cell of the source's heap is valid off `P`. -/
theorem HeapInv.valueAt {P : List Nat} {heap : Heap M} (h : HeapInv A P heap) {l : Nat} {t : Ty}
    (hl : l < heap.cells.size) (ht : (heap.cells[l]'hl).1 = t) :
    A.ValOK (typOff heap P) t (heap.valueAt hl ht) := by
  have hd := h.cells l _ (Array.getElem?_eq_getElem hl)
  have e := sigma_cast (heap.cells[l]'hl) ht
  unfold Accounts.DynOK at hd
  rw [← e] at hd
  exact hd

/-- Heaps that agree at a location read the same value there. -/
theorem HeapRel.valueAt_eq {P : List Nat} {heap heap₁ : Heap M} (hH : HeapRel P heap heap₁)
    {l : Nat} (hlP : l ∉ P) {t : Ty} (hl : l < heap.cells.size) (ht : (heap.cells[l]'hl).1 = t)
    (hl₁ : l < heap₁.cells.size) (ht₁ : (heap₁.cells[l]'hl₁).1 = t) :
    heap₁.valueAt hl₁ ht₁ = heap.valueAt hl ht := by
  have e := hH.get_eq hlP hl hl₁
  unfold Heap.valueAt
  have key : ∀ (d₁ d : Dyn M.interp) (p₁ : d₁.1 = t) (p : d.1 = t), d₁ = d →
      cast (congrArg M.interp p₁) d₁.2 = cast (congrArg M.interp p) d.2 := by
    intro d₁ d p₁ p he
    subst he
    rfl
  exact key _ _ ht₁ ht e

include hok in
/-- **Answering a rule's world or cell request alike**: a tree that respects the typing off `P`
asks for no promoted cell, so the machine answers it in the source as in the target, and the
states they lead to correspond. -/
theorem serve_lock {s s₁ : State M} {P : List Nat} {Fs : List (List Fact)} {F : List Fact}
    {c c₁ : Core M} {i : Inst M} {pc₁ : Nat} {succs₁ : List LSite} {args₁ : List Nat}
    (h : InstOK X.m c.top i ∧ ContsOK X.m B c.top.func.ret c.conts)
    (h₁ : InstOK X.m₁ c₁.top (mkInst i pc₁ succs₁ args₁) ∧
      ContsOK X.m₁ B₁ c₁.top.func.ret c₁.conts) {drawn : Nat}
    (hC : CoreRel A X P Fs c c₁) (hD : Disjoint ((c.top.env, F) :: stackFacts Fs c.conts))
    (hp : PendOK A X P c.heap F c.top c₁.top i succs₁ args₁) (t : i.Tree)
    (ht : A.TreeOK (A.StOK i.rerun.key) (typOff c.heap P) i.ret t) :
    Diagram hwf₁ oracle (Rel A X) measure Wrong s s₁ (serve hwf oracle c i t h drawn)
      (serve hwf₁ oracle c₁ (mkInst i pc₁ succs₁ args₁) t h₁ drawn) := by
  cases t with
  | choose k =>
    simp only [serve]
    exact settle_lock hwf hwf₁ hok oracle _ _ _ _ hC hD hp rfl (A.treeOK_choose.mp ht _)
  | update f =>
    obtain ⟨top, conts, heap, w⟩ := c
    obtain ⟨top₁, conts₁, heap₁, w₁⟩ := c₁
    have hw : w₁ = w := hC.world
    subst hw
    have hu := (A.treeOK_update.mp ht) w₁ hC.wok
    simp only [serve]
    exact settle_lock hwf hwf₁ hok oracle (c := ⟨top, conts, heap, (f w₁).1⟩)
      (c₁ := ⟨top₁, conts₁, heap₁, (f w₁).1⟩) _ _ _ _ ⟨rfl, hC.heap, hC.inv, hu.1, hC.stack⟩ hD hp
      rfl hu.2
  | ret a =>
    simp only [serve]
    exact settle_lock hwf hwf₁ hok oracle _ _ _ _ hC hD hp rfl ht
  | stop s =>
    simp only [serve]
    exact settle_lock hwf hwf₁ hok oracle _ _ _ _ hC hD hp rfl ht
  | vis q k =>
    have hsat := A.treeOK_vis.mp ht
    cases q with
    | region j args =>
      simp only [serve]
      exact settle_lock hwf hwf₁ hok oracle _ _ _ _ hC hD hp rfl ht
    | call sig idx captured args =>
      simp only [serve]
      exact settle_lock hwf hwf₁ hok oracle _ _ _ _ hC hD hp rfl ht
    | new ty v =>
      simp only [serve]
      have hsz := hC.heap.size
      have hst : HeapStep P P c.heap (c.heap.push ⟨ty, v⟩) (fun _ => False) :=
        .of_frame hC.heap.bound (typOff_push _ (.inr rfl)) (HeapFrame.push _)
      have hval : (typOff (c.heap.push ⟨ty, v⟩) P).Valid c.heap.cells.size ty :=
        typOff_valid.mpr ⟨fun hm => Nat.lt_irrefl _ (hC.heap.bound _ hm),
          by simp [Heap.push], by simp [Heap.push]⟩
      refine settle_lock hwf hwf₁ hok oracle (c := { c with heap := c.heap.push ⟨ty, v⟩ })
        (c₁ := { c₁ with heap := c₁.heap.push ⟨ty, v⟩ }) _ _ _ _
        ⟨hC.world, hC.heap.push _, hC.inv.push _ (.inr rfl) hsat.1,
          Typing.AllValid.mono hst.typ hC.wok, hC.stack.stepOff hst⟩ hD
        (hp.step hst fun _ _ h => h) (by rw [hsz]) (hsat.2 _ hst.typ _ hval)
    | get ty l =>
      obtain ⟨hlP, hl, htl⟩ := typOff_valid.mp hsat.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      have hh₁ : c₁.heap.Holds l ty := (hC.heap.holds_iff hlP ty).mpr hh
      simp only [serve]
      rw [Heap.cell_pos hh, Heap.cell_pos hh₁]
      exact settle_lock hwf hwf₁ hok oracle _ _ _ _ hC hD hp
        (by rw [hC.heap.valueAt_eq hlP hh.lt hh.code hh₁.lt hh₁.code])
        (hsat.2 _ (Typing.Extends.refl _) _ (hC.inv.valueAt hh.lt hh.code))
    | set ty l v =>
      obtain ⟨hlP, hl, htl⟩ := typOff_valid.mp hsat.1.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      have hh₁ : c₁.heap.Holds l ty := (hC.heap.holds_iff hlP ty).mpr hh
      simp only [serve]
      rw [Heap.cell_pos hh, Heap.cell_pos hh₁]
      have e := typOff_set (P := P) (d := ⟨ty, v⟩) hh.lt hh.code.symm
      have hst : HeapStep P P c.heap (c.heap.set l ⟨ty, v⟩ hh.lt) (fun _ => False) :=
        .of_frame hC.heap.bound (by rw [e]; exact Typing.Extends.refl _)
          (HeapFrame.set hh.lt hsat.1.1 _)
      exact settle_lock hwf hwf₁ hok oracle (c := { c with heap := c.heap.set l ⟨ty, v⟩ hh.lt })
        (c₁ := { c₁ with heap := c₁.heap.set l ⟨ty, v⟩ hh₁.lt }) _ _ _ _
        ⟨hC.world, hC.heap.set _ _ _, hC.inv.set _ hh.code.symm hsat.1.2,
          Typing.AllValid.mono hst.typ hC.wok, hC.stack.stepOff hst⟩ hD
        (hp.step hst fun _ _ h => h) rfl (hsat.2 _ hst.typ () trivial)
    | modify ty l g =>
      obtain ⟨hlP, hl, htl⟩ := typOff_valid.mp hsat.1.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      have hh₁ : c₁.heap.Holds l ty := (hC.heap.holds_iff hlP ty).mpr hh
      simp only [serve]
      rw [Heap.cell_pos hh, Heap.cell_pos hh₁, Heap.modifyAt_eq, Heap.modifyAt_eq]
      have e : typOff (c.heap.modify l ty g) P = typOff c.heap P := typOff_modify
      have hst : HeapStep P P c.heap (c.heap.modify l ty g) (fun _ => False) :=
        .of_frame hC.heap.bound (by rw [e]; exact Typing.Extends.refl _)
          (HeapFrame.modify hsat.1.1 _)
      exact settle_lock hwf hwf₁ hok oracle (c := { c with heap := c.heap.modify l ty g })
        (c₁ := { c₁ with heap := c₁.heap.modify l ty g }) _ _ _ _
        ⟨hC.world, hC.heap.modify hlP _ _, hC.inv.modify hsat.1.2,
          Typing.AllValid.mono hst.typ hC.wok, hC.stack.stepOff hst⟩ hD
        (hp.step hst fun _ _ h => h) rfl (hsat.2 _ hst.typ () trivial)
    | bind ty v sig idx captured =>
      simp only [serve]
      refine hok.sameSigs.callee_rec₂ hC.heap.caps rfl rfl (fun caps hco hco₁ => ?_) fun e => ?_
      · have hds : ∀ d ∈ caps ++ [⟨ty, v⟩], A.DynOK (typOff c.heap P) d := by
          intro d hd
          rcases List.mem_append.mp hd with hd | hd
          · exact hC.inv.captures hco.2.1 d hd
          · rw [List.mem_singleton.mp hd]; exact hsat.1.2
        have hst : HeapStep P P c.heap (c.heap.capture (caps ++ [⟨ty, v⟩])) (fun _ => False) :=
          .of_frame hC.heap.bound (typOff_capture _) (HeapFrame.capture _)
        exact settle_lock hwf hwf₁ hok oracle
          (c := { c with heap := c.heap.capture (caps ++ [⟨ty, v⟩]) })
          (c₁ := { c₁ with heap := c₁.heap.capture (caps ++ [⟨ty, v⟩]) }) _ _ _ _
          ⟨hC.world, hC.heap.capture _, hC.inv.capture _ hds,
            Typing.AllValid.mono hst.typ hC.wok, hC.stack.stepOff hst⟩ hD
          (hp.step hst fun _ _ h => h) (by rw [hC.heap.caps])
          (hsat.2 _ hst.typ _ (typOff_capture_valid _))
      · exact e ▸ .next (Rel.of A X hC (.done _) hD.2)

end

/-! ## One step -/

section
variable {B B₁ : Ty}

/-- The facts without some contents, again without them, are the same. -/
private theorem dropCells_idem (Wr : List Nat) (F : List Fact) :
    dropCells Wr (dropCells Wr F) = dropCells Wr F := by
  unfold dropCells
  rw [List.filter_filter]
  congr 1
  funext φ
  cases φ <;> simp

/-- The rule of an operation certified with the write set `Wr`, from facts `F`, runs as
`PendOK` says, with the facts without the contents of `Wr`'s cells. -/
private theorem pendOK_of {P : List Nat} {heap : Heap M} {F : List Fact} {f f₁ : Frame M}
    {i : Inst M} {E : Nat → List Fact} {Wr : List Nat} {succs₁ : List LSite} {args₁ : List Nat}
    (hB : BodyOK X f.func f₁.func E) (hS : Sound A P F f.env f₁.env heap) (hWr : WrOK F Wr)
    (ha : ArgsEq (dropCells Wr F) args₁ i.rerun.args)
    (hs : All₂ (SiteOK E f.func f₁.func (dropCells Wr F)) i.succs succs₁)
    (hregs : ∀ k ∈ i.regs, RegionOK X (regFacts Wr F) k) (hag : AgainOK A i)
    (hnext : ∀ r, i.ret = some r →
      CodeOK X E f.func f₁.func (after i.dst (dropCells Wr F)) f.code f.term f₁.code f₁.term) :
    PendOK A X P heap (dropCells Wr F) f f₁ i succs₁ args₁ := by
  refine ⟨E, Wr, hB, hS.sub fun φ hφ => (List.mem_filter.mp hφ).1,
    fun c hc => List.mem_filter.mpr ⟨hWr c hc, rfl⟩, fun u c hm hc => ?_, ha, hs, ?_, hag, hnext⟩
  · have := (List.mem_filter.mp hm).2
    simp only [List.contains_iff_mem.mpr hc] at this
    exact Bool.false_ne_true this
  · intro k hk
    have := hregs k hk
    unfold regFacts at this ⊢
    rwa [dropCells_idem]

end

section
variable {B B₁ : Ty} (hwf : WF X.m) (hwf₁ : WF X.m₁) (hok : ModOK X)
  (hR : ∀ i, X.R i → A.InsnOK i) (hRT : ∀ t, X.RT t → A.TermOK t)

/-- Corresponding cores with new top frames that `FrameOK` relates, about to run. -/
private theorem rel_exec {P : List Nat} {Fs : List (List Fact)} {F : List Fact} {c c₁ : Core M}
    (hC : CoreRel A X P Fs c c₁) {f f₁ : Frame M} (hF : FrameOK A X P c.heap F f f₁)
    (hD : Disjoint ((f.env, F) :: stackFacts Fs c.conts)) {drawn : Nat} :
    Rel A X ⟨{ c with top := f }, .exec, drawn, ()⟩ ⟨{ c₁ with top := f₁ }, .exec, drawn, ()⟩ :=
  Rel.of A X (hC.withTop f f₁) (.exec hF) hD

/-- The stack's frames hold the contents of cells of the heap only. -/
private theorem StackRel.cellLocs_lt {P : List Nat} {heap : Heap M} {Fs : List (List Fact)}
    {ws ws₁ : List (Wait M)} (h : StackRel A X P heap Fs ws ws₁) :
    ∀ q ∈ stackFacts Fs ws, ∀ l, cellLocs q.1 q.2 l → l < heap.cells.size := by
  induction h with
  | nil => exact fun _ hq => nomatch hq
  | cons hw _ ih =>
    intro q hq l hl
    rcases List.mem_cons.mp hq with rfl | hq
    · cases hw with
      | rule hp _ =>
        obtain ⟨_, _, _, hS, _⟩ := hp
        exact (hS.cellLocs_lt hl).1
      | call _ _ hS => exact (hS.cellLocs_lt hl).1
    · exact ih q hq l hl

end

/-- Rebinding the source's and the target's value `d` keeps the facts that do not mention it. -/
theorem Sound.rebind {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {d : Nat} (x x₁ : Dyn M.interp)
    (hd : d < env.size) (hd₁ : d < env₁.size) :
    Sound A P (dropTgt d (dropSrc d F)) (env.set d x hd) (env₁.set d x₁ hd₁) heap := by
  refine h.congr (fun φ hφ => (mem_dropSrc.mp (mem_dropTgt.mp hφ).1).1) (fun φ hφ => ?_)
    (fun φ hφ u hu => ?_) (Nat.le_refl _) (fun _ h => h) (Typing.Extends.refl _)
    (fun _ _ _ _ _ _ _ => rfl)
  · exact Array.getElem?_set_ne _ (Ne.symm (mem_dropSrc.mp (mem_dropTgt.mp hφ).1).2)
  · refine Array.getElem?_set_ne _ fun he => (mem_dropTgt.mp hφ).2 ?_
    rw [hu, he]

/-- A slot that an `eq` fact names and that holds a ref of tag `t` holds one to a cell that is
valid off `P` at `t`, so not to a promoted cell. -/
theorem Sound.eq_valid {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (h : Sound A P F env env₁ heap) {c₁ c : Nat} (hm : Fact.eq c₁ c ∈ F) {t : Ty}
    (ht : HasTy env c (Ty.ref t)) :
    (typOff heap P).Valid (M.locOf (getT env c (Ty.ref t) ht)) t := by
  have hd := h.eq_ok hm _ (Array.getElem?_eq_getElem ht.1)
  have hv : A.ValOK (typOff heap P) (Ty.ref t) (getT env c (Ty.ref t) ht) := by
    unfold getT
    have e := sigma_cast (env[c]'ht.1) (ht.2 ht.1)
    unfold Accounts.DynOK at hd
    rw [← e] at hd
    exact hd
  exact Accounts.valid_of_ref hv

section
variable {B B₁ : Ty} (hwf : WF X.m) (hwf₁ : WF X.m₁) (hok : ModOK X)
  (hR : ∀ i, X.R i → A.InsnOK i) (hRT : ∀ t, X.RT t → A.TermOK t) (oracle : Nat → Nat)
include hok hR hRT

/-- **Running an instruction or a terminator** of frames that `FrameOK` relates. -/
theorem exec_good {P : List Nat} {Fs : List (List Fact)} {F : List Fact} {top top₁ : Frame M}
    {conts conts₁ : List (Wait M)} {heap heap₁ : Heap M} {world : M.W} {drawn : Nat}
    (h : CoreOK X.m B ⟨top, conts, heap, world⟩) (h₁ : CoreOK X.m₁ B₁ ⟨top₁, conts₁, heap₁, world⟩)
    (hC : CoreRel A X P Fs ⟨top, conts, heap, world⟩ ⟨top₁, conts₁, heap₁, world⟩)
    (hD : Disjoint ((top.env, F) :: stackFacts Fs conts)) (hF : FrameOK A X P heap F top top₁) :
    Diagram hwf₁ oracle (Rel A X) measure Wrong ⟨⟨top, conts, heap, world⟩, .exec, drawn, ()⟩
      ⟨⟨top₁, conts₁, heap₁, world⟩, .exec, drawn, ()⟩
      (exec hwf ⟨top, conts, heap, world⟩ h drawn)
      (exec hwf₁ ⟨top₁, conts₁, heap₁, world⟩ h₁ drawn) := by
  obtain ⟨E, hB, hcode, hS⟩ := hF
  obtain ⟨func, code, term, env, blk, pc, fits⟩ := top
  obtain ⟨func₁, code₁, term₁, env₁, blk₁, pc₁, fits₁⟩ := top₁
  simp only at hB hcode hS hD
  cases hcode with
  | term ht =>
    cases ht with
    | case hr ha hs =>
      simp only [exec, execCode, execTerm]
      refine transfer_lock hwf₁ oracle _ _ _ _ hC hD ?_
      rw [applyFn_congr (hS.args_get ha) _ _ _ (h.termReady rfl rfl).1]
      exact exitTo_rel A X hB hS _ (Accounts.FnOK.applyFn _ (hS.args_ok ha) (hRT _ hr _)) _ _ hs
    | sem Wr hr hWr ha hs hregs =>
      simp only [exec, execCode, execTerm]
      have hok₀ := hRT _ hr
      have hS₁ := hS.sub (F₁ := dropCells Wr F) fun φ hφ => (List.mem_filter.mp hφ).1
      refine settle_lock (F := dropCells Wr F) hwf hwf₁ hok oracle _ _ _ _ hC
        (hD.sub (F₁ := dropCells Wr F) fun _ h => promLocs_dropCells h) ?_ ?_ ?_
      · exact pendOK_of hB hS hWr ha hs hregs hok₀.2 fun _ h => nomatch h
      · exact applyFn_congr (hS₁.args_get ha) _ _ _ _
      · exact Accounts.FnOK.applyFn _ (hS₁.args_ok ha) (hok₀.1 _)
  | sem Wr hr hWr ha hs hregs hk =>
    simp only [exec, execCode]
    have hok₀ := hR _ hr
    have hS₁ := hS.sub (F₁ := dropCells Wr F) fun φ hφ => (List.mem_filter.mp hφ).1
    refine settle_lock (F := dropCells Wr F) hwf hwf₁ hok oracle _ _ _ _ (hC.withTop _ _)
      (hD.sub (F₁ := dropCells Wr F) fun _ h => promLocs_dropCells h) ?_ ?_ ?_
    · exact pendOK_of hB hS hWr ha hs hregs hok₀.2 fun _ _ => hk
    · exact applyFn_congr (hS₁.args_get ha) _ _ _ _
    · exact Accounts.FnOK.applyFn _ (hS₁.args_ok ha) (hok₀.1 _)
  | const hr hk =>
    simp only [exec, execCode, Core.next]
    have e := hR _ hr
    refine .next (rel_exec hC ⟨E, hB, hk, ?_⟩ ?_)
    · refine hS.bind _ ?_ (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)
        (Nat.lt_of_lt_of_le (h₁.dst_lt (i := .const _ _) rfl) fits₁)
      unfold Accounts.DynOK Accounts.ValOK
      rw [e]
      exact Typing.allValid_nil _
    · exact hD.sub fun _ h₂ => promLocs_after (hd := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) h₂
  | @pure _ d ts r f args args₁ is is₁ t t₁ hr ha hk =>
    simp only [exec, execCode, Core.next]
    have hv := Accounts.FnOK.applyFn (h.ready rfl) (hS.args_ok ha) (hR _ hr (typOff heap P))
    refine .next (rel_exec hC ⟨E, hB, hk, ?_⟩ ?_)
    · exact hS.bind' (congrArg _ (applyFn_congr (hS.args_get ha) _ _ _ _)) hv
        (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)
        (Nat.lt_of_lt_of_le (h₁.dst_lt (i := .pure d ts r f args₁) rfl) fits₁)
    · exact hD.sub fun _ h₂ => promLocs_after (hd := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) h₂
  | @getProm _ r ty c u is _ _ _ hu hk =>
    simp only [exec, execCode, Core.cellLoc]
    obtain ⟨l, d, hr, hlP, hld, hud⟩ := hS.holds _ hu
    have hl := locOf_getT hr (h.ready rfl)
    by_cases hh : heap.Holds l ty
    · rw [Heap.cell_pos (by rw [hl]; exact hh)]
      have hd : heap.cells[l]'hh.lt = d := by
        rw [Array.getElem?_eq_getElem hh.lt] at hld
        exact Option.some.inj hld
      simp only [Core.refGet, Core.next]
      refine Or.inr ⟨by simp [measure], Rel.of A X ⟨hC.world, hC.heap, hC.inv, hC.wok, hC.stack⟩
        (.exec ⟨E, hB, hk, ?_⟩) (hD.sub fun l₁ h₂ => ?_)⟩
      · refine (hS.bindSrc _ (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)).cons
          ⟨d, ?_, hud, hC.inv.cells l d hld⟩ rfl
        simp only [LInsn.dst, Array.getElem?_set_self, hl, hd]
      · obtain ⟨c₁, hm, hr₁⟩ := h₂
        rcases List.mem_cons.mp hm with e | hm
        · exact nomatch e
        · exact promLocs_dropSrc (hd := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) ⟨c₁, hm, hr₁⟩
    · rw [Heap.cell_neg (by rw [hl]; exact hh)]
      exact Or.inr ⟨by simp [measure], rfl, hC.world, P, [], Fs, hC.heap, hC.inv, hC.wok,
        .wrong ⟨_, rfl⟩, hC.stack, hD.2⟩
  | @setProm _ d ty c v u is _ _ _ hp hu hdc hk =>
    simp only [exec, execCode, Core.cellLoc]
    obtain ⟨l, hr, hlP, hlt⟩ := hS.holds _ hp
    have hl := locOf_getT hr (h.ready rfl).1
    by_cases hh : heap.Holds l ty
    · rw [Heap.cell_pos (by rw [hl]; exact hh)]
      simp only [Core.refSet, Core.next, hl]
      have hvt := CoreOK.refSet_tag h rfl
      have hv : v < env.size := (h.ready rfl).2
      have hx : A.DynOK (typOff heap P) (getD env v hv) :=
        hS.eq_ok hu _ (Array.getElem?_eq_getElem hv)
      have htag : (getD env v hv).1 = (heap.cells[l]'hh.lt).1 := (hvt.2 hv).trans hh.code.symm
      have e := typOff_set (P := P) hh.lt htag
      have hst : HeapStep P P heap (heap.set l (getD env v hv) hh.lt) (· = l) :=
        ⟨by simp [Heap.set], fun _ h => h, by rw [e]; exact Typing.Extends.refl _,
          fun l₁ _ hne => by simp only [Heap.set]; exact Array.getElem?_set_ne _ (Ne.symm hne)⟩
      have hpl : promLocs env F l := ⟨c, hp, hr⟩
      refine Or.inr ⟨by simp [measure], Rel.of A X ⟨hC.world, ?_, hC.inv.set hh.lt htag hx,
        Typing.AllValid.mono hst.typ hC.wok, hC.stack.step hst fun q hq l₁ hl₁ he => ?_⟩
        (.exec ⟨E, hB, hk, ?_⟩) (hD.sub fun l₁ h₂ => ?_)⟩
      · refine ⟨by simpa [Heap.set] using hC.heap.size, fun l₁ hl₁ => ?_, fun l₁ hl₁ => ?_,
          by simpa [Heap.set] using hC.heap.caps⟩
        · rw [hC.heap.agree l₁ hl₁]
          simp only [Heap.set]
          rw [Array.getElem?_set_ne _ (fun he => hl₁ (by rw [← he]; exact hlP))]
        · simp only [Heap.set, Array.size_set]
          exact hC.heap.bound l₁ hl₁
      · exact hD.head l hpl q hq (he ▸ hl₁)
      · have hpm : Fact.prom c ∈ dropSrc d (dropCell c F) :=
          mem_dropSrc.mpr ⟨mem_dropCell.mpr ⟨hp, rfl⟩, Ne.symm hdc⟩
        refine Sound.cons_same ?_ ?_ rfl hpm rfl
        · refine hS.congr (fun φ hφ => (mem_dropCell.mp (mem_dropSrc.mp hφ).1).1)
            (fun φ hφ => Array.getElem?_set_ne (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)
              (Ne.symm (mem_dropSrc.mp hφ).2))
            (fun _ _ _ _ => rfl) (by simp [Heap.set]) (fun _ h => h) hst.typ ?_
          intro φ hφ u₁ c₁ l₁ he hr₁
          subst he
          obtain ⟨hφ₁, hcc⟩ := mem_dropCell.mp (mem_dropSrc.mp hφ).1
          have hne : c₁ ≠ c := fun e => by simp [Fact.isCellOf, e] at hcc
          have hll : l₁ ≠ l := fun e =>
            hS.distinct _ hp _ hφ₁ c c₁ l rfl rfl (Ne.symm hne) hr (e ▸ hr₁)
          simp only [Heap.set]
          exact Array.getElem?_set_ne _ (Ne.symm hll)
        · refine ⟨l, getD env v hv, ?_, hlP, ?_, (hS.eq_get hu).trans (Array.getElem?_eq_getElem _)⟩
          · obtain ⟨t₀, x₀, hx₀, hl₀⟩ := hr
            exact ⟨t₀, x₀,
              (Array.getElem?_set_ne (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) hdc).trans hx₀, hl₀⟩
          · simp only [Heap.set]
            exact Array.getElem?_set_self _
      · obtain ⟨c₁, hm, hr₁⟩ := h₂
        rcases List.mem_cons.mp hm with e | hm
        · exact nomatch e
        · obtain ⟨c₂, hm₂, hr₂⟩ := promLocs_dropSrc (hd := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)
            ⟨c₁, hm, hr₁⟩
          exact ⟨c₂, (mem_dropCell.mp hm₂).1, hr₂⟩
    · rw [Heap.cell_neg (by rw [hl]; exact hh)]
      exact Or.inr ⟨by simp [measure], rfl, hC.world, P, [], Fs, hC.heap, hC.inv, hC.wok,
        .wrong ⟨_, rfl⟩, hC.stack, hD.2⟩
  | @newKept _ d ty v u is _ _ _ hu hk =>
    simp only [exec, execCode, Core.refNew, Core.next]
    have hv : v < env.size := h.ready rfl
    have hu₁ : u < env₁.size := h₁.ready (i := .refNew d ty u) rfl
    have hxx : getD env₁ u hu₁ = getD env v hv := by
      have hx := hS.eq_get hu
      rw [Array.getElem?_eq_getElem hu₁, Array.getElem?_eq_getElem hv] at hx
      exact Option.some.inj hx
    have hx : A.DynOK (typOff heap P) (getD env v hv) :=
      hS.eq_ok hu _ (Array.getElem?_eq_getElem hv)
    have hst : HeapStep P P heap (heap.push (getD env v hv)) (fun _ => False) :=
      .of_frame hC.heap.bound (typOff_push _ (.inr rfl)) (HeapFrame.push _)
    have hval : (typOff (heap.push (getD env v hv)) P).Valid heap.cells.size ty :=
      typOff_valid.mpr ⟨fun hm => Nat.lt_irrefl _ (hC.heap.bound _ hm), by simp [Heap.push],
        by simpa [Heap.push, getD] using (CoreOK.refNew_tag h rfl).2 hv⟩
    have hd₀ : d < env.size := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits
    have hd₁ : d < env₁.size := Nat.lt_of_lt_of_le (h₁.dst_lt (i := .refNew d ty u) rfl) fits₁
    have hnew : A.DynOK (typOff (heap.push (getD env v hv)) P)
        ⟨Ty.ref ty, M.cellAt ty heap.cells.size⟩ := by
      unfold Accounts.DynOK Accounts.ValOK
      rw [A.ref, M.locOf_cellAt]
      exact Typing.allValid_singleton.mpr hval
    refine .next (Rel.of A X ⟨hC.world, hC.heap.push' hxx, hC.inv.push _ (.inr rfl) hx,
      Typing.AllValid.mono hst.typ hC.wok, hC.stack.stepOff hst⟩ (.exec ⟨E, hB, hk, ?_⟩)
      (hD.sub fun _ h₂ => promLocs_after (hd := hd₀) h₂))
    exact (hS.step hst fun _ _ h => h).bind' (d := d)
      (x := ⟨Ty.ref ty, M.cellAt ty heap.cells.size⟩)
      (x₁ := ⟨Ty.ref ty, M.cellAt ty heap₁.cells.size⟩) (by rw [hC.heap.size]) hnew hd₀ hd₁
  | @getKept _ d ty c c₁ is _ _ _ hc hk =>
    simp only [exec, execCode, Core.cellLoc]
    have hv := hS.eq_valid hc (h.ready rfl)
    obtain ⟨hlP, hlt, htl⟩ := typOff_valid.mp hv
    have hl₁ : M.locOf (getT env₁ c₁ (Ty.ref ty) (h₁.ready (i := .refGet d ty c₁) rfl)) =
        M.locOf (getT env c (Ty.ref ty) (h.ready rfl)) := locOf_getT_congr _ _ (hS.eq_get hc)
    have hh : heap.Holds _ ty := ⟨hlt, htl⟩
    have hh₁ := (hC.heap.holds_iff hlP ty).mpr hh
    rw [Heap.cell_pos hh, Heap.cell_pos (by rw [hl₁]; exact hh₁)]
    simp only [Core.refGet, Core.next]
    refine .next (rel_exec hC ⟨E, hB, hk, ?_⟩ ?_)
    · refine hS.bind' ?_ (hC.inv.cells _ _ (Array.getElem?_eq_getElem hlt))
        (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)
        (Nat.lt_of_lt_of_le (h₁.dst_lt (i := .refGet d ty c₁) rfl) fits₁)
      simp only [hl₁]
      exact hC.heap.get_eq hlP hlt _
    · exact hD.sub fun _ h₂ => promLocs_after (hd := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) h₂
  | @setKept _ d ty c c₁ v v₁ is _ _ _ hc hv hk =>
    simp only [exec, execCode, Core.cellLoc]
    have hval := hS.eq_valid hc (h.ready rfl).1
    obtain ⟨hlP, hlt, htl⟩ := typOff_valid.mp hval
    have hl₁ : M.locOf (getT env₁ c₁ (Ty.ref ty) (h₁.ready (i := .refSet d ty c₁ v₁) rfl).1) =
        M.locOf (getT env c (Ty.ref ty) (h.ready rfl).1) := locOf_getT_congr _ _ (hS.eq_get hc)
    have hh : heap.Holds _ ty := ⟨hlt, htl⟩
    have hh₁ := (hC.heap.holds_iff hlP ty).mpr hh
    rw [Heap.cell_pos hh, Heap.cell_pos (by rw [hl₁]; exact hh₁)]
    simp only [Core.refSet, Core.next]
    have hvb : v < env.size := (h.ready rfl).2
    have hvb₁ : v₁ < env₁.size := (h₁.ready (i := .refSet d ty c₁ v₁) rfl).2
    have hxx : getD env₁ v₁ hvb₁ = getD env v hvb := by
      have hx := hS.eq_get hv
      rw [Array.getElem?_eq_getElem hvb₁, Array.getElem?_eq_getElem hvb] at hx
      exact Option.some.inj hx
    have hx : A.DynOK (typOff heap P) (getD env v hvb) :=
      hS.eq_ok hv _ (Array.getElem?_eq_getElem hvb)
    have htag : (getD env v hvb).1 =
        (heap.cells[M.locOf (getT env c (Ty.ref ty) (h.ready rfl).1)]'hlt).1 :=
      ((CoreOK.refSet_tag h rfl).2 hvb).trans htl.symm
    have e := typOff_set (P := P) hlt htag
    have hst : HeapStep P P heap (heap.set (M.locOf (getT env c (Ty.ref ty) (h.ready rfl).1))
        (getD env v hvb) hlt) (fun _ => False) :=
      .of_frame hC.heap.bound (by rw [e]; exact Typing.Extends.refl _) (HeapFrame.set hlt hval _)
    have hunit : A.DynOK (typOff (heap.set (M.locOf (getT env c (Ty.ref ty) (h.ready rfl).1))
        (getD env v hvb) hlt) P) ⟨M.unit, M.unitVal⟩ := by
      unfold Accounts.DynOK Accounts.ValOK
      rw [A.unit]
      exact Typing.allValid_nil _
    refine .next (Rel.of A X ⟨hC.world, ?_, hC.inv.set hlt htag hx,
      Typing.AllValid.mono hst.typ hC.wok, hC.stack.stepOff hst⟩ (.exec ⟨E, hB, hk, ?_⟩) ?_)
    · have hset := hC.heap.set' (l := M.locOf (getT env c (Ty.ref ty) (h.ready rfl).1)) hlt
        hh₁.lt hxx
      simp only [hl₁]
      exact hset
    · exact (hS.step hst fun _ _ h => h).bind' rfl hunit (Nat.lt_of_lt_of_le (h.dst_lt rfl) fits)
        (Nat.lt_of_lt_of_le (h₁.dst_lt (i := .refSet d ty c₁ v₁) rfl) fits₁)
    · exact hD.sub fun _ h₂ => promLocs_after (hd := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits) h₂
  | @newProm _ d ty v u is _ _ _ hu hud hk =>
    simp only [exec, execCode, Core.refNew, Core.next]
    have hv : v < env.size := h.ready rfl
    have hx : A.DynOK (typOff heap P) (getD env v hv) :=
      hS.eq_ok hu _ (Array.getElem?_eq_getElem hv)
    have hst :
        HeapStep P (heap.cells.size :: P) heap (heap.push (getD env v hv)) (fun _ => False) :=
      ⟨by simp [Heap.push], fun _ h => List.mem_cons_of_mem _ h, typOff_push _ (.inl rfl),
        fun l hl _ => by
          simp only [Heap.push, Array.getElem?_push]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (Nat.ne_of_lt (hC.heap.bound l hl)))]⟩
    have hd₀ : d < env.size := Nat.lt_of_lt_of_le (h.dst_lt rfl) fits
    have hd₁ : d < env₁.size := Nat.lt_of_lt_of_le (h₁.dst_lt (i := .refNew d ty u) rfl) fits₁
    have hrd : RefAt (env.set d ⟨Ty.ref ty, M.cellAt ty heap.cells.size⟩ hd₀) d heap.cells.size :=
      ⟨ty, _, Array.getElem?_set_self _, M.locOf_cellAt ty _⟩
    have h₀ := (hS.step hst fun _ _ h => h).rebind ⟨Ty.ref ty, M.cellAt ty heap.cells.size⟩
      ⟨Ty.ref ty, M.cellAt ty heap₁.cells.size⟩ hd₀ hd₁
    have hnew : ∀ ψ ∈ dropTgt d (dropSrc d F), ∀ c₁ l, ψ.prom? = some c₁ → c₁ ≠ d →
        RefAt (env.set d ⟨Ty.ref ty, M.cellAt ty heap.cells.size⟩ hd₀) d l →
        ¬ RefAt (env.set d ⟨Ty.ref ty, M.cellAt ty heap.cells.size⟩ hd₀) c₁ l := by
      intro ψ hψ c₁ l hc₁ hne hr hr₁
      rw [← hrd.unique hr] at hr₁
      obtain ⟨hψ₁, hs⟩ := mem_dropSrc.mp (mem_dropTgt.mp hψ).1
      rw [Fact.src_of_prom? hc₁] at hs
      obtain ⟨t₀, x₀, hx₀, hl₀⟩ := hr₁
      rw [Array.getElem?_set_ne _ (Ne.symm hs)] at hx₀
      have := ((hS.holds _ hψ₁).prom_lt hc₁ ⟨t₀, x₀, hx₀, hl₀⟩).1
      omega
    have h₃ := h₀.cons_prom (φ := .prom d) (c := d)
      ⟨_, hrd, List.mem_cons_self, by simp [Heap.push]⟩ rfl hnew
    refine .next (Rel.of A X ⟨hC.world, hC.heap.pushProm _ _, hC.inv.push _ (.inl rfl) hx,
      Typing.AllValid.mono hst.typ hC.wok, hC.stack.step hst fun _ _ _ _ h => h⟩
      (.exec ⟨E, hB, hk, ?_⟩) ⟨fun l₁ h₂ q hq hc => ?_, hD.2⟩)
    · refine h₃.cons_same (ψ := .prom d) ⟨heap.cells.size, getD env v hv, hrd,
        List.mem_cons_self, by simp [Heap.push], ?_⟩ rfl List.mem_cons_self rfl
      rw [Array.getElem?_set_ne _ (Ne.symm hud), hS.eq_get hu, Array.getElem?_eq_getElem hv]
      rfl
    · obtain ⟨c₂, hm, hr₂⟩ := h₂
      rcases List.mem_cons.mp hm with e | hm
      · exact nomatch e
      rcases List.mem_cons.mp hm with e | hm
      · cases e
        obtain rfl := hrd.unique hr₂
        exact Nat.lt_irrefl _ (StackRel.cellLocs_lt hC.stack q hq _ hc)
      · obtain ⟨hm₁, hs⟩ := mem_dropSrc.mp (mem_dropTgt.mp hm).1
        obtain ⟨t₀, x₀, hx₀, hl₀⟩ := hr₂
        change (env.set d _ hd₀)[c₂]? = _ at hx₀
        rw [Array.getElem?_set_ne _ (Ne.symm (show c₂ ≠ d from hs))] at hx₀
        exact hD.head l₁ ⟨c₂, hm₁, t₀, x₀, hx₀, hl₀⟩ q hq hc
  | @callCode _ d ts r fn fn₁ args args₁ is is₁ t t₁ hf ha hk =>
    simp only [exec, execCode]
    have hr : HasTy env fn (Ty.fn ts r) ∧ AllBound env args := h.ready rfl
    have hr₁ : HasTy env₁ fn₁ (Ty.fn ts r) ∧ AllBound env₁ args₁ :=
      h₁.ready (i := .callCode d ts r fn₁ args₁) rfl
    have key : M.fnOf (getT env₁ fn₁ (Ty.fn ts r) hr₁.1) = M.fnOf (getT env fn (Ty.fn ts r) hr.1) :=
      congrArg _ (getT_congr _ _ (hS.eq_get hf))
    have hla : lookupAll env₁ args₁ hr₁.2 = lookupAll env args hr.2 :=
      lookupAll_congr (hS.args_get ha) _ _
    refine hok.sameSigs.callee_rec₂ hC.heap.caps (congrArg (·.idx) key)
      (congrArg (·.captured) key) (fun caps hco hco₁ => ?_) fun e => ?_
    · have hv : ∀ d ∈ appendCaps caps (lookupAll env args hr.2) ++
          Args.toList (Args.nil (I := M.interp)), A.DynOK (typOff heap P) d := by
        intro d hd
        rw [Args.toList, List.append_nil, appendCaps_eq] at hd
        rcases List.mem_append.mp hd with hd | hd
        · exact hC.inv.captures hco.2.1 d hd
        · exact Sound.lookupAll_ok A hS ha hr.2 d hd
      have hp : (X.m.funcs[(M.fnOf (getT env fn (Ty.fn ts r) hr.1)).idx]'hco.1).params =
          (appendCaps caps (lookupAll env args hr.2)).map (·.1) ++ [] := by
        rw [List.append_nil, appendCaps_eq, List.map_append, CoreOK.callCode_args h rfl hr.2]
        exact hco.2.2.1
      obtain ⟨F₀, hfr, hnp⟩ := callFrame_ok hok hwf hwf₁ hco.1 hco₁.1 (by rw [key])
        (ds₁ := appendCaps caps (lookupAll env₁ args₁ hr₁.2)) (by rw [hla]) _ hv hp
      exact .next (Rel.of A X hC (.call hfr (.call hB hk hS))
        ⟨fun l hl => (hnp l hl).elim, hD⟩)
    · exact e ▸ .next (Rel.of A X hC (.done _) hD.2)

end

section
variable {B B₁ : Ty} (hwf : WF X.m) (hwf₁ : WF X.m₁) (hok : ModOK X)
  (hR : ∀ i, X.R i → A.InsnOK i) (hRT : ∀ t, X.RT t → A.TermOK t) (oracle : Nat → Nat)

include hok in
/-- **Leaving a body alike**: a valid value, left by frames whose waiting frames correspond. -/
theorem leave_good {s s₁ : State M} {P : List Nat} {Fs : List (List Fact)} {top top₁ : Frame M}
    {conts conts₁ : List (Wait M)} {heap heap₁ : Heap M} {world : M.W} {drawn : Nat}
    {v : Dyn M.interp} (h : LeftOK X.m B ⟨top, conts, heap, world⟩ v)
    (h₁ : LeftOK X.m₁ B₁ ⟨top₁, conts₁, heap₁, world⟩ v)
    (hC : CoreRel A X P Fs ⟨top, conts, heap, world⟩ ⟨top₁, conts₁, heap₁, world⟩)
    (hD : Disjoint (stackFacts Fs conts)) (hv : A.DynOK (typOff heap P) v) :
    Diagram hwf₁ oracle (Rel A X) measure Wrong s s₁
      (leave hwf ⟨top, conts, heap, world⟩ v h drawn)
      (leave hwf₁ ⟨top₁, conts₁, heap₁, world⟩ v h₁ drawn) := by
  have hst : StackRel A X P heap Fs conts conts₁ := hC.stack
  simp only [leave]
  cases hst with
  | nil =>
    simp only [leaveTo]
    exact .next (Rel.of A X hC (.done _) hD)
  | @cons Fw Fs w w₁ cs cs₁ hw hcs =>
    cases hw with
    | rule hp hres =>
      simp only [leaveTo]
      exact settle_lock (c := ⟨_, cs, heap, world⟩) (c₁ := ⟨_, cs₁, heap₁, world⟩) (F := Fw)
        hwf hwf₁ hok oracle _ _ _ _ ⟨hC.world, hC.heap, hC.inv, hC.wok, hcs⟩ hD hp rfl
        (hres _ (Typing.Extends.refl _) _ (Accounts.dynOK_at hv _))
    | @call f f₁ dst r E hB hk hS =>
      simp only [leaveTo]
      refine .next (Rel.of A X ⟨hC.world, hC.heap, hC.inv, hC.wok, hcs⟩
        (.exec ⟨E, hB, hk, ?_⟩) (hD.sub fun _ h₂ =>
          promLocs_after (hd := Nat.lt_of_lt_of_le (LeftOK.call_dst h rfl) f.fits) h₂))
      simp only [Frame.bind]
      exact hS.bind v hv _ _

include hok hR hRT in
/-- **The step diagram.**  From corresponding states, a source step is matched by a target step
and then silent steps to states that correspond, or by none with a smaller measure; a source
that has ended has a wrong result, or the target has ended with the same result, world and
number of choices. -/
theorem step_good {s s₁ : State M} (h : StateOK X.m B s) (h₁ : StateOK X.m₁ B₁ s₁)
    (hr : Rel A X s s₁) :
    Diagram hwf₁ oracle (Rel A X) measure Wrong s s₁ (Exec.step hwf oracle s h)
      (Exec.step hwf₁ oracle s₁ h₁) := by
  obtain ⟨⟨top, conts, heap, world⟩, mode, drawn, ⟨⟩⟩ := s
  obtain ⟨⟨top₁, conts₁, heap₁, world₁⟩, mode₁, drawn₁, ⟨⟩⟩ := s₁
  obtain ⟨hd, hw, P, L, Fs, hH, hI, hW, hm, hst, hD⟩ := hr
  simp only at hd hw hH hI hW hm hst hD
  have hd₀ := hd.symm
  have hw₀ := hw.symm
  subst hd₀ hw₀
  have hC : CoreRel A X P Fs ⟨top, conts, heap, world⟩ ⟨top₁, conts₁, heap₁, world⟩ :=
    ⟨rfl, hH, hI, hW, hst⟩
  cases hm with
  | wrong hw => exact Or.inl hw
  | done r => exact Or.inr ⟨_, rfl⟩
  | exec hF => exact exec_good hwf hwf₁ hok hR hRT oracle h h₁ hC hD hF
  | jump hF =>
    simp only [Exec.step]
    exact .next (rel_exec hC hF hD)
  | @call F Fw callee callee₁ w w₁ hF hW₁ =>
    simp only [Exec.step]
    have hC₁ : CoreRel A X P (Fw :: Fs) ⟨callee, w :: conts, heap, world⟩
        ⟨callee₁, w₁ :: conts₁, heap₁, world⟩ := ⟨rfl, hH, hI, hW, .cons hW₁ hst⟩
    exact .next (Rel.of A X hC₁ (.exec hF) hD)
  | ret hv =>
    simp only [Exec.step]
    exact leave_good hwf hwf₁ hok oracle h h₁ hC hD hv
  | request t hp ht =>
    simp only [Exec.step]
    exact serve_lock hwf hwf₁ hok oracle h h₁ hC hD hp t ht
  | again st hp hst₀ =>
    obtain ⟨_, _, _, hS, -, -, hargs, -, -, hag, -⟩ := id hp
    simp only [Exec.step]
    refine settle_lock hwf hwf₁ hok oracle _ _ _ _ hC hD hp ?_ ?_
    · simp only [Inst.again, mkInst]
      exact congrFun (applyFn_congr (hS.args_get hargs) _ _ _ _) _
    · exact Accounts.FnOK.applyFn _ (hS.args_ok hargs) (hag _) _ hst₀

end

end

end Strata.Dyn.RefToRegSound
