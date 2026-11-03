/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Frame

set_option autoImplicit false

/-!
# Calls: a body's start, the stack lemma, and the frame theorem for a call

A call runs its callee above the frames that wait on it, and the machine never looks below the
frames it runs until the callee returns.  So the run of a call is the callee's own run, from its
start, with the waiting frames below, and what is proved of the callee's run holds of the call.

* `bodyStart g heap world drawn`: the frame `g` run alone, on a run's heap and world.  A pending
  call steps to it with the waiting frames below (`step_call`); a `callCode` and a rule's call
  make the pending call of a function's entry frame (`step_callCode`, `settle_call`), and a
  function's run from a snapshot is its body's start (`startCore_bodyStart`).
* `State.atop s cs`: `s` with the frames `cs` waiting below its own.  **The stack lemma**,
  `trace_atop`: until the run under an oracle leaves its bottom frame (`State.Returns`), the run of
  `s.atop cs` is the run of `s` with `cs` below, configuration by configuration, so `cs` is
  untouched.  It rests on `step_atop`, one step.  `trace_call` reads it from a pending call:
  after the entry, the run of the call is the callee's run from `bodyStart`, until the callee
  returns.  `run_atop` and `run_call` state them for every run: each is, until the callee returns,
  a run of the callee with the waiting frames below.
* `leave_keeps`: returning to a waiting frame changes no cell, and goes on with the frames below
  it.
* **The frame theorem for a call**, `frame_call`: from a pending call, every run keeps the cells
  at a set `P` of locations that the callee's store and the world do not reach, along
  each of its callee's runs (`CallKeeps`, for every `r₀` with `CalleeRun r r₀`, which `run_call`
  provides): at every configuration until the callee returns, though the caller's frames may
  reach them, and when the callee returns, the caller goes on with them.  A fact proved of every
  run of the callee applies to the same `r₀`.
  `frame_callFrame` states it for a function's entry frame, at the roots of its arguments and the
  world, and `frame_call_of_inv` at the roots of the callee's frame (`frameRoots`) in any state
  where the run invariant holds, which makes those roots well tagged
  (`Accounts.HeapOK.wellTagged`).  All are `frame` applied to the callee's own run, from
  `inv_bodyStart`.  `frame_call_of_run` applies `frame_call_of_inv` at a pending call that a run
  reaches from a state where the invariant holds, such as a function's start, so that only the
  hypotheses on `P` are left to prove.
-/

namespace Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-! ## Frames waiting below a run -/

section
variable {m : LModule M}

/-- `c` with the frames `cs` waiting below its own. -/
def Core.atop (c : Core M) (cs : List (Wait M)) : Core M :=
  { c with conts := c.conts ++ cs }

/-- `s` with the frames `cs` waiting below its own. -/
def State.atop (s : State M) (cs : List (Wait M)) : State M :=
  { s with core := s.core.atop cs }

/-- Waiting frames that end in a frame expecting `R`, above frames that expect `R` and end in
one expecting `B`, end in one expecting `B`. -/
theorem ContsOK.append {R B : Ty} {cs : List (Wait M)} (hcs : ContsOK m B R cs) :
    ∀ {X : Ty} (ws : List (Wait M)), ContsOK m R X ws → ContsOK m B X (ws ++ cs)
  | _, [], h => h ▸ hcs
  | _, _ :: ws, h => ⟨h.1, ContsOK.append hcs ws h.2⟩

/-- A state of a run whose bottom frame returns `R`, above frames that expect `R`. -/
theorem StateOK.atop {R B : Ty} {cs : List (Wait M)} (hcs : ContsOK m B R cs) {s : State M}
    (h : StateOK m R s) : StateOK m B (s.atop cs) := by
  obtain ⟨⟨top, conts, heap, world⟩, mode, drawn, ⟨⟩⟩ := s
  cases mode with
  | exec => exact ⟨h.1, hcs.append _ h.2⟩
  | jump to => exact ⟨h.1, hcs.append _ h.2⟩
  | call g w => exact ⟨h.1, hcs.append (w :: conts) h.2⟩
  | ret v => exact ⟨h.1, hcs.append _ h.2⟩
  | request i t => exact ⟨h.1, hcs.append _ h.2⟩
  | again r => exact ⟨h.1, hcs.append _ h.2⟩
  | done r => trivial

/-- A step's outcome, with the frames `cs` waiting below. -/
def StepR.atop {R B : Ty} {cs : List (Wait M)} (hcs : ContsOK m B R cs) : StepR m R → StepR m B
  | .next e s h => .next e (s.atop cs) (h.atop hcs)
  | .final r heap world drawn => .final r heap world drawn

/-- A configuration of a run, with the frames `cs` waiting below. -/
def Config.atop {R B : Ty} {cs : List (Wait M)} (hcs : ContsOK m B R cs) :
    Config m R → Config m B :=
  Trace.Config.mapS fun c => ⟨c.1.atop cs, c.2.atop hcs⟩

/-- `s` leaves its bottom frame: it returns a value, and no frame waits below. -/
def State.Returns (s : State M) : Prop :=
  (∃ v, s.mode = .ret v) ∧ s.core.conts = []

end

/-! ## A step does not look below the frames it runs -/

section
variable {m : LModule M} (hwf : WF m) (oracle : Nat → Nat) {R B : Ty} {cs : List (Wait M)}
  (hcs : ContsOK m B R cs)

/-- A cell check, with frames waiting below either outcome. -/
private theorem StepR.atop_cell {heap : Heap M} {l : Nat} {t : Ty}
    {ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → StepR m R}
    {bad : Unit → StepR m R} :
    (heap.cell l t ok bad).atop hcs =
      heap.cell l t (fun a b => (ok a b).atop hcs) (fun u => (bad u).atop hcs) := by
  by_cases h : heap.Holds l t
  · rw [Heap.cell_pos h, Heap.cell_pos h]
  · rw [Heap.cell_neg h, Heap.cell_neg h]

/-- A call check, with frames waiting below either outcome. -/
private theorem StepR.atop_callee {heap : Heap M} {idx captured : Nat} {ts : List Ty} {r : Ty}
    {ok : (hi : idx < m.funcs.size) → (caps : List (Dyn M.interp)) →
      (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts → (m.funcs[idx]'hi).ret = r → StepR m R}
    {bad : Unit → StepR m R} :
    (m.callee heap idx captured ts r ok bad).atop hcs =
      m.callee heap idx captured ts r (fun a b c d => (ok a b c d).atop hcs)
        (fun u => (bad u).atop hcs) := by
  by_cases h : ∃ caps, m.CallOK heap idx captured ts r caps
  · obtain ⟨caps, h⟩ := h
    rw [LModule.callee_pos h, LModule.callee_pos h]
  · rw [LModule.callee_neg (fun caps hc => h ⟨caps, hc⟩),
      LModule.callee_neg (fun caps hc => h ⟨caps, hc⟩)]

/-- A transfer does not look below the frames it runs. -/
private theorem transfer_atop {top : Frame M} {conts : List (Wait M)} {heap : Heap M} {world : M.W}
    {n : Next M} (hn : NextOK m top n) (hK : ContsOK m R top.func.ret conts)
    (hK₁ : ContsOK m B top.func.ret (conts ++ cs)) {drawn : Nat} {ev : Event} :
    transfer ⟨top, conts ++ cs, heap, world⟩ n hn hK₁ drawn ev =
      (transfer ⟨top, conts, heap, world⟩ n hn hK drawn ev).atop hcs := by
  cases n <;> rfl

/-- Continuing a rule's tree does not look below the frames it runs. -/
private theorem settle_atop {top : Frame M} {conts : List (Wait M)} {heap : Heap M} {world : M.W}
    {i : Inst M} (hi : InstOK m top i) (hK : ContsOK m R top.func.ret conts)
    (hK₁ : ContsOK m B top.func.ret (conts ++ cs)) {drawn : Nat} {ev : Event} (t : i.Tree) :
    settle hwf ⟨top, conts ++ cs, heap, world⟩ i hi hK₁ drawn ev t =
      (settle hwf ⟨top, conts, heap, world⟩ i hi hK drawn ev t).atop hcs := by
  cases t with
  | ret a => rfl
  | stop s =>
    cases s with
    | jump o =>
      cases o with
      | exit e => exact transfer_atop hcs _ hK hK₁
      | again st => rfl
    | fault f => rfl
  | choose k => rfl
  | update f => rfl
  | vis q k =>
    cases q with
    | region j args => rfl
    | call sig idx captured args =>
      simp only [settle, visitCall]
      rw [StepR.atop_callee]
      rfl
    | new _ _ => rfl
    | get _ _ => rfl
    | set _ _ _ => rfl
    | modify _ _ _ => rfl
    | bind _ _ _ _ _ => rfl

/-- Answering a rule's request does not look below the frames it runs. -/
private theorem serve_atop {top : Frame M} {conts : List (Wait M)} {heap : Heap M} {world : M.W}
    {i : Inst M} (t : i.Tree) (h : InstOK m top i ∧ ContsOK m R top.func.ret conts)
    (h₁ : InstOK m top i ∧ ContsOK m B top.func.ret (conts ++ cs)) {drawn : Nat} :
    serve hwf oracle ⟨top, conts ++ cs, heap, world⟩ i t h₁ drawn =
      (serve hwf oracle ⟨top, conts, heap, world⟩ i t h drawn).atop hcs := by
  cases t
  case' vis q k => cases q
  case vis.get | vis.set | vis.modify =>
    simp only [serve]
    rw [StepR.atop_cell]
    congr
    funext a b
    exact settle_atop hwf hcs h.1 h.2 h₁.2 _
  case vis.bind =>
    simp only [serve]
    rw [StepR.atop_callee]
    congr
    funext a b c d
    exact settle_atop hwf hcs h.1 h.2 h₁.2 _
  all_goals
    simp only [serve]
    exact settle_atop hwf hcs h.1 h.2 h₁.2 _

/-- A terminator does not look below the frames it runs. -/
private theorem execTerm_atop {top : Frame M} {conts : List (Wait M)} {heap : Heap M} {world : M.W}
    (h : CoreOK m R ⟨top, conts, heap, world⟩) (h₁ : CoreOK m B ⟨top, conts ++ cs, heap, world⟩)
    (hc : top.code = []) {drawn : Nat} : ∀ (t : LTerm M) (ht : top.term = t),
    execTerm hwf ⟨top, conts ++ cs, heap, world⟩ h₁ hc drawn t ht =
      (execTerm hwf ⟨top, conts, heap, world⟩ h hc drawn t ht).atop hcs
  | LTerm.case .., _ => transfer_atop hcs _ h.2 h₁.2
  | LTerm.sem .., _ => settle_atop hwf hcs _ h.2 h₁.2 _

/-- An instruction does not look below the frames it runs. -/
private theorem execCode_atop {top : Frame M} {conts : List (Wait M)} {heap : Heap M} {world : M.W}
    (h : CoreOK m R ⟨top, conts, heap, world⟩) (h₁ : CoreOK m B ⟨top, conts ++ cs, heap, world⟩)
    {drawn : Nat} : ∀ (code : List (LInsn M)) (hc : top.code = code),
    execCode hwf ⟨top, conts ++ cs, heap, world⟩ h₁ drawn code hc =
      (execCode hwf ⟨top, conts, heap, world⟩ h drawn code hc).atop hcs
  | [], hc => execTerm_atop hwf hcs h h₁ hc _ rfl
  | LInsn.const .. :: _, _ => rfl
  | LInsn.pure .. :: _, _ => rfl
  | LInsn.sem .. :: _, _ => by
    simp only [execCode]
    exact settle_atop hwf hcs (top := { top with code := _, pc := top.pc + 1 }) _ h.2 h₁.2 _
  | LInsn.refNew .. :: _, _ => rfl
  | LInsn.refGet .. :: _, _ => by
    simp only [execCode]
    rw [StepR.atop_cell]
    rfl
  | LInsn.refSet .. :: _, _ => by
    simp only [execCode]
    rw [StepR.atop_cell]
    rfl
  | LInsn.callCode .. :: _, _ => by
    simp only [execCode]
    rw [StepR.atop_callee]
    rfl

/-- **A step does not look below the frames it runs.**  A step of `s` with frames `cs` waiting
below is the step of `s`, with `cs` waiting below, unless `s` leaves its bottom frame. -/
theorem step_atop {s : State M} (h : StateOK m R s) (h₁ : StateOK m B (s.atop cs))
    (hn : ¬ s.Returns) : step hwf oracle (s.atop cs) h₁ = (step hwf oracle s h).atop hcs := by
  obtain ⟨⟨top, conts, heap, world⟩, mode, drawn, ⟨⟩⟩ := s
  cases mode with
  | exec => exact execCode_atop hwf hcs h h₁ _ rfl
  | jump to => rfl
  | call g w => rfl
  | ret v =>
    cases conts with
    | nil => exact absurd ⟨⟨v, rfl⟩, rfl⟩ hn
    | cons w conts =>
      cases w with
      | rule f p =>
        simp only [step, leave, leaveTo]
        exact settle_atop hwf hcs (top := f) _ _ _ _
      | call f dst r => rfl
  | request i t => exact serve_atop hwf oracle hcs t h h₁
  | again r => exact settle_atop hwf hcs h.1 h.2 h₁.2 _
  | done r => rfl

/-- A configuration of a run where it leaves its bottom frame. -/
def Config.Returns : Config m R → Prop :=
  Trace.Config.Sat (fun c => c.1.Returns) fun _ => False

/-- A step of a state that does not leave its bottom frame, as configurations. -/
private theorem stepAt_atop (c : Cfg m R) (hn : ¬ c.1.Returns) :
    stepAt hwf oracle ⟨c.1.atop cs, c.2.atop hcs⟩ = (stepAt hwf oracle c).atop hcs := by
  unfold stepAt
  rw [step_atop hwf oracle hcs c.2 _ hn]
  cases step hwf oracle c.1 c.2 <;> rfl

/-- **The stack lemma.**  Until a run leaves its bottom frame, the run of the same state with frames
`cs` waiting below is the same run, with `cs` waiting below: `cs` is untouched, and every
configuration is the configuration of the run without them.  The run without them is the
body's own. -/
theorem trace_atop : ∀ (n : Nat) {s : State M} (h : StateOK m R s),
    (∀ k < n, ¬ (trace hwf oracle s h k).Returns) →
      trace hwf oracle (s.atop cs) (h.atop hcs) n = (trace hwf oracle s h n).atop hcs
  | 0, _, _, _ => rfl
  | n + 1, s, h, hn => by
    have h0 : ¬ s.Returns := hn 0 (Nat.succ_pos n)
    have hs := stepAt_atop hwf oracle hcs ⟨s, h⟩ h0
    unfold trace
    revert hs
    cases hc : stepAt hwf oracle ⟨s, h⟩ with
    | running c₁ =>
      intro hs
      rw [Trace.trace_succ_running hs, Trace.trace_succ_running hc]
      refine trace_atop n c₁.2 fun k hk => ?_
      have := hn (k + 1) (Nat.succ_lt_succ hk)
      unfold trace at this
      rwa [Trace.trace_succ_running hc] at this
    | ended f =>
      intro hs
      rw [Trace.trace_succ_ended hs, Trace.trace_succ_ended hc]
      rfl

end

/-! ## The stack lemma over runs -/

section
variable {m : LModule M} {hwf : WF m} {R B : Ty} {cs : List (Wait M)} (hcs : ContsOK m B R cs)

/-- **The stack lemma over runs.**  Every run of a state with frames `cs` waiting below is, until
it leaves its bottom frame, a run of the same state without them, with `cs` below: there is a run
`r₀` of the state alone whose configurations, with `cs` below, are the run's until `r₀`
returns. -/
theorem run_atop {s : State M} (h : StateOK m R s) (r : RunFrom hwf (s.atop cs) (h.atop hcs)) :
    ∃ r₀ : RunFrom hwf s h, ∀ n, (∀ k < n, ¬ Config.Returns (r₀.cfg k)) →
      r.cfg n = Config.atop hcs (r₀.cfg n) := by
  obtain ⟨o, ho⟩ := complete r
  exact ⟨oracleRun hwf o s h, fun n hn => (ho n).trans (trace_atop hwf o hcs n h hn)⟩

end

/-! ## Entering a body -/

section
variable {m : LModule M} (hwf : WF m) (oracle : Nat → Nat) {B : Ty}

/-- **A body started inside a run**: the frame `g` alone, on the heap and the world of the
run, with `drawn` choices made.  It is the state a call enters, without the frames
waiting on it (`step_call`). -/
def bodyStart (g : Frame M) (heap : Heap M) (world : M.W) (drawn : Nat) : State M :=
  ⟨⟨g, [], heap, world⟩, .exec, drawn, ()⟩

/-- A body started from a frame that runs checked code is a state of its own run. -/
theorem bodyStart_ok {g : Frame M} (hg : Runs m g) (heap : Heap M) (world : M.W) (drawn : Nat) :
    StateOK m g.func.ret (bodyStart g heap world drawn) :=
  ⟨hg, rfl⟩

/-- A function's run from a snapshot is its body started on the snapshot. -/
theorem startCore_bodyStart {i : Nat} {args : List (Dyn M.interp)} {snap : Snapshot M}
    {c : Core M} {hc : CoreOK m B c} (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩) :
    (⟨c, .exec, 0, ()⟩ : State M) = bodyStart c.top snap.heap snap.world 0 := by
  obtain ⟨fn, b, hf, hb, rfl⟩ := startCore_entry hst
  rfl

/-- **Entering a body**: a pending call of `g`, with `w` waiting on it, steps to `g`'s start
on the run's heap and world, with `w` and the run's waiting frames below. -/
theorem step_call {c : Core M} {g : Frame M} {w : Wait M} {drawn : Nat}
    (h : StateOK m B ⟨c, .call g w, drawn, ()⟩) :
    step hwf oracle ⟨c, .call g w, drawn, ()⟩ h =
      .next (.enter g.func.name) ((bodyStart g c.heap c.world drawn).atop (w :: c.conts))
        ((bodyStart_ok h.1 c.heap c.world drawn).atop h.2) :=
  rfl

/-- **A `callCode`** whose check passes, with the closure's captures `caps`, makes the call of
its function's entry frame on the captures and the arguments, the caller waiting to bind the
result to `dst`. -/
theorem step_callCode {c : Core M} (h : CoreOK m B c) {dst : Nat} {ts : List Ty} {r : Ty}
    {f : Nat} {args : List Nat} {code : List (LInsn M)}
    (hc : c.top.code = .callCode dst ts r f args :: code) {caps : List (Dyn M.interp)}
    (hok : m.CallOK c.heap (M.fnOf (getT c.top.env f (Ty.fn ts r) (h.ready hc).1)).idx
      (M.fnOf (getT c.top.env f (Ty.fn ts r) (h.ready hc).1)).captured ts r caps)
    (drawn : Nat) :
    ∃ h₁, step hwf oracle ⟨c, .exec, drawn, ()⟩ h = .next (.instr c.top.pos)
      ⟨c, .call (callFrame hwf _ hok.1 (appendCaps caps (lookupAll c.top.env args (h.ready hc).2))
          .nil) (.call { c.top with code, pc := c.top.pc + 1 } dst r), drawn, ()⟩ h₁ := by
  obtain ⟨⟨func, code₀, term, env, block, pc, fits⟩, conts, heap, world⟩ := c
  dsimp only at hc hok ⊢
  subst hc
  refine ⟨?_, ?_⟩
  · exact h.callCode hwf rfl (h.ready rfl) hok.1 hok.2.2.1 hok.2.2.2
  · simp only [step, exec, execCode]
    rw [LModule.callee_pos hok]

/-- **A rule's call** of a closure whose check passes, with captures `caps`, makes the call of
its function's entry frame on the captures and the call's arguments, the rule waiting for the
result. -/
theorem settle_call {c : Core M} {i : Inst M} (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) {drawn : Nat} {ev : Event} {sig : List Ty × Ty}
    {idx captured : Nat} {args : Payload (sig.1.map M.interp)} {k : M.interp sig.2 → i.Tree}
    {caps : List (Dyn M.interp)} (hok : m.CallOK c.heap idx captured sig.1 sig.2 caps) :
    settle hwf c i hi hK drawn ev (.vis (.call sig idx captured args) k) =
      .next ev ⟨c, .call (callFrame hwf idx hok.1 caps (Args.ofPayload sig.1 args))
        (.rule c.top ⟨i, .call sig idx captured args, sig.2, k⟩), drawn, ()⟩
        (hi.call hwf hK hok.1 hok.2.2.1 hok.2.2.2 args k) := by
  simp only [settle, visitCall]
  rw [LModule.callee_pos hok]

variable {hwf} {oracle}

/-- **The run of a call is its body's own run**, with the waiting frames below, until the body
returns: from a pending call of `g`, the run after `n + 1` steps is the run of `g`'s start after
`n` steps with `w` and the run's waiting frames below, if `g`'s run has not returned in its
first `n` steps. -/
theorem trace_call {c : Core M} {g : Frame M} {w : Wait M} {drawn : Nat}
    (h : StateOK m B ⟨c, .call g w, drawn, ()⟩) (n : Nat)
    (hn : ∀ k < n, ¬ (trace hwf oracle (bodyStart g c.heap c.world drawn)
      (bodyStart_ok h.1 c.heap c.world drawn) k).Returns) :
    trace hwf oracle ⟨c, .call g w, drawn, ()⟩ h (n + 1) =
      (trace hwf oracle (bodyStart g c.heap c.world drawn)
        (bodyStart_ok h.1 c.heap c.world drawn) n).atop h.2 := by
  unfold trace
  rw [Trace.trace_succ_running (show stepAt hwf oracle ⟨_, h⟩ = .running ⟨_, _⟩ by
    unfold stepAt
    rw [step_call]
    rfl)]
  exact trace_atop hwf oracle h.2 n _ hn

/-- **`r₀` is the callee's run in `r`**, a run of a pending call of `g`: `r₀` is a run of `g`'s
start, and until it returns, its configuration after `n` steps, with `w` and the run's waiting
frames below, is `r`'s after `n + 1`. -/
def CalleeRun {c : Core M} {g : Frame M} {w : Wait M} {drawn : Nat}
    {h : StateOK m B ⟨c, .call g w, drawn, ()⟩} (r : RunFrom hwf ⟨c, .call g w, drawn, ()⟩ h)
    (r₀ : RunFrom hwf (bodyStart g c.heap c.world drawn) (bodyStart_ok h.1 c.heap c.world drawn)) :
    Prop :=
  ∀ n, (∀ k < n, ¬ Config.Returns (r₀.cfg k)) → r.cfg (n + 1) = Config.atop h.2 (r₀.cfg n)

/-- **A run of a call is its body's run**, with the waiting frames below, until the body
returns: every run of a pending call has a callee's run (`CalleeRun`). -/
theorem run_call {c : Core M} {g : Frame M} {w : Wait M} {drawn : Nat}
    (h : StateOK m B ⟨c, .call g w, drawn, ()⟩) (r : RunFrom hwf ⟨c, .call g w, drawn, ()⟩ h) :
    ∃ r₀, CalleeRun r r₀ := by
  obtain ⟨o, ho⟩ := complete r
  exact ⟨oracleRun hwf o _ _, fun n hn => (ho (n + 1)).trans (trace_call h n hn)⟩

end

/-! ## Returning from a body -/

section
variable {m : LModule M} (hwf : WF m) {B : Ty}

/-- A step that goes on with the heap and the waiting frames of `c`. -/
def StepR.Keeps (c : Core M) : StepR m B → Prop
  | .next _ s _ => s.core.heap = c.heap ∧ s.core.conts = c.conts
  | .final .. => False

/-- Continuing a rule's tree in a frame changes neither the heap nor the waiting frames. -/
theorem settle_keeps {c : Core M} {i : Inst M} (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) {drawn : Nat} {ev : Event} (t : i.Tree) :
    (settle hwf c i hi hK drawn ev t).Keeps c := by
  cases t with
  | ret a => exact ⟨rfl, rfl⟩
  | stop s =>
    cases s with
    | jump o =>
      cases o with
      | exit e =>
        simp only [settle, transfer]
        split <;> exact ⟨rfl, rfl⟩
      | again st => exact ⟨rfl, rfl⟩
    | fault f => exact ⟨rfl, rfl⟩
  | choose k => exact ⟨rfl, rfl⟩
  | update f => exact ⟨rfl, rfl⟩
  | vis q k =>
    cases q with
    | region j args => exact ⟨rfl, rfl⟩
    | call sig idx captured args =>
      simp only [settle, visitCall]
      by_cases hc : ∃ caps, m.CallOK c.heap idx captured sig.1 sig.2 caps
      · obtain ⟨caps, hco⟩ := hc
        rw [LModule.callee_pos hco]
        exact ⟨rfl, rfl⟩
      · rw [LModule.callee_neg (fun caps h => hc ⟨caps, h⟩)]
        exact ⟨rfl, rfl⟩
    | new _ _ => exact ⟨rfl, rfl⟩
    | get _ _ => exact ⟨rfl, rfl⟩
    | set _ _ _ => exact ⟨rfl, rfl⟩
    | modify _ _ _ => exact ⟨rfl, rfl⟩
    | bind _ _ _ _ _ => exact ⟨rfl, rfl⟩

/-- **Returning to a waiting frame** changes no cell: the run goes on with the heap it returned
on, and the frames waiting below the one returned to. -/
theorem leave_keeps {top : Frame M} {w : Wait M} {cs : List (Wait M)} {heap : Heap M}
    {world : M.W} {v : Dyn M.interp} (h : LeftOK m B ⟨top, w :: cs, heap, world⟩ v)
    (drawn : Nat) :
    (leave hwf ⟨top, w :: cs, heap, world⟩ v h drawn).Keeps ⟨w.frame, cs, heap, world⟩ := by
  cases w with
  | rule f p =>
    simp only [leave, leaveTo]
    exact settle_keeps hwf _ _ _
  | call f dst r => exact ⟨rfl, rfl⟩

end

/-! ## The frame theorem for a call -/

section
variable {A : Accounts M} {m : LModule M} {hwf : WF m} {B : Ty}
  {P : Nat → Prop}

/-- **A body's start satisfies the invariant**, at the typing of what `roots` reach, for any set
`P` of locations they do not reach, when the roots hold the world's refs, every ref they reach
names a cell of its tag, and the frame is one of the run at that typing (its store's values are
valid in it and its code is certified). -/
theorem inv_bodyStart {g : Frame M} {heap : Heap M} {world : M.W} {roots : List Loc}
    (hw : WellTagged A heap roots) (hwr : ∀ p ∈ A.world world, p ∈ roots)
    (hu : ∀ l, P l → ¬ ReachesCell A heap roots l) (hf : A.FrameInv (reachTyping A heap roots) g)
    (drawn : Nat) :
    A.Inv P heap (reachTyping A heap roots) (bodyStart g heap world drawn) :=
  ⟨⟨hw.heapOK, fun l hl => reachTyping_none (hu l hl), fun p hp => hw.rootsValid p (hwr p hp),
    fun _ hm => absurd hm List.not_mem_nil, Kept.refl _ _⟩, hf⟩

/-- A function's entry frame, on values whose refs are roots, is a frame of the run at the typing
of what the roots reach, when every ref they reach names a cell of its tag. -/
private theorem frameInv_callFrame (hR : m.RulesOK A) {heap : Heap M} {roots : List Loc}
    (hw : WellTagged A heap roots) {i : Nat} {hi : i < m.funcs.size} {ds : List (Dyn M.interp)}
    {ts : List Ty} {xs : Args M.interp ts}
    (hr : ∀ d ∈ ds ++ Args.toList xs, ∀ p ∈ A.acct d.1 d.2, p ∈ roots) :
    A.FrameInv (reachTyping A heap roots) (callFrame hwf i hi ds xs) :=
  Accounts.FrameInv.callFrame hR hwf
    (fun d hd p hp => hw.rootsValid p (hr d (List.mem_append_left _ hd) p hp)) xs
    (fun d hd p hp => hw.rootsValid p (hr d (List.mem_append_right _ hd) p hp))

/-- **What a call keeps**, along a run `r` of a pending call and a run `r₀` of the callee's start:
until the callee returns, at every configuration of `r`, and at its end if it ends there, the
cells at `P` are as they were at the call; and when the callee returns, the step after is the
caller's, with the frames that waited below the call and the cells at `P` as they were. -/
def CallKeeps (P : Nat → Prop) {c : Core M} {g : Frame M} {w : Wait M} {drawn : Nat}
    {h : StateOK m B ⟨c, .call g w, drawn, ()⟩} (r : RunFrom hwf ⟨c, .call g w, drawn, ()⟩ h)
    (r₀ : RunFrom hwf (bodyStart g c.heap c.world drawn) (bodyStart_ok h.1 c.heap c.world drawn)) :
    Prop :=
  (∀ n, (∀ k < n, ¬ Config.Returns (r₀.cfg k)) →
    (r.cfg (n + 1)).Sat (fun c₁ => Kept P c.heap c₁.1.core.heap)
      (fun f => Kept P c.heap f.snapshot.heap)) ∧
  (∀ n, (∀ k < n, ¬ Config.Returns (r₀.cfg k)) → Config.Returns (r₀.cfg n) →
    (r.cfg (n + 2)).Sat (fun c₁ => Kept P c.heap c₁.1.core.heap ∧ c₁.1.core.conts = c.conts)
      (fun _ => False))

/-- **The frame theorem for a call.**  From a pending call of `g` in a run of a module whose rules
are certified, let `roots` hold the refs of `g`'s store and of the world, and `P` be a set of
locations of the heap that they do not reach, though the caller's frames may.  Then every run of
the call keeps the cells at `P` along each of its callee's runs (`CallKeeps`), such as the one
that `run_call` gives. -/
theorem frame_call (hR : m.RulesOK A) {c : Core M} {g : Frame M} {w : Wait M} {drawn : Nat}
    (h : StateOK m B ⟨c, .call g w, drawn, ()⟩) {roots : List Loc}
    (hw : WellTagged A c.heap roots) (hwr : ∀ p ∈ A.world c.world, p ∈ roots)
    (hf : A.FrameInv (reachTyping A c.heap roots) g) (hP : ∀ l, P l → l < c.heap.cells.size)
    (hu : ∀ l, P l → ¬ ReachesCell A c.heap roots l)
    (r : RunFrom hwf ⟨c, .call g w, drawn, ()⟩ h) (r₀ : RunFrom hwf _ (bodyStart_ok h.1 _ _ _))
    (hr₀ : CalleeRun r r₀) : CallKeeps P r r₀ := by
  have hk := frame hR hP (inv_bodyStart hw hwr hu hf drawn) r₀
  refine ⟨fun n hn => ?_, fun n hn hr => ?_⟩
  · rw [hr₀ n hn]
    have := hk n
    revert this
    cases r₀.cfg n <;> exact id
  · have h₁ := hr₀ n hn
    have hk₁ := hk n
    revert hk₁ hr h₁
    cases r₀.cfg n with
    | ended f => exact fun hr _ _ => hr.elim
    | running c₁ =>
      obtain ⟨⟨⟨top, conts, heap, world⟩, mode, drawn₁, ⟨⟩⟩, h₂⟩ := c₁
      rintro ⟨⟨v, rfl⟩, rfl⟩ h₁ hk₁
      obtain ⟨o, ho⟩ := r.next h₁
      rw [← ho]
      show (leave hwf ⟨top, w :: c.conts, heap, world⟩ v (h₂.atop h.2) drawn₁).config.Sat _ _
      have hl := leave_keeps hwf (B := B) (h₂.atop h.2) drawn₁
      revert hl
      cases leave hwf ⟨top, w :: c.conts, heap, world⟩ v (h₂.atop h.2) drawn₁ with
      | next e s₂ h₃ =>
        rintro ⟨hh, hc⟩
        exact ⟨hh ▸ hk₁, hc⟩
      | final _ _ _ _ => exact False.elim

/-- The start roots hold the world's refs. -/
private theorem world_mem_startRoots {args : List (Dyn M.interp)} {world : M.W} {p : Loc}
    (hp : p ∈ A.world world) : p ∈ startRoots A args world :=
  List.mem_append_right _ hp

/-- The start roots hold the arguments' refs. -/
private theorem arg_mem_startRoots {args : List (Dyn M.interp)} {world : M.W} {d : Dyn M.interp}
    (hd : d ∈ args) {p : Loc} (hp : p ∈ A.acct d.1 d.2) : p ∈ startRoots A args world :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨d, hd, hp⟩)

/-- **The frame theorem for a function's call**, `frame_call` at the roots of its arguments and
the world: the cells at a set `P` of locations that the call's arguments and the world do not
reach are kept until the function returns, and when it returns the caller goes on with them. -/
theorem frame_callFrame (hR : m.RulesOK A) {c : Core M} {i : Nat} {hi : i < m.funcs.size}
    {ds : List (Dyn M.interp)} {ts : List Ty} {xs : Args M.interp ts} {w : Wait M} {drawn : Nat}
    (h : StateOK m B ⟨c, .call (callFrame hwf i hi ds xs) w, drawn, ()⟩)
    (hw : WellTagged A c.heap (startRoots A (ds ++ Args.toList xs) c.world))
    (hP : ∀ l, P l → l < c.heap.cells.size)
    (hu : ∀ l, P l → ¬ ReachesCell A c.heap (startRoots A (ds ++ Args.toList xs) c.world) l)
    (r : RunFrom hwf ⟨c, .call (callFrame hwf i hi ds xs) w, drawn, ()⟩ h)
    (r₀ : RunFrom hwf _ (bodyStart_ok h.1 _ _ _)) (hr₀ : CalleeRun r r₀) : CallKeeps P r r₀ :=
  frame_call hR h hw (fun _ => world_mem_startRoots)
    (frameInv_callFrame hR hw fun _ hd _ => arg_mem_startRoots hd) hP hu r r₀ hr₀

/-! ## Calls inside a run with the invariant -/

/-- The refs a frame starts with: its store's and the world's. -/
def frameRoots (A : Accounts M) (g : Frame M) (world : M.W) : List Loc :=
  g.env.toList.flatMap (fun d => A.acct d.1 d.2) ++ A.world world

/-- **A pending call in a run with the invariant** starts its body where the roots of its frame
are well tagged and the frame is one of the run at the typing of what they reach. -/
theorem Accounts.Inv.call {Q : Nat → Prop} {heap₀ : Heap M} {T : Typing} {c : Core M}
    {g : Frame M} {w : Wait M} {drawn : Nat} (hs : A.Inv Q heap₀ T ⟨c, .call g w, drawn, ()⟩) :
    WellTagged A c.heap (frameRoots A g c.world) ∧
      A.FrameInv (reachTyping A c.heap (frameRoots A g c.world)) g := by
  obtain ⟨hC, hg, -⟩ := hs
  have hr : T.AllValid (frameRoots A g c.world) := fun p hp => by
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨d, hd, hp⟩ := List.mem_flatMap.mp hp
      exact hg.env d (Array.mem_toList_iff.mp hd) p hp
    · exact hC.world p hp
  have hw := hC.heap.wellTagged hr
  exact ⟨hw, fun d hd p hp => hw.rootsValid p (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨d, Array.mem_toList_iff.mpr hd, hp⟩)), hg.body, hg.code, hg.term⟩

/-- **The frame theorem for a call, inside a run with the invariant.**  At a pending call of `g`
in a state where the run invariant holds, at any typing and for any set of locations, the cells
at a set `P` of locations of the heap that `g`'s store and the world do not reach are kept until
`g` returns, and when it returns the caller goes on with them. -/
theorem frame_call_of_inv (hR : m.RulesOK A) {Q : Nat → Prop} {heap₀ : Heap M} {T : Typing}
    {c : Core M} {g : Frame M} {w : Wait M} {drawn : Nat}
    (h : StateOK m B ⟨c, .call g w, drawn, ()⟩) (hs : A.Inv Q heap₀ T ⟨c, .call g w, drawn, ()⟩)
    (hP : ∀ l, P l → l < c.heap.cells.size)
    (hu : ∀ l, P l → ¬ ReachesCell A c.heap (frameRoots A g c.world) l)
    (r : RunFrom hwf ⟨c, .call g w, drawn, ()⟩ h) (r₀ : RunFrom hwf _ (bodyStart_ok h.1 _ _ _))
    (hr₀ : CalleeRun r r₀) : CallKeeps P r r₀ :=
  frame_call hR h hs.call.1 (fun _ hp => List.mem_append_right _ hp) hs.call.2 hP hu r r₀ hr₀

/-- **The frame theorem for a call that a run reaches.**  Let a run of a module whose rules are
certified start in a state where the invariant holds at the typing `T` for a set `Q` of
locations of `heap₀`, such as a function's start (`inv_startCore`), and be at a pending call of
`g` after `n` steps.  Let `P` be a set of locations that are in the heap at the call and that
`g`'s store and the world do not reach there, whenever the invariant holds at the call at a
typing that extends `T`.  Then the run from the call has a callee's run along which it keeps
the cells at `P`. -/
theorem frame_call_of_run (hR : m.RulesOK A) {Q : Nat → Prop} {heap₀ : Heap M}
    (hQ : ∀ l, Q l → l < heap₀.cells.size) {s : State M} {h : StateOK m B s} {T : Typing}
    (hs : A.Inv Q heap₀ T s) (r : RunFrom hwf s h) {n : Nat} {c : Core M} {g : Frame M}
    {w : Wait M} {drawn : Nat} {h₁ : StateOK m B ⟨c, .call g w, drawn, ()⟩}
    (hn : r.cfg n = .running ⟨_, h₁⟩)
    (hu : ∀ T₁, T.Extends T₁ → A.Inv Q heap₀ T₁ ⟨c, .call g w, drawn, ()⟩ →
      ∀ l, P l → l < c.heap.cells.size ∧ ¬ ReachesCell A c.heap (frameRoots A g c.world) l) :
    ∃ r₀, CalleeRun (r.drop n hn) r₀ ∧ CallKeeps P (r.drop n hn) r₀ := by
  have hi := inv_always hR hQ hs r n
  rw [hn] at hi
  obtain ⟨T₁, he, hi⟩ := hi
  obtain ⟨r₀, hr₀⟩ := run_call h₁ (r.drop n hn)
  exact ⟨r₀, hr₀, frame_call_of_inv hR h₁ hi (fun l hl => (hu T₁ he hi l hl).1)
    (fun l hl => (hu T₁ he hi l hl).2) _ r₀ hr₀⟩

end

end

end Strata.Dyn.Exec
