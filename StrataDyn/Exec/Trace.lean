/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Machine
public import StrataDyn.Util.Trace

set_option autoImplicit false

/-!
# Runs and behaviours of modules

`step` is a function of a module, an oracle and a state.  Its step relation, `StepRel hwf`,
steps wherever some oracle does, so a run of it (`RunFrom hwf s h`) answers each choice freely,
and its behaviour does not record how.  Every statement about what a module does is about its
runs, through the library of `StrataDyn/Util/Trace.lean`.

**What `choose` means.**  A choice is internal nondeterminism: freedom that the implementation
has, such as an unspecified order or a havocked value.  Trace refinement over runs (`Refines`)
lets a translation resolve it, drop it or move it, since the source's answers are picked to
match the target's run.  So `x := choose; print(x)` compiled to `print(5)` refines its source.
Inputs from the environment come through the world (`update`), which is observed, and a
translation must keep them.  Where a translation keeps every choice as it is, trace refinement
under one oracle (`OracleRefines`) says more: under every oracle, the target's run improves on
the source's under the same oracle, so a source that goes wrong on some answers frees the
target only on those.

* `StepRel`, `RunFrom`, `stepRel_total`: the relation, its runs, and the fact that every state
  steps, so that trace refinement over runs is meaningful (`Trace.Total`).
* `Reach`, `Diverges`, `always`: the configurations reached by steps, divergence, and invariants
  over runs, from a property of states, and of how runs end, that every step under every oracle
  preserves.
* `obsW`, `behW`: what a run shows, the world through `obs` but not the choices made, and its
  behaviour.  The heap is not observed: a later run started from the run's `Snapshot` reads it.
* `Refines`, trace refinement: every run of the target improves on some run of the source, where
  `wrong` says which results the target may replace (`Result.Wrong`: the faults `failure`,
  `badCall` and `badCell`).  `OracleRefines`, trace refinement under one oracle: under every
  oracle, the target's run improves on the source's under the same oracle; it implies `Refines`
  (`OracleRefines.refines`), and a forward `Trace.Sim` under each oracle proves it
  (`oracleRefines_of_sim`, `oracleRefines_of_sim_obsCfg`).  `refines_iff` states `Refines` with
  oracles: for every target oracle, some source oracle.

**Computing a run.**  The run under one oracle, `oracleRun`, is one of the runs; its
configurations, `trace hwf oracle s h n` (`trace_succ`, `trace_add`), compute, and so does what
its first steps show, `obsTrace`, in one pass.  `Exec/Fused.lean` proves that the engine,
`runFused`, follows them.  `complete` says that every run is the run under some oracle: the one
that answers each choice as the run did.  It holds because a step reads the oracle only at
`drawn` (`stepAt_local`), and `drawn` never decreases and grows when the oracle is read
(`stepAdvance`), so each answer is read once.  `diverges_iff` follows: a state has a run that
never ends iff some oracle's run never ends.  `runHooked_observer` and `runHooked_stopped`: a hook
that only observes ends at the trace's configuration, and a hook that never modifies stops at a
state of the trace.
-/

namespace Strata.Dyn.Exec

@[expose] public section

section
variable {M : RunModel} {m : LModule M} {B : Ty}

variable (m B) in
/-- A state with its run invariant. -/
abbrev Cfg : Type := { s : State M // StateOK m B s }

variable (M) in
/-- How a run ended: its result, the snapshot of its heap and its world, and the number of
choices made. -/
structure Final where
  result : Result M.interp
  snapshot : Snapshot M
  drawn : Nat

variable (m B) in
/-- Where a run stands, a configuration: running in a state, or ended with how the run ended. -/
abbrev Config : Type := Trace.Config (Cfg m B) (Final M)

/-- A step's outcome, as a configuration. -/
def StepR.config : StepR m B → Config m B
  | .next _ s h => .running ⟨s, h⟩
  | .final r hp w d => .ended ⟨r, ⟨hp, w⟩, d⟩

/-- Where a run of bounded fuel stopped or ended, as a configuration. -/
def RunEnd.config : RunEnd m B → Config m B
  | .done r sn d _ => .ended ⟨r, sn, d⟩
  | .timeout s h => .running ⟨s, h⟩

/-- A result is wrong: a fault that a correct translation may replace by any behaviour. -/
def Result.Wrong {I : Ty → Type} : Result I → Prop
  | .fault (.failure _) | .fault (.badCall _) | .fault (.badCell _) => True
  | _ => False

variable (hwf : WF m)

/-- `step`, from states with their invariant to configurations, under the oracle `oracle`. -/
def stepAt (oracle : Nat → Nat) (c : Cfg m B) : Config m B := (step hwf oracle c.1 c.2).config

/-- **The step relation**: the steps that some oracle takes. -/
def StepRel : Cfg m B → Config m B → Prop := Trace.Oracle.Rel (fun o c => stepAt hwf o c)

/-- **Every state steps**, under any oracle, so trace refinement over runs is meaningful. -/
theorem stepRel_total : Trace.Total (StepRel hwf (m := m) (B := B)) :=
  fun _ => ⟨_, fun _ => 0, rfl⟩

/-- The runs of the module from `s`. -/
abbrev RunFrom (s : State M) (h : StateOK m B s) : Type := Trace.Run (StepRel hwf) ⟨s, h⟩

variable (oracle : Nat → Nat)

/-- **The run under `oracle`.** -/
def oracleRun (s : State M) (h : StateOK m B s) : RunFrom hwf s h :=
  Trace.Oracle.run (fun o c => stepAt hwf o c) oracle ⟨s, h⟩

/-- **The run under `oracle`, after `n` steps**: the configuration, running in the state reached
or ended with how the run ended, which every later step count keeps.  These are the
configurations of `oracleRun`, by definition. -/
def trace (s : State M) (h : StateOK m B s) (n : Nat) : Config m B :=
  Trace.trace (stepAt hwf oracle) ⟨s, h⟩ n

/-- A step's outcome, followed by the trace for `n` more steps. -/
def StepR.run : StepR m B → Nat → Config m B
  | .next _ s h, n => trace hwf oracle s h n
  | .final r hp w d, _ => .ended ⟨r, ⟨hp, w⟩, d⟩

/-- `p` is reached from `s` by steps of the module. -/
def Reach (s : State M) (h : StateOK m B s) (p : Config m B) : Prop :=
  Trace.Reach (StepRel hwf) ⟨s, h⟩ p

/-- **Some run from `s` never ends.** -/
def Diverges (s : State M) (h : StateOK m B s) : Prop := Trace.Diverges (StepRel hwf) ⟨s, h⟩

section
variable {O : Type} [DecidableEq O]

/-- What a state shows: its world, through `obs`. -/
def obsW (obs : M.W → O) (c : Cfg m B) : O := obs c.1.core.world

/-- What a state shows to a simulation that also keeps the choices: its world, through `obs`,
and the number of choices made. -/
def obsCfg (obs : M.W → O) (c : Cfg m B) : O × Nat := (obs c.1.core.world, c.1.drawn)

/-- **The behaviour of a run**: the world through `obs` at each state, and the result if the
run ends.  It is `r.beh (obsW obs) Final.result`. -/
noncomputable def behW (obs : M.W → O) {s : State M} {h : StateOK m B s} (r : RunFrom hwf s h) :
    Trace.Beh O (Result M.interp) :=
  r.beh (obsW obs) Final.result

/-- What the first `n` steps of the run under `oracle` show, through `obs` of a state, with
repeats dropped, computed in one pass (`oracleRun_obsUpTo`). -/
def obsTrace (obs : Cfg m B → O) (s : State M) (h : StateOK m B s) (n : Nat) : List O :=
  Trace.obsFrom obs (stepAt hwf oracle) [obs ⟨s, h⟩] ⟨s, h⟩ n

/-- What the run under `oracle` shows is `obsTrace`. -/
theorem oracleRun_obsUpTo (obs : Cfg m B → O) (s : State M) (h : StateOK m B s) (n : Nat) :
    (oracleRun hwf oracle s h).obsUpTo obs n = obsTrace hwf oracle obs s h n :=
  (Trace.Run.obsUpTo_congr (oracleRun hwf oracle s h) (Trace.Run.ofFun (stepAt hwf oracle) _)
    (fun _ => rfl) n).trans (Trace.Run.obsUpTo_ofFun _ _ n)

variable {m₁ : LModule M} {B₁ : Ty} (hwf₁ : WF m₁)

/-- **Trace refinement**: every run of `m₁` from `c₁` improves, by `wrong`, on some run of `m` from
`c`, observing the world through `obs`.  The source comes first. -/
def Refines (obs : M.W → O) (wrong : Result M.interp → Prop) (c : Cfg m B) (c₁ : Cfg m₁ B₁) :
    Prop :=
  Trace.Refines (StepRel hwf) (StepRel hwf₁) (obsW obs) (obsW obs) Final.result Final.result
    wrong c c₁

/-- **Trace refinement under one oracle**: under every oracle, the run of `m₁` from `c₁`
improves, by `wrong`, on the run of `m` from `c` under the same oracle, observing the world
through `obs`.  The oracle is shared, so a choice is an input that `m₁` must answer as `m`
does. -/
def OracleRefines (obs : M.W → O) (wrong : Result M.interp → Prop) (c : Cfg m B)
    (c₁ : Cfg m₁ B₁) : Prop :=
  Trace.Oracle.Refines (fun o c => stepAt hwf o c) (fun o c => stepAt hwf₁ o c) (obsW obs)
    (obsW obs) Final.result Final.result wrong c c₁

end

variable {hwf} {oracle}

/-- **One step**: the trace after `n + 1` steps is `step`'s outcome, followed for `n` more. -/
theorem trace_succ (n : Nat) (s : State M) (h : StateOK m B s) :
    trace hwf oracle s h (n + 1) = (step hwf oracle s h).run hwf oracle n := by
  unfold trace
  cases hs : step hwf oracle s h with
  | next e s₁ h₁ =>
    exact Trace.trace_succ_running (show stepAt hwf oracle ⟨s, h⟩ = .running ⟨s₁, h₁⟩ by
      rw [stepAt, hs]; rfl) n
  | final r hp w d =>
    exact Trace.trace_succ_ended (show stepAt hwf oracle ⟨s, h⟩ = .ended ⟨r, ⟨hp, w⟩, d⟩ by
      rw [stepAt, hs]; rfl) n

/-- The trace after `n + k` steps is the trace after `n`, followed for `k` more. -/
theorem trace_add (n k : Nat) (s : State M) (h : StateOK m B s) :
    trace hwf oracle s h (n + k) = (trace hwf oracle s h n).after (stepAt hwf oracle) k :=
  Trace.trace_add n k _

/-! ## Reading the oracle -/

/-- The state's next step answers a choice. -/
def State.Chooses (s : State M) : Prop :=
  ∃ (i : Inst M) (k : Nat → i.Tree), s.mode = .request i (.choose k)

/-- **A step that answers no choice does not read the oracle.** -/
private theorem step_oracle {s : State M} (h : StateOK m B s) (hc : ¬ s.Chooses)
    (o o₁ : Nat → Nat) :
    step hwf o s h = step hwf o₁ s h := by
  obtain ⟨c, mode, d, p⟩ := s
  cases mode with
  | request i t =>
    cases t with
    | choose k => exact absurd ⟨i, k, rfl⟩ hc
    | vis q k => cases q <;> rfl
    | _ => rfl
  | _ => rfl

/-- **A step reads the oracle only at `drawn`.** -/
theorem stepAt_local : Trace.Oracle.Local (fun o c => stepAt hwf o c)
    (fun c : Cfg m B => c.1.drawn) := by
  rintro o o₁ ⟨⟨c, mode, d, p⟩, h⟩ hd
  by_cases hc : State.Chooses ⟨c, mode, d, p⟩
  · obtain ⟨i, k, rfl⟩ := hc
    show (settle hwf c i h.1 h.2 (d + 1) (.answer (.choose (o d))) (k (o d))).config =
      (settle hwf c i h.1 h.2 (d + 1) (.answer (.choose (o₁ d))) (k (o₁ d))).config
    rw [hd]
  · exact congrArg StepR.config (step_oracle h hc o o₁)

section
variable (hwf)

/-- The step's next state, if any, has `drawn = d`. -/
private def StepR.DrawnIs (d : Nat) : StepR m B → Prop
  | .next _ s _ => s.drawn = d
  | .final .. => True

/-- Both outcomes of a cell check satisfy `P`. -/
private theorem Heap.cell_rec {R : Type} {P : R → Prop} (heap : Heap M) (l : Nat) (t : Ty)
    {ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → R} {bad : Unit → R}
    (hok : ∀ hl ht, P (ok hl ht)) (hbad : P (bad ())) : P (heap.cell l t ok bad) := by
  by_cases h : heap.Holds l t
  · rw [Heap.cell_pos h]
    exact hok _ _
  · rw [Heap.cell_neg h]
    exact hbad

/-- Both outcomes of a call check satisfy `P`. -/
private theorem LModule.callee_rec {R : Type} {P : R → Prop} (m : LModule M) (heap : Heap M)
    (idx captured : Nat) (ts : List Ty) (r : Ty)
    {ok : (hi : idx < m.funcs.size) → (caps : List (Dyn M.interp)) →
      (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts → (m.funcs[idx]'hi).ret = r → R}
    {bad : Unit → R} (hok : ∀ hi caps hp hr, P (ok hi caps hp hr)) (hbad : P (bad ())) :
    P (m.callee heap idx captured ts r ok bad) := by
  unfold LModule.callee
  split
  · split
    · split
      · exact hok _ _ _ _
      · exact hbad
    · exact hbad
  · exact hbad

/-- A transfer keeps `drawn`. -/
private theorem transfer_drawn (c : Core M) (n : Next M) (hn : NextOK m c.top n)
    (hK : ContsOK m B c.top.func.ret c.conts) (d : Nat) (ev : Event) :
    (transfer c n hn hK d ev).DrawnIs d := by
  cases n <;> rfl

/-- Settling a rule's tree keeps `drawn`. -/
private theorem settle_drawn (c : Core M) (i : Inst M) (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) (d : Nat) (ev : Event) (t : i.Tree) :
    (settle hwf c i hi hK d ev t).DrawnIs d := by
  unfold settle
  split
  all_goals first
    | rfl
    | (unfold transfer; split <;> rfl)
    | (unfold visitCall; exact LModule.callee_rec _ _ _ _ _ _ (fun _ _ _ _ => rfl) rfl)

/-- Answering a request other than a choice keeps `drawn`. -/
private theorem serve_drawn (c : Core M) (i : Inst M) (t : i.Tree)
    (h : InstOK m c.top i ∧ ContsOK m B c.top.func.ret c.conts) (d : Nat) (o : Nat → Nat)
    (ht : ∀ k, t ≠ .choose k) : (serve hwf o c i t h d).DrawnIs d := by
  unfold serve
  split
  · exact absurd rfl (ht _)
  all_goals first
    | exact settle_drawn hwf _ _ _ _ _ _ _
    | (split; exact settle_drawn hwf _ _ _ _ _ _ _)
    | exact Heap.cell_rec _ _ _ (fun _ _ => settle_drawn hwf _ _ _ _ _ _ _) rfl
    | exact LModule.callee_rec _ _ _ _ _ _ (fun _ _ _ _ => settle_drawn hwf _ _ _ _ _ _ _) rfl

/-- Running an instruction or a terminator keeps `drawn`. -/
private theorem exec_drawn (c : Core M) (h : CoreOK m B c) (d : Nat) :
    (exec hwf c h d).DrawnIs d := by
  unfold exec execCode
  split
  · unfold execTerm
    split
    · exact transfer_drawn _ _ _ _ _ _
    · exact settle_drawn hwf _ _ _ _ _ _ _
  all_goals first
    | rfl
    | exact settle_drawn hwf _ _ _ _ _ _ _
    | exact Heap.cell_rec _ _ _ (fun _ _ => rfl) rfl
    | exact LModule.callee_rec _ _ _ _ _ _ (fun _ _ _ _ => rfl) rfl

/-- Leaving a frame keeps `drawn`. -/
private theorem leave_drawn (c : Core M) (v : Dyn M.interp) (h : LeftOK m B c v) (d : Nat) :
    (leave hwf c v h d).DrawnIs d := by
  unfold leave leaveTo
  split
  all_goals first
    | rfl
    | exact settle_drawn hwf _ _ _ _ _ _ _

/-- A step that answers no choice keeps `drawn`. -/
private theorem step_drawn {s : State M} (h : StateOK m B s) (hc : ¬ s.Chooses) (o : Nat → Nat) :
    (step hwf o s h).DrawnIs s.drawn := by
  obtain ⟨c, mode, d, p⟩ := s
  cases mode with
  | request i t => exact serve_drawn hwf c i t h d o fun k he => hc ⟨i, k, congrArg _ he⟩
  | exec => exact exec_drawn hwf c h d
  | ret v => exact leave_drawn hwf c v h d
  | again r => exact settle_drawn hwf _ _ _ _ _ _ _
  | jump to => rfl
  | call callee w => rfl
  | done r => trivial

/-- A step whose next state has `drawn = d` steps to a configuration with that `drawn`. -/
private theorem StepR.drawn_config {e : StepR m B} {d : Nat} {c₁ : Cfg m B} (he : e.DrawnIs d)
    (hc : e.config = .running c₁) : c₁.1.drawn = d := by
  cases e with
  | next ev s hs => cases hc; exact he
  | final _ _ _ _ => exact nomatch hc

/-- **`drawn` never decreases, and a step that keeps it does not read the oracle.**  Answering a
choice counts it, and every other step keeps `drawn`. -/
theorem stepAdvance :
    Trace.Oracle.Advance (fun o c => stepAt hwf o c) (fun c : Cfg m B => c.1.drawn) := by
  rintro o ⟨⟨c, mode, d, p⟩, h⟩ c₁ hs
  by_cases hc : State.Chooses ⟨c, mode, d, p⟩
  · obtain ⟨i, k, rfl⟩ := hc
    have := StepR.drawn_config (settle_drawn hwf c i h.1 h.2 (d + 1) _ _) hs
    exact ⟨Nat.le_trans (Nat.le_succ d) (Nat.le_of_eq this.symm),
      fun he => absurd (he.symm.trans this) (Nat.succ_ne_self d).symm⟩
  · exact ⟨Nat.le_of_eq (StepR.drawn_config (step_drawn hwf h hc o) hs).symm,
      fun _ o₁ => congrArg StepR.config (step_oracle h hc o₁ o)⟩

end

/-! ## Every run is the run under an oracle -/

/-- **Completeness.** Every run of the module is the run under some oracle: the one that answers
each choice as the run did. -/
theorem complete {s : State M} {h : StateOK m B s} (r : RunFrom hwf s h) :
    ∃ oracle, ∀ n, r.cfg n = trace hwf oracle s h n :=
  Trace.Oracle.complete stepAt_local (stepAdvance hwf) r

/-- **Divergence is divergence under some oracle.** -/
theorem diverges_iff {s : State M} {h : StateOK m B s} :
    Diverges hwf s h ↔ ∃ oracle, ∀ n, ∃ c, trace hwf oracle s h n = .running c :=
  Trace.Oracle.diverges_iff stepAt_local (stepAdvance hwf)

/-- A property of states that every step, under every oracle, preserves, with a property of how
runs end that every final step establishes, is preserved by the step relation. -/
theorem inductive_of_step {P : State M → Prop} {Q : Final M → Prop}
    (hI : ∀ oracle s (h : StateOK m B s), P s →
      (step hwf oracle s h).config.Sat (fun c => P c.1) Q) :
    Trace.Inductive (StepRel hwf) (fun c : Cfg m B => P c.1) Q := by
  rintro c _ hc ⟨o, rfl⟩
  exact hI o c.1 c.2 hc

/-- **Invariance.** A property of states that every step preserves, with a property of how runs
end that every final step establishes, holds at every configuration of every run that starts
where it holds. -/
theorem always {P : State M → Prop} {Q : Final M → Prop}
    (hI : ∀ oracle s (h : StateOK m B s), P s → (step hwf oracle s h).config.Sat (fun c => P c.1) Q)
    {s : State M} {h : StateOK m B s} (r : RunFrom hwf s h) (hs : P s) (n : Nat) :
    (r.cfg n).Sat (fun c => P c.1) Q :=
  r.always (inductive_of_step hI) hs n

section
variable {m₁ : LModule M} {B₁ : Ty} {hwf₁ : WF m₁} {O : Type} [DecidableEq O]
  {obs : M.W → O} {wrong : Result M.interp → Prop} {c : Cfg m B} {c₁ : Cfg m₁ B₁}

/-- **Trace refinement under one oracle gives trace refinement over runs.** -/
theorem OracleRefines.refines (h : OracleRefines hwf hwf₁ obs wrong c c₁) :
    Refines hwf hwf₁ obs wrong c c₁ :=
  Trace.Oracle.Refines.refines stepAt_local (stepAdvance hwf₁) h

/-- Trace refinement under one oracle with fewer wrong results is trace refinement with
more. -/
theorem OracleRefines.mono {wrong₁ : Result M.interp → Prop} (hw : ∀ r, wrong r → wrong₁ r)
    (h : OracleRefines hwf hwf₁ obs wrong c c₁) : OracleRefines hwf hwf₁ obs wrong₁ c c₁ :=
  fun o => (h o).mono hw

/-- **Trace refinement under one oracle is transitive**, so passes that keep choices compose. -/
theorem OracleRefines.trans {m₂ : LModule M} {B₂ : Ty} {hwf₂ : WF m₂} {c₂ : Cfg m₂ B₂}
    (h₁ : OracleRefines hwf hwf₁ obs wrong c c₁) (h₂ : OracleRefines hwf₁ hwf₂ obs wrong c₁ c₂) :
    OracleRefines hwf hwf₂ obs wrong c c₂ :=
  Trace.Oracle.Refines.trans h₁ h₂

/-- **Equal behaviours under every oracle are equal behaviours of runs**: every run of `m₁` behaves
as some run of `m`, and every run of `m` as some run of `m₁`. -/
theorem behW_runs_of_oracle
    (h : ∀ oracle, behW hwf₁ obs (oracleRun hwf₁ oracle c₁.1 c₁.2) =
      behW hwf obs (oracleRun hwf oracle c.1 c.2)) :
    (∀ r₁ : RunFrom hwf₁ c₁.1 c₁.2, ∃ r : RunFrom hwf c.1 c.2,
      behW hwf₁ obs r₁ = behW hwf obs r) ∧
    ∀ r : RunFrom hwf c.1 c.2, ∃ r₁ : RunFrom hwf₁ c₁.1 c₁.2,
      behW hwf₁ obs r₁ = behW hwf obs r := by
  constructor
  · intro r₁
    obtain ⟨o, ho⟩ := complete r₁
    refine ⟨oracleRun hwf o c.1 c.2, ?_⟩
    rw [← h o]
    exact Trace.Run.beh_congr r₁ (oracleRun hwf₁ o c₁.1 c₁.2) ho
  · intro r
    obtain ⟨o, ho⟩ := complete r
    refine ⟨oracleRun hwf₁ o c₁.1 c₁.2, ?_⟩
    rw [h o]
    exact (Trace.Run.beh_congr r (oracleRun hwf o c.1 c.2) ho).symm

variable (obs) in
/-- **Trace refinement, with oracles**: every run of `m₁` refines some run of `m` iff for every
oracle of `m₁` there is an oracle of `m` whose run the run of `m₁` improves on. -/
theorem refines_iff : Refines hwf hwf₁ obs wrong c c₁ ↔
    ∀ oracle₁, ∃ oracle, Trace.Improves wrong (behW hwf₁ obs (oracleRun hwf₁ oracle₁ c₁.1 c₁.2))
      (behW hwf obs (oracleRun hwf oracle c.1 c.2)) :=
  Trace.Oracle.refines_iff stepAt_local (stepAdvance hwf) stepAt_local (stepAdvance hwf₁) c c₁

variable (obs) in
/-- **A forward simulation under one oracle, for every oracle, gives trace refinement under
one oracle.**  For modules `m` and `m₁`, if for every oracle a `Trace.Sim` relates the starts,
observing the world, then under every oracle the run of `m₁` improves on the run of `m`. -/
theorem oracleRefines_of_sim
    (hsim : ∀ oracle, ∃ sim : Trace.Sim (stepAt hwf oracle) (stepAt hwf₁ oracle) (obsW obs)
      (obsW obs) Final.result Final.result wrong, sim.rel c c₁) :
    OracleRefines hwf hwf₁ obs wrong c c₁ :=
  Trace.Oracle.refines_of_sim hsim

variable (obs) in
/-- **A simulation that observes the choices gives trace refinement that does not.** A `Trace.Sim`
under one oracle for every oracle, observing the world and the choices made through
`obsCfg obs`, gives trace refinement under one oracle observing the world alone. -/
theorem oracleRefines_of_sim_obsCfg
    (hsim : ∀ oracle, ∃ sim : Trace.Sim (stepAt hwf oracle) (stepAt hwf₁ oracle) (obsCfg obs)
      (obsCfg obs) Final.result Final.result wrong, sim.rel c c₁) :
    OracleRefines hwf hwf₁ obs wrong c c₁ :=
  oracleRefines_of_sim obs fun oracle =>
    let ⟨sim, hr⟩ := hsim oracle
    ⟨sim.mapObs Prod.fst, hr⟩

end

/-! ## Hooks against the trace -/

/-- A hook that only observes never stops the run, and on `n` fuel ends at the configuration
the trace has after `n` steps. -/
theorem runHooked_observer {ρ : Type} (hook : Hook m B ρ)
    (hobs : ∀ st ev s, ∃ st₁, hook st ev s = .continue st₁) :
    ∀ (n : Nat) (st : ρ) (s : State M) (h : StateOK m B s),
      (runHooked hwf oracle hook n st s h).1.toRunEnd.map RunEnd.config =
        some (trace hwf oracle s h n)
  | 0, _, _, _ => rfl
  | n + 1, st, s, h => by
    rw [runHooked, trace_succ]
    cases step hwf oracle s h with
    | final r hp w d => rfl
    | next ev s₁ h₁ =>
      obtain ⟨st₁, hst⟩ := hobs st ev s₁
      dsimp only
      rw [hst]
      exact runHooked_observer hook hobs n st₁ s₁ h₁

/-- A hook that never modifies, if it stops a run on `n` fuel with `l` left, stops it in the
state that the trace is running in after the `n - l` steps taken. -/
theorem runHooked_stopped {ρ : Type} (hook : Hook m B ρ)
    (hnm : ∀ st ev s st₁ s₁ h₁, hook st ev s ≠ .modify st₁ s₁ h₁) :
    ∀ (n : Nat) (st : ρ) (s : State M) (h : StateOK m B s) {s₁ : State M}
      {h₁ : StateOK m B s₁} {l : Nat}, (runHooked hwf oracle hook n st s h).1 = .stopped s₁ h₁ l →
      l ≤ n ∧ trace hwf oracle s h (n - l) = .running ⟨s₁, h₁⟩
  | 0, _, _, _, _, _, _, hs => nomatch hs
  | n + 1, st, s, h, s₁, h₁, l, hs => by
    rw [runHooked] at hs
    cases hstep : step hwf oracle s h with
    | final r hp w d =>
      rw [hstep] at hs
      exact nomatch hs
    | next ev s₂ h₂ =>
      rw [hstep] at hs
      dsimp only at hs
      cases hk : hook st ev s₂ with
      | «continue» st₁ =>
        rw [hk] at hs
        obtain ⟨hl, ht⟩ := runHooked_stopped hook hnm n st₁ s₂ h₂ hs
        refine ⟨Nat.le_succ_of_le hl, ?_⟩
        rw [Nat.sub_add_comm hl, trace_succ, hstep]
        exact ht
      | modify st₁ s₃ h₃ => exact absurd hk (hnm _ _ _ _ _ _)
      | stop st₁ =>
        rw [hk] at hs
        cases hs
        refine ⟨Nat.le_succ _, ?_⟩
        rw [Nat.add_sub_cancel_left, trace_succ, hstep]
        rfl

end

end

end Strata.Dyn.Exec
