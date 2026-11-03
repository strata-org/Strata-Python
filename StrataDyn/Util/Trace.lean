/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

set_option autoImplicit false

/-!
# Runs of machines, their behaviours, and trace refinement

A machine is a step relation `step : S → Config S F → Prop`: from a state, the configurations it
may step to, running in a next state or ended with an outcome.  A run is a configuration at every
time, each a step from the one before; a run that never ends is a run like any other, so no
theorem here takes fuel.  Runs are quantified over, not computed: a machine with choices has
many, and nothing records how a step was chosen.

* `Run`, `Run.drop`, `Reach`, `Inductive`, `always`, `Run.always`: runs, the configurations
  reachable by steps, and invariants over both.
* `Run.Diverges`, `Diverges`: a run that never ends, and a state with such a run.  `Total`: every
  state has a step.  Trace refinement is meaningful only over a total relation, since a state
  with no step has no run.
* A machine given by a function `f` is the relation `graph f`.  Its run from `s` is
  `Run.ofFun f s`, whose configurations `trace f s n` compute by recursion (`trace_succ`,
  `trace_add`); every run of `graph f` has them (`Run.eq_trace`), so it has one behaviour
  (`Run.beh_graph`).  `Run.ofDet` projects the run of a function through a map of its states.
* `Run.obsUpTo`: what the first `n` steps of a run show, through an observation of its states,
  with repeats dropped.  It is for proofs: evaluated on a function's run it recomputes the run at
  every step.  `obsFrom` computes the same in one pass (`Run.obsUpTo_ofFun`).
* `Beh` and `Run.beh`: the behaviour of a run, as in CompCert: it ends with the observations made
  and a result, diverges after finitely many observations (`silent`), or makes infinitely many
  (`react`).  `Run.beh_extends_iff`, `Run.beh_ended`, `Run.beh_silent` and `Run.beh_react` give it
  from the configurations.
* `Improves` and `Refines`: a behaviour improves on another if it is the same, or the other goes
  wrong after observations it extends; a target refines a source (trace refinement) if every
  target run improves on some source run.  Both are transitive (`Improves.trans`,
  `Refines.trans`), and trace refinement of a source that never goes wrong keeps behaviours
  (`Refines.beh_eq`).
* Proofs of trace refinement:
  * `RunMatch.improves`: a forward matching of two given runs, with a measure, gives improvement.
    The other methods reduce to it.
  * `Sim.refines`: a forward simulation of a function by a function.
  * `BSim.refines`, in `Util/Trace/Backward.lean`: a backward simulation, which chooses the
    source's steps, so a translation may drop or move a choice.
* Oracle machines `ostep : (Nat → Nat) → S → Config S F`, in `Oracle`: `Oracle.Rel` is the steps
  that some oracle takes and `Oracle.run` the run under one oracle.  Under `Oracle.Local` and
  `Oracle.Advance`, every run of the relation is the run under one oracle (`Oracle.complete`), so
  divergence is divergence under some oracle (`Oracle.diverges_iff`) and trace refinement is
  "for every target oracle, some source oracle" (`Oracle.refines_iff`).  `Oracle.Refines` is
  trace refinement under one oracle shared by both, which gives `Refines`
  (`Oracle.Refines.refines`), and which a forward `Sim` under each oracle proves
  (`Oracle.refines_of_sim`).
-/

namespace Strata.Dyn.Trace

@[expose] public section

/-- Where a run stands, a configuration: running in a state, or ended with an outcome. -/
inductive Config (S F : Type) where
  | running (s : S)
  | ended (f : F)

variable {S F : Type}

/-- `P` holds of the state, or `Q` of the outcome. -/
def Config.Sat (P : S → Prop) (Q : F → Prop) : Config S F → Prop
  | .running s => P s
  | .ended f => Q f

/-- The configuration, with its state, if running, mapped through `p`. -/
def Config.mapS {Q : Type} (p : Q → S) : Config Q F → Config S F
  | .running q => .running (p q)
  | .ended f => .ended f

/-- The measure `μ` of the state, or `0` for an outcome. -/
def Config.measure (μ : S → Nat) : Config S F → Nat
  | .running s => μ s
  | .ended _ => 0

/-- Mapping through the identity changes nothing. -/
theorem Config.mapS_id (c : Config S F) : c.mapS id = c := by
  cases c <;> rfl

/-! ## Runs -/

/-- **A run of `step` from `s`**: a configuration at every time, starting running in `s`, each
one a step of `step` from the one before while running, and kept once ended. -/
structure Run (step : S → Config S F → Prop) (s : S) where
  cfg : Nat → Config S F
  start : cfg 0 = .running s
  next : ∀ {n : Nat} {s₁ : S}, cfg n = .running s₁ → step s₁ (cfg (n + 1))
  stay : ∀ {n : Nat} {f : F}, cfg n = .ended f → cfg (n + 1) = .ended f

variable {step : S → Config S F → Prop}

/-- `c` is reached from `s` by steps of `step`. -/
inductive Reach (step : S → Config S F → Prop) : S → Config S F → Prop where
  | refl (s : S) : Reach step s (.running s)
  | ended {s : S} {f : F} : step s (.ended f) → Reach step s (.ended f)
  | cons {s s₁ : S} {c : Config S F} : step s (.running s₁) → Reach step s₁ c → Reach step s c

/-- `P` holds after every step from a state it holds of: of the next state, or `Q` of the
outcome. -/
def Inductive (step : S → Config S F → Prop) (P : S → Prop) (Q : F → Prop) : Prop :=
  ∀ s c, P s → step s c → c.Sat P Q

/-- A run of a smaller relation is a run of a larger one. -/
def Run.mono {step₁ : S → Config S F → Prop} (h : ∀ s c, step s c → step₁ s c) {s : S}
    (r : Run step s) : Run step₁ s where
  cfg := r.cfg
  start := r.start
  next hn := h _ _ (r.next hn)
  stay := r.stay

/-- The run from `n` steps on, from the state it is running in then. -/
def Run.drop {s : S} (r : Run step s) (n : Nat) {s₁ : S} (h : r.cfg n = .running s₁) :
    Run step s₁ where
  cfg i := r.cfg (i + n)
  start := by rw [Nat.zero_add]; exact h
  next := by
    intro i s₂ h₂
    rw [Nat.add_right_comm]
    exact r.next h₂
  stay := by
    intro i f h₂
    rw [Nat.add_right_comm]
    exact r.stay h₂

/-- An ended run stays ended. -/
theorem Run.ended_le {s : S} (r : Run step s) {i j : Nat} {f : F} (h : r.cfg i = .ended f)
    (hle : i ≤ j) : r.cfg j = .ended f := by
  induction hle with
  | refl => exact h
  | step _ ih => exact r.stay ih

/-- A run that ends ends with one outcome. -/
theorem Run.ended_unique {s : S} (r : Run step s) {i j : Nat} {f f₁ : F}
    (h : r.cfg i = .ended f) (h₁ : r.cfg j = .ended f₁) : f = f₁ := by
  rcases Nat.le_total i j with hle | hle
  · exact Config.ended.inj ((r.ended_le h hle).symm.trans h₁)
  · exact Config.ended.inj (h.symm.trans (r.ended_le h₁ hle))

/-- A run still going at `m` was going at every `n ≤ m`. -/
theorem Run.running_le {s : S} (r : Run step s) {n m : Nat} {s₁ : S}
    (h : r.cfg m = .running s₁) (hle : n ≤ m) : ∃ s₂, r.cfg n = .running s₂ := by
  cases hn : r.cfg n with
  | running s₂ => exact ⟨s₂, rfl⟩
  | ended f => exact nomatch (r.ended_le hn hle).symm.trans h

/-- A step is reached. -/
theorem Reach.single {s : S} {c : Config S F} (h : step s c) : Reach step s c := by
  cases c with
  | running s₁ => exact .cons h (.refl s₁)
  | ended f => exact .ended h

/-- A step from a state reached is reached. -/
theorem Reach.tail {s s₁ : S} {c : Config S F} (h : Reach step s (.running s₁)) (hs : step s₁ c) :
    Reach step s c := by
  generalize hc : Config.running s₁ = c₁ at h
  induction h with
  | refl => cases hc; exact .single hs
  | ended => exact nomatch hc
  | cons hst _ ih => exact .cons hst (ih hc)

/-- Every configuration of a run is reached. -/
theorem Run.reach {s : S} (r : Run step s) : ∀ n, Reach step s (r.cfg n)
  | 0 => by rw [r.start]; exact .refl s
  | n + 1 => by
    have ih := Run.reach r n
    cases hn : r.cfg n with
    | running s₁ => rw [hn] at ih; exact ih.tail (r.next hn)
    | ended f => rw [r.stay hn]; rw [hn] at ih; exact ih

/-- **Invariance.** A property that every step preserves holds at every configuration reached
from a state where it holds. -/
theorem always {P : S → Prop} {Q : F → Prop} (hI : Inductive step P Q) {s : S} {c : Config S F}
    (hs : P s) (h : Reach step s c) : c.Sat P Q := by
  induction h with
  | refl => exact hs
  | ended hst => exact hI _ _ hs hst
  | cons hst _ ih => exact ih (hI _ _ hs hst)

/-- **Invariance on runs.** A property that every step preserves holds at every configuration of
a run from a state where it holds. -/
theorem Run.always {P : S → Prop} {Q : F → Prop} (hI : Inductive step P Q) {s : S}
    (r : Run step s) (hs : P s) (n : Nat) : (r.cfg n).Sat P Q :=
  Trace.always hI hs (r.reach n)

/-- **The run never ends**: it is running at every time. -/
def Run.Diverges {s : S} (r : Run step s) : Prop := ∀ n, ∃ s₁, r.cfg n = .running s₁

/-- **Some run from `s` never ends.** -/
def Diverges (step : S → Config S F → Prop) (s : S) : Prop := ∃ r : Run step s, r.Diverges

/-- **Every state has a step.**  A state with no step has no run, so over a relation that is
not total, trace refinement and the backward simulation say nothing of a target that gets
stuck: it refines any source.  Dyn's relation is total (`Exec.stepRel_total`), and its faults are
outcomes. -/
def Total (step : S → Config S F → Prop) : Prop := ∀ s, ∃ c, step s c

/-- A run that does not diverge ends. -/
theorem Run.exists_ended {s : S} (r : Run step s) (h : ¬ r.Diverges) :
    ∃ n f, r.cfg n = .ended f := by
  apply Classical.byContradiction
  intro hne
  apply h
  intro n
  cases hn : r.cfg n with
  | running s₁ => exact ⟨s₁, rfl⟩
  | ended f => exact absurd ⟨n, f, hn⟩ hne

/-! ## Machines given by a function -/

section
variable (f : S → Config S F)

/-- The configurations of the run of the function `f` from `s`, after `n` steps. -/
def trace (s : S) : Nat → Config S F
  | 0 => .running s
  | n + 1 => match f s with
    | .running s₁ => trace s₁ n
    | .ended e => .ended e

/-- One more step of `f` from a configuration. -/
def Config.next : Config S F → Config S F
  | .running s => f s
  | .ended e => .ended e

/-- `k` more steps of `f` from a configuration. -/
def Config.after (k : Nat) : Config S F → Config S F
  | .running s => trace f s k
  | .ended e => .ended e

/-- The graph of a step function, as a relation. -/
def graph : S → Config S F → Prop := fun s c => f s = c

end

section
variable {f : S → Config S F}

/-- A step to a running configuration: the run goes on from its state. -/
theorem trace_succ_running {s s₁ : S} (h : f s = .running s₁) (n : Nat) :
    trace f s (n + 1) = trace f s₁ n := by
  rw [trace, h]

/-- A step that ends the run: the run keeps its outcome. -/
theorem trace_succ_ended {s : S} {e : F} (h : f s = .ended e) (n : Nat) :
    trace f s (n + 1) = .ended e := by
  rw [trace, h]

/-- A run on `n + k` steps is the run on `n`, continued for `k`. -/
theorem trace_add : ∀ (n k : Nat) (s : S), trace f s (n + k) = (trace f s n).after f k
  | 0, k, s => by rw [Nat.zero_add]; rfl
  | n + 1, k, s => by
    rw [Nat.add_right_comm]
    cases h : f s with
    | running s₁ => rw [trace_succ_running h, trace_succ_running h]; exact trace_add n k s₁
    | ended e => rw [trace_succ_ended h, trace_succ_ended h]; rfl

/-- The run on `n + 1` steps is one step from the run on `n`. -/
theorem trace_succ (n : Nat) (s : S) : trace f s (n + 1) = (trace f s n).next f := by
  rw [trace_add]
  cases trace f s n with
  | running s₁ =>
    show trace f s₁ 1 = f s₁
    cases h : f s₁ with
    | running s₂ => rw [trace_succ_running h]; rfl
    | ended e => rw [trace_succ_ended h]
  | ended e => rfl

end

/-- **The run of a function.** -/
def Run.ofFun (f : S → Config S F) (s : S) : Run (graph f) s where
  cfg := trace f s
  start := rfl
  next := by
    intro n s₁ h
    show f s₁ = _
    rw [trace_succ, h]
    rfl
  stay := by
    intro n e h
    rw [trace_succ, h]
    rfl

/-- **A run of a function's graph is its trace.** -/
theorem Run.eq_trace {f : S → Config S F} {s : S} (r : Run (graph f) s) :
    ∀ n, r.cfg n = trace f s n
  | 0 => r.start
  | n + 1 => by
    rw [trace_succ, ← Run.eq_trace r n]
    cases hn : r.cfg n with
    | running s₁ => exact (r.next hn).symm
    | ended e => exact r.stay hn

section
variable {Q : Type}

/-- **A projected run.** The run of a function `det` from a state where an invariant `P` holds,
projected through `p`, is a run of `step` if each step of `det` from where `P` holds projects to
one of `step`. -/
def Run.ofDet (det : Q → Config Q F) (p : Q → S) (P : Q → Prop)
    (hI : Inductive (graph det) P (fun _ => True))
    (hR : ∀ q, P q → step (p q) ((det q).mapS p)) (q₀ : Q) (h₀ : P q₀) : Run step (p q₀) where
  cfg n := (trace det q₀ n).mapS p
  start := rfl
  next := by
    intro n s₁ h
    rw [trace_succ]
    cases hn : trace det q₀ n with
    | ended f => rw [hn] at h; exact nomatch h
    | running q =>
      rw [hn] at h
      have hq : (trace det q₀ n).Sat P fun _ => True := (Run.ofFun det q₀).always hI h₀ n
      rw [hn] at hq
      cases h
      exact hR q hq
  stay := by
    intro n f h
    rw [trace_succ]
    cases hn : trace det q₀ n with
    | running q => rw [hn] at h; exact nomatch h
    | ended f₁ => rw [hn] at h; exact h

/-- Under a total relation, every state has a run. -/
theorem Total.nonempty (h : Total step) (s : S) : Nonempty (Run step s) :=
  ⟨Run.ofDet (fun x => (h x).choose) id (fun _ => True) (fun _ c _ _ => by cases c <;> trivial)
    (fun x _ => by rw [Config.mapS_id]; exact (h x).choose_spec) s trivial⟩

end

/-! ## Observations -/

section
variable {O : Type} [DecidableEq O]

/-- `acc` followed by `o`, unless `o` is already its last element. -/
def addObs (acc : List O) (o : O) : List O :=
  if acc.getLast? = some o then acc else acc ++ [o]

/-- After `addObs`, the last observation is the one added. -/
theorem addObs_last (acc : List O) (o : O) : (addObs acc o).getLast? = some o := by
  unfold addObs
  split
  · assumption
  · exact List.getLast?_concat

/-- Adding the last observation again changes nothing. -/
theorem addObs_of_last {acc : List O} {o : O} (h : acc.getLast? = some o) :
    addObs acc o = acc := by
  unfold addObs
  split
  · rfl
  · contradiction

/-- Adding an observation other than the last appends it. -/
theorem addObs_of_ne {acc : List O} {o : O} (h : acc.getLast? ≠ some o) :
    addObs acc o = acc ++ [o] := by
  unfold addObs
  split
  · contradiction
  · rfl

/-- `addObs` only extends. -/
theorem prefix_addObs (acc : List O) (o : O) : acc <+: addObs acc o := by
  unfold addObs
  split
  · exact List.prefix_refl acc
  · exact List.prefix_append acc [o]

variable (obs : S → O)

/-- What the first `n` steps of a run show: the observations of the states that it passes
through, from its start on, with repeats dropped.  An outcome shows nothing.  This is for proofs:
evaluated on a function's run, it recomputes the run to each time, so a computation uses
`obsFrom` (`Run.obsUpTo_ofFun`). -/
def Run.obsUpTo {s : S} (r : Run step s) : Nat → List O
  | 0 => [obs s]
  | n + 1 => match r.cfg (n + 1) with
    | .running s₁ => addObs (r.obsUpTo n) (obs s₁)
    | .ended _ => r.obsUpTo n

variable {obs}

/-- One more step shows the next state, if it differs from the last observation. -/
theorem Run.obsUpTo_succ {s : S} (r : Run step s) (n : Nat) :
    r.obsUpTo obs (n + 1) = match r.cfg (n + 1) with
      | .running s₁ => addObs (r.obsUpTo obs n) (obs s₁)
      | .ended _ => r.obsUpTo obs n := rfl

/-- A step to a running configuration shows its state. -/
theorem Run.obsUpTo_running {s : S} (r : Run step s) {n : Nat} {s₁ : S}
    (h : r.cfg (n + 1) = .running s₁) :
    r.obsUpTo obs (n + 1) = addObs (r.obsUpTo obs n) (obs s₁) := by
  rw [Run.obsUpTo_succ, h]

/-- A step to an outcome shows nothing. -/
theorem Run.obsUpTo_ended {s : S} (r : Run step s) {n : Nat} {f : F}
    (h : r.cfg (n + 1) = .ended f) : r.obsUpTo obs (n + 1) = r.obsUpTo obs n := by
  rw [Run.obsUpTo_succ, h]

/-- The last observation is that of the state reached. -/
theorem Run.obsUpTo_last {s : S} (r : Run step s) :
    ∀ {n : Nat} {s₁ : S}, r.cfg n = .running s₁ → (r.obsUpTo obs n).getLast? = some (obs s₁)
  | 0, s₁, h => by
    rw [r.start] at h
    cases h
    rfl
  | n + 1, s₁, h => by
    rw [r.obsUpTo_running h]
    exact addObs_last _ _

/-- What a run shows only grows with the steps. -/
theorem Run.obsUpTo_mono {s : S} (r : Run step s) {n m : Nat} (hle : n ≤ m) :
    r.obsUpTo obs n <+: r.obsUpTo obs m := by
  induction hle with
  | refl => exact List.prefix_refl _
  | @step m _ ih =>
    refine ih.trans ?_
    rw [Run.obsUpTo_succ]
    cases r.cfg (m + 1) with
    | running s₁ => exact prefix_addObs _ _
    | ended f => exact List.prefix_refl _

/-- After a run ends, it shows nothing new. -/
theorem Run.obsUpTo_ended_le {s : S} (r : Run step s) {n m : Nat} {f : F}
    (h : r.cfg n = .ended f) (hle : n ≤ m) : r.obsUpTo obs m = r.obsUpTo obs n := by
  induction hle with
  | refl => rfl
  | @step m hle ih => rw [r.obsUpTo_ended (r.ended_le h (Nat.le_succ_of_le hle)), ih]

/-- Two prefixes of what one run shows agree wherever both are defined. -/
theorem Run.obsUpTo_getElem {s : S} (r : Run step s) {n m i : Nat}
    (hn : i < (r.obsUpTo obs n).length) (hm : i < (r.obsUpTo obs m).length) :
    (r.obsUpTo obs n)[i] = (r.obsUpTo obs m)[i] := by
  rcases Nat.le_total n m with hle | hle
  · exact (r.obsUpTo_mono hle).getElem hn
  · exact ((r.obsUpTo_mono hle).getElem hm).symm

/-- Two runs with the same configurations show the same. -/
theorem Run.obsUpTo_congr {step₁ : S → Config S F → Prop} {s : S} (r : Run step s)
    (r₁ : Run step₁ s) (h : ∀ n, r.cfg n = r₁.cfg n) : ∀ n, r.obsUpTo obs n = r₁.obsUpTo obs n
  | 0 => rfl
  | n + 1 => by rw [Run.obsUpTo_succ, Run.obsUpTo_succ, h, Run.obsUpTo_congr r r₁ h n]

/-! ### Observations of a function's run, computed in one pass -/

variable (obs) in
/-- `acc`, then the observations of the states that `n` steps of `f` from `s` pass through, each
kept if it differs from the one before.  It takes one step of `f` per step, where `Run.obsUpTo`
of `Run.ofFun` recomputes the run to each time. -/
def obsFrom (f : S → Config S F) (acc : List O) (s : S) : Nat → List O
  | 0 => acc
  | n + 1 => match f s with
    | .running s₁ => obsFrom f (addObs acc (obs s₁)) s₁ n
    | .ended _ => acc

/-- A step of `f` to a running state observes it, then goes on from it. -/
theorem obsFrom_running {f : S → Config S F} {s s₁ : S} (h : f s = .running s₁) (acc : List O)
    (n : Nat) : obsFrom obs f acc s (n + 1) = obsFrom obs f (addObs acc (obs s₁)) s₁ n := by
  rw [obsFrom, h]

/-- A step of `f` that ends observes nothing more. -/
theorem obsFrom_ended {f : S → Config S F} {s : S} {e : F} (h : f s = .ended e) (acc : List O)
    (n : Nat) : obsFrom obs f acc s (n + 1) = acc := by
  rw [obsFrom, h]

/-- One more step adds the observation of where the run of `f` is then. -/
theorem obsFrom_succ (f : S → Config S F) : ∀ (n : Nat) (acc : List O) (s : S),
    obsFrom obs f acc s (n + 1) = match trace f s (n + 1) with
      | .running s₁ => addObs (obsFrom obs f acc s n) (obs s₁)
      | .ended _ => obsFrom obs f acc s n
  | 0, acc, s => by
    cases h : f s with
    | running s₁ => rw [obsFrom_running h, trace_succ_running h]; rfl
    | ended e => rw [obsFrom_ended h, trace_succ_ended h]; rfl
  | n + 1, acc, s => by
    cases h : f s with
    | running s₁ =>
      rw [obsFrom_running h, obsFrom_running h, trace_succ_running h]
      exact obsFrom_succ f n _ s₁
    | ended e => rw [obsFrom_ended h, obsFrom_ended h, trace_succ_ended h]

/-- **What the run of a function shows**, computed in one pass. -/
theorem Run.obsUpTo_ofFun (f : S → Config S F) (s : S) :
    ∀ n, (Run.ofFun f s).obsUpTo obs n = obsFrom obs f [obs s] s n
  | 0 => rfl
  | n + 1 => by
    rw [Run.obsUpTo_succ, obsFrom_succ, Run.obsUpTo_ofFun f s n]
    rfl

/-- **The run is still** from `i` to `j`: running at every time between, in states observed as
the one at `i` is. -/
def Still (obs : S → O) (c : Nat → Config S F) (i j : Nat) : Prop :=
  ∃ y, c i = .running y ∧ ∀ x, i ≤ x → x ≤ j → ∃ z, c x = .running z ∧ obs z = obs y

/-- A still stretch of a run shows nothing new. -/
theorem Run.obsUpTo_still {s : S} (r : Run step s) {i j : Nat} (h : Still obs r.cfg i j) :
    ∀ m, i ≤ m → m ≤ j → r.obsUpTo obs m = r.obsUpTo obs i := by
  obtain ⟨y, hy, hq⟩ := h
  intro m him hmj
  induction him with
  | refl => rfl
  | @step m him ih =>
    obtain ⟨z, hz, ho⟩ := hq (m + 1) (Nat.le_succ_of_le him) hmj
    rw [r.obsUpTo_running hz, ih (Nat.le_of_succ_le hmj), ho]
    exact addObs_of_last (r.obsUpTo_last hy)


omit [DecidableEq O] in
/-- A running configuration is a still stretch of its own. -/
theorem Still.single {obs : S → O} {c : Nat → Config S F} {i : Nat} {y : S}
    (h : c i = .running y) : Still obs c i i :=
  ⟨y, h, fun x h₁ h₂ => ⟨y, by rw [Nat.le_antisymm h₂ h₁]; exact h, rfl⟩⟩

omit [DecidableEq O] in
/-- A still stretch of the configurations from `n` on is a still stretch of them all. -/
theorem Still.of_drop {obs : S → O} {c : Nat → Config S F} {n k : Nat}
    (h : Still obs (fun i => c (i + n)) 0 k) : Still obs c n (n + k) := by
  obtain ⟨y, hy, hq⟩ := h
  change c (0 + n) = _ at hy
  rw [Nat.zero_add] at hy
  refine ⟨y, hy, fun x h₁ h₂ => ?_⟩
  obtain ⟨z, hz, ho⟩ := hq (x - n) (Nat.zero_le _) (by omega)
  change c (x - n + n) = _ at hz
  rw [Nat.sub_add_cancel h₁] at hz
  exact ⟨z, hz, ho⟩

omit [DecidableEq O] in
/-- A step to a state observed alike, then a still stretch, is a still stretch. -/
theorem Still.cons {obs : S → O} {c : Nat → Config S F} {y y₁ : S} {k : Nat}
    (h₀ : c 0 = .running y) (h₁ : c 1 = .running y₁) (ho : obs y₁ = obs y)
    (h : Still obs (fun i => c (i + 1)) 0 k) : Still obs c 0 (k + 1) := by
  obtain ⟨y₂, hy₂, hq⟩ := h
  have hy : y₂ = y₁ := Config.running.inj (hy₂.symm.trans h₁)
  subst hy
  refine ⟨y, h₀, fun x _ hx => ?_⟩
  cases x with
  | zero => exact ⟨y, h₀, rfl⟩
  | succ x =>
    obtain ⟨z, hz, hoz⟩ := hq x (Nat.zero_le _) (by omega)
    exact ⟨z, hz, hoz.trans ho⟩

end

/-! ## Behaviours -/

/-- The behaviour of a run, given what it observes, `O`, and what its outcome shows, `R`. -/
inductive Beh (O R : Type) where
  /-- The run ends with the result `r`, after the observations `t`. -/
  | term (t : List O) (r : R)
  /-- The run never ends, and makes no observation after `t`. -/
  | silent (t : List O)
  /-- The run never ends, and makes infinitely many observations, `σ 0`, `σ 1`, and so on. -/
  | react (σ : Nat → O)

section
variable {O R : Type}

/-- `l` is a prefix of the behaviour's observations. -/
def Beh.Extends : Beh O R → List O → Prop
  | .term t _, l => l <+: t
  | .silent t, l => l <+: t
  | .react σ, l => ∀ i (h : i < l.length), l[i] = σ i

/-- The behaviour ends. -/
def Beh.IsTerm : Beh O R → Prop
  | .term .. => True
  | _ => False

/-- The first `n` observations of `σ` are a prefix of `react σ`. -/
theorem Beh.extends_ofFn (σ : Nat → O) (n : Nat) :
    (Beh.react (R := R) σ).Extends (List.ofFn (n := n) fun i => σ i) := by
  intro i hi
  rw [List.getElem_ofFn]

/-- A behaviour that does not end is determined by its finite prefixes. -/
theorem Beh.eq_of_extends_iff {b b₁ : Beh O R} (hb : ¬ b.IsTerm) (hb₁ : ¬ b₁.IsTerm)
    (h : ∀ l, b.Extends l ↔ b₁.Extends l) : b = b₁ := by
  match b, b₁, hb, hb₁ with
  | .term .., _, hb, _ => exact absurd trivial hb
  | _, .term .., _, hb₁ => exact absurd trivial hb₁
  | .silent t, .silent t₁, _, _ =>
    have h₁ : t <+: t₁ := (h t).mp (List.prefix_refl t)
    have h₂ : t₁ <+: t := (h t₁).mpr (List.prefix_refl t₁)
    rw [h₁.eq_of_length (Nat.le_antisymm h₁.length_le h₂.length_le)]
  | .silent t, .react σ, _, _ =>
    have hl := ((h _).mpr (Beh.extends_ofFn σ (t.length + 1))).length_le
    rw [List.length_ofFn] at hl
    exact absurd hl (Nat.not_succ_le_self _)
  | .react σ, .silent t, _, _ =>
    have hl := ((h _).mp (Beh.extends_ofFn σ (t.length + 1))).length_le
    rw [List.length_ofFn] at hl
    exact absurd hl (Nat.not_succ_le_self _)
  | .react σ, .react σ₁, _, _ =>
    have hσ : σ = σ₁ := by
      funext i
      have hi : i < (List.ofFn (n := i + 1) fun j => σ j).length := by
        rw [List.length_ofFn]
        exact Nat.lt_succ_self i
      have := (h _).mp (Beh.extends_ofFn σ (i + 1)) i hi
      rwa [List.getElem_ofFn] at this
    rw [hσ]

end

/-- A bounded function of `Nat` reaches its maximum. -/
theorem exists_max (f : Nat → Nat) : ∀ L, (∀ n, f n ≤ L) → ∃ N, ∀ n, f n ≤ f N
  | 0, h => ⟨0, fun n => Nat.le_trans (h n) (Nat.zero_le _)⟩
  | L + 1, h => by
    by_cases hL : ∃ n, L + 1 ≤ f n
    · obtain ⟨N, hN⟩ := hL
      exact ⟨N, fun n => Nat.le_trans (h n) hN⟩
    · exact exists_max f L fun n => Nat.le_of_lt_succ (Nat.lt_of_not_le fun hn => hL ⟨n, hn⟩)

/-- A function of `Nat` that is not unbounded is bounded. -/
theorem bounded_of_not_unbounded {f : Nat → Nat} (h : ¬ ∀ i, ∃ n, i < f n) :
    ∃ L, ∀ n, f n ≤ L := by
  obtain ⟨L, hL⟩ := Classical.not_forall.mp h
  exact ⟨L, fun n => Nat.le_of_not_lt fun hn => hL ⟨n, hn⟩⟩

section
variable {O R : Type} [DecidableEq O] (obs : S → O) (res : F → R)

/-- The behaviour of the configurations `c` that show `ob n` after `n` steps: if they end, what
they show and the result; otherwise the limit of what they show, `react` if it never stops
growing and `silent` if it does. -/
noncomputable def behSeq (c : Nat → Config S F) (ob : Nat → List O) : Beh O R :=
  open Classical in
  if h : ∃ n f, c n = .ended f then
    .term (ob h.choose) (res h.choose_spec.choose)
  else if hu : ∀ i, ∃ n, i < (ob n).length then
    .react fun i => (ob (hu i).choose)[i]'(hu i).choose_spec
  else
    .silent (ob (exists_max _ _ (bounded_of_not_unbounded hu).choose_spec).choose)

/-- **The behaviour of a run**, observed through `obs`, with its outcome shown through `res`: if
the run ends, its observations and its result; otherwise the limit of its observations, `react` if
they never stop and `silent` if they do. -/
noncomputable def Run.beh {s : S} (r : Run step s) : Beh O R :=
  behSeq res r.cfg (r.obsUpTo obs)

variable {obs} {res}

/-- Two runs with the same configurations behave alike. -/
theorem Run.beh_congr {step₁ : S → Config S F → Prop} {s : S} (r : Run step s)
    (r₁ : Run step₁ s) (h : ∀ n, r.cfg n = r₁.cfg n) : r.beh obs res = r₁.beh obs res := by
  have hc : r.cfg = r₁.cfg := funext h
  have ho : r.obsUpTo obs = r₁.obsUpTo obs := funext (Run.obsUpTo_congr r r₁ h)
  unfold Run.beh
  rw [hc, ho]

/-- **A machine without choices has one behaviour**: every run of a function's graph behaves as
the function's run. -/
theorem Run.beh_graph {f : S → Config S F} {s : S} (r : Run (graph f) s) :
    r.beh obs res = (Run.ofFun f s).beh obs res :=
  r.beh_congr (Run.ofFun f s) r.eq_trace

/-- **Termination.** A run that ends behaves as its observations and its result. -/
theorem Run.beh_ended {s : S} (r : Run step s) {n : Nat} {f : F} (h : r.cfg n = .ended f) :
    r.beh obs res = .term (r.obsUpTo obs n) (res f) := by
  have he : ∃ n f, r.cfg n = .ended f := ⟨n, f, h⟩
  unfold Run.beh behSeq
  split
  case isFalse hne => exact absurd he hne
  have h₀ := he.choose_spec.choose_spec
  have hf : he.choose_spec.choose = f := r.ended_unique h₀ h
  have ho : r.obsUpTo obs he.choose = r.obsUpTo obs n := by
    rcases Nat.le_total he.choose n with hle | hle
    · exact (r.obsUpTo_ended_le h₀ hle).symm
    · exact r.obsUpTo_ended_le h hle
  rw [hf, ho]

/-- A run that never ends does not behave as one that ends. -/
theorem Run.beh_not_isTerm {s : S} (r : Run step s) (hd : r.Diverges) :
    ¬ (r.beh obs res).IsTerm := by
  have hn : ¬ ∃ n f, r.cfg n = .ended f := by
    rintro ⟨n, f, h⟩
    obtain ⟨s₁, h₁⟩ := hd n
    exact nomatch h.symm.trans h₁
  unfold Run.beh behSeq
  split
  · contradiction
  · split <;> exact id

/-- **The behaviour ends exactly when the run does**, with its observations and its result. -/
theorem Run.beh_eq_term_iff {s : S} (r : Run step s) {t : List O} {x : R} :
    r.beh obs res = .term t x ↔
      ∃ n f, r.cfg n = .ended f ∧ r.obsUpTo obs n = t ∧ res f = x := by
  constructor
  · intro hb
    by_cases hd : r.Diverges
    · exact absurd (hb ▸ trivial) (r.beh_not_isTerm (obs := obs) (res := res) hd)
    · obtain ⟨n, f, h⟩ := r.exists_ended hd
      rw [r.beh_ended h] at hb
      cases hb
      exact ⟨n, f, h, rfl, rfl⟩
  · rintro ⟨n, f, h, rfl, rfl⟩
    exact r.beh_ended h

/-- **Prefixes.** The finite prefixes of a run's behaviour are exactly the prefixes of what its
first `n` steps show, for some `n`. -/
theorem Run.beh_extends_iff {s : S} (r : Run step s) {l : List O} :
    (r.beh obs res).Extends l ↔ ∃ n, l <+: r.obsUpTo obs n := by
  unfold Run.beh behSeq
  split
  next he =>
    have h₀ := he.choose_spec.choose_spec
    refine ⟨fun hl => ⟨_, hl⟩, fun ⟨n, hl⟩ => hl.trans ?_⟩
    rcases Nat.le_total n he.choose with hle | hle
    · exact r.obsUpTo_mono hle
    · rw [r.obsUpTo_ended_le h₀ hle]
      exact List.prefix_refl _
  split
  next hu =>
    constructor
    · intro hl
      obtain ⟨n, hn⟩ := hu l.length
      refine ⟨n, List.prefix_iff_getElem.mpr ⟨Nat.le_of_lt hn, fun i hi => ?_⟩⟩
      rw [hl i hi]
      exact r.obsUpTo_getElem _ _
    · rintro ⟨n, hl⟩ i hi
      rw [hl.getElem hi]
      exact r.obsUpTo_getElem _ _
  next _ hu =>
    have hN := (exists_max _ _ (bounded_of_not_unbounded hu).choose_spec).choose_spec
    generalize (exists_max _ _ (bounded_of_not_unbounded hu).choose_spec).choose = N at hN ⊢
    refine ⟨fun hl => ⟨_, hl⟩, fun ⟨n, hl⟩ => hl.trans ?_⟩
    rcases Nat.le_total n N with hle | hle
    · exact r.obsUpTo_mono hle
    · have hp := r.obsUpTo_mono (obs := obs) hle
      rw [hp.eq_of_length (Nat.le_antisymm hp.length_le (hN n))]
      exact List.prefix_refl _

/-- **Silent divergence.** A run that never ends, and shows nothing after its first `N` steps,
diverges silently. -/
theorem Run.beh_silent {s : S} (r : Run step s) {N : Nat} (hd : r.Diverges)
    (hN : ∀ n, N ≤ n → r.obsUpTo obs n = r.obsUpTo obs N) :
    r.beh obs res = .silent (r.obsUpTo obs N) := by
  apply Beh.eq_of_extends_iff (r.beh_not_isTerm hd) id
  intro l
  rw [r.beh_extends_iff]
  constructor
  · rintro ⟨n, hl⟩
    refine hl.trans ?_
    rcases Nat.le_total n N with hle | hle
    · exact r.obsUpTo_mono hle
    · rw [hN n hle]
      exact List.prefix_refl _
  · exact fun hl => ⟨N, hl⟩

/-- **Reactive divergence.** A run that never ends, whose observations are prefixes of `σ` and
grow without bound, reacts with `σ`. -/
theorem Run.beh_react {s : S} (r : Run step s) {σ : Nat → O} (hd : r.Diverges)
    (hσ : ∀ n, (Beh.react (R := R) σ).Extends (r.obsUpTo obs n))
    (hu : ∀ i, ∃ n, i < (r.obsUpTo obs n).length) :
    r.beh obs res = .react σ := by
  apply Beh.eq_of_extends_iff (r.beh_not_isTerm hd) id
  intro l
  rw [r.beh_extends_iff]
  constructor
  · rintro ⟨n, hl⟩ i hi
    rw [hl.getElem hi]
    exact hσ n i _
  · intro hl
    obtain ⟨n, hn⟩ := hu l.length
    refine ⟨n, List.prefix_iff_getElem.mpr ⟨Nat.le_of_lt hn, fun i hi => ?_⟩⟩
    rw [hl i hi]
    exact (hσ n i _).symm

/-- What the first `n` steps of a run show is a prefix of its behaviour. -/
theorem Run.beh_extends {s : S} (r : Run step s) (n : Nat) :
    (r.beh obs res).Extends (r.obsUpTo obs n) :=
  r.beh_extends_iff.mpr ⟨n, List.prefix_refl _⟩

end

/-! ## Improvement and trace refinement -/

/-- **Improvement.** `b₁` improves on `b`: it is `b`, or `b` goes wrong, by `wrong`, after
observations that `b₁` extends.  This is CompCert's behaviour improvement. -/
def Improves {O R : Type} (wrong : R → Prop) (b₁ b : Beh O R) : Prop :=
  b₁ = b ∨ ∃ t r, b = .term t r ∧ wrong r ∧ b₁.Extends t

/-- Improvement with fewer wrong results is improvement with more. -/
theorem Improves.mono {O R : Type} {wrong wrong₁ : R → Prop} (hw : ∀ r, wrong r → wrong₁ r)
    {b₁ b : Beh O R} : Improves wrong b₁ b → Improves wrong₁ b₁ b
  | .inl h => .inl h
  | .inr ⟨t, r, hb, hr, he⟩ => .inr ⟨t, r, hb, hw r hr, he⟩

/-- A prefix of a prefix of a behaviour's observations is one. -/
theorem Beh.Extends.of_prefix {O R : Type} {b : Beh O R} {l l₁ : List O} (h : b.Extends l₁)
    (hl : l <+: l₁) : b.Extends l :=
  match b, h with
  | .term .., h => hl.trans h
  | .silent _, h => hl.trans h
  | .react _, h => fun i hi => (hl.getElem hi).trans (h i _)

/-- **Improvement is transitive.** -/
theorem Improves.trans {O R : Type} {wrong : R → Prop} {b₂ b₁ b : Beh O R}
    (h₂ : Improves wrong b₂ b₁) (h₁ : Improves wrong b₁ b) : Improves wrong b₂ b := by
  rcases h₁ with rfl | ⟨t, r, rfl, hw, he⟩
  · exact h₂
  · refine .inr ⟨t, r, rfl, hw, ?_⟩
    rcases h₂ with rfl | ⟨t₁, r₁, rfl, _, he₁⟩
    · exact he
    · exact he₁.of_prefix he

/-- Improvement on a behaviour that does not end wrong is equality. -/
theorem Improves.eq {O R : Type} {wrong : R → Prop} {b₁ b : Beh O R}
    (h : Improves wrong b₁ b) (hb : ∀ t r, b = .term t r → ¬ wrong r) : b₁ = b :=
  h.elim id fun ⟨t, r, he, hr, _⟩ => absurd hr (hb t r he)

section
variable {T G O R : Type} [DecidableEq O]

/-- **Trace refinement.** Every run of the target `stepₜ` from `t` improves on the behaviour of
some run of the source `stepₛ` from `s`: for every target run there exists a source run. -/
def Refines (stepₛ : S → Config S F → Prop) (stepₜ : T → Config T G → Prop) (obsₛ : S → O)
    (obsₜ : T → O) (resₛ : F → R) (resₜ : G → R) (wrong : R → Prop) (s : S) (t : T) : Prop :=
  ∀ rₜ : Run stepₜ t, ∃ rₛ : Run stepₛ s, Improves wrong (rₜ.beh obsₜ resₜ) (rₛ.beh obsₛ resₛ)

/-- Trace refinement with fewer wrong results is trace refinement with more. -/
theorem Refines.mono {stepₛ : S → Config S F → Prop} {stepₜ : T → Config T G → Prop}
    {obsₛ : S → O} {obsₜ : T → O} {resₛ : F → R} {resₜ : G → R}
    {wrong wrong₁ : R → Prop} (hw : ∀ r, wrong r → wrong₁ r) {s : S} {t : T}
    (h : Refines stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong s t) :
    Refines stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong₁ s t :=
  fun rₜ => let ⟨rₛ, hi⟩ := h rₜ; ⟨rₛ, hi.mono hw⟩

/-- **A machine refines itself.** -/
theorem Refines.refl {step : S → Config S F → Prop} {obs : S → O} {res : F → R}
    {wrong : R → Prop} (s : S) : Refines step step obs obs res res wrong s s :=
  fun r => ⟨r, .inl rfl⟩

/-- **Trace refinement is transitive**, so the passes of a pipeline compose. -/
theorem Refines.trans {U H : Type} {stepₛ : S → Config S F → Prop} {stepₘ : T → Config T G → Prop}
    {stepₜ : U → Config U H → Prop} {obsₛ : S → O} {obsₘ : T → O} {obsₜ : U → O} {resₛ : F → R}
    {resₘ : G → R} {resₜ : H → R} {wrong : R → Prop} {s : S} {m : T} {t : U}
    (h₁ : Refines stepₛ stepₘ obsₛ obsₘ resₛ resₘ wrong s m)
    (h₂ : Refines stepₘ stepₜ obsₘ obsₜ resₘ resₜ wrong m t) :
    Refines stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong s t := fun rₜ =>
  let ⟨rₘ, hi₂⟩ := h₂ rₜ
  let ⟨rₛ, hi₁⟩ := h₁ rₘ
  ⟨rₛ, hi₂.trans hi₁⟩

/-- **Trace refinement of a source that never goes wrong keeps behaviours**: if no run of the
source ends wrong, every target run behaves as some source run. -/
theorem Refines.beh_eq {stepₛ : S → Config S F → Prop} {stepₜ : T → Config T G → Prop}
    {obsₛ : S → O} {obsₜ : T → O} {resₛ : F → R} {resₜ : G → R} {wrong : R → Prop} {s : S}
    {t : T} (h : Refines stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong s t)
    (hsafe : ∀ (rₛ : Run stepₛ s) (l : List O) (x : R), rₛ.beh obsₛ resₛ = .term l x → ¬ wrong x)
    (rₜ : Run stepₜ t) : ∃ rₛ : Run stepₛ s, rₜ.beh obsₜ resₜ = rₛ.beh obsₛ resₛ :=
  let ⟨rₛ, hi⟩ := h rₜ
  ⟨rₛ, hi.eq (hsafe rₛ)⟩

/-! ## Matching two runs -/

section
variable {stepₛ : S → Config S F → Prop} {stepₜ : T → Config T G → Prop} {s : S} {t : T}
  (obsₛ : S → O) (obsₜ : T → O) (resₛ : F → R) (resₜ : G → R) (wrong : R → Prop)

/-- **A forward matching of two runs**, with a measure: related times, of the source run `rₛ`
and the target run `rₜ`, are running in states observed alike.  A source step from related
times is matched by target steps, still but for the last, to related times, or by none, and then
the measure decreases.  A source outcome is wrong, or is matched, after still target steps, by a
target outcome that shows the same. -/
structure RunMatch (rₛ : Run stepₛ s) (rₜ : Run stepₜ t) where
  rel : Nat → Nat → Prop
  measure : Nat → Nat
  start : rel 0 0
  obs_eq : ∀ {n n₁ : Nat}, rel n n₁ →
    ∃ x y, rₛ.cfg n = .running x ∧ rₜ.cfg n₁ = .running y ∧ obsₛ x = obsₜ y
  next : ∀ {n n₁ : Nat}, rel n n₁ → (∃ x, rₛ.cfg (n + 1) = .running x) →
    (∃ k, Still obsₜ rₜ.cfg n₁ (n₁ + k) ∧ rel (n + 1) (n₁ + k + 1)) ∨
      (measure (n + 1) < measure n ∧ rel (n + 1) n₁)
  final : ∀ {n n₁ : Nat} {f : F}, rel n n₁ → rₛ.cfg (n + 1) = .ended f →
    wrong (resₛ f) ∨ ∃ k g, Still obsₜ rₜ.cfg n₁ (n₁ + k) ∧ rₜ.cfg (n₁ + k + 1) = .ended g ∧
      resₜ g = resₛ f

end

namespace RunMatch

variable {stepₛ : S → Config S F → Prop} {stepₜ : T → Config T G → Prop} {s : S} {t : T}
  {obsₛ : S → O} {obsₜ : T → O} {resₛ : F → R} {resₜ : G → R} {wrong : R → Prop}
  {rₛ : Run stepₛ s} {rₜ : Run stepₜ t} (sim : RunMatch obsₛ obsₜ resₛ resₜ wrong rₛ rₜ)

/-- Related times that have shown the same. -/
private def Good (n n₁ : Nat) : Prop := sim.rel n n₁ ∧ rₜ.obsUpTo obsₜ n₁ = rₛ.obsUpTo obsₛ n

/-- One source step from good times is matched by target steps to good times, or by none, and
then the measure decreases. -/
private theorem next_good {n n₁ : Nat} (hg : sim.Good n n₁) {x : S}
    (hx : rₛ.cfg (n + 1) = .running x) :
    (∃ k, sim.Good (n + 1) (n₁ + k + 1)) ∨
      (sim.measure (n + 1) < sim.measure n ∧ sim.Good (n + 1) n₁) := by
  obtain ⟨hr, ho⟩ := hg
  rcases sim.next hr ⟨x, hx⟩ with ⟨k, hq, hr₁⟩ | ⟨hlt, hr₁⟩
  · left
    refine ⟨k, hr₁, ?_⟩
    obtain ⟨x₁, y₁, hx₁, hy₁, ho₁⟩ := sim.obs_eq hr₁
    rw [hx] at hx₁
    cases hx₁
    rw [rₜ.obsUpTo_running hy₁, rₜ.obsUpTo_still hq (n₁ + k) (Nat.le_add_right _ _)
      (Nat.le_refl _), ho, rₛ.obsUpTo_running hx, ho₁]
  · right
    refine ⟨hlt, hr₁, ?_⟩
    obtain ⟨x₀, y₀, hx₀, hy₀, ho₀⟩ := sim.obs_eq hr
    obtain ⟨x₁, y₁, hx₁, hy₁, ho₁⟩ := sim.obs_eq hr₁
    rw [hx] at hx₁
    cases hx₁
    rw [hy₀] at hy₁
    cases hy₁
    rw [rₛ.obsUpTo_running hx, ho₁, ← ho₀, addObs_of_last (rₛ.obsUpTo_last hx₀), ho]

/-- **Every configuration of the source run is matched**: running at a time good with some
target time, or ended, wrong or with the target ended alike, after what the target shows at some
time. -/
private theorem forward : ∀ n, (∃ n₁, sim.Good n n₁) ∨ ∃ f, rₛ.cfg n = .ended f ∧
    ∃ n₁, rₜ.obsUpTo obsₜ n₁ = rₛ.obsUpTo obsₛ n ∧
      (wrong (resₛ f) ∨ ∃ g, rₜ.cfg n₁ = .ended g ∧ resₜ g = resₛ f)
  | 0 => by
    left
    refine ⟨0, sim.start, ?_⟩
    obtain ⟨x, y, hx, hy, ho⟩ := sim.obs_eq sim.start
    rw [rₛ.start] at hx
    rw [rₜ.start] at hy
    cases hx
    cases hy
    show [obsₜ t] = [obsₛ s]
    rw [ho]
  | n + 1 => by
    rcases forward n with ⟨n₁, hg⟩ | ⟨f, hf, n₁, ho, hw⟩
    · cases hc : rₛ.cfg (n + 1) with
      | running x =>
        left
        rcases sim.next_good hg hc with ⟨k, hg₁⟩ | ⟨_, hg₁⟩
        · exact ⟨_, hg₁⟩
        · exact ⟨_, hg₁⟩
      | ended f =>
        right
        refine ⟨f, rfl, ?_⟩
        rw [rₛ.obsUpTo_ended hc]
        rcases sim.final hg.1 hc with hw | ⟨k, g, hq, hg₁, hres⟩
        · exact ⟨n₁, hg.2, .inl hw⟩
        · refine ⟨n₁ + k + 1, ?_, .inr ⟨g, hg₁, hres⟩⟩
          rw [rₜ.obsUpTo_ended hg₁, rₜ.obsUpTo_still hq (n₁ + k) (Nat.le_add_right _ _)
            (Nat.le_refl _)]
          exact hg.2
    · right
      refine ⟨f, rₛ.stay hf, n₁, ?_, hw⟩
      rw [rₛ.obsUpTo_ended (rₛ.stay hf)]
      exact ho

/-- Along a source run that never ends, the target advances from good times to later ones. -/
private theorem advance (hd : rₛ.Diverges) : ∀ (μ : Nat) {n n₁ : Nat}, sim.measure n ≤ μ →
    sim.Good n n₁ → ∃ m m₁, sim.Good m m₁ ∧ n₁ < m₁ := by
  intro μ
  induction μ using Nat.strongRecOn with
  | ind μ ih =>
    intro n n₁ hμ hg
    obtain ⟨x, hx⟩ := hd (n + 1)
    rcases sim.next_good hg hx with ⟨k, hg₁⟩ | ⟨hlt, hg₁⟩
    · exact ⟨_, _, hg₁, by omega⟩
    · exact ih _ (Nat.lt_of_lt_of_le hlt hμ) (Nat.le_refl _) hg₁

/-- Along a source run that never ends, the target reaches every time at good times. -/
private theorem unbounded (hd : rₛ.Diverges) : ∀ N, ∃ n n₁, N ≤ n₁ ∧ sim.Good n n₁
  | 0 => by
    rcases sim.forward 0 with ⟨n₁, hg⟩ | ⟨f, hf, _⟩
    · exact ⟨0, n₁, Nat.zero_le _, hg⟩
    · obtain ⟨_, hx⟩ := hd 0
      exact nomatch hf.symm.trans hx
  | N + 1 => by
    obtain ⟨n, n₁, hle, hg⟩ := unbounded hd N
    obtain ⟨m, m₁, hg₁, hlt⟩ := sim.advance hd _ (Nat.le_refl _) hg
    exact ⟨m, m₁, by omega, hg₁⟩

include sim in
/-- **Improvement from a matching.** The target run's behaviour improves on the source run's:
it is the same, or the source goes wrong after observations that the target's behaviour
extends. -/
theorem improves : Improves wrong (rₜ.beh obsₜ resₜ) (rₛ.beh obsₛ resₛ) := by
  by_cases hd : rₛ.Diverges
  · left
    have hd₁ : rₜ.Diverges := by
      intro N
      obtain ⟨n, n₁, hle, hg⟩ := sim.unbounded hd N
      obtain ⟨_, y, _, hy, _⟩ := sim.obs_eq hg.1
      exact rₜ.running_le hy hle
    apply Beh.eq_of_extends_iff (rₜ.beh_not_isTerm hd₁) (rₛ.beh_not_isTerm hd)
    intro l
    rw [rₜ.beh_extends_iff, rₛ.beh_extends_iff]
    constructor
    · rintro ⟨m, hl⟩
      obtain ⟨n, n₁, hle, hg⟩ := sim.unbounded hd m
      refine ⟨n, hl.trans ?_⟩
      rw [← hg.2]
      exact rₜ.obsUpTo_mono hle
    · rintro ⟨n, hl⟩
      rcases sim.forward n with ⟨n₁, hg⟩ | ⟨f, hf, _⟩
      · exact ⟨n₁, hg.2 ▸ hl⟩
      · obtain ⟨_, hx⟩ := hd n
        exact nomatch hf.symm.trans hx
  · obtain ⟨n, f, hf⟩ := rₛ.exists_ended hd
    rcases sim.forward n with ⟨n₁, hg⟩ | ⟨f₁, hf₁, n₁, ho, hw | ⟨g, hg, hres⟩⟩
    · obtain ⟨_, _, hx, _⟩ := sim.obs_eq hg.1
      exact nomatch hf.symm.trans hx
    · rw [hf] at hf₁
      cases hf₁
      right
      refine ⟨_, _, rₛ.beh_ended hf, hw, ?_⟩
      rw [← ho]
      exact rₜ.beh_extends n₁
    · rw [hf] at hf₁
      cases hf₁
      left
      rw [rₜ.beh_ended hg, rₛ.beh_ended hf, hres, ho]

end RunMatch

/-! ## Forward simulation of functions -/

section
variable {obs : T → O}

/-- `k` steps of `g` from `t` reach `t₁` without ending, and each state on the way is observed
as `t` is. -/
inductive Quiet (g : T → Config T G) (obs : T → O) : Nat → T → T → Prop where
  | refl (t : T) : Quiet g obs 0 t t
  | cons {k : Nat} {t t₁ t₂ : T} : g t = .running t₁ → obs t₁ = obs t → Quiet g obs k t₁ t₂ →
      Quiet g obs (k + 1) t t₂

omit [DecidableEq O] in
/-- Quiet steps stay quiet through any function of the observations. -/
theorem Quiet.map {O₁ : Type} {g : T → Config T G} (f : O → O₁) {k : Nat} {t t₁ : T}
    (h : Quiet g obs k t t₁) : Quiet g (fun x => f (obs x)) k t t₁ := by
  induction h with
  | refl => exact .refl _
  | cons hs ho _ ih => exact .cons hs (congrArg f ho) ih

omit [DecidableEq O] in
/-- Along a run of a function, quiet steps from a state of the run are a still stretch of it. -/
theorem Quiet.still {g : T → Config T G} {t₀ : T} (r : Run (graph g) t₀) {k : Nat} {t t₂ : T}
    (h : Quiet g obs k t t₂) : ∀ {n : Nat}, r.cfg n = .running t →
      Still obs r.cfg n (n + k) ∧ r.cfg (n + k) = .running t₂ := by
  induction h with
  | refl t =>
    intro n hn
    refine ⟨⟨t, hn, fun x h₁ h₂ => ⟨t, ?_, rfl⟩⟩, hn⟩
    rw [Nat.le_antisymm h₂ h₁]
    exact hn
  | @cons k t t₁ t₂ hs ho _ ih =>
    intro n hn
    have h₁ : r.cfg (n + 1) = .running t₁ := (r.next hn).symm.trans hs
    obtain ⟨⟨y, hy, hq⟩, h₂⟩ := ih h₁
    rw [hy] at h₁
    cases h₁
    refine ⟨⟨t, hn, fun x hx₁ hx₂ => ?_⟩, by rw [show n + (k + 1) = n + 1 + k by omega]; exact h₂⟩
    rcases Nat.eq_or_lt_of_le hx₁ with rfl | hlt
    · exact ⟨t, hn, rfl⟩
    · obtain ⟨z, hz, hoz⟩ := hq x hlt (by omega)
      exact ⟨z, hz, hoz.trans ho⟩

end

/-- **A forward simulation with a measure** of the function `step₁` by `step₂`, which observe
their states through `obs₁` and `obs₂` and show their outcomes through `res₁` and `res₂`.
Related states are observed alike.  A source step is matched by target steps, quiet but for the
last, to a related state, or by none, and then the measure decreases.  A source outcome is
wrong, or is matched, after quiet target steps, by a target outcome that shows the same. -/
structure Sim (step₁ : S → Config S F) (step₂ : T → Config T G) (obs₁ : S → O) (obs₂ : T → O)
    (res₁ : F → R) (res₂ : G → R) (wrong : R → Prop) where
  rel : S → T → Prop
  measure : S → Nat
  obs_eq : ∀ {s : S} {t : T}, rel s t → obs₁ s = obs₂ t
  next : ∀ {s : S} {t : T} {s₁ : S}, rel s t → step₁ s = .running s₁ →
    (∃ k t₂ t₁, Quiet step₂ obs₂ k t t₂ ∧ step₂ t₂ = .running t₁ ∧ rel s₁ t₁) ∨
      (measure s₁ < measure s ∧ rel s₁ t)
  final : ∀ {s : S} {t : T} {f : F}, rel s t → step₁ s = .ended f →
    wrong (res₁ f) ∨ ∃ k t₂ g, Quiet step₂ obs₂ k t t₂ ∧ step₂ t₂ = .ended g ∧ res₂ g = res₁ f

namespace Sim

variable {step₁ : S → Config S F} {step₂ : T → Config T G} {obs₁ : S → O} {obs₂ : T → O}
  {res₁ : F → R} {res₂ : G → R} {wrong : R → Prop}
  (sim : Sim step₁ step₂ obs₁ obs₂ res₁ res₂ wrong)

/-- A forward simulation observes less through any function of its observations. -/
def mapObs {O₁ : Type} [DecidableEq O₁] (f : O → O₁) :
    Sim step₁ step₂ (fun s => f (obs₁ s)) (fun t => f (obs₂ t)) res₁ res₂ wrong where
  rel := sim.rel
  measure := sim.measure
  obs_eq h := congrArg f (sim.obs_eq h)
  next h hs := (sim.next h hs).imp (fun ⟨k, t₂, t₁, hq, ht, hr⟩ => ⟨k, t₂, t₁, hq.map f, ht, hr⟩) id
  final h hs := (sim.final h hs).imp id fun ⟨k, t₂, g, hq, ht, hg⟩ => ⟨k, t₂, g, hq.map f, ht, hg⟩

/-- The simulation, as a matching of runs of the two functions from related states. -/
def toRunMatch {s : S} {t : T} (rₛ : Run (graph step₁) s) (rₜ : Run (graph step₂) t)
    (hr : sim.rel s t) : RunMatch obs₁ obs₂ res₁ res₂ wrong rₛ rₜ where
  rel n n₁ := ∃ x y, rₛ.cfg n = .running x ∧ rₜ.cfg n₁ = .running y ∧ sim.rel x y
  measure n := (rₛ.cfg n).measure sim.measure
  start := ⟨s, t, rₛ.start, rₜ.start, hr⟩
  obs_eq := fun ⟨x, y, hx, hy, hr⟩ => ⟨x, y, hx, hy, sim.obs_eq hr⟩
  next := by
    rintro n n₁ ⟨x, y, hx, hy, hr⟩ ⟨x₁, hx₁⟩
    have hs : step₁ x = .running x₁ := (rₛ.next hx).trans hx₁
    rcases sim.next hr hs with ⟨k, t₂, t₁, hq, ht, hr₁⟩ | ⟨hlt, hr₁⟩
    · obtain ⟨hst, h₂⟩ := hq.still rₜ hy
      exact .inl ⟨k, hst, x₁, t₁, hx₁, (rₜ.next h₂).symm.trans ht, hr₁⟩
    · refine .inr ⟨?_, x₁, y, hx₁, hy, hr₁⟩
      show (rₛ.cfg (n + 1)).measure sim.measure < (rₛ.cfg n).measure sim.measure
      rw [hx₁, hx]
      exact hlt
  final := by
    rintro n n₁ f ⟨x, y, hx, hy, hr⟩ hf
    rcases sim.final hr ((rₛ.next hx).trans hf) with hw | ⟨k, t₂, g, hq, ht, hg⟩
    · exact .inl hw
    · obtain ⟨hst, h₂⟩ := hq.still rₜ hy
      exact .inr ⟨k, g, hst, (rₜ.next h₂).symm.trans ht, hg⟩

/-- **Improvement from simulation.** For related starts, every run of the target function
improves on the run of the source function: it is the same, or the source goes wrong after
observations that the target's behaviour extends.  The measure is what keeps a target from
diverging where the source does not. -/
theorem improves {s : S} {t : T} (hr : sim.rel s t) (rₜ : Run (graph step₂) t) :
    Improves wrong (rₜ.beh obs₂ res₂) ((Run.ofFun step₁ s).beh obs₁ res₁) :=
  (sim.toRunMatch (Run.ofFun step₁ s) rₜ hr).improves

/-- **A forward simulation of functions gives trace refinement of their graphs.** -/
theorem refines {s : S} {t : T} (hr : sim.rel s t) :
    Refines (graph step₁) (graph step₂) obs₁ obs₂ res₁ res₂ wrong s t :=
  fun rₜ => ⟨Run.ofFun step₁ s, sim.improves hr rₜ⟩

end Sim

/-! ## Oracle machines

An oracle machine steps under an oracle `Nat → Nat`, and reads it at the index `idx s` of its
state.  Its relation `Oracle.Rel` steps wherever some oracle steps, and `Oracle.run` is its run
under one oracle. -/

namespace Oracle

section
variable (ostep : (Nat → Nat) → S → Config S F) (idx : S → Nat)

/-- A step that some oracle takes. -/
def Rel : S → Config S F → Prop := fun s c => ∃ o, ostep o s = c

/-- A step reads the oracle only at the state's index. -/
def Local : Prop :=
  ∀ (o o₁ : Nat → Nat) (s : S), o (idx s) = o₁ (idx s) → ostep o s = ostep o₁ s

/-- The index never decreases, and a step that keeps it does not read the oracle. -/
def Advance : Prop :=
  ∀ (o : Nat → Nat) (s s₁ : S), ostep o s = .running s₁ →
    idx s ≤ idx s₁ ∧ (idx s₁ = idx s → ∀ o₁, ostep o₁ s = ostep o s)

/-- **The run under an oracle**, as a run of the relation. -/
def run (o : Nat → Nat) (s : S) : Run (Rel ostep) s :=
  (Run.ofFun (ostep o) s).mono fun _ _ h => ⟨o, h⟩

variable {ostep} {idx}

omit [DecidableEq O] in
/-- Along a run of the relation, the index never decreases. -/
private theorem idx_mono (ha : Advance ostep idx) {s : S} (r : Run (Rel ostep) s) {i j : Nat}
    {a b : S} (hij : i ≤ j) (hi : r.cfg i = .running a) (hj : r.cfg j = .running b) :
    idx a ≤ idx b := by
  induction hij generalizing b with
  | refl => cases hi.symm.trans hj; exact Nat.le_refl _
  | @step j hij ih =>
    obtain ⟨c, hc⟩ := r.running_le hj (Nat.le_succ j)
    obtain ⟨o, ho⟩ := r.next hc
    rw [hj] at ho
    exact Nat.le_trans (ih hc) (ha _ _ _ ho).1

variable (idx) in
/-- The step of the run `r` at time `n` reads the index `d`: it runs at `n` in a state of index
`d`, and leaves `d`, to a larger index or to an end. -/
private def Reads {s : S} (r : Run (Rel ostep) s) (n d : Nat) : Prop :=
  ∃ a, r.cfg n = .running a ∧ idx a = d ∧ (r.cfg (n + 1)).Sat (fun b => d < idx b) (fun _ => True)

omit [DecidableEq O] in
/-- **Each index is read at most once** along a run of the relation. -/
private theorem reads_unique (ha : Advance ostep idx) {s : S} (r : Run (Rel ostep) s)
    {m n d : Nat} (hm : Reads idx r m d) (hn : Reads idx r n d) : m = n := by
  have early : ∀ {m n : Nat}, Reads idx r m d → Reads idx r n d → ¬ m < n := by
    rintro m n ⟨_, _, _, hm⟩ ⟨a, hna, hd, _⟩ hlt
    cases hm₁ : r.cfg (m + 1) with
    | ended f => exact nomatch (r.ended_le hm₁ hlt).symm.trans hna
    | running b =>
      rw [hm₁] at hm
      have hd₁ : d < idx b := hm
      have := idx_mono ha r hlt hm₁ hna
      omega
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact absurd h (early hm hn)
  · exact h
  · exact absurd h (early hn hm)

omit [DecidableEq O] in
/-- **Completeness.** For a machine that reads the oracle only at an index that never decreases,
and that grows when it is read, every run of the relation is the run under one oracle: the
one that answers each index as the step that read it did (`Reads`), which is unique
(`reads_unique`). -/
theorem complete (hl : Local ostep idx) (ha : Advance ostep idx) {s : S}
    (r : Run (Rel ostep) s) : ∃ o, ∀ n, r.cfg n = trace (ostep o) s n := by
  have hw : ∀ n, ∃ o : Nat → Nat, ∀ a, r.cfg n = .running a → ostep o a = r.cfg (n + 1) := by
    intro n
    cases hn : r.cfg n with
    | ended f => exact ⟨fun _ => 0, fun _ h => nomatch h⟩
    | running a =>
      obtain ⟨o, ho⟩ := r.next hn
      exact ⟨o, fun _ h => by cases h; exact ho⟩
  let w n := (hw n).choose
  have hws : ∀ n {a}, r.cfg n = .running a → ostep (w n) a = r.cfg (n + 1) :=
    fun n a h => (hw n).choose_spec a h
  open Classical in
  let o : Nat → Nat := fun d => if h : ∃ n, Reads idx r n d then w h.choose d else 0
  refine ⟨o, fun n => ?_⟩
  induction n with
  | zero => exact r.start
  | succ n ih =>
    rw [trace_succ, ← ih]
    cases hn : r.cfg n with
    | ended f => exact r.stay hn
    | running a =>
      show r.cfg (n + 1) = ostep o a
      by_cases hR : Reads idx r n (idx a)
      · have ho : o (idx a) = w n (idx a) := by
          show (if h : ∃ m, Reads idx r m (idx a) then w h.choose (idx a) else 0) = _
          split
          · next h => rw [reads_unique ha r h.choose_spec hR]
          · next h => exact absurd ⟨n, hR⟩ h
        rw [hl o (w n) a ho, hws n hn]
      · cases hn₁ : r.cfg (n + 1) with
        | ended f => exact absurd ⟨a, hn, rfl, by rw [hn₁]; trivial⟩ hR
        | running b =>
          have h₁ := hws n hn
          rw [hn₁] at h₁
          obtain ⟨hle, hind⟩ := ha _ _ _ h₁
          have heq : idx b = idx a :=
            Nat.le_antisymm
              (Nat.le_of_not_lt fun hlt => hR ⟨a, hn, rfl, by rw [hn₁]; exact hlt⟩) hle
          rw [hind heq o, h₁]

omit [DecidableEq O] in
/-- **Divergence is divergence under some oracle.** -/
theorem diverges_iff (hl : Local ostep idx) (ha : Advance ostep idx) {s : S} :
    Diverges (Rel ostep) s ↔ ∃ o, ∀ n, ∃ s₁, trace (ostep o) s n = .running s₁ := by
  constructor
  · rintro ⟨r, hd⟩
    obtain ⟨o, ho⟩ := complete hl ha r
    exact ⟨o, fun n => ho n ▸ hd n⟩
  · rintro ⟨o, hd⟩
    exact ⟨run ostep o s, hd⟩

end

section
variable {ostepₛ : (Nat → Nat) → S → Config S F} {idxₛ : S → Nat}
  {ostepₜ : (Nat → Nat) → T → Config T G} {idxₜ : T → Nat}
  {obsₛ : S → O} {obsₜ : T → O} {resₛ : F → R} {resₜ : G → R} {wrong : R → Prop}

/-- **Trace refinement is "for every target oracle, some source oracle".** For oracle machines
with `Local` and `Advance` on both sides, trace refinement over runs of their relations says the
same as: for every oracle of the target there exists an oracle of the source whose run the
target's improves on. -/
theorem refines_iff (hlₛ : Local ostepₛ idxₛ) (haₛ : Advance ostepₛ idxₛ)
    (hlₜ : Local ostepₜ idxₜ) (haₜ : Advance ostepₜ idxₜ) (s : S) (t : T) :
    Trace.Refines (Rel ostepₛ) (Rel ostepₜ) obsₛ obsₜ resₛ resₜ wrong s t ↔
      ∀ oₜ, ∃ oₛ, Improves wrong ((run ostepₜ oₜ t).beh obsₜ resₜ)
        ((run ostepₛ oₛ s).beh obsₛ resₛ) := by
  constructor
  · intro h oₜ
    obtain ⟨rₛ, hi⟩ := h (run ostepₜ oₜ t)
    obtain ⟨oₛ, ho⟩ := complete hlₛ haₛ rₛ
    rw [Run.beh_congr (obs := obsₛ) (res := resₛ) rₛ (run ostepₛ oₛ s) ho] at hi
    exact ⟨oₛ, hi⟩
  · intro h rₜ
    obtain ⟨oₜ, ho⟩ := complete hlₜ haₜ rₜ
    obtain ⟨oₛ, hi⟩ := h oₜ
    rw [← Run.beh_congr (obs := obsₜ) (res := resₜ) rₜ (run ostepₜ oₜ t) ho] at hi
    exact ⟨run ostepₛ oₛ s, hi⟩

variable (ostepₛ ostepₜ obsₛ obsₜ resₛ resₜ wrong) in
/-- **Trace refinement under one oracle**: under every oracle, the target's run from `t`
improves on the source's run from `s` under the same oracle.  The oracle is shared, so each
choice is an input that the target must answer as the source does; it implies trace refinement
over runs (`Refines.refines`). -/
def Refines (s : S) (t : T) : Prop :=
  ∀ o, Improves wrong ((run ostepₜ o t).beh obsₜ resₜ) ((run ostepₛ o s).beh obsₛ resₛ)

/-- **Trace refinement under one oracle gives trace refinement over runs.**  The target run is
the run under some oracle (`complete`), and the source's run under the same oracle is the source
run.  Only the target needs `Local` and `Advance`. -/
theorem Refines.refines (hlₜ : Local ostepₜ idxₜ) (haₜ : Advance ostepₜ idxₜ) {s : S} {t : T}
    (h : Refines ostepₛ ostepₜ obsₛ obsₜ resₛ resₜ wrong s t) :
    Trace.Refines (Rel ostepₛ) (Rel ostepₜ) obsₛ obsₜ resₛ resₜ wrong s t := by
  intro rₜ
  obtain ⟨o, ho⟩ := complete hlₜ haₜ rₜ
  refine ⟨run ostepₛ o s, ?_⟩
  rw [Run.beh_congr rₜ (run ostepₜ o t) ho]
  exact h o

/-- **Trace refinement under one oracle is transitive**, so passes that keep choices compose. -/
theorem Refines.trans {U H : Type} {ostepₘ : (Nat → Nat) → T → Config T G}
    {ostepᵤ : (Nat → Nat) → U → Config U H} {obsₘ : T → O} {obsᵤ : U → O} {resₘ : G → R}
    {resᵤ : H → R} {s : S} {t : T} {u : U}
    (h₁ : Refines ostepₛ ostepₘ obsₛ obsₘ resₛ resₘ wrong s t)
    (h₂ : Refines ostepₘ ostepᵤ obsₘ obsᵤ resₘ resᵤ wrong t u) :
    Refines ostepₛ ostepᵤ obsₛ obsᵤ resₛ resᵤ wrong s u :=
  fun o => (h₂ o).trans (h₁ o)

/-- **A forward simulation under each oracle gives trace refinement under one oracle.** -/
theorem refines_of_sim {s : S} {t : T}
    (h : ∀ o, ∃ sim : Sim (ostepₛ o) (ostepₜ o) obsₛ obsₜ resₛ resₜ wrong, sim.rel s t) :
    Refines ostepₛ ostepₜ obsₛ obsₜ resₛ resₜ wrong s t := by
  intro o
  obtain ⟨sim, hr⟩ := h o
  rw [Run.beh_congr (run ostepₜ o t) (Run.ofFun (ostepₜ o) t) fun _ => rfl,
    Run.beh_congr (run ostepₛ o s) (Run.ofFun (ostepₛ o) s) fun _ => rfl]
  exact sim.improves hr _

end

end Oracle

end

end

end Strata.Dyn.Trace
