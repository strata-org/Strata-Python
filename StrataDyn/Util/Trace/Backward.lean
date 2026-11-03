/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Util.Trace

set_option autoImplicit false

/-!
# Backward simulation

A backward simulation proves trace refinement (`Refines`) by matching every target run with source
steps that the proof chooses, so a translation may drop, add or reorder choices.  It is the
method for passes whose choices do not correspond one to one; a pass that keeps them uses a
forward `Sim` under one oracle (`Oracle.refines_of_sim`).

* `BSim`: every target run, from related states, matches after one or more target steps,
  still but for the last, one or more source steps (`BSim.Seg`) to a configuration that
  `BSim.MatchEnd` accepts.  `BSim.refines` proves trace refinement from it.
* `BSimStep`: the form with one target step per match and a measure that bounds the target steps
  the source does not match.  `BSimStep.toBSim` turns it into a `BSim`.

`BSim.refines` builds the source run as the projection of a deterministic driver, which walks
the target run and takes the planned source steps of each match one at a time; the matching of
the two runs (`RunMatch`) gives the improvement.
-/

namespace Strata.Dyn.Trace

@[expose] public section

variable {S F T G O R : Type} [DecidableEq O]

/-! ## Backward simulation -/

/-- Source steps from `s` through the configurations `cs`: each a step from the state before,
all but the last running in a state observed as `s` is, and the last satisfying `fin`. -/
inductive BSim.Seg (stepₛ : S → Config S F → Prop) (obsₛ : S → O) (fin : Config S F → Prop) :
    S → List (Config S F) → Prop where
  | last {s : S} {c : Config S F} : stepₛ s c → fin c → BSim.Seg stepₛ obsₛ fin s [c]
  | cons {s s₁ : S} {cs : List (Config S F)} : stepₛ s (.running s₁) → obsₛ s₁ = obsₛ s →
      BSim.Seg stepₛ obsₛ fin s₁ cs → BSim.Seg stepₛ obsₛ fin s (.running s₁ :: cs)

omit [DecidableEq O] in
/-- A weaker ending keeps the steps. -/
theorem BSim.Seg.mono {stepₛ : S → Config S F → Prop} {obsₛ : S → O}
    {fin fin₁ : Config S F → Prop} (hf : ∀ c, fin c → fin₁ c) {s : S} {cs : List (Config S F)}
    (h : BSim.Seg stepₛ obsₛ fin s cs) : BSim.Seg stepₛ obsₛ fin₁ s cs := by
  induction h with
  | last hs hc => exact .last hs (hf _ hc)
  | cons hs ho _ ih => exact .cons hs ho ih

section
variable (stepₛ : S → Config S F → Prop) (stepₜ : T → Config T G → Prop) (obsₛ : S → O)
  (obsₜ : T → O) (resₛ : F → R) (resₜ : G → R) (wrong : R → Prop)

/-- How a match ends at the target configuration `cₜ`: the source runs in a state related to
the target's, or ends wrong, or ends with what the target's outcome shows. -/
def BSim.MatchEnd (rel : S → T → Prop) (cₜ : Config T G) : Config S F → Prop :=
  Config.Sat (fun s₁ => ∃ t₁, cₜ = .running t₁ ∧ rel s₁ t₁)
    (fun f => wrong (resₛ f) ∨ ∃ g, cₜ = .ended g ∧ resₜ g = resₛ f)

/-- **A match** from the source state `s` along the target configurations `c`: the target is
still from `0` to `k`, and one or more source steps from `s`, quiet but for the last, reach a
configuration that `BSim.MatchEnd` accepts against the target's at `k + 1`. -/
def BSim.Match (rel : S → T → Prop) (s : S) (c : Nat → Config T G) : Prop :=
  ∃ k cs, Still obsₜ c 0 k ∧
    BSim.Seg stepₛ obsₛ (BSim.MatchEnd resₛ resₜ wrong rel (c (k + 1))) s cs

/-- **A backward simulation** of the source `stepₛ` by the target `stepₜ`.  Related states are
observed alike.  From related states, every target run matches: for every target run, there
exist a number of its steps and source steps that `BSim.Match` accepts.  Each match takes at least
one step on each side, so a target that runs forever is matched by a source that does. -/
structure BSim where
  rel : S → T → Prop
  obs_eq : ∀ {s : S} {t : T}, rel s t → obsₛ s = obsₜ t
  «match» : ∀ {s : S} {t : T}, rel s t → ∀ r : Run stepₜ t,
    BSim.Match stepₛ obsₛ obsₜ resₛ resₜ wrong rel s r.cfg

/-- **A backward simulation with a measure.** Each target step, from related states, is
matched by source steps, quiet but for the last, to a state related to the target's next one,
or to a wrong outcome; or by no source step, and then the measure decreases.  A target outcome
is matched by source steps to an outcome that is wrong or shows the same. -/
structure BSimStep where
  rel : S → T → Prop
  measure : T → Nat
  obs_eq : ∀ {s : S} {t : T}, rel s t → obsₛ s = obsₜ t
  next : ∀ {s : S} {t t₁ : T}, rel s t → stepₜ t (.running t₁) →
    (∃ cs, BSim.Seg stepₛ obsₛ (Config.Sat (fun s₁ => rel s₁ t₁) (fun f => wrong (resₛ f))) s cs) ∨
      (measure t₁ < measure t ∧ rel s t₁)
  final : ∀ {s : S} {t : T} {g : G}, rel s t → stepₜ t (.ended g) →
    ∃ cs, BSim.Seg stepₛ obsₛ
      (Config.Sat (fun _ => False) (fun f => wrong (resₛ f) ∨ resₜ g = resₛ f)) s cs

end

variable {stepₛ : S → Config S F → Prop} {stepₜ : T → Config T G → Prop} {obsₛ : S → O}
  {obsₜ : T → O} {resₛ : F → R} {resₜ : G → R} {wrong : R → Prop}

/-- **The measure form is a special case.** A backward simulation with a measure gives one whose
matches take one or more target steps: the steps on which the source stays are bounded by the
measure. -/
def BSimStep.toBSim (sim : BSimStep stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong) :
    BSim stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong where
  rel := sim.rel
  obs_eq := sim.obs_eq
  «match» := by
    have key : ∀ μ {s : S} {t : T}, sim.measure t ≤ μ → sim.rel s t → ∀ r : Run stepₜ t,
        BSim.Match stepₛ obsₛ obsₜ resₛ resₜ wrong sim.rel s r.cfg := by
      intro μ
      induction μ using Nat.strongRecOn with
      | ind μ ih =>
        intro s t hμ hr r
        have h₁ := r.next r.start
        cases hc : r.cfg (0 + 1) with
        | running t₁ =>
          rw [hc] at h₁
          rcases sim.next hr h₁ with ⟨cs, hs⟩ | ⟨hlt, hr₁⟩
          · refine ⟨0, cs, .single r.start, hs.mono fun c hc₁ => ?_⟩
            cases c with
            | running s₁ => exact ⟨t₁, hc, hc₁⟩
            | ended f => exact .inl hc₁
          · obtain ⟨k, cs, hq, hs⟩ :=
              ih _ (Nat.lt_of_lt_of_le hlt hμ) (Nat.le_refl _) hr₁ (r.drop 1 hc)
            exact ⟨k + 1, cs, .cons r.start hc ((sim.obs_eq hr₁).symm.trans (sim.obs_eq hr)) hq,
              hs⟩
        | ended g =>
          rw [hc] at h₁
          obtain ⟨cs, hs⟩ := sim.final hr h₁
          refine ⟨0, cs, .single r.start, hs.mono fun c hc₁ => ?_⟩
          cases c with
          | running s₁ => exact absurd hc₁ id
          | ended f => exact hc₁.imp id fun he => ⟨g, hc, he⟩
    intro s t hr r
    exact key _ (Nat.le_refl _) hr r

/-! ### The source run that a backward simulation builds -/

/-- Where the source run being built stands: in the state `cur`, in a match that started with the
target at time `idx` and ends with it at `idx + len + 1`, with `pend` the source configurations
still to visit in it. -/
private structure Pos (S F : Type) where
  cur : S
  idx : Nat
  len : Nat
  pend : List (Config S F)

namespace BSim

variable (sim : BSim stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong) {t₀ : T} (r : Run stepₜ t₀)

/-- The source state `x` is related to the target's state at time `n`. -/
private def At (x : S) (n : Nat) : Prop := ∃ t, r.cfg n = .running t ∧ sim.rel x t

/-- A match in progress: the target at `p.idx` is observed as `p.cur` is, and still until
`p.idx + p.len`; `p.pend` are source steps from `p.cur` that end where the target is at
`p.idx + p.len + 1`. -/
private def InMatch (p : Pos S F) : Prop :=
  (∃ t, r.cfg p.idx = .running t ∧ obsₛ p.cur = obsₜ t) ∧ Still obsₜ r.cfg p.idx (p.idx + p.len) ∧
    Seg stepₛ obsₛ (MatchEnd resₛ resₜ wrong sim.rel (r.cfg (p.idx + p.len + 1))) p.cur p.pend

omit [DecidableEq O] in
/-- From a related state, a match starts. -/
private theorem exists_plan {x : S} {n : Nat} (h : sim.At r x n) :
    ∃ q : Nat × List (Config S F), sim.InMatch r ⟨x, n, q.1, q.2⟩ := by
  obtain ⟨t, ht, hr⟩ := h
  obtain ⟨k, cs, hq, hs⟩ := sim.match hr (r.drop n ht)
  refine ⟨(k, cs), ⟨t, ht, sim.obs_eq hr⟩, hq.of_drop, ?_⟩
  rw [show n + k + 1 = k + 1 + n by omega]
  exact hs

open Classical in
/-- The match planned from the source state `x`, with the target at time `n`. -/
private noncomputable def plan (x : S) (n : Nat) : Pos S F :=
  let q := if h : sim.At r x n then (sim.exists_plan r h).choose else (0, [])
  ⟨x, n, q.1, q.2⟩

omit [DecidableEq O] in
/-- A match planned from a related state is in progress. -/
private theorem plan_spec {x : S} {n : Nat} (h : sim.At r x n) :
    sim.InMatch r (sim.plan r x n) := by
  unfold plan
  split
  · exact (sim.exists_plan r h).choose_spec
  · contradiction

/-- **One step of the source run**: the next configuration of the match, and at its end the
match planned from there. -/
private noncomputable def drive (p : Pos S F) : Config (Pos S F) F :=
  match p.pend with
  | [] => .running p
  | [.running x₁] => .running (sim.plan r x₁ (p.idx + p.len + 1))
  | .running x₁ :: c :: cs => .running ⟨x₁, p.idx, p.len, c :: cs⟩
  | .ended f :: _ => .ended f

omit [DecidableEq O] in
/-- **The driving function keeps matches in progress.** -/
private theorem drive_inductive :
    Inductive (graph (sim.drive r)) (sim.InMatch r) (fun _ => True) := by
  rintro ⟨x, n, k, pend⟩ c ⟨⟨t, ht, ho⟩, hq, hs⟩ rfl
  cases hs with
  | @last _ c hst hf =>
    cases c with
    | ended f => trivial
    | running x₁ =>
      obtain ⟨t₁, h₁, hr₁⟩ := hf
      exact sim.plan_spec r ⟨t₁, h₁, hr₁⟩
  | @cons _ x₁ cs hst hob hs₁ =>
    cases cs with
    | nil => exact nomatch hs₁
    | cons c cs => exact ⟨⟨t, ht, hob.trans ho⟩, hq, hs₁⟩

omit [DecidableEq O] in
/-- Each step of the driving function projects to a source step. -/
private theorem drive_step {p : Pos S F} (hp : sim.InMatch r p) :
    stepₛ p.cur ((sim.drive r p).mapS Pos.cur) := by
  obtain ⟨x, n, k, pend⟩ := p
  obtain ⟨_, _, hs⟩ := hp
  cases hs with
  | @last _ c hst _ =>
    cases c with
    | running x₁ => exact hst
    | ended f => exact hst
  | @cons _ x₁ cs hst _ hs₁ =>
    cases cs with
    | nil => exact nomatch hs₁
    | cons c cs => exact hst

/-- **The source run** that the matches build, one source step at a time. -/
private noncomputable def srcRun {s : S} (hr : sim.rel s t₀) : Run stepₛ s :=
  Run.ofDet (sim.drive r) Pos.cur (sim.InMatch r) (sim.drive_inductive r)
    (fun _ hq => sim.drive_step r hq) (sim.plan r s 0) (sim.plan_spec r ⟨t₀, r.start, hr⟩)

omit [DecidableEq O] in
/-- From time `n` of the driver's run at `p`, the next configuration is the driver's step. -/
private theorem drive_succ {s : S} {n : Nat} {p : Pos S F}
    (hp : trace (sim.drive r) (sim.plan r s 0) n = .running p) :
    trace (sim.drive r) (sim.plan r s 0) (n + 1) = sim.drive r p := by
  rw [trace_succ, hp]
  rfl

/-- **The source run is matched forward by the target run.** -/
private noncomputable def runSim {s : S} (hr : sim.rel s t₀) :
    RunMatch obsₛ obsₜ resₛ resₜ wrong (sim.srcRun r hr) r where
  rel n n₁ := ∃ p, trace (sim.drive r) (sim.plan r s 0) n = .running p ∧ sim.InMatch r p ∧
    p.idx = n₁
  measure n := (trace (sim.drive r) (sim.plan r s 0) n).measure (·.pend.length)
  start := ⟨_, rfl, sim.plan_spec r ⟨t₀, r.start, hr⟩, rfl⟩
  obs_eq := by
    rintro n _ ⟨p, hp, ⟨⟨t, ht, ho⟩, _⟩, rfl⟩
    refine ⟨p.cur, t, ?_, ht, ho⟩
    show (trace (sim.drive r) (sim.plan r s 0) n).mapS Pos.cur = _
    rw [hp]
    rfl
  next := by
    rintro n _ ⟨p, hp, ⟨⟨t, ht, ho⟩, hq, hs⟩, rfl⟩ ⟨y, hy⟩
    change (trace (sim.drive r) (sim.plan r s 0) (n + 1)).mapS Pos.cur = _ at hy
    show _ ∨ ((trace (sim.drive r) (sim.plan r s 0) (n + 1)).measure (·.pend.length) <
      (trace (sim.drive r) (sim.plan r s 0) n).measure (·.pend.length) ∧ _)
    rw [sim.drive_succ r hp] at hy ⊢
    rw [hp]
    obtain ⟨x, i, k, pend⟩ := p
    cases hs with
    | @last _ c hst hf =>
      cases c with
      | ended f => exact nomatch hy
      | running x₁ =>
        obtain ⟨t₁, h₁, hr₁⟩ := hf
        exact .inl ⟨k, hq, _, rfl, sim.plan_spec r ⟨t₁, h₁, hr₁⟩, rfl⟩
    | @cons _ x₁ cs hst hob hs₁ =>
      cases cs with
      | nil => exact nomatch hs₁
      | cons c cs => exact .inr ⟨Nat.lt_succ_self _, _, rfl, ⟨⟨t, ht, hob.trans ho⟩, hq, hs₁⟩, rfl⟩
  final := by
    rintro n _ f ⟨p, hp, ⟨_, hq, hs⟩, rfl⟩ hf
    change (trace (sim.drive r) (sim.plan r s 0) (n + 1)).mapS Pos.cur = _ at hf
    rw [sim.drive_succ r hp] at hf
    obtain ⟨x, i, k, pend⟩ := p
    cases hs with
    | @last _ c hst hfin =>
      cases c with
      | running x₁ => exact nomatch hf
      | ended f₁ =>
        cases hf
        exact hfin.imp id fun ⟨g, h₁, hg₁⟩ => ⟨k, g, hq, h₁, hg₁⟩
    | @cons _ x₁ cs hst hob hs₁ =>
      cases cs with
      | nil => exact nomatch hs₁
      | cons c cs => exact nomatch hf

end BSim

/-- **Trace refinement from a backward simulation.** From related states, every target run improves
on some source run: the source run that the matches build, one source step at a time. -/
theorem BSim.refines (sim : BSim stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong) {s : S} {t : T}
    (hr : sim.rel s t) : Refines stepₛ stepₜ obsₛ obsₜ resₛ resₜ wrong s t :=
  fun r => ⟨sim.srcRun r hr, (sim.runSim r hr).improves⟩

end

end Strata.Dyn.Trace
