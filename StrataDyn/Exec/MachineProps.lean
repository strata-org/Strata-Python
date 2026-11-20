/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Machine

set_option autoImplicit false

/-!
# Properties of the machine's step

## Main theorems

* `step_ret`: a step that leaves a frame with a value (the next mode is `.ret`) took a site to
  the body's exit, among the sites of the instruction or terminator that it ran
  (`StepSites`).  Linking makes an exit site of a successor exactly when it names `Label.exit`
  (`linkSite_target_exit`), so a run of a body ends normally only along a successor that the IR's
  `Body.Leaves` sees (`Body.leaves_iff`), given that linking makes an instruction's sites from its
  successors, in order, which is not proved yet (`link_wf`).  It is about `step` only: a hook's
  `Action.modify` may continue from any well-formed state.

## Main definitions

* `StepSites`: the frame that a step from a state may leave, and the sites it may take: those of
  the instruction or terminator that the step runs;
* `LeftByExit`: a frame is left with a value along one of the given sites, to the body's exit.
-/

namespace Strata.Dyn.Exec

public section

variable {M : RunModel} {m : LModule M} {B : Ty}

/-- The frame `f` is left with `v` along a site of `ss` to the body's exit. -/
def LeftByExit (f : Frame M) (ss : List LSite) (v : Dyn M.interp) : Prop :=
  ∃ x ∈ ss, x.target = .exit ∧
    ∃ (ts : List Ty) (xs : Args M.interp ts) (hc : CanTake f x ts), take f x xs hc = .leave v

/-- A step from `s` runs an instruction or a terminator whose sites are `ss`, in the frame `f`:
the top frame's next instruction, of a rule, or its terminator; a rule paused at a request or
running again; or, when the top frame is left, the rule that waits on it. -/
inductive StepSites (s : State M) : Frame M → List LSite → Prop
  | sem {op : Name} {dst : Nat} {rs : List (List Ty × Ty)} {r : Ty} {ps : List (List Ty)}
      {re : Rerun M rs ps (M.interp r)}
      {fn : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) (M.interp r)) re.ts}
      {regs : List Nat} {succs : List LSite} {code : List (LInsn M)} :
      s.mode = .exec → s.core.top.code = .sem op dst rs r ps re fn regs succs :: code →
      StepSites s { s.core.top with code, pc := s.core.top.pc + 1 } succs
  | case {ts : List Ty} {ps : List (List Ty)} {fn : Fn M.interp (Exit M.interp ps) ts}
      {args : List Nat} {succs : List LSite} :
      s.mode = .exec → s.core.top.code = [] → s.core.top.term = .case ts ps fn args succs →
      StepSites s s.core.top succs
  | term {op : Name} {rs : List (List Ty × Ty)} {ps : List (List Ty)} {re : Rerun M rs ps Empty}
      {fn : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) Empty) re.ts}
      {regs : List Nat} {succs : List LSite} :
      s.mode = .exec → s.core.top.code = [] → s.core.top.term = .sem op rs ps re fn regs succs →
      StepSites s s.core.top succs
  | request {i : Inst M} {t : i.Tree} : s.mode = .request i t → StepSites s s.core.top i.succs
  | again {r : Reentry M} : s.mode = .again r → StepSites s s.core.top r.inst.succs
  | resume {v : Dyn M.interp} {f : Frame M} {p : Pending M} {cs : List (Wait M)} :
      s.mode = .ret v → s.core.conts = .rule f p :: cs → StepSites s f p.inst.succs

variable (m B) in
/-- Every next state that `r` gives whose mode leaves a frame comes from leaving `f` along a site
of `ss` to the body's exit. -/
private def RetFromExit (r : StepR m B) (f : Frame M) (ss : List LSite) : Prop :=
  ∀ ev s' h' v, r = .next ev s' h' → s'.mode = .ret v → LeftByExit f ss v

/-- Leaving `f` along the site of `ss` that an exit picks leaves the body only along a site of
`ss` to its exit. -/
private theorem exitTo_leave {f : Frame M} {v : Dyn M.interp} (ss : List LSite) :
    ∀ {ps : List (List Ty)} (e : Exit M.interp ps) (h : SitesOK f ss ps),
      exitTo f ss e h = .leave v → LeftByExit f ss v := by
  induction ss with
  | nil =>
    intro ps e h
    obtain ⟨_, _, hs⟩ := h
    cases e <;> exact absurd hs (fun hs => checkSites_nil_cons hs)
  | cons x ss ih =>
    intro ps e h hx
    cases e with
    | here xs =>
      obtain ⟨target, args⟩ := x
      cases target with
      | block i => simp [exitTo, take] at hx
      | exit => exact ⟨_, List.mem_cons_self, rfl, _, xs, _, hx⟩
    | there e =>
      obtain ⟨y, hy, hyt, hyx⟩ := ih e _ hx
      exact ⟨y, List.mem_cons_of_mem _ hy, hyt, hyx⟩

/-- A transfer along the site of `ss` that an exit picks leaves `f` only along a site of `ss` to
the body's exit. -/
private theorem transfer_exitTo {c : Core M} {ps : List (List Ty)} {ss : List LSite}
    {e : Exit M.interp ps} {h : SitesOK c.top ss ps} {hn : NextOK m c.top (exitTo c.top ss e h)}
    {hK : ContsOK m B c.top.func.ret c.conts} {drawn : Nat} {ev : Event} :
    RetFromExit m B (transfer c (exitTo c.top ss e h) hn hK drawn ev) c.top ss := by
  intro ev' s' h' v hs hm
  revert hn hs
  cases hx : exitTo c.top ss e h with
  | frame g => intro hn hs; cases hs; cases hm
  | leave w => intro hn hs; cases hs; cases hm; exact exitTo_leave ss e h hx

/-- A next state that `r` gives whose mode does not leave a frame satisfies `RetFromExit`. -/
private theorem retFromExit_of {r : StepR m B} {f : Frame M} {ss : List LSite}
    (h : ∀ ev s' h', r = .next ev s' h' → ∀ v, s'.mode ≠ .ret v) : RetFromExit m B r f ss :=
  fun ev s' h' v hs hm => absurd hm (h ev s' h' hs v)

/-- A fault leaves no frame. -/
private theorem faultStep_retFromExit {c : Core M} {f' : Fault} {drawn : Nat} {f : Frame M}
    {ss : List LSite} : RetFromExit m B (faultStep c f' drawn) f ss :=
  retFromExit_of fun _ _ _ hs _ hm => by cases hs; cases hm

/-- What the call check gives satisfies `P` when both of its outcomes do. -/
private theorem LModule.callee_cases {R : Type} {heap : Heap M} {idx captured : Nat}
    {ts : List Ty} {r : Ty} {ok : (hi : idx < m.funcs.size) → (caps : List (Dyn M.interp)) →
      (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts → (m.funcs[idx]'hi).ret = r → R}
    {bad : Unit → R} (P : R → Prop) (hok : ∀ hi caps hp hr, P (ok hi caps hp hr))
    (hbad : P (bad ())) : P (m.callee heap idx captured ts r ok bad) := by
  by_cases hc : ∃ caps, m.CallOK heap idx captured ts r caps
  · obtain ⟨caps, hc⟩ := hc
    rw [LModule.callee_pos hc]
    exact hok _ _ _ _
  · rw [LModule.callee_neg fun caps h => hc ⟨caps, h⟩]
    exact hbad

/-- What the cell check gives satisfies `P` when both of its outcomes do. -/
private theorem Heap.cell_cases {R : Type} {heap : Heap M} {l : Nat} {t : Ty}
    {ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → R} {bad : Unit → R}
    (P : R → Prop) (hok : ∀ hl ht, P (ok hl ht)) (hbad : P (bad ())) :
    P (heap.cell l t ok bad) := by
  by_cases hh : heap.Holds l t
  · rw [Heap.cell_pos hh]
    exact hok _ _
  · rw [Heap.cell_neg hh]
    exact hbad

section
variable (hwf : WF m) (oracle : Nat → Nat)

/-- Continuing the rule of `i` in `c`'s top frame leaves that frame only along a site of `i` to
the body's exit. -/
private theorem settle_retFromExit (c : Core M) (i : Inst M) (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) (ev : Event) (t : i.Tree) :
    RetFromExit m B (settle hwf c i hi hK drawn ev t) c.top i.succs := by
  unfold settle
  split
  · exact retFromExit_of fun _ _ _ hs _ hm => by cases hs; cases hm
  · exact transfer_exitTo
  · exact retFromExit_of fun _ _ _ hs _ hm => by cases hs; cases hm
  · exact faultStep_retFromExit
  · exact retFromExit_of fun _ _ _ hs _ hm => by cases hs; cases hm
  · unfold visitCall
    refine LModule.callee_cases (RetFromExit m B · c.top i.succs) (fun _ _ _ _ => ?_)
      faultStep_retFromExit
    exact retFromExit_of fun _ _ _ hs _ hm => by cases hs; cases hm
  · exact retFromExit_of fun _ _ _ hs _ hm => by cases hs; cases hm

/-- Answering the request of the rule of `i` leaves the top frame only along a site of `i` to
the body's exit. -/
private theorem serve_retFromExit (c : Core M) (i : Inst M) (t : i.Tree)
    (h : InstOK m c.top i ∧ ContsOK m B c.top.func.ret c.conts) (drawn : Nat) :
    RetFromExit m B (serve hwf oracle c i t h drawn) c.top i.succs := by
  unfold serve
  split
  · exact settle_retFromExit hwf _ _ _ _ _ _ _
  · split
    exact settle_retFromExit hwf _ _ _ _ _ _ _
  · exact settle_retFromExit hwf _ _ _ _ _ _ _
  · exact Heap.cell_cases (RetFromExit m B · c.top i.succs)
      (fun _ _ => settle_retFromExit hwf _ _ _ _ _ _ _) faultStep_retFromExit
  · exact Heap.cell_cases (RetFromExit m B · c.top i.succs)
      (fun _ _ => settle_retFromExit hwf _ _ _ _ _ _ _) faultStep_retFromExit
  · exact Heap.cell_cases (RetFromExit m B · c.top i.succs)
      (fun _ _ => settle_retFromExit hwf _ _ _ _ _ _ _) faultStep_retFromExit
  · exact LModule.callee_cases (RetFromExit m B · c.top i.succs)
      (fun _ _ _ _ => settle_retFromExit hwf _ _ _ _ _ _ _) faultStep_retFromExit
  · exact settle_retFromExit hwf _ _ _ _ _ _ _

/-- Running the top frame's terminator leaves a frame only along an exit site of the
terminator. -/
private theorem execTerm_ret (c : Core M) (h : CoreOK m B c) (hc : c.top.code = [])
    (drawn : Nat) (path : Unit) (t : LTerm M) (ht : c.top.term = t) {ev : Event}
    {s' : State M} {h' : StateOK m B s'} {v : Dyn M.interp}
    (hs : execTerm hwf c h hc drawn t ht = .next ev s' h') (hm : s'.mode = .ret v) :
    ∃ f ss, StepSites ⟨c, .exec, drawn, path⟩ f ss ∧ LeftByExit f ss v := by
  cases t with
  | case ts ps fn args succs =>
    simp only [execTerm] at hs
    exact ⟨_, _, .case rfl hc ht, transfer_exitTo _ _ _ _ hs hm⟩
  | sem op rs ps re fn regs succs =>
    simp only [execTerm] at hs
    exact ⟨_, _, .term rfl hc ht, settle_retFromExit hwf _ _ _ _ _ _ _ _ _ _ _ hs hm⟩

/-- Running the top frame's next instruction, or its terminator, leaves a frame only along an
exit site of what it runs. -/
private theorem execCode_ret (c : Core M) (h : CoreOK m B c) (drawn : Nat) (path : Unit)
    (code : List (LInsn M)) (hc : c.top.code = code) {ev : Event} {s' : State M}
    {h' : StateOK m B s'} {v : Dyn M.interp}
    (hs : execCode hwf c h drawn code hc = .next ev s' h') (hm : s'.mode = .ret v) :
    ∃ f ss, StepSites ⟨c, .exec, drawn, path⟩ f ss ∧ LeftByExit f ss v := by
  cases code with
  | nil =>
    simp only [execCode] at hs
    exact execTerm_ret hwf c h hc drawn path _ rfl hs hm
  | cons i code =>
    cases i with
    | sem op dst rs r ps re fn regs succs =>
      simp only [execCode] at hs
      exact ⟨_, _, .sem rfl hc, settle_retFromExit hwf _ _ _ _ _ _ _ _ _ _ _ hs hm⟩
    | const => simp only [execCode] at hs; cases hs; cases hm
    | pure => simp only [execCode] at hs; cases hs; cases hm
    | refNew => simp only [execCode] at hs; cases hs; cases hm
    | refGet dst t x =>
      simp only [execCode] at hs
      exact absurd hm (Heap.cell_cases
        (fun r : StepR m B => ∀ ev s' h', r = .next ev s' h' → s'.mode ≠ .ret v)
        (fun _ _ _ _ _ hr hm => by cases hr; cases hm)
        (fun _ _ _ hr hm => by cases hr; cases hm) _ _ _ hs)
    | refSet dst t x v' =>
      simp only [execCode] at hs
      exact absurd hm (Heap.cell_cases
        (fun r : StepR m B => ∀ ev s' h', r = .next ev s' h' → s'.mode ≠ .ret v)
        (fun _ _ _ _ _ hr hm => by cases hr; cases hm)
        (fun _ _ _ hr hm => by cases hr; cases hm) _ _ _ hs)
    | callCode dst ts r f args =>
      simp only [execCode] at hs
      exact absurd hm (LModule.callee_cases
        (fun r : StepR m B => ∀ ev s' h', r = .next ev s' h' → s'.mode ≠ .ret v)
        (fun _ _ _ _ _ _ _ hr hm => by cases hr; cases hm)
        (fun _ _ _ hr hm => by cases hr; cases hm) _ _ _ hs)

/-- Leaving the top frame resumes the frame that waits on it, which a resumed rule may leave at
once, only along an exit site of that rule. -/
private theorem leaveTo_ret (c : Core M) (v' : Dyn M.interp) (h : LeftOK m B c v') (drawn : Nat)
    (path : Unit) (cs : List (Wait M)) (hk : c.conts = cs) {ev : Event} {s' : State M}
    {h' : StateOK m B s'} {v : Dyn M.interp}
    (hs : leaveTo hwf c v' h drawn cs hk = .next ev s' h') (hm : s'.mode = .ret v) :
    ∃ f ss, StepSites ⟨c, .ret v', drawn, path⟩ f ss ∧ LeftByExit f ss v := by
  cases cs with
  | nil => simp only [leaveTo] at hs; cases hs; cases hm
  | cons w cs =>
    cases w with
    | rule f p =>
      simp only [leaveTo] at hs
      exact ⟨_, _, .resume rfl hk, settle_retFromExit hwf _ _ _ _ _ _ _ _ _ _ _ hs hm⟩
    | call f dst r => simp only [leaveTo] at hs; cases hs; cases hm

/-- **A step leaves a frame only along an exit site of what it runs**: if the next state's mode
leaves a frame with `v`, the step from `s` left the frame `f` that it runs in along an exit site
of `ss`, the sites of the instruction or terminator that it runs. -/
theorem step_ret {s : State M} {h : StateOK m B s} {ev : Event} {s' : State M}
    {h' : StateOK m B s'} {v : Dyn M.interp} (hs : step hwf oracle s h = .next ev s' h')
    (hm : s'.mode = .ret v) : ∃ f ss, StepSites s f ss ∧ LeftByExit f ss v := by
  obtain ⟨c, mode, drawn, path⟩ := s
  cases mode with
  | exec => exact execCode_ret hwf c h drawn path _ rfl hs hm
  | jump to => cases hs; cases hm
  | call callee w => cases hs; cases hm
  | ret v' => exact leaveTo_ret hwf c v' h drawn path _ rfl hs hm
  | request i t =>
    exact ⟨_, _, .request rfl, serve_retFromExit hwf oracle c i t h drawn _ _ _ v hs hm⟩
  | again r =>
    exact ⟨_, _, .again rfl, settle_retFromExit hwf c r.inst h.1 h.2 drawn _ _ _ _ _ v hs hm⟩
  | done r => cases hs

end

end

end Strata.Dyn.Exec
