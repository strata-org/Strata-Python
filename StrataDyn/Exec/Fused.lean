/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Machine

set_option autoImplicit false

/-!
# The fused run

`runFused` runs as `runFrames` does, but performs each transition in the step that decides it:
an edge, an entry into a body, and a rule's choices and world accesses take no step of their
own, and no event is built.  It is the engine for execution; `step` stays the reference, and
hooks and debuggers use it.  A fused step ends in an `FStep`: a running configuration, a frame
about to leave with a value, or a rule about to run again with a new state.  The loop,
`fusedLoop` and `fusedLeave`, continues from each; `fusedLoop` runs both a configuration and a
rule about to run again (`FPend`).  A leave that a step does not
perform is a step of its own, because resuming the waiting rule may leave again, to the rule
below, and so on; stopping there keeps the loop structural.  So is a run of a rule again, whose
new tree is no part of the old one.

* `runFused_eq`: `runFused n` ends as `runFrames t` does for some `t ≥ n`, with the same
  outcome, snapshot and number of choices, or at the same configuration.
* `runFused_of_runFrames`: a run that `runFrames` finishes on `n` fuel, `runFused` finishes on
  `n` too, with at least as much fuel left.
* `runFrames_of_runFused` and `runFrames_timeout`: the converses, up to more fuel.
* `runHooked_fused`: a hook that only observes, run long enough, ends as `runFused` does.
* `runHooked_resume`: a run that a hook which never modifies stopped, resumed with
  `runFused`, ends as the uninterrupted `runFrames` does.

`runFused n` and `runFrames n` differ in general.  A rule's requests are each a step of
`runFrames` but all part of one fused step, so `t` grows with the number of requests one rule
makes, and no bound `t ≤ c · n` with a fixed `c` holds across models.  While's `sum 100` ends
after 606 fused steps and 810 by step (`StrataDynTest/Examples/While/RunTest.lean`), so on
606 fuel `runFused` finishes and `runFrames` runs out.  So `runFused_eq` relates a fused run
to `runFrames` on some fuel `t ≥ n`, not on `n`.
-/

namespace Strata.Dyn.Exec

@[expose] public section

section
variable {M : RunModel} {m : LModule M} (hwf : WF m) (oracle : Nat → Nat) {B : Ty}

variable (m B) in
/-- A fused step's outcome: a running configuration, a frame about to leave with a value, a
rule about to run again with a new state, or the run's outcome, the heap, the world and the
number of choices made. -/
inductive FStep where
  | next (c : Core M) (drawn : Nat) (h : CoreOK m B c)
  | leave (c : Core M) (v : Dyn M.interp) (drawn : Nat) (h : LeftOK m B c v)
  | again (c : Core M) (r : Reentry M) (drawn : Nat)
    (h : InstOK m c.top r.inst ∧ ContsOK m B c.top.func.ret c.conts)
  | final (r : Result M.interp) (heap : Heap M) (world : M.W) (drawn : Nat)

/-- Perform a transfer: take the edge, or stop at the leave. -/
@[inline] def ftransfer (c : Core M) (n : Next M) (hn : NextOK m c.top n)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) :
    FStep m B :=
  match n, hn with
  | .frame g, hn => .next { c with top := g } drawn ⟨hn.1, hn.2 ▸ hK⟩
  | .leave v, hn => .leave c v drawn ⟨hn, hK⟩

/-- Enter the function of the closure `(idx, captured)`, if the check of the call passes.  It
is out of line: inlined, it costs the fused loop about 1% on runs that make no rule calls, more
than it saves on those that do. -/
@[noinline] def fvisitCall (c : Core M) (i : Inst M)
    (hi : InstOK m c.top i) (hK : ContsOK m B c.top.func.ret c.conts)
    (drawn : Nat) (sig : List Ty × Ty) (idx captured : Nat) (args : Payload (sig.1.map M.interp))
    (k : M.interp sig.2 → i.Tree) : FStep m B :=
  m.callee c.heap idx captured sig.1 sig.2
    (fun hl caps hp hr =>
      .next { c with top := callFrame hwf idx hl caps (Args.ofPayload sig.1 args),
                     conts := .rule c.top ⟨i, .call sig idx captured args, sig.2, k⟩ :: c.conts }
        drawn (hi.call hwf hK hl hp hr args k))
    (fun _ => .final (.fault (.badCall (m.fnName idx))) c.heap c.world drawn)

/-- Enter region `j`. -/
@[inline] def fvisitRegion (c : Core M) (i : Inst M)
    (hi : InstOK m c.top i) (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat)
    (j : Fin i.rs.length) (args : Args M.interp (i.rs.get j).1)
    (k : M.interp (i.rs.get j).2 → i.Tree) : FStep m B :=
  .next { c with
    top := regionStart m c.top (i.region j hi.length) (hi.region_lt j) (hi.region_entry j)
      (hi.region_fits j).1 (hi.region_fits j).2 args,
    conts := .rule c.top ⟨i, .region j args, (i.rs.get j).2, k⟩ :: c.conts } drawn
    (hi.start hwf hK j args k)

mutual
/-- Run the rule of operation `i` from its tree, in `c`'s top frame, answering its choices and
world accesses, until it binds its result, takes a transfer, jumps to its `Again`, stops or
enters a body. -/
@[specialize]
def fsettleLoop (c : Core M) (i : Inst M) (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) : i.Tree → FStep m B
  | .ret v =>
    .next { c with top := c.top.bind i.dst (resDyn i.ret v) (hi.dst_lt v) } drawn
      (hi.next hK v)
  | .stop (.jump (.exit e)) =>
    ftransfer c (exitTo c.top i.succs e hi.sitesOK) (hi.exit hwf e) hK drawn
  | .stop (.jump (.again st)) => .again c ⟨i, st⟩ drawn ⟨hi, hK⟩
  | .stop (.fault f) => .final (.fault f) c.heap c.world drawn
  | .choose k => fsettleLoop c i hi hK (drawn + 1) (k (oracle drawn))
  | .update f =>
    -- Taking the configuration apart first leaves `f` the only holder of the world.
    match c, hi, hK with
    | ⟨top, conts, heap, w⟩, hi, hK => fsettleAfter top conts heap i hi hK drawn (f w)
  | .vis (.region j args) k => fvisitRegion hwf c i hi hK drawn j args k
  | .vis (.call sig idx captured args) k => fvisitCall hwf c i hi hK drawn sig idx captured args k
  | .vis (.new t v) k =>
    -- The new location is read before the push, so that the push finds the heap unshared.
    let l := c.heap.cells.size
    fsettleLoop { c with heap := c.heap.push ⟨t, v⟩ } i hi hK drawn (k ⟨⟨l, trivial⟩⟩)
  | .vis (.get t l) k =>
    c.heap.cell l t (fun hl ht => fsettleLoop c i hi hK drawn (k (c.heap.valueAt hl ht)))
      (fun _ => .final (.fault (.badCell l)) c.heap c.world drawn)
  | .vis (.set t l v) k =>
    c.heap.cell l t
      (fun hl _ => fsettleLoop { c with heap := c.heap.set l ⟨t, v⟩ hl } i hi hK drawn (k ()))
      (fun _ => .final (.fault (.badCell l)) c.heap c.world drawn)
  | .vis (.modify t l g) k =>
    c.heap.cell l t
      (fun _ _ => fsettleLoop { c with heap := c.heap.modify l t g } i hi hK drawn (k ()))
      (fun _ => .final (.fault (.badCell l)) c.heap c.world drawn)
  | .vis (.bind t v sig idx captured) k =>
    let l := c.heap.caps.size + 1
    m.callee c.heap idx captured (t :: sig.1) sig.2
      (fun _ caps _ _ => fsettleLoop { c with heap := c.heap.capture (caps ++ [⟨t, v⟩]) } i hi hK
        drawn (k ⟨⟨idx, l, trivial⟩⟩))
      (fun _ => .final (.fault (.badCall (m.fnName idx))) c.heap c.world drawn)

/-- Continue the rule of operation `i` after an update of the world: with the new world and
the continuation the update gave. -/
@[specialize]
def fsettleAfter (top : Frame M) (conts : List (Wait M)) (heap : Heap M) (i : Inst M)
    (hi : InstOK m top i) (hK : ContsOK m B top.func.ret conts) (drawn : Nat) :
    M.W × i.Tree → FStep m B
  | (w, k) => fsettleLoop ⟨top, conts, heap, w⟩ i hi hK drawn k
end

/-- `fsettleLoop`, with its first step inlined if it is a result, a stop or a region: a rule
that makes no other request, as most do, runs with no call.  The other requests go to
`fsettleLoop`, so that each of the fused loop's inlined copies stays small. -/
@[inline] def fsettle (c : Core M) (i : Inst M)
    (hi : InstOK m c.top i) (hK : ContsOK m B c.top.func.ret c.conts)
    (drawn : Nat) : i.Tree → FStep m B
  | .ret v =>
    .next { c with top := c.top.bind i.dst (resDyn i.ret v) (hi.dst_lt v) } drawn
      (hi.next hK v)
  | .stop (.jump (.exit e)) =>
    ftransfer c (exitTo c.top i.succs e hi.sitesOK) (hi.exit hwf e) hK drawn
  | .stop (.jump (.again st)) => .again c ⟨i, st⟩ drawn ⟨hi, hK⟩
  | .stop (.fault f) => .final (.fault f) c.heap c.world drawn
  | .vis (.region j args) k => fvisitRegion hwf c i hi hK drawn j args k
  | t => fsettleLoop hwf oracle c i hi hK drawn t

/-- `fsettle`, which inlines the common first steps, settles a rule as `fsettleLoop` does. -/
theorem fsettle_eq (c : Core M) (i : Inst M)
    (hi : InstOK m c.top i) (hK : ContsOK m B c.top.func.ret c.conts)
    (drawn : Nat) (t : i.Tree) :
    fsettle hwf oracle c i hi hK drawn t = fsettleLoop hwf oracle c i hi hK drawn t := by
  cases t with
  | stop s => cases s with
    | jump e => cases e <;> rfl
    | fault => rfl
  | vis q k => cases q <;> rfl
  | _ => rfl

/-- Leave the top frame with `v`, the rules `cs` waiting: end the run, or resume the rule
waiting on the body. -/
@[inline] def fleaveTo (c : Core M) (v : Dyn M.interp) (h : LeftOK m B c v) (drawn : Nat) :
    (cs : List (Wait M)) → c.conts = cs → FStep m B
  | [], _ => .final (.ok v) c.heap c.world drawn
  | .rule f p :: cs, hk =>
    have hw := h.rule hk
    fsettle hwf oracle { top := f, conts := cs, heap := c.heap, world := c.world } p.inst
      hw.2.1 hw.2.2 drawn (p.k (v.at hw.1))
  | .call f dst _ :: cs, hk =>
    .next { top := f.bind dst v (h.call_dst hk), conts := cs, heap := c.heap,
            world := c.world } drawn (h.call hk)

/-- Leave the top frame with `v`: end the run, or resume the rule waiting on the body. -/
@[inline] def fleave (c : Core M) (v : Dyn M.interp) (h : LeftOK m B c v) (drawn : Nat) :
    FStep m B :=
  fleaveTo hwf oracle c v h drawn c.conts rfl

/-- Run the terminator of the top frame, `t`, whose code is done, and perform its transfer. -/
@[inline] def fexecTerm (c : Core M) (h : CoreOK m B c) (hc : c.top.code = []) (drawn : Nat) :
    (t : LTerm M) → c.top.term = t → FStep m B
  | .case ts ps f args succs, ht =>
    have hr : TermReady c (.case ts ps f args succs) := h.termReady hc ht
    let e := applyFn c.top.env ts f args hr.1
    ftransfer c (exitTo c.top succs e hr.2) (h.caseNext hwf hc ht e hr.2) h.2 drawn
  | .sem op rs ps re f regs succs, ht =>
    have hr : TermReady c (.sem op rs ps re f regs succs) := h.termReady hc ht
    fsettle hwf oracle c ⟨op, c.top.pc, 0, none, ps, rs, regs, succs, re⟩
      (h.termInst hc ht) h.2 drawn (applyFn c.top.env re.ts f re.args hr)

/-- Run the top frame's next instruction, the head of `code`, or its terminator, and perform
its transfer. -/
@[inline] def fexecCode (c : Core M) (h : CoreOK m B c) (drawn : Nat) :
    (code : List (LInsn M)) → c.top.code = code → FStep m B
  | [], hc => fexecTerm hwf oracle c h hc drawn c.top.term rfl
  | .const dst v :: code, hc => .next (c.next code dst v c.heap (h.dst_lt hc)) drawn (h.const hc)
  | .pure dst ts r f args :: code, hc =>
    .next (c.next code dst ⟨r, applyFn c.top.env ts f args (h.ready hc)⟩ c.heap (h.dst_lt hc))
      drawn (h.pure hc _)
  | .sem op dst rs r ps re f regs succs :: code, hc =>
    fsettle hwf oracle { c with top := { c.top with code, pc := c.top.pc + 1 } }
      ⟨op, c.top.pc, dst, some r, ps, rs, regs, succs, re⟩
      (h.inst hc) h.2 drawn (applyFn c.top.env re.ts f re.args (h.ready hc))
  | .refNew dst t v :: code, hc =>
    .next (c.refNew code dst t v (h.ready hc) (h.dst_lt hc)) drawn (h.refNew hc (h.ready hc))
  | .refGet dst t x :: code, hc =>
    let l := c.cellLoc t x (h.ready hc)
    c.heap.cell l t
      (fun hl ht => .next (c.refGet code dst l hl (h.dst_lt hc)) drawn (h.refGet hc hl ht))
      (fun _ => .final (.fault (.badCell l)) c.heap c.world drawn)
  | .refSet dst t x v :: code, hc =>
    have hr : HasTy c.top.env x (Ty.ref t) ∧ Bound c.top.env v := h.ready hc
    let l := c.cellLoc t x hr.1
    c.heap.cell l t
      (fun hl _ => .next (c.refSet code dst l hl v hr.2 (h.dst_lt hc)) drawn (h.refSet hc hl hr.2))
      (fun _ => .final (.fault (.badCell l)) c.heap c.world drawn)
  | .callCode dst ts r f args :: code, hc =>
    have hr : Ready c (.callCode dst ts r f args) := h.ready hc
    let g := M.fnOf (getT c.top.env f (Ty.fn ts r) hr.1)
    m.callee c.heap g.idx g.captured ts r
      (fun hl caps hp hret =>
        .next { c with top := callFrame hwf g.idx hl (appendCaps caps (lookupAll c.top.env args hr.2)) .nil,
                       conts := .call { c.top with code, pc := c.top.pc + 1 } dst r :: c.conts }
          drawn (h.callCode hwf hc hr hl hp hret))
      (fun _ => .final (.fault (.badCall (m.fnName g.idx))) c.heap c.world drawn)

/-- Perform a leave that a fused step stopped at: the common return, from a body to the rule
waiting on it.  A leave that the resumed rule makes in turn is left to the next step. -/
@[inline] def FStep.leaveOnce : FStep m B → FStep m B
  | .leave c v d h => fleave hwf oracle c v h d
  | s => s

/-- Run the top frame's next instruction, or its terminator, and perform its transfer. -/
@[inline] def fexec (c : Core M) (h : CoreOK m B c) (drawn : Nat) : FStep m B :=
  (fexecCode hwf oracle c h drawn c.top.code rfl).leaveOnce hwf oracle

/-- Run the rule of operation `r.inst` again, with the state `r.st`, and perform its
transfer. -/
@[inline] def fagain (c : Core M) (r : Reentry M)
    (h : InstOK m c.top r.inst ∧ ContsOK m B c.top.func.ret c.conts) (drawn : Nat) : FStep m B :=
  (fsettle hwf oracle c r.inst h.1 h.2 drawn (r.inst.again c.top.env h.1.typed r.st)).leaveOnce
    hwf oracle

variable (M) in
/-- What a fused loop runs from, besides a frame about to leave: the top frame's next
instruction or terminator, or a rule about to run again with a new state. -/
inductive FPend where
  | exec
  | again (r : Reentry M)

variable (m B) in
/-- What running from `p` in `c` needs: `StateOK` of the configuration it stands for. -/
def FPend.OK (c : Core M) : FPend M → Prop
  | .exec => CoreOK m B c
  | .again r => InstOK m c.top r.inst ∧ ContsOK m B c.top.func.ret c.conts

-- The loop matches each fused step's outcome where it is made, so that the common one, a running
-- configuration, is never built as an `FStep`.  A rule about to run again is a state of
-- `fusedLoop` itself, so that a loop of re-entries and bodies stays one loop of the compiled
-- code: a call from one function to another with as many arguments is no tail call there.
mutual
/-- Run at most `fuel` fused steps from a running configuration, or from a rule about to run
again. -/
@[specialize] def fusedLoop : Nat → (c : Core M) → Nat → (p : FPend M) → p.OK m B c → RunEnd m B
  | 0, c, d, .exec, h => .timeout ⟨c, .exec, d, ()⟩ h
  | 0, c, d, .again r, h => .timeout ⟨c, .again r, d, ()⟩ h
  | n + 1, c, d, .exec, h => match fexec hwf oracle c h d with
    | .next c₁ d₁ h₁ => fusedLoop n c₁ d₁ .exec h₁
    | .leave c₁ v d₁ h₁ => fusedLeave n c₁ v d₁ h₁
    | .again c₁ r d₁ h₁ => fusedLoop n c₁ d₁ (.again r) h₁
    | .final r hp w d₁ => .done r ⟨hp, w⟩ d₁ n
  | n + 1, c, d, .again r, h => match fagain hwf oracle c r h d with
    | .next c₁ d₁ h₁ => fusedLoop n c₁ d₁ .exec h₁
    | .leave c₁ v d₁ h₁ => fusedLeave n c₁ v d₁ h₁
    | .again c₁ r₁ d₁ h₁ => fusedLoop n c₁ d₁ (.again r₁) h₁
    | .final r hp w d₁ => .done r ⟨hp, w⟩ d₁ n

/-- Run at most `fuel` fused steps from a frame about to leave with `v`. -/
@[specialize]
def fusedLeave : Nat → (c : Core M) → (v : Dyn M.interp) → Nat → LeftOK m B c v → RunEnd m B
  | 0, c, v, d, h => .timeout ⟨c, .ret v, d, ()⟩ h
  | n + 1, c, v, d, h => match fleave hwf oracle c v h d with
    | .next c₁ d₁ h₁ => fusedLoop n c₁ d₁ .exec h₁
    | .leave c₁ v₁ d₁ h₁ => fusedLeave n c₁ v₁ d₁ h₁
    | .again c₁ r d₁ h₁ => fusedLoop n c₁ d₁ (.again r) h₁
    | .final r hp w d₁ => .done r ⟨hp, w⟩ d₁ n
end

/-- Continue from a fused step's outcome for at most `fuel` fused steps. -/
@[specialize] def FStep.loop (n : Nat) : FStep m B → RunEnd m B
  | .next c d h => fusedLoop hwf oracle n c d .exec h
  | .leave c v d h => fusedLeave hwf oracle n c v d h
  | .again c r d h => fusedLoop hwf oracle n c d (.again r) h
  | .final r hp w d => .done r ⟨hp, w⟩ d n

/-- Run at most `fuel` fused steps.  A configuration with another pending transition first
performs it as `step` does, for one unit of fuel. -/
@[specialize] def runFused : Nat → (s : State M) → StateOK m B s → RunEnd m B
  | n, ⟨c, .exec, d, _⟩, h => fusedLoop hwf oracle n c d .exec h
  | n, ⟨c, .ret v, d, _⟩, h => fusedLeave hwf oracle n c v d h
  | 0, s, h => .timeout s h
  | n + 1, s, h => match step hwf oracle s h with
    | .next _ s₁ h₁ => runFused n s₁ h₁
    | .final r hp w d => .done r ⟨hp, w⟩ d n

/-! ## `runFused` against `runFrames`

Each fused transition is a run of zero or more steps after the first: `fexec_sim` says that
`exec`'s result, continued for `j + k` steps, is where `fexec` leads, continued for `j`.
`settle_sim` and `leave_sim` say the same of a rule's tree and of a leaving frame, by induction
on the tree. -/

/-- A step's outcome, continued by `runFrames` for `n` more steps. -/
def StepR.run : StepR m B → Nat → RunEnd m B
  | .next _ s h, n => runFrames hwf oracle n s h
  | .final r hp w d, n => .done r ⟨hp, w⟩ d n

/-- A fused step's outcome, continued by `runFrames` for `n` more steps. -/
def FStep.run : FStep m B → Nat → RunEnd m B
  | .next c d h, n => runFrames hwf oracle n ⟨c, .exec, d, ()⟩ h
  | .leave c v d h, n => runFrames hwf oracle n ⟨c, .ret v, d, ()⟩ h
  | .again c r d h, n => runFrames hwf oracle n ⟨c, .again r, d, ()⟩ h
  | .final r hp w d, n => .done r ⟨hp, w⟩ d n

/-- A run's end, continued by `runFrames` for `j` more steps. -/
def RunEnd.resume : RunEnd m B → Nat → RunEnd m B
  | .done r sn d l, j => .done r sn d (l + j)
  | .timeout s h, j => runFrames hwf oracle j s h

/-- Running `n + 1` steps takes one step, then runs `n` more from where it left off. -/
theorem runFrames_succ (n : Nat) (s : State M) (h : StateOK m B s) :
    runFrames hwf oracle (n + 1) s h = (step hwf oracle s h).run hwf oracle n := by
  show (match step hwf oracle s h with
    | .next _ s₁ h₁ => runFrames hwf oracle n s₁ h₁
    | .final r hp w d => .done r ⟨hp, w⟩ d n) = _
  cases step hwf oracle s h <;> rfl

/-- A run on `n + j` fuel is the run on `n`, resumed for `j`. -/
theorem runFrames_add : ∀ (n j : Nat) (s : State M) (h : StateOK m B s),
    runFrames hwf oracle (n + j) s h = (runFrames hwf oracle n s h).resume hwf oracle j
  | 0, j, s, h => by rw [Nat.zero_add]; rfl
  | n + 1, j, s, h => by
    rw [Nat.add_right_comm, runFrames_succ, runFrames_succ]
    cases step hwf oracle s h with
    | next _ s₁ h₁ => exact runFrames_add n j s₁ h₁
    | final r hp w d => rfl

/-- A transfer, made pending by `step` and run `k` steps further, is where `ftransfer`
leads. -/
private theorem transfer_sim (c : Core M) (n : Next M) (hn : NextOK m c.top n)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat)
    (ev : Event) : ∃ k, ∀ j, (transfer c n hn hK drawn ev).run hwf oracle (j + k) =
      (ftransfer c n hn hK drawn).run hwf oracle j := by
  cases n with
  | frame g => exact ⟨1, fun _ => rfl⟩
  | leave v => exact ⟨0, fun _ => rfl⟩

/-- A rule's tree, settled by `step` and run `k` steps further, is where `fsettleLoop`
leads.  By recursion on the tree, through each update's new world and continuation. -/
private theorem settleLoop_sim (i : Inst M) (t : i.Tree) :
    ∀ (c : Core M) (hi : InstOK m c.top i)
      (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) (ev : Event), ∃ k, ∀ j,
      (settle hwf c i hi hK drawn ev t).run hwf oracle (j + k) =
        (fsettleLoop hwf oracle c i hi hK drawn t).run hwf oracle j := by
  refine Sem.rec
    (motive_1 := fun t => ∀ (c : Core M) (hi : InstOK m c.top i)
      (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) (ev : Event), ∃ k, ∀ j,
      (settle hwf c i hi hK drawn ev t).run hwf oracle (j + k) =
        (fsettleLoop hwf oracle c i hi hK drawn t).run hwf oracle j)
    (motive_2 := fun p => ∀ (top : Frame M) (conts : List (Wait M)) (heap : Heap M)
      (hi : InstOK m top i) (hK : ContsOK m B top.func.ret conts) (drawn : Nat) (ev : Event),
      ∃ k, ∀ j, (settle hwf ⟨top, conts, heap, p.1⟩ i hi hK drawn ev p.2).run hwf oracle (j + k) =
        (fsettleAfter hwf oracle top conts heap i hi hK drawn p).run hwf oracle j)
    ?ret ?stop ?choose ?vis ?update ?after t
  case ret => exact fun v _ _ _ _ _ => ⟨0, fun _ => rfl⟩
  case stop =>
    intro s
    cases s with
    | jump e => cases e with
      | exit e => exact fun c hi hK drawn ev => transfer_sim hwf oracle c _ _ hK drawn ev
      | again st => exact fun _ _ _ _ _ => ⟨0, fun _ => rfl⟩
    | fault f => exact fun _ _ _ _ _ => ⟨1, fun _ => rfl⟩
  case choose =>
    intro k ih c hi hK drawn _
    obtain ⟨t, ht⟩ := ih (oracle drawn) c hi hK (drawn + 1) (.answer (.choose (oracle drawn)))
    refine ⟨t + 1, fun j => ?_⟩
    rw [← Nat.add_assoc]
    exact (runFrames_succ hwf oracle (j + t) _ _).trans (ht j)
  case update =>
    intro f ih c hi hK drawn _
    obtain ⟨top, conts, heap, w⟩ := c
    obtain ⟨t, ht⟩ := ih w top conts heap hi hK drawn (.answer .world)
    refine ⟨t + 1, fun j => ?_⟩
    rw [← Nat.add_assoc]
    exact (runFrames_succ hwf oracle (j + t) _ _).trans (ht j)
  case after =>
    exact fun w k ih top conts heap hi hK drawn ev => ih ⟨top, conts, heap, w⟩ hi hK drawn ev
  case vis =>
    intro q k ih
    cases q with
    | region j args => exact fun _ _ _ _ _ => ⟨1, fun _ => rfl⟩
    | call sig idx captured args =>
      intro c hi hK drawn _
      by_cases hh : ∃ caps, m.CallOK c.heap idx captured sig.1 sig.2 caps
      · obtain ⟨caps, hcall⟩ := hh
        refine ⟨1, fun j => ?_⟩
        dsimp only [settle, visitCall, fsettleLoop, fvisitCall]
        rw [LModule.callee_pos hcall, LModule.callee_pos hcall]
        rfl
      · refine ⟨1, fun j => ?_⟩
        dsimp only [settle, visitCall, fsettleLoop, fvisitCall]
        rw [LModule.callee_neg fun caps h => hh ⟨caps, h⟩,
          LModule.callee_neg fun caps h => hh ⟨caps, h⟩]
        rfl
    | new t v =>
      intro c hi hK drawn _
      obtain ⟨n, hn⟩ := ih ⟨⟨c.heap.cells.size, trivial⟩⟩ { c with heap := c.heap.push ⟨t, v⟩ } hi
        hK drawn (.answer (.cell .new c.heap.cells.size))
      refine ⟨n + 1, fun j => ?_⟩
      rw [← Nat.add_assoc]
      exact (runFrames_succ hwf oracle (j + n) _ _).trans (hn j)
    | get t l =>
      intro c hi hK drawn _
      by_cases hh : c.heap.Holds l t
      · obtain ⟨n, hn⟩ := ih (c.heap.valueAt hh.lt hh.code) c hi hK drawn
          (.answer (.cell .get l))
        refine ⟨n + 1, fun j => ?_⟩
        rw [← Nat.add_assoc]
        refine (runFrames_succ hwf oracle (j + n) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [Heap.cell_pos hh, Heap.cell_pos hh]
        exact hn j
      · refine ⟨2, fun j => ?_⟩
        refine (runFrames_succ hwf oracle (j + 1) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [Heap.cell_neg hh, Heap.cell_neg hh]
        rfl
    | set t l v =>
      intro c hi hK drawn _
      by_cases hh : c.heap.Holds l t
      · obtain ⟨n, hn⟩ := ih () { c with heap := c.heap.set l ⟨t, v⟩ hh.lt } hi hK drawn
          (.answer (.cell .set l))
        refine ⟨n + 1, fun j => ?_⟩
        rw [← Nat.add_assoc]
        refine (runFrames_succ hwf oracle (j + n) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [Heap.cell_pos hh, Heap.cell_pos hh]
        exact hn j
      · refine ⟨2, fun j => ?_⟩
        refine (runFrames_succ hwf oracle (j + 1) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [Heap.cell_neg hh, Heap.cell_neg hh]
        rfl
    | modify t l g =>
      intro c hi hK drawn _
      by_cases hh : c.heap.Holds l t
      · obtain ⟨n, hn⟩ := ih () { c with heap := c.heap.modify l t g } hi hK drawn
          (.answer (.cell .modify l))
        refine ⟨n + 1, fun j => ?_⟩
        rw [← Nat.add_assoc]
        refine (runFrames_succ hwf oracle (j + n) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [Heap.cell_pos hh, Heap.cell_pos hh]
        exact hn j
      · refine ⟨2, fun j => ?_⟩
        refine (runFrames_succ hwf oracle (j + 1) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [Heap.cell_neg hh, Heap.cell_neg hh]
        rfl
    | bind t v sig idx captured =>
      intro c hi hK drawn _
      by_cases hh : ∃ caps, m.CallOK c.heap idx captured (t :: sig.1) sig.2 caps
      · obtain ⟨caps, hcall⟩ := hh
        obtain ⟨n, hn⟩ := ih ⟨⟨idx, c.heap.caps.size + 1, trivial⟩⟩
          { c with heap := c.heap.capture (caps ++ [⟨t, v⟩]) } hi hK drawn
          (.answer (.capture (c.heap.caps.size + 1)))
        refine ⟨n + 1, fun j => ?_⟩
        rw [← Nat.add_assoc]
        refine (runFrames_succ hwf oracle (j + n) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [LModule.callee_pos hcall, LModule.callee_pos hcall]
        exact hn j
      · refine ⟨2, fun j => ?_⟩
        refine (runFrames_succ hwf oracle (j + 1) _ _).trans ?_
        dsimp only [step, serve, fsettleLoop]
        rw [LModule.callee_neg fun caps h => hh ⟨caps, h⟩, LModule.callee_neg fun caps h => hh ⟨caps, h⟩]
        rfl

/-- A rule's tree, settled by `step` and run `k` steps further, is where `fsettle` leads. -/
private theorem settle_sim (i : Inst M) (t : i.Tree) (c : Core M)
    (hi : InstOK m c.top i) (hK : ContsOK m B c.top.func.ret c.conts)
    (drawn : Nat) (ev : Event) : ∃ k, ∀ j,
      (settle hwf c i hi hK drawn ev t).run hwf oracle (j + k) =
        (fsettle hwf oracle c i hi hK drawn t).run hwf oracle j := by
  rw [fsettle_eq]
  exact settleLoop_sim hwf oracle i t c hi hK drawn ev

/-- A frame leaving by `step`, run `k` steps further, is where `fleave` leads. -/
private theorem leave_sim (c : Core M) (v : Dyn M.interp) (h : LeftOK m B c v) (drawn : Nat) :
    ∃ k, ∀ j, (leave hwf c v h drawn).run hwf oracle (j + k) =
      (fleave hwf oracle c v h drawn).run hwf oracle j :=
  go c.conts rfl
where
  go : ∀ (cs : List (Wait M)) (hk : c.conts = cs), ∃ k, ∀ j,
      (leaveTo hwf c v h drawn cs hk).run hwf oracle (j + k) =
        (fleaveTo hwf oracle c v h drawn cs hk).run hwf oracle j
    | [], _ => ⟨1, fun _ => rfl⟩
    | .call .. :: _, _ => ⟨0, fun _ => rfl⟩
    | .rule .. :: _, _ => settle_sim hwf oracle _ _ _ _ _ _ _

/-- A fused step's outcome, run `k` steps further, is where performing its pending leave
leads. -/
private theorem leaveOnce_sim : ∀ st : FStep m B, ∃ k, ∀ j,
    st.run hwf oracle (j + k) = (st.leaveOnce hwf oracle).run hwf oracle j
  | .leave c v d h => by
    obtain ⟨k, hk⟩ := leave_sim hwf oracle c v h d
    refine ⟨k + 1, fun j => ?_⟩
    rw [← Nat.add_assoc]
    exact (runFrames_succ hwf oracle (j + k) _ _).trans (hk j)
  | .next .. | .again .. | .final .. => ⟨0, fun _ => rfl⟩

/-- A step from `Mode.again`, run `k` steps further, is where `fagain` leads. -/
private theorem fagain_sim (c : Core M) (r : Reentry M)
    (h : InstOK m c.top r.inst ∧ ContsOK m B c.top.func.ret c.conts) (drawn : Nat) :
    ∃ k, ∀ j, (step hwf oracle ⟨c, .again r, drawn, ()⟩ h).run hwf oracle (j + k) =
      (fagain hwf oracle c r h drawn).run hwf oracle j := by
  obtain ⟨k₁, hk₁⟩ := settle_sim hwf oracle r.inst (r.inst.again c.top.env h.1.typed r.st) c h.1
    h.2 drawn (.instr ⟨c.top.func.name, c.top.block, r.inst.pc⟩)
  obtain ⟨k₂, hk₂⟩ := leaveOnce_sim hwf oracle
    (fsettle hwf oracle c r.inst h.1 h.2 drawn (r.inst.again c.top.env h.1.typed r.st))
  refine ⟨k₂ + k₁, fun j => ?_⟩
  rw [← Nat.add_assoc]
  exact (hk₁ (j + k₂)).trans (hk₂ j)

/-- An `exec` step, run `k` steps further, is where `fexec` leads. -/
private theorem fexec_sim (c : Core M) (h : CoreOK m B c) (drawn : Nat) :
    ∃ k, ∀ j, (exec hwf c h drawn).run hwf oracle (j + k) =
      (fexec hwf oracle c h drawn).run hwf oracle j := by
  obtain ⟨k₁, hk₁⟩ := code c.top.code rfl
  obtain ⟨k₂, hk₂⟩ := leaveOnce_sim hwf oracle (fexecCode hwf oracle c h drawn c.top.code rfl)
  refine ⟨k₂ + k₁, fun j => ?_⟩
  rw [← Nat.add_assoc]
  exact (hk₁ (j + k₂)).trans (hk₂ j)
where
  term (hc : c.top.code = []) : ∀ (t : LTerm M) (ht : c.top.term = t), ∃ k, ∀ j,
      (execTerm hwf c h hc drawn t ht).run hwf oracle (j + k) =
        (fexecTerm hwf oracle c h hc drawn t ht).run hwf oracle j
    | .case .., _ => transfer_sim hwf oracle c _ _ h.2 drawn _
    | .sem .., _ => settle_sim hwf oracle _ _ _ _ _ _ _
  code : ∀ (code : List (LInsn M)) (hc : c.top.code = code), ∃ k, ∀ j,
      (execCode hwf c h drawn code hc).run hwf oracle (j + k) =
        (fexecCode hwf oracle c h drawn code hc).run hwf oracle j
    | [], hc => term hc c.top.term rfl
    | .const .. :: _, _ | .pure .. :: _, _ | .refNew .. :: _, _ => ⟨0, fun _ => rfl⟩
    | .refGet _ t x :: _, hc => by
      dsimp only [execCode, fexecCode]
      by_cases hh : c.heap.Holds (c.cellLoc t x (h.ready hc)) t
      · rw [Heap.cell_pos hh, Heap.cell_pos hh]
        exact ⟨0, fun _ => rfl⟩
      · rw [Heap.cell_neg hh, Heap.cell_neg hh]
        exact ⟨1, fun _ => rfl⟩
    | .refSet _ t x _ :: _, hc => by
      dsimp only [execCode, fexecCode]
      by_cases hh : c.heap.Holds (c.cellLoc t x (h.ready hc).1) t
      · rw [Heap.cell_pos hh, Heap.cell_pos hh]
        exact ⟨0, fun _ => rfl⟩
      · rw [Heap.cell_neg hh, Heap.cell_neg hh]
        exact ⟨1, fun _ => rfl⟩
    | .callCode dst ts r f args :: _, hc => by
      dsimp only [execCode, fexecCode]
      by_cases hh : ∃ caps, m.CallOK c.heap
          (M.fnOf (getT c.top.env f (Ty.fn ts r) (h.ready hc).1)).idx
          (M.fnOf (getT c.top.env f (Ty.fn ts r) (h.ready hc).1)).captured ts r caps
      · obtain ⟨caps, hcall⟩ := hh
        rw [LModule.callee_pos hcall, LModule.callee_pos hcall]
        exact ⟨1, fun _ => rfl⟩
      · rw [LModule.callee_neg fun caps h => hh ⟨caps, h⟩,
          LModule.callee_neg fun caps h => hh ⟨caps, h⟩]
        exact ⟨1, fun _ => rfl⟩
    | .sem .. :: _, _ => settle_sim hwf oracle _ _ _ _ _ _ _

/-- A fused loop from a running configuration takes `fexec`'s step, then continues. -/
private theorem fusedLoop_succ (n : Nat) (c : Core M) (d : Nat) (h : CoreOK m B c) :
    fusedLoop hwf oracle (n + 1) c d .exec h = (fexec hwf oracle c h d).loop hwf oracle n := by
  refine (fusedLoop.eq_3 ..).trans ?_
  cases fexec hwf oracle c h d <;> rfl

/-- A fused loop from a frame about to leave takes `fleave`'s step, then continues. -/
private theorem fusedLeave_succ (n : Nat) (c : Core M) (v : Dyn M.interp) (d : Nat)
    (h : LeftOK m B c v) :
    fusedLeave hwf oracle (n + 1) c v d h = (fleave hwf oracle c v h d).loop hwf oracle n := by
  rw [fusedLeave]
  cases fleave hwf oracle c v h d <;> rfl

/-- A fused loop from a rule about to run again takes `fagain`'s step, then continues. -/
private theorem fusedLoop_again_succ (n : Nat) (c : Core M) (r : Reentry M) (d : Nat)
    (h : InstOK m c.top r.inst ∧ ContsOK m B c.top.func.ret c.conts) :
    fusedLoop hwf oracle (n + 1) c d (.again r) h =
      (fagain hwf oracle c r h d).loop hwf oracle n := by
  refine (fusedLoop.eq_4 ..).trans ?_
  cases fagain hwf oracle c r h d <;> rfl

/-- A fused loop on `n` fuel ends as `runFrames` does, from where the fused step left off, on
some `t ≥ n`. -/
private theorem fusedLoop_eq : ∀ (n : Nat) (st : FStep m B),
    ∃ t, n ≤ t ∧ st.run hwf oracle t = st.loop hwf oracle n
  | 0, .final _ _ _ _ | 0, .next _ _ _ | 0, .leave _ _ _ _ | 0, .again _ _ _ _ =>
    ⟨0, Nat.le_refl 0, rfl⟩
  | n + 1, .final _ _ _ _ => ⟨n + 1, Nat.le_refl _, rfl⟩
  | n + 1, .next c d h => by
    obtain ⟨k, hk⟩ := fexec_sim hwf oracle c h d
    obtain ⟨t, hnt, ht⟩ := fusedLoop_eq n (fexec hwf oracle c h d)
    exact ⟨t + k + 1, by omega, (runFrames_succ hwf oracle _ _ _).trans
      ((hk t).trans (ht.trans (fusedLoop_succ hwf oracle n c d h).symm))⟩
  | n + 1, .leave c v d h => by
    obtain ⟨k, hk⟩ := leave_sim hwf oracle c v h d
    obtain ⟨t, hnt, ht⟩ := fusedLoop_eq n (fleave hwf oracle c v h d)
    exact ⟨t + k + 1, by omega, (runFrames_succ hwf oracle _ _ _).trans
      ((hk t).trans (ht.trans (fusedLeave_succ hwf oracle n c v d h).symm))⟩
  | n + 1, .again c r d h => by
    obtain ⟨k, hk⟩ := fagain_sim hwf oracle c r h d
    obtain ⟨t, hnt, ht⟩ := fusedLoop_eq n (fagain hwf oracle c r h d)
    exact ⟨t + k + 1, by omega, (runFrames_succ hwf oracle _ _ _).trans
      ((hk t).trans (ht.trans (fusedLoop_again_succ hwf oracle n c r d h).symm))⟩

/-- `runFused` on `n` fuel ends as `runFrames` does on some `t ≥ n`: with the same outcome,
snapshot and number of choices, or at the same configuration. -/
theorem runFused_eq : ∀ (n : Nat) (s : State M) (h : StateOK m B s),
    ∃ t, n ≤ t ∧ runFrames hwf oracle t s h = runFused hwf oracle n s h
  | n, ⟨c, .exec, d, ()⟩, h => by
    cases n <;> exact fusedLoop_eq hwf oracle _ (.next c d h)
  | n, ⟨c, .ret v, d, ()⟩, h => by
    cases n <;> exact fusedLoop_eq hwf oracle _ (.leave c v d h)
  | 0, ⟨_, .jump _, _, ()⟩, _ | 0, ⟨_, .call .., _, ()⟩, _ | 0, ⟨_, .request .., _, ()⟩, _
  | 0, ⟨_, .again .., _, ()⟩, _ | 0, ⟨_, .done _, _, ()⟩, _ => ⟨0, Nat.le_refl 0, rfl⟩
  | n + 1, ⟨c, .jump to, d, ()⟩, h | n + 1, ⟨c, .call callee w, d, ()⟩, h
  | n + 1, ⟨c, .request i t, d, ()⟩, h | n + 1, ⟨c, .again r, d, ()⟩, h
  | n + 1, ⟨c, .done r, d, ()⟩, h => by
    -- A pending transition: one step, then the rest of the run.
    have hr : ∀ e : StepR m B, ∃ t, n ≤ t ∧ e.run hwf oracle t = (match e with
        | .next _ s₁ h₁ => runFused hwf oracle n s₁ h₁
        | .final r hp w d => .done r ⟨hp, w⟩ d n) := fun
      | .next _ s₁ h₁ => runFused_eq n s₁ h₁
      | .final _ _ _ _ => ⟨n, Nat.le_refl n, rfl⟩
    obtain ⟨t, hnt, ht⟩ := hr (step hwf oracle _ h)
    exact ⟨t + 1, Nat.succ_le_succ hnt, (runFrames_succ hwf oracle t _ h).trans ht⟩

/-- If `runFused` ends with an outcome, `runFrames` ends with the same outcome, snapshot and
number of choices on any fuel from some `t ≥ n` on. -/
theorem runFrames_of_runFused {n : Nat} {s : State M} {h : StateOK m B s}
    {r : Result M.interp} {sn : Snapshot M} {d l : Nat}
    (hf : runFused hwf oracle n s h = .done r sn d l) :
    ∃ t, n ≤ t ∧ ∀ j, runFrames hwf oracle (t + j) s h = .done r sn d (l + j) := by
  obtain ⟨t, hnt, ht⟩ := runFused_eq hwf oracle n s h
  refine ⟨t, hnt, fun j => ?_⟩
  rw [runFrames_add, ht, hf]
  rfl

/-- A run that `runFrames` ends with an outcome on `n` fuel, `runFused` ends with the same
outcome, snapshot and number of choices on `n`, with at least as much fuel left. -/
theorem runFused_of_runFrames {n : Nat} {s : State M} {h : StateOK m B s}
    {r : Result M.interp} {sn : Snapshot M} {d l : Nat}
    (hd : runFrames hwf oracle n s h = .done r sn d l) :
    ∃ l₁, l ≤ l₁ ∧ runFused hwf oracle n s h = .done r sn d l₁ := by
  obtain ⟨t, hnt, ht⟩ := runFused_eq hwf oracle n s h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hnt
  refine ⟨l + j, Nat.le_add_right l j, ?_⟩
  rw [← ht, runFrames_add, hd]
  rfl

/-- If `runFused` runs out of fuel, so does `runFrames` on the same fuel, and on some `t ≥ n` it
stops at the same configuration. -/
theorem runFrames_timeout {n : Nat} {s s₁ : State M} {h : StateOK m B s} {h₁ : StateOK m B s₁}
    (hf : runFused hwf oracle n s h = .timeout s₁ h₁) :
    (∃ s₂ h₂, runFrames hwf oracle n s h = .timeout s₂ h₂) ∧
      ∃ t, n ≤ t ∧ runFrames hwf oracle t s h = .timeout s₁ h₁ := by
  refine ⟨?_, hf ▸ runFused_eq hwf oracle n s h⟩
  cases hd : runFrames hwf oracle n s h with
  | timeout s₂ h₂ => exact ⟨s₂, h₂, rfl⟩
  | done r sn d l =>
    obtain ⟨_, _, he⟩ := runFused_of_runFrames hwf oracle hd
    exact nomatch hf.symm.trans he

/-- A hook that only observes, run long enough, ends as `runFused` does. -/
theorem runHooked_fused {ρ : Type} (hook : Hook m B ρ)
    (hobs : ∀ st ev s, ∃ st₁, hook st ev s = .continue st₁) (n : Nat) (st : ρ) (s : State M)
    (h : StateOK m B s) :
    ∃ t, n ≤ t ∧
      (runHooked hwf oracle hook t st s h).1.toRunEnd = some (runFused hwf oracle n s h) := by
  obtain ⟨t, hnt, ht⟩ := runFused_eq hwf oracle n s h
  exact ⟨t, hnt, ht ▸ runHooked_observer hwf oracle hook hobs t st s h⟩

/-- A run that a hook which never modifies stopped, resumed with `runFused` on `j` fuel, ends
as `runFrames` does from the start, on the steps taken before the stop and some `t ≥ j`
after it.  This is what a debugger's stop-then-resume rests on. -/
theorem runHooked_resume {ρ : Type} (hook : Hook m B ρ)
    (hnm : ∀ st ev s st₁ s₁ h₁, hook st ev s ≠ .modify st₁ s₁ h₁) {n : Nat} {st : ρ}
    {s s₁ : State M} {h : StateOK m B s} {h₁ : StateOK m B s₁} {l : Nat}
    (hs : (runHooked hwf oracle hook n st s h).1 = .stopped s₁ h₁ l) (j : Nat) :
    ∃ t, j ≤ t ∧ runFrames hwf oracle (n - l + t) s h = runFused hwf oracle j s₁ h₁ := by
  obtain ⟨_, hstop⟩ := runHooked_stopped hwf oracle hook hnm n st s h hs
  obtain ⟨t, hjt, ht⟩ := runFused_eq hwf oracle j s₁ h₁
  refine ⟨t, hjt, ?_⟩
  rw [runFrames_add, hstop]
  exact ht

end

end

end Strata.Dyn.Exec
