/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Call

set_option autoImplicit false

/-!
# Heap safety

The machine checks every access of a cell (`Heap.cell`) and faults with `Fault.badCell` when the
check fails.  For a module whose rules are certified, the check never fails: every ref a run
holds is valid in a typing of the heap, so it names a cell of its tag.

* `access_ok`: at every configuration of a run from a state where the run invariant holds, the
  access the next step makes, a `refGet` or `refSet` of the top frame or a rule's request to
  read, write or update a cell (`State.Accesses`), finds a cell of its tag.
* A rule may still stop with `Fault.badCell` itself: a certificate says nothing of faults.
  `Sem.Avoids bad t` says that a tree never stops with a fault in `bad`, and `LModule.Avoids`
  that no rule of a module's instructions and terminators does.  `State.Avoids` carries it along
  a run, with the run invariant (`step_avoids`, `avoids_always`).
* **Heap safety**, `never_badCell`: no run of a module whose rules are certified and stop with no
  bad cell themselves, from a state where the invariant holds, faults with `Fault.badCell`, at any
  configuration or at its end.  `never_badCell_startCore` starts it from a function's
  entry, from a snapshot that a typing of its heap types (`Snapshot.OK`), on arguments that hold no
  ref: the start satisfies the invariant at that typing (`inv_startCore_of`) and avoids what the
  module avoids (`startCore_avoids`).  `never_badCell_start` reads it from `start`.
* Snapshots: `Snapshot.ok_initial` (the engine's start, whose world holds no ref) and
  `ended_ok` (where a run ends; every tree avoids the empty set of faults, `Sem.avoids_none`, so
  it needs no hypothesis on the rules' faults).  From either, on arguments that hold no ref, the
  refs a function starts with are well tagged (`Snapshot.OK.wellTagged`), so the frame theorem
  from a function's start needs no hypothesis about tags (`frame_startCore_ok`).

`Fault.badCall` is not covered: a typing gives a closure's captures cell its tags, not the
function it calls, so a closure that a certified rule hands the machine may name a function of
another signature.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-! ## Trees that avoid some faults -/

section
variable {ε : Eff} {E α : Type} (bad : Fault → Prop)

mutual
/-- **The tree `t` avoids the faults `bad`**: no leaf it reaches, under any answer, choice and
world, stops with a fault in `bad`. -/
def Sem.Avoids : Sem ε E α → Prop
  | .ret _ => True
  | .stop (.jump _) => True
  | .stop (.fault f) => ¬ bad f
  | .choose k => ∀ c, Sem.Avoids (k c)
  | .vis _ k => ∀ o, Sem.Avoids (k o)
  | .update f => ∀ w, Sem.AvoidsAfter (f w)

/-- An update's continuation avoids the faults `bad`. -/
def Sem.AvoidsAfter : ε.W × Sem ε E α → Prop
  | (_, k) => Sem.Avoids k
end

variable {bad}

/-- A fault avoids `bad` when it is not in `bad`. -/
theorem Sem.avoids_fault {f : Fault} : (Sem.stop (.fault f) : Sem ε E α).Avoids bad ↔ ¬ bad f := by
  rw [Sem.Avoids]

/-- A choice avoids `bad` when every continuation does. -/
theorem Sem.avoids_choose {k : Nat → Sem ε E α} :
    (Sem.choose k).Avoids bad ↔ ∀ c, (k c).Avoids bad := by
  rw [Sem.Avoids]

/-- A request avoids `bad` when its continuation does on every answer. -/
theorem Sem.avoids_vis {i : ε.I} {k : ε.O i → Sem ε E α} :
    (Sem.vis i k).Avoids bad ↔ ∀ o, (k o).Avoids bad := by
  rw [Sem.Avoids]

/-- A world update avoids `bad` when its continuation does from every world. -/
theorem Sem.avoids_update {f : ε.W → ε.W × Sem ε E α} :
    (Sem.update f).Avoids bad ↔ ∀ w, (f w).2.Avoids bad := by
  rw [Sem.Avoids]
  exact forall_congr' fun w => by
    obtain ⟨w₁, k⟩ := f w
    rw [Sem.AvoidsAfter]

mutual
/-- Every tree avoids the empty set of faults. -/
theorem Sem.avoids_none : (t : Sem ε E α) → t.Avoids (fun _ => False)
  | .ret _ => by rw [Sem.Avoids]; trivial
  | .stop (.jump _) => by rw [Sem.Avoids]; trivial
  | .stop (.fault _) => by rw [Sem.Avoids]; exact id
  | .choose k => by rw [Sem.Avoids]; exact fun c => Sem.avoids_none (k c)
  | .vis _ k => by rw [Sem.Avoids]; exact fun o => Sem.avoids_none (k o)
  | .update f => by rw [Sem.Avoids]; exact fun w => Sem.avoidsAfter_none (f w)

/-- Every update's continuation avoids the empty set of faults. -/
theorem Sem.avoidsAfter_none : (p : ε.W × Sem ε E α) → Sem.AvoidsAfter (fun _ => False) p
  | (_, k) => by rw [Sem.AvoidsAfter]; exact Sem.avoids_none k
end

end

/-! ## Modules and runs that avoid some faults -/

section
variable {M : RunModel} (bad : Fault → Prop)

/-- A run's result avoids `bad`: it is a value, or a fault not in `bad`. -/
def Result.Avoids : Result M.interp → Prop
  | .ok _ => True
  | .fault f => ¬ bad f

/-- The rule of operation `i` avoids `bad` when it runs again, on any operands, from any
state. -/
def Inst.Avoids (i : Inst M) : Prop :=
  ∀ env (h : Typed env i.rerun.args i.rerun.ts) (st : i.St), (i.again env h st).Avoids bad

/-- The rule's tree `f`, and its tree `re.tree` from any state, avoid `bad` at any values of
`re`'s operands. -/
def Rerun.Avoids {rs : List (List Ty × Ty)} {ps : List (List Ty)} {R : Type}
    (re : Rerun M rs ps R) (f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) R) re.ts) :
    Prop :=
  (∀ env (h : Typed env re.args re.ts), (applyFn env re.ts f re.args h).Avoids bad) ∧
    ∀ env (h : Typed env re.args re.ts) st, (applyFn env re.ts re.tree re.args h st).Avoids bad

/-- A linked instruction's rule avoids `bad`, on any operands, and again from any state. -/
def LInsn.Avoids : LInsn M → Prop
  | .sem _ _ _ _ _ re f _ _ => re.Avoids bad f
  | _ => True

/-- A linked terminator's rule avoids `bad`, on any operands, and again from any state. -/
def LTerm.Avoids : LTerm M → Prop
  | .case .. => True
  | .sem _ _ _ re f _ _ => re.Avoids bad f

/-- **No rule of the module stops with a fault in `bad` itself**: every instruction and
terminator of every function and region avoids it. -/
def LModule.Avoids (m : LModule M) : Prop :=
  m.All (·.Avoids bad) (·.Avoids bad)

/-- A frame's body, rest of a block and terminator avoid `bad`. -/
structure Frame.Avoids (f : Frame M) : Prop where
  body : f.func.All (·.Avoids bad) (·.Avoids bad)
  code : ∀ i ∈ f.code, i.Avoids bad
  term : f.term.Avoids bad

/-- A waiting frame avoids `bad`, and a paused rule does when it runs again and on every
answer. -/
def Wait.Avoids : Wait M → Prop
  | .rule f p => f.Avoids bad ∧ p.inst.Avoids bad ∧ ∀ o, (p.k o).Avoids bad
  | .call f _ _ => f.Avoids bad

/-- A pending transition avoids `bad`: the frames it runs, its rule's tree, and the result of
a run that ended. -/
def Mode.Avoids (c : Core M) : Mode M → Prop
  | .exec => c.top.Avoids bad
  | .jump to => to.Avoids bad
  | .call g w => g.Avoids bad ∧ w.Avoids bad
  | .ret _ => True
  | .request i t => c.top.Avoids bad ∧ i.Avoids bad ∧ t.Avoids bad
  | .again r => c.top.Avoids bad ∧ r.inst.Avoids bad
  | .done r => r.Avoids bad

/-- **A state avoids `bad`**: its waiting frames and its pending transition do. -/
def State.Avoids (s : State M) : Prop :=
  (∀ w ∈ s.core.conts, w.Avoids bad) ∧ s.mode.Avoids bad s.core

variable {m : LModule M} {B : Ty}

/-- A step leads to a state that avoids `bad`. -/
def StepR.NextAvoids : StepR m B → Prop
  | .next _ s _ => s.Avoids bad
  | .final .. => False

/-- A step from `s` leads to a state that avoids `bad`, or ends the run with the
result, the heap and the world of `s`, which has ended. -/
def StepR.Avoids (s : State M) : StepR m B → Prop
  | .next _ s₁ _ => s₁.Avoids bad
  | .final r hp w _ => s.mode = .done r ∧ hp = s.core.heap ∧ w = s.core.world

variable {bad}

/-- A step to a state that avoids `bad` is a step that does. -/
theorem StepR.NextAvoids.avoids {s : State M} : ∀ {r : StepR m B}, r.NextAvoids bad →
    r.Avoids bad s
  | .next .., h => h

/-- Binding a value keeps a frame's code. -/
theorem Frame.Avoids.bind {f : Frame M} (h : f.Avoids bad) {v : Nat} {d : Dyn M.interp}
    (hv : v < f.func.slots) : (f.bind v d hv).Avoids bad :=
  ⟨h.body, h.code, h.term⟩

/-- The frame that runs a block of a body that avoids `bad` avoids it. -/
theorem Frame.Avoids.entry {g : LBody M} {b : LBlock M}
    (hg : g.All (·.Avoids bad) (·.Avoids bad)) (hb : b ∈ g.blocks) {env : Array (Dyn M.interp)}
    {ts : List Ty} {ds : List (Dyn M.interp)} {xs : Args M.interp ts} {hle : g.slots ≤ env.size}
    {hp : ParamsFit g b} :
    (Frame.entry g b env ds xs hle hp).Avoids bad :=
  ⟨hg, (hg b hb).1, (hg b hb).2⟩

/-- A function's frame, in a module that avoids `bad`, avoids it. -/
theorem Frame.Avoids.callFrame (hN : m.Avoids bad) (hwf : WF m) {i : Nat}
    {hi : i < m.funcs.size} {ds : List (Dyn M.interp)} {ts : List Ty} (xs : Args M.interp ts) :
    (Exec.callFrame hwf i hi ds xs).Avoids bad := by
  unfold Exec.callFrame
  exact Frame.Avoids.entry (hN.1 _ (Array.getElem_mem hi)) (Array.getElem_mem _)

/-- A region's frame, in a module that avoids `bad`, avoids it. -/
theorem Frame.Avoids.regionStart (hN : m.Avoids bad) {f : Frame M} {k : Nat}
    {hk : k < m.regions.size} {hb : 0 < (m.regions[k]'hk).blocks.size}
    {hs : (m.regions[k]'hk).slots ≤ f.func.slots}
    {hp : ParamsFit (m.regions[k]'hk) ((m.regions[k]'hk).blocks[0]'hb)} {ts : List Ty}
    (args : Args M.interp ts) : (Exec.regionStart m f k hk hb hs hp args).Avoids bad := by
  unfold Exec.regionStart
  exact Frame.Avoids.entry (hN.2 _ (Array.getElem_mem hk)) (Array.getElem_mem hb)

/-- Where a transfer leads avoids `bad`: a frame that does, or out of the body. -/
def Next.Avoids (bad : Fault → Prop) : Next M → Prop
  | .frame g => g.Avoids bad
  | .leave _ => True

/-- A transfer from a frame that avoids `bad` leads to a frame that does. -/
theorem Frame.Avoids.take {f : Frame M} (hf : f.Avoids bad) :
    ∀ (s : LSite) {ts : List Ty} (xs : Args M.interp ts) (h : CanTake f s ts),
      (take f s xs h).Avoids bad
  | ⟨.block i, _⟩, _, _, h => by
    have hb := Array.getElem_mem (xs := f.func.blocks) h.2.1
    exact ⟨hf.body, (hf.body _ hb).1, (hf.body _ hb).2⟩
  | ⟨.exit, _⟩, _, _, _ => trivial

/-- An exit of a frame that avoids `bad` leads to a frame that does. -/
theorem Frame.Avoids.exitTo {f : Frame M} (hf : f.Avoids bad) :
    ∀ {ps : List (List Ty)} (ss : List LSite) (e : Exit M.interp ps) (h : SitesOK f ss ps),
      (Exec.exitTo f ss e h).Avoids bad
  | _, s :: _, .here xs, _ => hf.take s xs _
  | _, _ :: ss, .there e, _ => hf.exitTo ss e _
  | _, [], .here _, h => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)
  | _, [], .there _, h => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)

end

/-! ## A step avoids the faults its rules avoid -/

section
variable {M : RunModel} {A : Accounts M} {m : LModule M} (hwf : WF m) (oracle : Nat → Nat)
  {B : Ty} {bad : Fault → Prop} (hR : m.RulesOK A) (hN : m.Avoids bad)
  (hbad : ∀ n, ¬ bad (.badCall n)) {P : Nat → Prop} {heap₀ : Heap M}
  (hP : ∀ l, P l → l < heap₀.cells.size)

/-- Stopping with a fault not in `bad` avoids `bad`. -/
theorem faultStep_avoids {c : Core M} (hcs : ∀ w ∈ c.conts, w.Avoids bad) {f : Fault}
    (hf : ¬ bad f) (drawn : Nat) : (faultStep (m := m) (B := B) c f drawn).NextAvoids bad :=
  ⟨hcs, hf⟩

/-- A transfer from a frame that avoids `bad` avoids it. -/
theorem transfer_avoids {c : Core M} {n : Next M} (hn : NextOK m c.top n)
    (hK : ContsOK m B c.top.func.ret c.conts) {drawn : Nat} {ev : Event}
    (hcs : ∀ w ∈ c.conts, w.Avoids bad) (hN₁ : n.Avoids bad) :
    (transfer c n hn hK drawn ev).NextAvoids bad := by
  cases n with
  | frame g => exact ⟨hcs, hN₁⟩
  | leave v => exact ⟨hcs, trivial⟩

include hN hbad in
/-- **A rule's tree, continued**: a tree that avoids `bad`, of a rule that does when it runs
again, in a frame that does, leads to a state that avoids `bad`. -/
theorem settle_avoids {c : Core M} {i : Inst M} (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) {drawn : Nat} {ev : Event}
    (hcs : ∀ w ∈ c.conts, w.Avoids bad) (hf : c.top.Avoids bad) (hag : i.Avoids bad)
    (t : i.Tree) (ht : t.Avoids bad) : (settle hwf c i hi hK drawn ev t).NextAvoids bad := by
  cases t with
  | ret a =>
    obtain ⟨op, pc, dst, ret, ps, rs, regs, succs, rerun⟩ := i
    cases ret with
    | none => exact nomatch a
    | some r =>
      simp only [settle]
      exact ⟨hcs, hf.bind (hi.dst_lt a)⟩
  | stop s =>
    cases s with
    | jump o =>
      cases o with
      | exit e =>
        simp only [settle]
        exact transfer_avoids _ _ hcs (hf.exitTo i.succs e hi.sitesOK)
      | again st =>
        simp only [settle]
        exact ⟨hcs, hf, hag⟩
    | fault f =>
      simp only [settle]
      exact faultStep_avoids hcs (Sem.avoids_fault.mp ht) drawn
  | choose k =>
    simp only [settle]
    exact ⟨hcs, hf, hag, ht⟩
  | update f =>
    simp only [settle]
    exact ⟨hcs, hf, hag, ht⟩
  | vis q k =>
    have hk := Sem.avoids_vis.mp ht
    cases q with
    | region j args =>
      simp only [settle, visitRegion]
      exact ⟨hcs, Frame.Avoids.regionStart hN args, hf, hag, hk⟩
    | call sig idx captured args =>
      simp only [settle, visitCall]
      by_cases hc : ∃ caps, m.CallOK c.heap idx captured sig.1 sig.2 caps
      · obtain ⟨caps, hco⟩ := hc
        rw [LModule.callee_pos hco]
        exact ⟨hcs, Frame.Avoids.callFrame hN hwf _, hf, hag, hk⟩
      · rw [LModule.callee_neg (fun caps h => hc ⟨caps, h⟩)]
        exact faultStep_avoids hcs (hbad _) drawn
    | new _ _ =>
      simp only [settle]
      exact ⟨hcs, hf, hag, ht⟩
    | get _ _ =>
      simp only [settle]
      exact ⟨hcs, hf, hag, ht⟩
    | set _ _ _ =>
      simp only [settle]
      exact ⟨hcs, hf, hag, ht⟩
    | modify _ _ _ =>
      simp only [settle]
      exact ⟨hcs, hf, hag, ht⟩
    | bind _ _ _ _ _ =>
      simp only [settle]
      exact ⟨hcs, hf, hag, ht⟩

include hN hbad in
/-- **Answering a rule's request**: a tree that respects the typing of the run invariant asks
only for cells valid in it, so every cell check passes, and the rule continues with a tree that
avoids `bad`. -/
theorem serve_avoids {T : Typing} {c : Core M} {i : Inst M} (t : i.Tree)
    (h : InstOK m c.top i ∧ ContsOK m B c.top.func.ret c.conts) {drawn : Nat}
    (hC : A.CoreInv P heap₀ T c) (htk : A.TreeOK (A.StOK i.rerun.key) T i.ret t)
    (hcs : ∀ w ∈ c.conts, w.Avoids bad) (hf : c.top.Avoids bad) (hag : i.Avoids bad)
    (ht : t.Avoids bad) : (serve hwf oracle c i t h drawn).NextAvoids bad := by
  cases t with
  | choose k =>
    simp only [serve]
    exact settle_avoids hwf hN hbad _ _ hcs hf hag _ (Sem.avoids_choose.mp ht _)
  | update f =>
    obtain ⟨top, conts, heap, w⟩ := c
    simp only [serve]
    exact settle_avoids hwf hN hbad (c := ⟨top, conts, heap, (f w).1⟩) _ _ hcs hf hag _
      (Sem.avoids_update.mp ht w)
  | ret a =>
    simp only [serve]
    exact settle_avoids hwf hN hbad _ _ hcs hf hag _ ht
  | stop s =>
    simp only [serve]
    exact settle_avoids hwf hN hbad _ _ hcs hf hag _ ht
  | vis q k =>
    have hsat := A.treeOK_vis.mp htk
    have hk := Sem.avoids_vis.mp ht
    cases q with
    | region j args =>
      simp only [serve]
      exact settle_avoids hwf hN hbad _ _ hcs hf hag _ ht
    | call sig idx captured args =>
      simp only [serve]
      exact settle_avoids hwf hN hbad _ _ hcs hf hag _ ht
    | new ty v =>
      simp only [serve]
      exact settle_avoids hwf hN hbad (c := { c with heap := c.heap.push ⟨ty, v⟩ }) _ _ hcs hf
        hag _ (hk _)
    | get ty l =>
      obtain ⟨hl, htl, -⟩ := hC.heap.cellOK hsat.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      simp only [serve]
      rw [Heap.cell_pos hh]
      exact settle_avoids hwf hN hbad _ _ hcs hf hag _ (hk _)
    | set ty l v =>
      obtain ⟨hl, htl, -⟩ := hC.heap.cellOK hsat.1.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      simp only [serve]
      rw [Heap.cell_pos hh]
      exact settle_avoids hwf hN hbad (c := { c with heap := c.heap.set l ⟨ty, v⟩ hh.lt }) _ _
        hcs hf hag _ (hk _)
    | modify ty l g =>
      obtain ⟨hl, htl, -⟩ := hC.heap.cellOK hsat.1.1
      have hh : c.heap.Holds l ty := ⟨hl, htl⟩
      simp only [serve]
      rw [Heap.cell_pos hh, Heap.modifyAt_eq]
      exact settle_avoids hwf hN hbad (c := { c with heap := c.heap.modify l ty g }) _ _ hcs hf
        hag _ (hk _)
    | bind ty v sig idx captured =>
      simp only [serve]
      by_cases hc : ∃ caps, m.CallOK c.heap idx captured (ty :: sig.1) sig.2 caps
      · obtain ⟨caps, hco⟩ := hc
        rw [LModule.callee_pos hco]
        exact settle_avoids hwf hN hbad
          (c := { c with heap := c.heap.capture (caps ++ [(⟨ty, v⟩ : Dyn M.interp)]) }) _ _ hcs
          hf hag _ (hk _)
      · rw [LModule.callee_neg (fun caps h => hc ⟨caps, h⟩)]
        exact faultStep_avoids hcs (hbad _) drawn

include hN hbad in
/-- **Running an instruction or a terminator** of a frame of the run: a `refGet` or `refSet`
finds a cell of its tag, since the ref is valid in the typing of the run invariant, and the step
leads to a state that avoids `bad`. -/
theorem exec_avoids {T : Typing} {c : Core M} (h : CoreOK m B c) {drawn : Nat}
    (hC : A.CoreInv P heap₀ T c) (hfi : A.FrameInv T c.top) (hcs : ∀ w ∈ c.conts, w.Avoids bad)
    (hf : c.top.Avoids bad) : (exec hwf c h drawn).NextAvoids bad := by
  obtain ⟨⟨func, code, term, env, blk, pc, fits⟩, conts, heap, world⟩ := c
  cases code with
  | nil =>
    cases term with
    | case ts ps f args succs =>
      simp only [exec, execCode, execTerm]
      exact transfer_avoids _ _ hcs (hf.exitTo succs _ _)
    | sem op rs ps re f regs succs =>
      simp only [exec, execCode, execTerm]
      exact settle_avoids hwf hN hbad _ _ hcs hf (by exact hf.term.2) _ (by exact hf.term.1 _ _)
  | cons i code =>
    have hi : i.Avoids bad := hf.code i List.mem_cons_self
    have hcode : ∀ i₁ ∈ code, i₁.Avoids bad := fun i₁ hm => hf.code i₁ (List.mem_cons_of_mem _ hm)
    cases i with
    | const dst v =>
      simp only [exec, execCode, Core.next]
      exact ⟨hcs, hf.body, hcode, hf.term⟩
    | pure dst ts r f args =>
      simp only [exec, execCode, Core.next]
      exact ⟨hcs, hf.body, hcode, hf.term⟩
    | sem op dst rs r ps re f regs succs =>
      simp only [exec, execCode]
      refine settle_avoids hwf hN hbad _ _ ?_ ?_ ?_ _ ?_
      · exact hcs
      · exact ⟨hf.body, hcode, hf.term⟩
      · exact hi.2
      · exact hi.1 _ _
    | refNew dst t v =>
      simp only [exec, execCode, Core.refNew, Core.next]
      exact ⟨hcs, hf.body, hcode, hf.term⟩
    | refGet dst t x =>
      simp only [exec, execCode, Core.cellLoc]
      have hl := Accounts.valid_of_ref (Accounts.EnvOK.getT hfi.env (h.ready rfl))
      obtain ⟨hl₁, ht₁, -⟩ := hC.heap.cellOK hl
      rw [Heap.cell_pos ⟨hl₁, ht₁⟩]
      simp only [Core.refGet, Core.next]
      exact ⟨hcs, hf.body, hcode, hf.term⟩
    | refSet dst t x v =>
      simp only [exec, execCode, Core.cellLoc]
      have hl := Accounts.valid_of_ref (Accounts.EnvOK.getT hfi.env (h.ready rfl).1)
      obtain ⟨hl₁, ht₁, -⟩ := hC.heap.cellOK hl
      rw [Heap.cell_pos ⟨hl₁, ht₁⟩]
      simp only [Core.refSet, Core.next]
      exact ⟨hcs, hf.body, hcode, hf.term⟩
    | callCode dst ts r fn args =>
      simp only [exec, execCode]
      have hr : HasTy env fn (Ty.fn ts r) ∧ AllBound env args := h.ready rfl
      by_cases hc : ∃ caps, m.CallOK heap (M.fnOf (getT env fn (Ty.fn ts r) hr.1)).idx
          (M.fnOf (getT env fn (Ty.fn ts r) hr.1)).captured ts r caps
      · obtain ⟨caps, hco⟩ := hc
        rw [LModule.callee_pos hco]
        exact ⟨hcs, Frame.Avoids.callFrame hN hwf _, hf.body, hcode, hf.term⟩
      · rw [LModule.callee_neg (fun caps h => hc ⟨caps, h⟩)]
        exact faultStep_avoids hcs (hbad _) drawn

include hN hbad in
/-- **Leaving a body**: to the end of the run, a paused rule that resumes with a tree that avoids
`bad`, or a caller. -/
theorem leave_avoids {c : Core M} {v : Dyn M.interp} (h : LeftOK m B c v) {drawn : Nat}
    (hcs : ∀ w ∈ c.conts, w.Avoids bad) : (leave hwf c v h drawn).NextAvoids bad := by
  obtain ⟨top, conts, heap, world⟩ := c
  cases conts with
  | nil =>
    simp only [leave, leaveTo]
    exact ⟨fun _ hw => (nomatch hw), trivial⟩
  | cons w cs =>
    have hw := hcs w List.mem_cons_self
    have htl : ∀ w₁ ∈ cs, w₁.Avoids bad := fun w₁ hm => hcs w₁ (List.mem_cons_of_mem _ hm)
    cases w with
    | rule f p =>
      simp only [leave, leaveTo]
      exact settle_avoids hwf hN hbad _ _ htl hw.1 hw.2.1 _ (hw.2.2 _)
    | call f dst r =>
      simp only [leave, leaveTo]
      exact ⟨htl, hw.bind (LeftOK.call_dst h rfl)⟩

include hN hbad in
/-- **A step avoids the faults its rules avoid**: from a state where the run invariant
holds and that avoids `bad`, a step of a module whose rules are certified and avoid `bad`, and
with `bad` holding no bad call, leads to a state that avoids `bad`, or ends the run with
the state's result, heap and world. -/
theorem step_avoids {s : State M} (h : StateOK m B s) {T : Typing} (hs : A.Inv P heap₀ T s)
    (ha : s.Avoids bad) : (step hwf oracle s h).Avoids bad s := by
  obtain ⟨⟨top, conts, heap, world⟩, mode, drawn, ⟨⟩⟩ := s
  obtain ⟨hC, hm⟩ := hs
  obtain ⟨hcs, hma⟩ := ha
  cases mode with
  | exec => exact (exec_avoids hwf hN hbad h hC hm hcs hma).avoids
  | jump to =>
    simp only [step]
    exact ⟨hcs, hma⟩
  | call callee w =>
    simp only [step]
    refine ⟨fun w₁ hw₁ => ?_, hma.1⟩
    rcases List.mem_cons.mp hw₁ with rfl | hw₁
    · exact hma.2
    · exact hcs w₁ hw₁
  | ret v => exact (leave_avoids hwf hN hbad h hcs).avoids
  | request i t =>
    exact (serve_avoids hwf oracle hN hbad t h hC hm.2.2 hcs hma.1 hma.2.1 hma.2.2).avoids
  | again r =>
    simp only [step, Inst.again]
    exact (settle_avoids hwf hN hbad _ _ hcs hma.1 hma.2 _ (hma.2 _ _ _)).avoids
  | done r =>
    simp only [step]
    exact ⟨rfl, rfl, rfl⟩

end

/-! ## Heap safety over runs -/

/-- A snapshot that a typing of its heap types, with the world's refs valid in it: one a run can
start from. -/
def Snapshot.OK {M : RunModel} (A : Accounts M) (snap : Snapshot M) : Prop :=
  ∃ T : Typing, A.HeapOK T snap.heap ∧ T.AllValid (A.world snap.world)

/-- A fault at a cell, `Fault.badCell`. -/
def Fault.IsBadCell (f : Fault) : Prop := ∃ l, f = .badCell l

/-- **The step from `s` accesses location `l` at tag `t`**: a `refGet` or a `refSet` at the head
of the top frame's code, through a ref to `l` that the store holds, or a rule's request to read,
write or update the cell at `l`. -/
def State.Accesses {M : RunModel} (s : State M) (l : Nat) (t : Ty) : Prop :=
  match s.mode with
  | .exec => match s.core.top.code with
    | .refGet _ t₁ x :: _ =>
      t₁ = t ∧ ∃ h : HasTy s.core.top.env x (Ty.ref t₁), M.locOf (getT s.core.top.env x _ h) = l
    | .refSet _ t₁ x _ :: _ =>
      t₁ = t ∧ ∃ h : HasTy s.core.top.env x (Ty.ref t₁), M.locOf (getT s.core.top.env x _ h) = l
    | _ => False
  | .request _ (.vis (.get t₁ l₁) _) => t₁ = t ∧ l₁ = l
  | .request _ (.vis (.set t₁ l₁ _) _) => t₁ = t ∧ l₁ = l
  | .request _ (.vis (.modify t₁ l₁ _) _) => t₁ = t ∧ l₁ = l
  | _ => False

section
variable {M : RunModel} {A : Accounts M} {m : LModule M} {hwf : WF m}
  {B : Ty} {P : Nat → Prop} {heap₀ : Heap M}

/-- **The invariant and avoidance hold at every configuration of every run**, and a run that ends
ends with a result that avoids `bad`, at a snapshot that a typing types.  Any set `P` of kept cells
works, and callers that need none take `P := fun _ => False`. -/
theorem avoids_always {bad : Fault → Prop} (hR : m.RulesOK A) (hN : m.Avoids bad)
    (hbad : ∀ n, ¬ bad (.badCall n)) (hP : ∀ l, P l → l < heap₀.cells.size) {s : State M}
    {h : StateOK m B s} {T : Typing} (hs : A.Inv P heap₀ T s) (ha : s.Avoids bad)
    (r : RunFrom hwf s h) (n : Nat) :
    (r.cfg n).Sat
      (fun c => (∃ T₁, T.Extends T₁ ∧ A.Inv P heap₀ T₁ c.1) ∧ c.1.Avoids bad)
      (fun f => f.result.Avoids bad ∧ f.snapshot.OK A) := by
  refine always (P := fun s => (∃ T₁, T.Extends T₁ ∧ A.Inv P heap₀ T₁ s) ∧ s.Avoids bad) ?_ r
    ⟨⟨T, .refl _, hs⟩, ha⟩ n
  rintro o s₁ h₁ ⟨⟨T₁, he, hi⟩, ha₁⟩
  have hst := step_inv hwf o hR hP h₁ hi
  have hsa := step_avoids hwf o hN hbad h₁ hi ha₁
  revert hst hsa
  cases step hwf o s₁ h₁ with
  | next e s₂ h₂ =>
    rintro ⟨T₂, he₂, hi₂⟩ ha₂
    exact ⟨⟨T₂, he.trans he₂, hi₂⟩, ha₂⟩
  | final r hp w d =>
    rintro - ⟨hm, rfl, rfl⟩
    have hd := ha₁.2
    rw [hm] at hd
    exact ⟨hd, T₁, hi.1.heap, hi.1.world⟩

/-- **Heap safety.**  A run of a module whose rules are certified and stop with no bad cell
themselves, from a state where the run invariant holds and that avoids bad cells, never faults with
`Fault.badCell`: no configuration of any run has ended with one, and no run ends with one.  The
conclusion does not mention `P` or `heap₀`, so any `P` works: a caller that keeps no cells may
take `P := fun _ => False`, with `heap₀` the heap it starts from. -/
theorem never_badCell (hR : m.RulesOK A) (hN : m.Avoids Fault.IsBadCell)
    (hP : ∀ l, P l → l < heap₀.cells.size) {s : State M} {h : StateOK m B s} {T : Typing}
    (hs : A.Inv P heap₀ T s) (ha : s.Avoids Fault.IsBadCell) (r : RunFrom hwf s h) (n : Nat) :
    (r.cfg n).Sat (fun c => ∀ l, c.1.mode ≠ .done (.fault (.badCell l)))
      (fun f => ∀ l, f.result ≠ .fault (.badCell l)) := by
  have h₁ := avoids_always hR hN (fun _ ⟨_, e⟩ => nomatch e) hP hs ha r n
  revert h₁
  cases r.cfg n with
  | running c =>
    rintro ⟨-, -, hd⟩ l hl
    rw [hl] at hd
    exact hd ⟨l, rfl⟩
  | ended f =>
    rintro ⟨hd, -⟩ l hl
    rw [hl] at hd
    exact hd ⟨l, rfl⟩

/-- **Every access is valid.**  At every configuration of every run of a module whose rules are
certified, from a state where the run invariant holds, the cell that the next step accesses holds a
value of the access's tag: a `refGet` or a `refSet` at the head of the top frame's code reads it
through a ref the frame holds, and a rule's request to read, write or update it names it.  The
conclusion does not mention `P` or `heap₀`, so any `P` works: a caller that keeps no cells may
take `P := fun _ => False`, with `heap₀` the heap it starts from. -/
theorem access_ok (hR : m.RulesOK A) (hP : ∀ l, P l → l < heap₀.cells.size) {s : State M}
    {h : StateOK m B s} {T : Typing} (hs : A.Inv P heap₀ T s) (r : RunFrom hwf s h) (n : Nat) :
    (r.cfg n).Sat (fun c => ∀ l t, c.1.Accesses l t → c.1.core.heap.Holds l t)
      (fun _ => True) := by
  have h₁ := inv_always hR hP hs r n
  revert h₁
  cases r.cfg n with
  | ended f => exact fun _ => trivial
  | running c =>
    obtain ⟨⟨⟨⟨func, code, term, env, blk, pc, fits⟩, conts, heap, world⟩, mode, drawn, ⟨⟩⟩, -⟩ := c
    rintro ⟨T₁, -, hC, hm⟩ l t hacc
    cases mode with
    | exec =>
      cases code with
      | nil => exact (hacc : False).elim
      | cons i code =>
        cases i with
        | refGet dst t₁ x =>
          obtain ⟨rfl, hx, rfl⟩ := hacc
          obtain ⟨hl, ht, -⟩ := hC.heap.cellOK (Accounts.valid_of_ref (hm.env.getT hx))
          exact ⟨hl, ht⟩
        | refSet dst t₁ x v =>
          obtain ⟨rfl, hx, rfl⟩ := hacc
          obtain ⟨hl, ht, -⟩ := hC.heap.cellOK (Accounts.valid_of_ref (hm.env.getT hx))
          exact ⟨hl, ht⟩
        | const _ _ => exact (hacc : False).elim
        | pure _ _ _ _ _ => exact (hacc : False).elim
        | sem _ _ _ _ _ _ _ _ _ => exact (hacc : False).elim
        | refNew _ _ _ => exact (hacc : False).elim
        | callCode _ _ _ _ _ => exact (hacc : False).elim
    | request i tr =>
      cases tr with
      | vis q k =>
        have hsat := A.treeOK_vis.mp hm.2.2
        cases q with
        | get t₁ l₁ =>
          obtain ⟨rfl, rfl⟩ := hacc
          obtain ⟨hl, ht, -⟩ := hC.heap.cellOK hsat.1
          exact ⟨hl, ht⟩
        | set t₁ l₁ v =>
          obtain ⟨rfl, rfl⟩ := hacc
          obtain ⟨hl, ht, -⟩ := hC.heap.cellOK hsat.1.1
          exact ⟨hl, ht⟩
        | modify t₁ l₁ g =>
          obtain ⟨rfl, rfl⟩ := hacc
          obtain ⟨hl, ht, -⟩ := hC.heap.cellOK hsat.1.1
          exact ⟨hl, ht⟩
        | region _ _ => exact (hacc : False).elim
        | call _ _ _ _ => exact (hacc : False).elim
        | new _ _ => exact (hacc : False).elim
        | bind _ _ _ _ _ => exact (hacc : False).elim
      | ret _ => exact (hacc : False).elim
      | stop _ => exact (hacc : False).elim
      | choose _ => exact (hacc : False).elim
      | update _ => exact (hacc : False).elim
    | jump _ => exact (hacc : False).elim
    | call _ _ => exact (hacc : False).elim
    | ret _ => exact (hacc : False).elim
    | again _ => exact (hacc : False).elim
    | done _ => exact (hacc : False).elim

end

/-! ## Starts -/

section
variable {M : RunModel} {A : Accounts M} {m : LModule M} {hwf : WF m}
  {B : Ty}

/-- Every instruction avoids the empty set of faults. -/
theorem LInsn.avoids_none : ∀ i : LInsn M, i.Avoids (fun _ => False)
  | .sem .. => ⟨fun _ _ => Sem.avoids_none _, fun _ _ _ => Sem.avoids_none _⟩
  | .const .. | .pure .. | .refNew .. | .refGet .. | .refSet .. | .callCode .. => trivial

/-- Every terminator avoids the empty set of faults. -/
theorem LTerm.avoids_none : ∀ t : LTerm M, t.Avoids (fun _ => False)
  | .sem .. => ⟨fun _ _ => Sem.avoids_none _, fun _ _ _ => Sem.avoids_none _⟩
  | .case .. => trivial

/-- Every frame avoids the empty set of faults. -/
theorem Frame.avoids_none (f : Frame M) : f.Avoids (fun _ => False) :=
  ⟨fun _ _ => ⟨fun i _ => i.avoids_none, LTerm.avoids_none _⟩, fun i _ => i.avoids_none,
    LTerm.avoids_none _⟩

/-- Every module avoids the empty set of faults. -/
theorem LModule.avoids_none (m : LModule M) : m.Avoids (fun _ => False) :=
  ⟨fun _ _ _ _ => ⟨fun i _ => i.avoids_none, LTerm.avoids_none _⟩,
    fun _ _ _ _ => ⟨fun i _ => i.avoids_none, LTerm.avoids_none _⟩⟩

/-- Every state avoids the empty set of faults. -/
theorem State.avoids_none (s : State M) : s.Avoids (fun _ => False) := by
  have hw : ∀ w : Wait M, w.Avoids (fun _ => False) := fun
    | .rule f _ => ⟨f.avoids_none, fun _ _ _ => Sem.avoids_none _, fun _ => Sem.avoids_none _⟩
    | .call f _ _ => f.avoids_none
  refine ⟨fun w _ => hw w, ?_⟩
  cases hm : s.mode with
  | exec => exact s.core.top.avoids_none
  | jump to => exact to.avoids_none
  | call g w => exact ⟨g.avoids_none, hw w⟩
  | ret v => trivial
  | request i t => exact ⟨s.core.top.avoids_none, fun _ _ _ => Sem.avoids_none _, Sem.avoids_none _⟩
  | again r => exact ⟨s.core.top.avoids_none, fun _ _ _ => Sem.avoids_none _⟩
  | done r =>
    cases r with
    | ok v => trivial
    | fault f => exact id

/-- **Where a run ends, a typing types the heap**, with the world's refs valid in it: a run of a
module whose rules are certified, from a state where the run invariant holds, ends at a
snapshot another run can start from. -/
theorem ended_ok {P : Nat → Prop} {heap₀ : Heap M} (hR : m.RulesOK A)
    (hP : ∀ l, P l → l < heap₀.cells.size) {s : State M} {h : StateOK m B s} {T : Typing}
    (hs : A.Inv P heap₀ T s) (r : RunFrom hwf s h) {n : Nat} {f : Final M}
    (he : r.cfg n = .ended f) : f.snapshot.OK A := by
  have h₁ := avoids_always hR m.avoids_none (fun _ => id) hP hs s.avoids_none r n
  rw [he] at h₁
  exact h₁.2

/-- **The engine's start**: an empty heap, and the initial world, which holds no ref. -/
theorem Snapshot.ok_initial (hw : A.world M.w0 = []) : (Snapshot.initial (M := M)).OK A :=
  ⟨{}, ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩, by
    show Typing.AllValid {} (A.world M.w0)
    rw [hw]
    exact Typing.allValid_nil _⟩

/-- A value that holds no ref is valid in every typing. -/
theorem Accounts.dynOK_of_nil {S : Typing} {d : Dyn M.interp} (h : A.acct d.1 d.2 = []) :
    A.DynOK S d := by
  unfold Accounts.DynOK Accounts.ValOK
  rw [h]
  exact Typing.allValid_nil _

/-- **Well-tagged starts.**  From a snapshot that a typing of its heap types, the refs a function
starts with, on arguments that hold no ref, are well tagged. -/
theorem Snapshot.OK.wellTagged {snap : Snapshot M} (hs : snap.OK A) {args : List (Dyn M.interp)}
    (hargs : ∀ d ∈ args, A.acct d.1 d.2 = []) :
    WellTagged A snap.heap (startRoots A args snap.world) := by
  obtain ⟨T, hH, hw⟩ := hs
  refine hH.wellTagged fun p hp => ?_
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨d, hd, hp⟩ := List.mem_flatMap.mp hp
    rw [hargs d hd] at hp
    exact absurd hp List.not_mem_nil
  · exact hw p hp

/-- A function's start, in a module that avoids `bad`, avoids it. -/
theorem startCore_avoids {bad : Fault → Prop} (hN : m.Avoids bad) {i : Nat}
    {args : List (Dyn M.interp)} {snap : Snapshot M} {c : Core M} {hc : CoreOK m B c}
    (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩) :
    (⟨c, .exec, 0, ()⟩ : State M).Avoids bad := by
  obtain ⟨fn, b, hf, hb, rfl⟩ := startCore_entry hst
  exact ⟨fun _ hm => absurd hm List.not_mem_nil,
    Frame.Avoids.entry (hle := fresh_fits fn) (hp := hwf.fits_of_getElem? hf hb)
      (hN.1 _ (Array.mem_of_getElem? hf)) (Array.mem_of_getElem? hb)⟩

/-- **Heap safety from a function's start.**  A run of a function of a module whose rules are
certified and stop with no bad cell themselves, from a snapshot that a typing of its heap types,
on arguments that hold no ref, never faults with `Fault.badCell`.  The snapshot may be the
engine's start (`Snapshot.ok_initial`) or where another run ended (`ended_ok`). -/
theorem never_badCell_startCore (hR : m.RulesOK A) (hN : m.Avoids Fault.IsBadCell) {i : Nat}
    {args : List (Dyn M.interp)} {snap : Snapshot M} {c : Core M} {hc : CoreOK m B c}
    (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩) (hs : snap.OK A)
    (hargs : ∀ d ∈ args, A.acct d.1 d.2 = []) (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc) (n : Nat) :
    (r.cfg n).Sat
      (fun c => ∀ l, c.1.mode ≠ .done (.fault (.badCell l)))
      (fun f => ∀ l, f.result ≠ .fault (.badCell l)) :=
  let ⟨_, hH, hw⟩ := hs
  never_badCell (P := fun _ => False) hR hN (fun _ h => h.elim)
    (inv_startCore_of hR hst hH (fun _ h => h.elim) hw fun d hd =>
      Accounts.dynOK_of_nil (hargs d hd))
    (startCore_avoids hN hst) r n

/-- **Heap safety from a state that `start` makes**, under `never_badCell_startCore`'s
hypotheses. -/
theorem never_badCell_start (hR : m.RulesOK A) (hN : m.Avoids Fault.IsBadCell) {i : Nat}
    {args : List (Dyn M.interp)} {snap : Snapshot M} {s : State M} {h : StateOK m B s}
    (hst : start hwf i args snap = .ok ⟨B, s, h⟩) (hs : snap.OK A)
    (hargs : ∀ d ∈ args, A.acct d.1 d.2 = []) (r : RunFrom hwf s h) (n : Nat) :
    (r.cfg n).Sat (fun c => ∀ l, c.1.mode ≠ .done (.fault (.badCell l)))
      (fun f => ∀ l, f.result ≠ .fault (.badCell l)) := by
  unfold start at hst
  cases hc : startCore hwf i args snap with
  | error e =>
    rw [hc] at hst
    exact nomatch hst
  | ok p =>
    obtain ⟨B₁, c, hc₁⟩ := p
    rw [hc] at hst
    cases hst
    exact never_badCell_startCore hR hN hc hs hargs r n

/-- **The frame theorem from a function's start**, from a snapshot that a typing of its heap
types, on arguments that hold no ref: the refs it starts with are then well tagged. -/
theorem frame_startCore_ok {P : Nat → Prop} (hR : m.RulesOK A) {i : Nat}
    {args : List (Dyn M.interp)} {snap : Snapshot M} {c : Core M} {hc : CoreOK m B c}
    (hst : startCore hwf i args snap = .ok ⟨B, c, hc⟩) (hs : snap.OK A)
    (hargs : ∀ d ∈ args, A.acct d.1 d.2 = []) (hP : ∀ l, P l → l < snap.heap.cells.size)
    (hu : ∀ l, P l → ¬ ReachesCell A snap.heap (startRoots A args snap.world) l)
    (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc) (n : Nat) :
    (r.cfg n).Sat (fun c => Kept P snap.heap c.1.core.heap)
      (fun f => Kept P snap.heap f.snapshot.heap) :=
  frame_startCore hR hst (hs.wellTagged hargs) hP hu r n

end

end

end Strata.Dyn.Exec
