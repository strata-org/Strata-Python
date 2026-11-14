/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.CasesSound.Edge

set_option autoImplicit false

/-!
# The step diagram of a case lowering

`step_match`: from states that correspond, a step of the source is matched by a step of the
target to a state that reaches a corresponding one silently, and a source that has ended by a
target that has ended alike (`Exec.Diagram`, with no measure and no wrong result).

An instruction or terminator that stays runs in lockstep, on the same operands, heap and world
(`exec_lock`, `settle_lock`, `serve_lock`, `leave_lock`); its edges are lowered edges
(`exitTo_rel`).  A lowered case is one source step, and the target's chain reaches where it
leads (`chain_silent`).  The cases of a rule's tree and of the machine's checks of a cell and
of a call are those of the eliminators of `Exec/SameSigs.lean`: the target's operation is the
source's with another position and lowered edges, so both run one tree.
-/

namespace Strata.Dyn.CasesSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

section
variable {bound : Nat → Nat}

/-- A slot of the smaller store holds the same value in the larger. -/
private theorem EnvRel.getD {env env₁ : Array (Dyn M.interp)} (h : EnvRel env env₁) {v : Nat}
    (hv : Bound env v) (hv₁ : Bound env₁ v) : Exec.getD env₁ v hv₁ = Exec.getD env v hv := by
  have he := h v hv
  rw [Array.getElem?_eq_getElem hv, Array.getElem?_eq_getElem hv₁] at he
  exact Option.some.inj he

/-- A slot of the smaller store holds the same value, at its tag, in the larger. -/
private theorem EnvRel.getT {env env₁ : Array (Dyn M.interp)} (h : EnvRel env env₁) {v : Nat}
    {t : Ty} (hv : HasTy env v t) (hv₁ : HasTy env₁ v t) :
    Exec.getT env₁ v t hv₁ = Exec.getT env v t hv :=
  getT_congr hv hv₁ (h v hv.1)

/-- A fresh store holds what a smaller fresh store holds. -/
theorem envRel_freshStore {k k₁ : Nat} (h : k ≤ k₁) :
    EnvRel (freshStore M k) (freshStore M k₁) := by
  intro v hv
  simp only [freshStore, Array.size_replicate] at hv ⊢
  rw [Array.getElem?_replicate, Array.getElem?_replicate]
  simp only [hv, Nat.lt_of_lt_of_le hv h, ↓reduceIte]

/-- Cores over the same heap and world whose waiting frames correspond. -/
private theorem DataRel.of {conts conts₁ : List (Wait M)} {f f₁ : Frame M} {heap : Heap M}
    {world : M.W} (h : All₂ (WaitRel bound) conts conts₁) :
    DataRel bound ⟨f, conts, heap, world⟩ ⟨f₁, conts₁, heap, world⟩ :=
  ⟨rfl, rfl, h⟩

/-- Corresponding frames, further on in their blocks, at code that the certificate relates. -/
private theorem FrameRel.withCode {n : Nat} {β : Nat → Nat} {f f₁ : Frame M}
    (hF : FrameRel bound n β f f₁) {code code₁ : List (LInsn M)}
    (hk : CodeOK bound n β f₁.func code f.term code₁ f₁.term) :
    FrameRel bound n β { f with code := code, pc := f.pc + 1 }
      { f₁ with code := code₁, pc := f₁.pc + 1 } :=
  ⟨hF.body, hF.size, hF.env, hk⟩

/-- Corresponding frames, with equal values bound to the same slot. -/
private theorem FrameRel.bind {n : Nat} {β : Nat → Nat} {f f₁ : Frame M}
    (hF : FrameRel bound n β f f₁) (v : Nat) {d d₁ : Dyn M.interp} (hd : d₁ = d)
    (h : v < f.func.slots) (h₁ : v < f₁.func.slots) :
    FrameRel bound n β (f.bind v d h) (f₁.bind v d₁ h₁) := by
  subst hd
  have hE := hF.env.set v d₁
  rw [Array.setIfInBounds_def, Array.setIfInBounds_def,
    dite_eq_left (Nat.lt_of_lt_of_le h f.fits), dite_eq_left (Nat.lt_of_lt_of_le h₁ f₁.fits)] at hE
  exact ⟨hF.body, (Array.size_set (Nat.lt_of_lt_of_le h f.fits)).trans hF.size, hE, hF.code⟩

end

section
variable {bound : Nat → Nat} {m m₁ : LModule M} {B B₁ : Ty} (hwf : WF m) (hwf₁ : WF m₁)
  (hok : CasesOK bound m m₁) (oracle : Nat → Nat)

omit hwf in
/-- Transfers whose pending transitions the target matches silently. -/
theorem transfer_lock {s s₁ : State M} {c c₁ : Core M} {x x₁ : Next M} (hn : NextOK m c.top x)
    (hK : ContsOK m B c.top.func.ret c.conts) (hn₁ : NextOK m₁ c₁.top x₁)
    (hK₁ : ContsOK m₁ B₁ c₁.top.func.ret c₁.conts) {d : Nat} {ev ev₁ : Event}
    (hr : ∀ h₁ : StateOK m₁ B₁ ⟨c₁, modeOf x₁, d, ()⟩,
      SilentRel hwf₁ oracle (Match bound) ⟨c, modeOf x, d, ()⟩ ⟨⟨c₁, modeOf x₁, d, ()⟩, h₁⟩) :
    Diagram hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) s s₁
      (transfer c x hn hK d ev)
      (transfer c₁ x₁ hn₁ hK₁ d ev₁) := by
  obtain ⟨h, e⟩ := transfer_eq (B := B) c x hn hK d ev
  obtain ⟨h₁, e₁⟩ := transfer_eq (B := B₁) c₁ x₁ hn₁ hK₁ d ev₁
  rw [e, e₁]
  exact .inl ⟨_, rfl, hr h₁⟩

include hok in
omit hwf hwf₁ in
/-- A region starts in frames that correspond. -/
private theorem regionStart_rel {n : Nat} {β : Nat → Nat} {f f₁ : Frame M}
    (hF : FrameRel bound n β f f₁) {k : Nat} (hkn : bound k = n) (hk : k < m.regions.size)
    (hb : 0 < (m.regions[k]'hk).blocks.size) (hs : (m.regions[k]'hk).slots ≤ f.func.slots)
    (hp : ParamsFit (m.regions[k]'hk) ((m.regions[k]'hk).blocks[0]'hb))
    (hk₁ : k < m₁.regions.size) (hb₁ : 0 < (m₁.regions[k]'hk₁).blocks.size)
    (hs₁ : (m₁.regions[k]'hk₁).slots ≤ f₁.func.slots)
    (hp₁ : ParamsFit (m₁.regions[k]'hk₁) ((m₁.regions[k]'hk₁).blocks[0]'hb₁)) {ts : List Ty}
    (args : Args M.interp ts) :
    ∃ n₁ β₁, FrameRel bound n₁ β₁ (regionStart m f k hk hb hs hp args)
      (regionStart m₁ f₁ k hk₁ hb₁ hs₁ hp₁ args) := by
  obtain ⟨g₁, β₁, hg₁, hB⟩ := hok.regions k _ (Array.getElem?_eq_getElem hk)
  obtain rfl : g₁ = m₁.regions[k]'hk₁ :=
    Option.some.inj (hg₁.symm.trans (Array.getElem?_eq_getElem hk₁))
  unfold regionStart
  exact ⟨bound k, β₁, entry_rel hB (Array.getElem?_eq_getElem hb) (Array.getElem?_eq_getElem hb₁)
    hF.env (hF.size.trans hkn.symm) [] args _ _ _ _⟩

include hok in
/-- A call of a function starts frames that correspond. -/
private theorem callFrame_rel {i i₁ : Nat} (hi : i < m.funcs.size) (hi₁ : i₁ < m₁.funcs.size)
    (hii : i₁ = i) {ds ds₁ : List (Dyn M.interp)} (hds : ds₁ = ds) {ts : List Ty}
    (xs : Args M.interp ts) :
    ∃ n β, FrameRel bound n β (callFrame hwf i hi ds xs) (callFrame hwf₁ i₁ hi₁ ds₁ xs) := by
  subst hii hds
  obtain ⟨g₁, β, hg₁, hsl, hB⟩ := hok.funcs i₁ _ (Array.getElem?_eq_getElem hi)
  obtain rfl : g₁ = m₁.funcs[i₁]'hi₁ :=
    Option.some.inj (hg₁.symm.trans (Array.getElem?_eq_getElem hi₁))
  unfold callFrame
  exact ⟨_, β, entry_rel hB (Array.getElem?_eq_getElem _) (Array.getElem?_eq_getElem _)
    (envRel_freshStore hsl) Array.size_replicate ds₁ xs _ _ _ _⟩

include hok in
/-- **A rule's tree, continued alike**: the same tree, of an operation and of the target's
version of it, in corresponding frames. -/
theorem settle_lock {s s₁ : State M} {n : Nat} {β : Nat → Nat} {c c₁ : Core M} {i : Inst M}
    {pc₁ : Nat} {succs₁ : List LSite} (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts)
    (hi₁ : InstOK m₁ c₁.top (mkInst i pc₁ succs₁ i.rerun.args))
    (hK₁ : ContsOK m₁ B₁ c₁.top.func.ret c₁.conts) {d : Nat} {ev ev₁ : Event}
    (hD : DataRel bound c c₁) (hF : FrameRel bound n β c.top c₁.top)
    (hI : InstRel bound n β c₁.top.func i succs₁) (t : i.Tree) :
    Diagram hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) s s₁
      (settle hwf c i hi hK d ev t)
      (settle hwf₁ c₁ (mkInst i pc₁ succs₁ i.rerun.args) hi₁ hK₁ d ev₁ t) := by
  refine hok.sigs.settle_rec₂ (congrArg Heap.caps hD.heap)
    (P := fun _ => Diagram hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) s s₁)
    (fun a => ?_) (fun e => ?_) (fun st => ?_) (fun _ f => ?_) (fun j args k => ?_)
    (fun sig idx captured args k caps hco hco₁ => ?_) (fun t => ?_) t
  · exact Diagram.next (Match.of (hD.withTop _ _)
      (.exec (hF.bind _ rfl (hi.dst_lt a) (hi₁.dst_lt a))))
  · exact transfer_lock hwf₁ oracle _ _ _ _ fun h₁ =>
      exitTo_rel rfl hF.body hF.size hF.env hI.sites e _ _ hD h₁
  · exact Diagram.next (Match.of hD (.again st hF hI))
  · exact Diagram.next (Match.of hD (.done _))
  · obtain ⟨n₁, β₁, hFr⟩ := regionStart_rel hok hF (hI.regs _ (List.getElem_mem _))
      (hi.region_lt j) (hi.region_entry j) (hi.region_fits j).1 (hi.region_fits j).2
      (hi₁.region_lt j) (hi₁.region_entry j) (hi₁.region_fits j).1 (hi₁.region_fits j).2 args
    exact Diagram.next (Match.of hD (.call hFr (.rule hF hI)))
  · obtain ⟨n₁, β₁, hFr⟩ := callFrame_rel hwf hwf₁ hok hco.1 hco₁.1 rfl (ds := caps) rfl
      (Args.ofPayload sig.1 args)
    exact Diagram.next (Match.of hD (.call hFr (.rule hF hI)))
  · exact Diagram.next (Match.of hD (.request t hF hI))

include hok in
/-- **A rule's request, answered alike**: the same tree, of an operation and of the target's
version of it, in corresponding frames, over the same heap and world. -/
theorem serve_lock {s s₁ : State M} {n : Nat} {β : Nat → Nat} {top top₁ : Frame M}
    {conts conts₁ : List (Wait M)} {heap : Heap M} {world : M.W} {i : Inst M} {pc₁ : Nat}
    {succs₁ : List LSite} (h : InstOK m top i ∧ ContsOK m B top.func.ret conts)
    (h₁ : InstOK m₁ top₁ (mkInst i pc₁ succs₁ i.rerun.args) ∧ ContsOK m₁ B₁ top₁.func.ret conts₁)
    {d : Nat} (hst : All₂ (WaitRel bound) conts conts₁) (hF : FrameRel bound n β top top₁)
    (hI : InstRel bound n β top₁.func i succs₁) (t : i.Tree) :
    Diagram hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) s s₁
      (serve hwf oracle ⟨top, conts, heap, world⟩ i t h d)
      (serve hwf₁ oracle ⟨top₁, conts₁, heap, world⟩ (mkInst i pc₁ succs₁ i.rerun.args) t h₁
        d) := by
  cases t with
  | vis q k =>
    cases q with
    | new | region | call =>
      simp only [serve]
      exact settle_lock hwf hwf₁ hok oracle _ _ _ _ (.of hst) hF hI _
    | get | set | modify =>
      simp only [serve]
      exact Heap.cell_rec₂ Iff.rfl
        (fun _ _ => settle_lock hwf hwf₁ hok oracle _ _ _ _ (.of hst) hF hI _)
        (Diagram.next (Match.of (.of hst) (.done _)))
    | bind =>
      simp only [serve]
      exact hok.sigs.callee_rec₂ rfl rfl rfl
        (fun _ _ _ => settle_lock hwf hwf₁ hok oracle _ _ _ _ (.of hst) hF hI _)
        fun e => by rw [e]; exact Diagram.next (Match.of (.of hst) (.done _))
  | _ =>
    simp only [serve]
    exact settle_lock hwf hwf₁ hok oracle _ _ _ _ (.of hst) hF hI _

include hok in
/-- **Running the top frame alike**: an instruction or a terminator that stays runs in lockstep,
and a lowered case is matched by its chain. -/
theorem exec_lock {s s₁ : State M} {n : Nat} {β : Nat → Nat} {top top₁ : Frame M}
    {conts conts₁ : List (Wait M)} {heap : Heap M} {world : M.W} {d : Nat}
    (h : CoreOK m B ⟨top, conts, heap, world⟩)
    (h₁ : CoreOK m₁ B₁ ⟨top₁, conts₁, heap, world⟩) (hst : All₂ (WaitRel bound) conts conts₁)
    (hF : FrameRel bound n β top top₁) :
    Diagram hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) s s₁
      (exec hwf ⟨top, conts, heap, world⟩ h d)
      (exec hwf₁ ⟨top₁, conts₁, heap, world⟩ h₁ d) := by
  obtain ⟨func, code, term, env, blk, pc, fits⟩ := top
  obtain ⟨func₁, code₁, term₁, env₁, blk₁, pc₁, fits₁⟩ := top₁
  have hE : EnvRel env env₁ := hF.env
  have hcode := hF.code
  simp only at hcode
  cases hcode with
  | case hch =>
    have hr := h.termReady rfl rfl
    obtain ⟨c₂, ⟨c', hstep, -, -, hsil⟩, hm⟩ := chain_silent (hwf₁ := hwf₁) (oracle := oracle)
      (f := ⟨func, [], _, env, blk, pc, fits⟩)
      (c := ⟨⟨func, [], _, env, blk, pc, fits⟩, conts, heap, world⟩) (d := d) hF.body hF.size
      hr.1 hr.2 hch (Nat.zero_le _) h₁ rfl rfl rfl hE (.of hst)
    simp only [exec, execCode, execTerm]
    obtain ⟨_, e⟩ := transfer_eq (B := B) _ _ (h.caseNext hwf rfl rfl _ hr.2) h.2 d
      (.instr (Frame.pos ⟨func, [], _, env, blk, pc, fits⟩))
    rw [e]
    exact .inl ⟨c', hstep, c₂, hsil, hm⟩
  | term ht =>
    cases term with
    | case ts ps f args succs =>
      obtain ⟨succs₁, rfl, hs⟩ := ht
      simp only [exec, execCode, execTerm]
      refine transfer_lock hwf₁ oracle _ _ _ _ ?_
      rw [hE.applyFn f (h.termReady rfl rfl).1 (h₁.termReady rfl rfl).1]
      exact fun h₂ => exitTo_rel rfl hF.body hF.size hE hs _ _ _ (.of hst) h₂
    | sem op rs ps re f regs succs =>
      obtain ⟨succs₁, rfl, hs, hregs⟩ := ht
      simp only [exec, execCode, execTerm]
      rw [hE.applyFn f (h.termReady rfl rfl) (h₁.termReady rfl rfl)]
      exact settle_lock hwf hwf₁ hok oracle (i := ⟨op, pc, 0, none, ps, rs, regs, succs, re⟩)
        _ _ _ _ (.of hst) hF ⟨hs, hregs⟩ _
  | @cons i i₁ is is₁ _ _ hi hk =>
    cases i with
    | const dst v =>
      obtain rfl : i₁ = LInsn.const dst v := hi
      simp only [exec, execCode, Core.next]
      exact Diagram.next (Match.of (.of hst)
        (.exec ((hF.withCode hk).bind _ rfl (h.dst_lt rfl) (h₁.dst_lt rfl))))
    | pure dst ts r f args =>
      obtain rfl : i₁ = LInsn.pure dst ts r f args := hi
      simp only [exec, execCode, Core.next]
      exact Diagram.next (Match.of (.of hst)
        (.exec ((hF.withCode hk).bind _ (congrArg _ (hE.applyFn f _ _)) (h.dst_lt rfl)
          (h₁.dst_lt rfl))))
    | refNew dst t v =>
      obtain rfl : i₁ = LInsn.refNew dst t v := hi
      simp only [exec, execCode, Core.refNew, Core.next]
      exact Diagram.next (Match.of ⟨rfl, congrArg heap.push (hE.getD (h.ready rfl) _), hst⟩
        (.exec ((hF.withCode hk).bind _ rfl (h.dst_lt rfl) (h₁.dst_lt rfl))))
    | refGet dst t x =>
      obtain rfl : i₁ = LInsn.refGet dst t x := hi
      simp only [exec, execCode, Core.cellLoc]
      have key := congrArg M.locOf
        (hE.getT (h.ready rfl) (h₁.ready (i := .refGet dst t x) rfl))
      refine Heap.cell_rec₂ (key ▸ Iff.rfl) (fun _ _ => ?_) ?_
      · exact Diagram.next (Match.of (.of hst) (.exec
          ((hF.withCode hk).bind _ (getElem_congr_idx key) (h.dst_lt rfl) (h₁.dst_lt rfl))))
      · exact key ▸ Diagram.next (Match.of (.of hst) (.done _))
    | refSet dst t x v =>
      obtain rfl : i₁ = LInsn.refSet dst t x v := hi
      simp only [exec, execCode, Core.cellLoc]
      have hr : HasTy env x (Ty.ref t) ∧ Bound env v := h.ready rfl
      have hr₁ : HasTy env₁ x (Ty.ref t) ∧ Bound env₁ v :=
        h₁.ready (i := .refSet dst t x v) rfl
      have key := congrArg M.locOf (hE.getT hr.1 hr₁.1)
      refine Heap.cell_rec₂ (key ▸ Iff.rfl) (fun _ _ => ?_) ?_
      · refine Diagram.next (Match.of ⟨rfl, ?_, hst⟩
          (.exec ((hF.withCode hk).bind _ rfl (h.dst_lt rfl) (h₁.dst_lt rfl))))
        simp only [Core.refSet, Core.next, key, hE.getD hr.2 hr₁.2]
      · exact key ▸ Diagram.next (Match.of (.of hst) (.done _))
    | callCode dst ts r fn args =>
      obtain rfl : i₁ = LInsn.callCode dst ts r fn args := hi
      simp only [exec, execCode]
      have hr : HasTy env fn (Ty.fn ts r) ∧ AllBound env args := h.ready rfl
      have hr₁ : HasTy env₁ fn (Ty.fn ts r) ∧ AllBound env₁ args :=
        h₁.ready (i := .callCode dst ts r fn args) rfl
      have key := congrArg M.fnOf (hE.getT hr.1 hr₁.1)
      refine hok.sigs.callee_rec₂ rfl (congrArg (·.idx) key) (congrArg (·.captured) key)
        (fun caps hco hco₁ => ?_) fun e => ?_
      · obtain ⟨n₁, β₁, hFr⟩ := callFrame_rel hwf hwf₁ hok hco.1 hco₁.1 (congrArg (·.idx) key)
          (ds := appendCaps caps (lookupAll env args hr.2))
          (ds₁ := appendCaps caps (lookupAll env₁ args hr₁.2))
          (by rw [hE.lookupAll hr.2 hr₁.2]) .nil
        exact Diagram.next (Match.of (.of hst) (.call hFr (.call (hF.withCode hk))))
      · exact e ▸ Diagram.next (Match.of (.of hst) (.done _))
    | sem op dst rs r ps re f regs succs =>
      obtain ⟨succs₁, rfl, hs, hregs⟩ := hi
      simp only [exec, execCode]
      rw [hE.applyFn f (h.ready rfl) (h₁.ready (i := .sem op dst rs r ps re f regs succs₁) rfl)]
      exact settle_lock hwf hwf₁ hok oracle (i := ⟨op, pc, dst, some r, ps, rs, regs, succs, re⟩)
        _ _ _ _ (.of hst) (hF.withCode hk) ⟨hs, hregs⟩ _

include hok in
/-- **Leaving a body alike**: the same value, left by frames whose waiting frames correspond. -/
theorem leave_lock {s s₁ : State M} {top top₁ : Frame M} {conts conts₁ : List (Wait M)}
    {heap : Heap M} {world : M.W} {d : Nat} {v : Dyn M.interp}
    (h : LeftOK m B ⟨top, conts, heap, world⟩ v)
    (h₁ : LeftOK m₁ B₁ ⟨top₁, conts₁, heap, world⟩ v)
    (hst : All₂ (WaitRel bound) conts conts₁) :
    Diagram hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) s s₁
      (leave hwf ⟨top, conts, heap, world⟩ v h d)
      (leave hwf₁ ⟨top₁, conts₁, heap, world⟩ v h₁ d) := by
  simp only [leave]
  cases hst with
  | nil =>
    simp only [leaveTo]
    exact Diagram.next (Match.of (.of .nil) (.done _))
  | cons hw hcs =>
    cases hw with
    | rule hF hI =>
      simp only [leaveTo]
      exact settle_lock hwf hwf₁ hok oracle _ _ _ _ (.of hcs) hF hI _
    | call hF =>
      simp only [leaveTo]
      exact Diagram.next (Match.of (.of hcs)
        (.exec (hF.bind _ rfl (LeftOK.call_dst h rfl) (LeftOK.call_dst h₁ rfl))))

include hok in
/-- **The step diagram.**  From states that correspond, a source step is matched by a target step
to a state that reaches a corresponding one silently, and a source that has ended by a target
that has ended with the same result, world and number of choices. -/
theorem step_match {s s₁ : State M} (h : StateOK m B s) (h₁ : StateOK m₁ B₁ s₁)
    (hm : Match bound s s₁) :
    Diagram hwf₁ oracle (Match bound) (fun _ => 0) (fun _ => False) s s₁ (step hwf oracle s h)
      (step hwf₁ oracle s₁ h₁) := by
  obtain ⟨⟨top, conts, heap, world⟩, mode, d, ⟨⟩⟩ := s
  obtain ⟨⟨top₁, conts₁, heap₁, world₁⟩, mode₁, d₁, ⟨⟩⟩ := s₁
  obtain ⟨hd, ⟨hw, hh, hst⟩, hmode⟩ := hm
  simp only at hd hw hh hst hmode
  subst hd hw hh
  cases hmode with
  | exec hF => exact exec_lock hwf hwf₁ hok oracle h h₁ hst hF
  | jump hF => exact Diagram.next (Match.of (.of hst) (.exec hF))
  | call hF hW => exact Diagram.next (Match.of (.of (.cons hW hst)) (.exec hF))
  | ret v => exact leave_lock hwf hwf₁ hok oracle h h₁ hst
  | request t hF hI => exact serve_lock hwf hwf₁ hok oracle h h₁ hst hF hI t
  | @again n β i pc₁ succs₁ st hF hI =>
    simp only [step]
    rw [show (mkInst i pc₁ succs₁ i.rerun.args).again top₁.env h₁.1.typed st =
      i.again top.env h.1.typed st from congrFun (hF.env.applyFn _ _ _) st]
    exact settle_lock hwf hwf₁ hok oracle _ _ _ _ (.of hst) hF hI _
  | done r => exact .inr ⟨_, rfl⟩

end

end

end Strata.Dyn.CasesSound
