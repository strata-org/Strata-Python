/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.CasesSound.Step

set_option autoImplicit false

/-!
# Edges of a lowered body

The states of a source module and of a target module that lowers its cases correspond
(`Match`) when they have the same heap, world and number of choices, their waiting frames
correspond, and their pending transitions do: frames of a certified pair of bodies, the target's
store holding the source's (`FrameRel`), at code that the certificate relates.  The transitions
are the same (`ModeRel`, `WaitRel`): a rule's operation in the target is the source's with
another position and lowered edges (`Exec.mkInst`, `InstRel`), so its tree, its state and what
resumes it are the source's.

A source step is one target step and then some silent ones, so the simulation relates a source
state to a target state that reaches a corresponding one silently (`Exec.SilentRel`).  This file
proves it for the edges: a lowered edge (`exitTo_rel`), which may pass through a block that only
jumps, and the chain that lowers a case (`chain_silent`), which tests the successors in order,
reads the payload of the one the case picks and jumps to it.  A block that reads and jumps
(`tail_silent`) and a test with its branch (`test_steps`) are straight-line code, which the
machine runs silently (`run_straight`) to a store that still holds the source's and has the new
values in their slots (`EnvRel.runsTo`, `RunsTo.holds`).  Both edges end by landing alike
(`lands_rel`): the target passes as arguments the values the source passes as arguments and
payload.
-/

namespace Strata.Dyn.CasesSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-! ## States that correspond -/

section
variable (bound : Nat → Nat)

/-- A source frame and a target frame correspond: their bodies are a certified pair, the source's
store has `n` slots, the target's store holds it, and the target's code lowers the source's. -/
structure FrameRel (n : Nat) (β : Nat → Nat) (f f₁ : Frame M) : Prop where
  body : BodyOK bound n β f₁.func f.func
  size : f.env.size = n
  env : EnvRel f.env f₁.env
  code : CodeOK bound n β f₁.func f.code f.term f₁.code f₁.term

/-- The target's version of the source rule's operation `i`, in the body `g₁`, has the lowered
edges `succs₁`, and the regions of `i` run in a store of `n` slots. -/
structure InstRel (n : Nat) (β : Nat → Nat) (g₁ : LBody M) (i : Inst M) (succs₁ : List LSite) :
    Prop where
  sites : SitesLow n β g₁ i.ps i.succs succs₁
  regs : ∀ k ∈ i.regs, bound k = n

/-- A source frame waiting for a body and a target frame waiting for one correspond: frames of
a rule paused at a request, the target's operation being the source's with another position and
lowered edges, or the callers of a `callCode`. -/
inductive WaitRel : Wait M → Wait M → Prop
  | rule {n : Nat} {β : Nat → Nat} {f f₁ : Frame M} {i : Inst M} {pc₁ : Nat}
      {succs₁ : List LSite} {req req₁ : MReq M.interp i.rs} {r : Ty} {k : M.interp r → i.Tree} :
      FrameRel bound n β f f₁ → InstRel bound n β f₁.func i succs₁ →
      WaitRel (.rule f ⟨i, req, r, k⟩) (.rule f₁ ⟨mkInst i pc₁ succs₁ i.rerun.args, req₁, r, k⟩)
  | call {n : Nat} {β : Nat → Nat} {f f₁ : Frame M} {dst : Nat} {r : Ty} :
      FrameRel bound n β f f₁ → WaitRel (.call f dst r) (.call f₁ dst r)

/-- The source's pending transition and the target's correspond: the same transition, of frames
that correspond, a rule's operation in the target being the source's with another position and
lowered edges. -/
inductive ModeRel (c c₁ : Core M) : Mode M → Mode M → Prop
  | exec {n : Nat} {β : Nat → Nat} : FrameRel bound n β c.top c₁.top → ModeRel c c₁ .exec .exec
  | jump {n : Nat} {β : Nat → Nat} {to to₁ : Frame M} :
      FrameRel bound n β to to₁ → ModeRel c c₁ (.jump to) (.jump to₁)
  | call {n : Nat} {β : Nat → Nat} {g g₁ : Frame M} {w w₁ : Wait M} :
      FrameRel bound n β g g₁ → WaitRel bound w w₁ → ModeRel c c₁ (.call g w) (.call g₁ w₁)
  | ret (v : Dyn M.interp) : ModeRel c c₁ (.ret v) (.ret v)
  | request {n : Nat} {β : Nat → Nat} {i : Inst M} {pc₁ : Nat} {succs₁ : List LSite}
      (t : i.Tree) : FrameRel bound n β c.top c₁.top → InstRel bound n β c₁.top.func i succs₁ →
      ModeRel c c₁ (.request i t) (.request (mkInst i pc₁ succs₁ i.rerun.args) t)
  | again {n : Nat} {β : Nat → Nat} {i : Inst M} {pc₁ : Nat} {succs₁ : List LSite} (st : i.St) :
      FrameRel bound n β c.top c₁.top → InstRel bound n β c₁.top.func i succs₁ →
      ModeRel c c₁ (.again ⟨i, st⟩) (.again ⟨mkInst i pc₁ succs₁ i.rerun.args, st⟩)
  | done (r : Result M.interp) : ModeRel c c₁ (.done r) (.done r)

/-- What corresponds between two cores, besides their top frames: the world, the heap and the
waiting frames. -/
structure DataRel (c c₁ : Core M) : Prop where
  world : c₁.world = c.world
  heap : c₁.heap = c.heap
  conts : All₂ (WaitRel bound) c.conts c₁.conts

/-- **A source state and a target state that correspond.** -/
def Match (s s₁ : State M) : Prop :=
  s₁.drawn = s.drawn ∧ DataRel bound s.core s₁.core ∧
    ModeRel bound s.core s₁.core s.mode s₁.mode

variable {bound}

/-- Corresponding cores, with corresponding pending transitions and the same choices drawn. -/
theorem Match.of {c c₁ : Core M} {mode mode₁ : Mode M} {d : Nat} (hD : DataRel bound c c₁)
    (hm : ModeRel bound c c₁ mode mode₁) : Match bound ⟨c, mode, d, ()⟩ ⟨c₁, mode₁, d, ()⟩ :=
  ⟨rfl, hD, hm⟩

/-- Cores that correspond still do with other top frames. -/
theorem DataRel.withTop {c c₁ : Core M} (hD : DataRel bound c c₁) (f f₁ : Frame M) :
    DataRel bound { c with top := f } { c₁ with top := f₁ } :=
  ⟨hD.world, hD.heap, hD.conts⟩

/-! ## Landing alike -/

/-- Operands that hold the values `xs` have them. -/
private theorem lookupAll_of {env : Array (Dyn M.interp)} :
    ∀ {as : List Nat} {xs : List (Dyn M.interp)}, All₂ (fun a v => env[a]? = some v) as xs →
      ∀ hb : AllBound env as, lookupAll env as hb = xs
  | _, _, .nil, _ => rfl
  | _, _, .cons h hs, hb => by
    rw [lookupAll, lookupAll_of hs hb.2]
    refine congrArg (· :: _) ?_
    rw [Array.getElem?_eq_getElem hb.1] at h
    exact Option.some.inj h

/-- Bound operands are slots of the store. -/
private theorem allBound_lt {env : Array (Dyn M.interp)} :
    ∀ {as : List Nat}, AllBound env as → ∀ a ∈ as, a < env.size
  | _ :: _, hb, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hb.1
    · exact allBound_lt hb.2 a ha

/-- The larger store holds the values of the smaller store's operands. -/
private theorem EnvRel.holds {env env₁ : Array (Dyn M.interp)} (hE : EnvRel env env₁) :
    ∀ {as : List Nat} (hb : AllBound env as),
      All₂ (fun a v => env₁[a]? = some v) as (Exec.lookupAll env as hb)
  | [], _ => .nil
  | a :: _, hb => .cons ((hE a hb.1).trans (Array.getElem?_eq_getElem hb.1)) (hE.holds hb.2)

/-- Related lists, one after the other. -/
private theorem All₂.append {α β : Type} {R : α → β → Prop} {cs : List α} {ds : List β} :
    ∀ {as : List α} {bs : List β}, All₂ R as bs → All₂ R cs ds → All₂ R (as ++ cs) (bs ++ ds)
  | _, _, .nil, h => h
  | _, _, .cons h₁ hs, h => .cons h₁ (All₂.append hs h)

/-- **Edges that pass the same values to corresponding targets land alike**: in frames that
correspond at the entry of a block, or with the same value out of the body. -/
theorem lands_rel {n : Nat} {β : Nat → Nat} {f f₁ : Frame M}
    (hB : BodyOK bound n β f₁.func f.func) (hsz : f.env.size = n) (hE : EnvRel f.env f₁.env)
    {tgt tgt₁ : LTarget} {ds : List (Dyn M.interp)} {x x₁ : Next M} (ht : TargetMap β tgt tgt₁)
    (hl : Lands f tgt ds x) (hl₁ : Lands f₁ tgt₁ ds x₁) (c c₁ : Core M) :
    ModeRel bound c c₁ (modeOf x) (modeOf x₁) := by
  cases x with
  | frame F =>
    obtain ⟨i, b, rfl, hb, hFf, hFc, hFt, hFe⟩ := hl
    cases x₁ with
    | frame F₁ =>
      obtain ⟨i₁, b₁, rfl, hb₁, hFf₁, hFc₁, hFt₁, hFe₁⟩ := hl₁
      obtain rfl : i₁ = β i := (LTarget.block.inj ht)
      obtain ⟨b₂, hb₂, hps, hcode⟩ := hB.2 i b hb
      obtain rfl : b₂ = b₁ := Option.some.inj (hb₂.symm.trans hb₁)
      refine .jump (n := n) (β := β) ⟨?_, ?_, ?_, ?_⟩
      · rw [hFf, hFf₁]; exact hB
      · rw [hFe, size_bindL]; exact hsz
      · rw [hFe, hFe₁, hps]; exact hE.bindL _ _
      · rw [hFf₁, hFc, hFt, hFc₁, hFt₁]; exact hcode
    | leave v₁ =>
      obtain ⟨rfl, -⟩ := hl₁
      exact nomatch ht
  | leave v =>
    obtain ⟨rfl, rfl⟩ := hl
    cases x₁ with
    | frame F₁ =>
      obtain ⟨i₁, b₁, rfl, -⟩ := hl₁
      exact nomatch ht
    | leave v₁ =>
      obtain ⟨-, hv⟩ := hl₁
      obtain rfl := (List.cons.inj hv).1
      exact .ret v

/-- **Entering corresponding blocks alike**: the frames that run the entry blocks of a certified
pair of bodies, in stores that correspond, on the same values. -/
theorem entry_rel {n : Nat} {β : Nat → Nat} {g g₁ : LBody M} (hB : BodyOK bound n β g₁ g)
    {b b₁ : LBlock M} (hb : g.blocks[0]? = some b) (hb₁ : g₁.blocks[0]? = some b₁)
    {env env₁ : Array (Dyn M.interp)} (hE : EnvRel env env₁) (hsz : env.size = n) {ts : List Ty}
    (ds : List (Dyn M.interp)) (xs : Args M.interp ts) (hle : g.slots ≤ env.size)
    (hp : ParamsFit g b) (hle₁ : g₁.slots ≤ env₁.size) (hp₁ : ParamsFit g₁ b₁) :
    FrameRel bound n β (Frame.entry g b env ds xs hle hp)
      (Frame.entry g₁ b₁ env₁ ds xs hle₁ hp₁) := by
  obtain ⟨b₂, hb₂, hps, hcode⟩ := hB.2 0 b hb
  rw [hB.1] at hb₂
  obtain rfl : b₂ = b₁ := Option.some.inj (hb₂.symm.trans hb₁)
  refine ⟨hB, ?_, ?_, hcode⟩
  · exact (size_bindSite ..).trans hsz
  · show EnvRel (bindSite ..) (bindSite ..)
    rw [bindSite_eq, bindSite_eq, hps]
    exact hE.bindL _ _

end

/-! ## Silent steps to a corresponding state -/

section
variable {bound : Nat → Nat} {m₁ : LModule M} {B₁ : Ty} {hwf₁ : WF m₁} {oracle : Nat → Nat}

/-- **The rest of a block that reads values and jumps**, run in the target: where the source's
transfer along `s` leads, on the values `vals` that the reads return in every store that holds
the source's, the target reaches by its reads and its jump, which are silent. -/
theorem tail_silent {n : Nat} {β : Nat → Nat} {f : Frame M} {g₁ : LBody M}
    (hB : BodyOK bound n β g₁ f.func) (hsz : f.env.size = n) {s : LSite} {x : Next M}
    {c c₁ : Core M} {d : Nat} {code : List (LInsn M)} {vals : List (Dyn M.interp)}
    (h₁ : StateOK m₁ B₁ ⟨c₁, .exec, d, ()⟩) (hf : c₁.top.func = g₁) (hc : c₁.top.code = code)
    (hE : EnvRel f.env c₁.top.env) (ht : Tail n β s code c₁.top.term)
    (hsel : ∀ env', EnvRel f.env env' → All₂ (Returns env') code vals)
    {hb : AllBound f.env s.args} (hl : Lands f s.target (lookupAll f.env s.args hb ++ vals) x)
    (hD : DataRel bound c c₁) :
    ∃ c₂, SilentPlus hwf₁ oracle ⟨⟨c₁, .exec, d, ()⟩, h₁⟩ c₂ ∧
      Match bound ⟨c, modeOf x, d, ()⟩ c₂.1 := by
  obtain ⟨hnd, hfr, s₂, hj, hargs, htm⟩ := ht
  obtain ⟨env₂, hrun, hE₂⟩ := hE.runsTo hsel fun i hi => hsz ▸ hfr i hi
  obtain ⟨top, hS, h₂, hsp, htf, rfl⟩ := run_straight hwf₁ oracle hrun h₁ hc rfl (hj env₂)
  obtain ⟨s₃, hs₃, hb₂, hl₁⟩ := exitTo_lands top [s₂] (.here .nil) hS
  obtain rfl : s₂ = s₃ := Option.some.inj hs₃
  have hx : lookupAll top.env s₂.args hb₂ ++ valsOf (Exit.here .nil : Exit M.interp [[]]) =
      lookupAll f.env s.args hb ++ vals := by
    refine (List.append_nil _).trans (lookupAll_of ?_ hb₂)
    rw [hargs]
    exact All₂.append (hE₂.holds hb) (hrun.holds hnd fun u hu =>
      allBound_lt hb₂ u (hargs ▸ List.mem_append_right _ hu))
  rw [hx] at hl₁
  exact ⟨_, hsp, Match.of (hD.withTop _ _)
    (lands_rel (htf.trans hf ▸ hB) hsz hE₂ htm hl hl₁ _ _)⟩

/-- An edge that passes nothing to a block without parameters leads to a frame at that block,
in the same store. -/
private theorem lands_via {f₁ : Frame M} {j : Nat} {b : LBlock M} (hb : f₁.func.blocks[j]? = some b)
    (hps : b.params = []) {ds : List (Dyn M.interp)} {x₁ : Next M}
    (hl : Lands f₁ (.block j) ds x₁) :
    ∃ F, x₁ = .frame F ∧ F.func = f₁.func ∧ F.code = b.insns ∧ F.term = b.term ∧
      F.env = f₁.env := by
  cases x₁ with
  | leave v => exact nomatch hl.1
  | frame F =>
    obtain ⟨i, b₁, hi, hb₁, hFf, hFc, hFt, hFe⟩ := hl
    obtain rfl : j = i := LTarget.block.inj hi
    obtain rfl : b = b₁ := Option.some.inj (hb.symm.trans hb₁)
    rw [hps] at hFe
    exact ⟨F, rfl, hFf, hFc, hFt, hFe⟩

/-- The target edge `s₁`, which passes the values `vals₁`, delivers the source edge `s`, which
passes the values `vals`: the same edge with the same values, or an edge that passes nothing to a
block that reads `vals` and jumps. -/
def Delivers (n : Nat) (β : Nat → Nat) (f : Frame M) (g₁ : LBody M) (s : LSite)
    (vals vals₁ : List (Dyn M.interp)) (s₁ : LSite) : Prop :=
  (vals₁ = vals ∧ s₁.args = s.args ∧ TargetMap β s.target s₁.target) ∨
    (vals₁ = [] ∧ Via g₁ s₁ fun code term => Tail n β s code term ∧
      ∀ env', EnvRel f.env env' → All₂ (Returns env') code vals)

/-- **A delivered edge**: where the source's transfer along `s` leads, the target's transfer
along `s₁` reaches silently. -/
private theorem deliver {n : Nat} {β : Nat → Nat} {f f₁ : Frame M} {g₁ : LBody M}
    (hf₁ : f₁.func = g₁) (hB : BodyOK bound n β g₁ f.func) (hsz : f.env.size = n)
    (hE : EnvRel f.env f₁.env)
    {s s₁ : LSite} {vals vals₁ : List (Dyn M.interp)} (hs : Delivers n β f g₁ s vals vals₁ s₁)
    {x x₁ : Next M} {hb : AllBound f.env s.args}
    (hl : Lands f s.target (lookupAll f.env s.args hb ++ vals) x)
    {hb₁ : AllBound f₁.env s₁.args}
    (hl₁ : Lands f₁ s₁.target (lookupAll f₁.env s₁.args hb₁ ++ vals₁) x₁) {c c₁ : Core M}
    {d : Nat} (hD : DataRel bound c c₁) (h₁ : StateOK m₁ B₁ ⟨c₁, modeOf x₁, d, ()⟩) :
    SilentRel hwf₁ oracle (Match bound) ⟨c, modeOf x, d, ()⟩ ⟨⟨c₁, modeOf x₁, d, ()⟩, h₁⟩ := by
  subst hf₁
  obtain ⟨tgt₁, args₁⟩ := s₁
  rcases hs with ⟨rfl, hargs, ht⟩ | ⟨rfl, j, b, hs₁, hbj, hps, htail, hsel⟩
  · simp only at hargs ht hl₁
    subst hargs
    rw [hE.lookupAll hb hb₁] at hl₁
    exact ⟨_, .refl _, Match.of hD (lands_rel hB hsz hE ht hl hl₁ _ _)⟩
  · obtain ⟨rfl, rfl⟩ := LSite.mk.inj hs₁
    obtain ⟨F, rfl, hFf, hFc, hFt, hFe⟩ := lands_via hbj hps hl₁
    obtain ⟨c₂, hsp, hm⟩ := tail_silent (hwf₁ := hwf₁) (oracle := oracle) hB hsz (x := x) (c := c)
      (c₁ := { c₁ with top := F }) h₁ hFf hFc (hFe ▸ hE) (hFt ▸ htail) hsel hl (hD.withTop _ _)
    exact ⟨c₂, .step (stepAt_jump hwf₁ oracle h₁) rfl rfl hsp.silent, hm⟩

/-- **A lowered edge**: where the source leaves along the successor an exit picks, the target,
leaving along the lowered successor, reaches silently. -/
theorem exitTo_rel {n : Nat} {β : Nat → Nat} {f f₁ : Frame M} {g₁ : LBody M}
    (hf₁ : f₁.func = g₁) (hB : BodyOK bound n β g₁ f.func) (hsz : f.env.size = n)
    (hE : EnvRel f.env f₁.env) {ps : List (List Ty)} {ss ss₁ : List LSite}
    (hs : SitesLow n β g₁ ps ss ss₁) (e : Exit M.interp ps) (hS : Exec.SitesOK f ss ps)
    (hS₁ : Exec.SitesOK f₁ ss₁ ps) {c c₁ : Core M} {d : Nat} (hD : DataRel bound c c₁)
    (h₁ : StateOK m₁ B₁ ⟨c₁, modeOf (exitTo f₁ ss₁ e hS₁), d, ()⟩) :
    SilentRel hwf₁ oracle (Match bound) ⟨c, modeOf (exitTo f ss e hS), d, ()⟩
      ⟨⟨c₁, modeOf (exitTo f₁ ss₁ e hS₁), d, ()⟩, h₁⟩ := by
  obtain ⟨p, s, s₁, hp, hs₀, hs₁, hlow⟩ := hs.get e
  obtain ⟨s', hs', hb, hl⟩ := exitTo_lands f ss e hS
  obtain ⟨s₁', hs₁', hb₁, hl₁⟩ := exitTo_lands f₁ ss₁ e hS₁
  obtain rfl : s = s' := Option.some.inj (hs₀.symm.trans hs')
  obtain rfl : s₁ = s₁' := Option.some.inj (hs₁.symm.trans hs₁')
  refine deliver hf₁ hB hsz hE ?_ hl hl₁ hD h₁
  rcases hlow with h | ⟨rfl, j, b, h1, h2, h3, hnil, ht⟩
  · exact .inl ⟨rfl, h.1, h.2⟩
  · rw [valsOf_nil e hp]
    exact .inr ⟨rfl, j, b, h1, h2, h3, ht, fun _ _ => hnil ▸ .nil⟩

/-! ## The chain -/

/-- The exit of a test's branch picks the first edge or the second, and passes nothing. -/
private theorem two_way {I : Ty → Type} (b : Prop) [Decidable b] (st sf : LSite) :
    [st, sf][armOf (if b then .here .nil else .there (.here .nil) : Exit I [[], []])]? =
        some (if b then st else sf) ∧
      valsOf (if b then .here .nil else .there (.here .nil) : Exit I [[], []]) = [] := by
  by_cases h : b <;> simp only [h, ↓reduceIte] <;> exact ⟨rfl, rfl⟩

/-- **An edge that delivers a successor of the case**: where the source's case leads when it
picks successor `k`, the target's transfer along the edge reaches silently. -/
private theorem arm_rel {n : Nat} {β : Nat → Nat} {f f₁ : Frame M} {g₁ : LBody M}
    (hf₁ : f₁.func = g₁) (hB : BodyOK bound n β g₁ f.func) (hsz : f.env.size = n)
    (hE : EnvRel f.env f₁.env)
    {ts : List Ty} {ps : List (List Ty)} {fn : Fn M.interp (Exit M.interp ps) ts}
    {args : List Nat} {succs : List LSite} (ht : Typed f.env args ts)
    (hS : Exec.SitesOK f succs ps) {k : Nat} {s₁ : LSite}
    (harm : ArmAt n β g₁ fn args succs k s₁) (hk : armOf (applyFn f.env ts fn args ht) = k)
    {x₁ : Next M} {hb₁ : AllBound f₁.env s₁.args}
    (hl₁ : Lands f₁ s₁.target (lookupAll f₁.env s₁.args hb₁ ++ []) x₁) {c c₁ : Core M}
    {d : Nat} (hD : DataRel bound c c₁) (h₁ : StateOK m₁ B₁ ⟨c₁, modeOf x₁, d, ()⟩) :
    SilentRel hwf₁ oracle (Match bound)
      ⟨c, modeOf (exitTo f succs (applyFn f.env ts fn args ht) hS), d, ()⟩
      ⟨⟨c₁, modeOf x₁, d, ()⟩, h₁⟩ := by
  obtain ⟨s, hs, harm⟩ := harm
  obtain ⟨s', hs', hb, hl⟩ := exitTo_lands f succs (applyFn f.env ts fn args ht) hS
  rw [hk] at hs'
  obtain rfl : s = s' := Option.some.inj (hs.symm.trans hs')
  refine deliver hf₁ hB hsz hE ?_ hl hl₁ hD h₁
  rcases harm with ⟨hp, hargs, htm⟩ | ⟨j, b, h1, h2, h3, htail, hsel⟩
  · exact .inl ⟨(valsOf_nil _ (by rw [hk]; exact hp)).symm, hargs, htm⟩
  · refine .inr ⟨rfl, j, b, h1, h2, h3, htail, fun env' hE' => ?_⟩
    have h := hsel env' (hE'.typed ht) (by rw [hE'.applyFn fn ht]; exact hk)
    rwa [hE'.applyFn fn ht] at h

/-- **A test and its branch**, run in the target: silent steps bind the test's value and leave,
pending, the transfer along the first edge if the case picks successor `k` and along the second
if it picks a later one. -/
theorem test_steps {n : Nat} {f : Frame M} (hsz : f.env.size = n) {ts : List Ty}
    {ps : List (List Ty)} {fn : Fn M.interp (Exit M.interp ps) ts} {args : List Nat}
    (ht : Typed f.env args ts) {k : Nat} {test : LInsn M} {br : LTerm M} {st sf : LSite}
    (hd : n ≤ test.dst) (htests : Tests fn args k test br st sf)
    (hk : k ≤ armOf (applyFn f.env ts fn args ht)) {c₁ : Core M} {d : Nat}
    (h₁ : StateOK m₁ B₁ ⟨c₁, .exec, d, ()⟩) (hc : c₁.top.code = [test]) (htm : c₁.top.term = br)
    (hE : EnvRel f.env c₁.top.env) :
    ∃ top x₁ h₂,
      SilentPlus hwf₁ oracle ⟨⟨c₁, .exec, d, ()⟩, h₁⟩
        ⟨⟨{ c₁ with top := top }, modeOf x₁, d, ()⟩, h₂⟩ ∧
      top.func = c₁.top.func ∧ EnvRel f.env top.env ∧
      ∃ hb₁, Lands top (if armOf (applyFn f.env ts fn args ht) = k then st else sf).target
        (lookupAll top.env (if armOf (applyFn f.env ts fn args ht) = k then st else sf).args hb₁
          ++ []) x₁ := by
  have hE₁ := hE.applyFn fn ht (hE.typed ht)
  obtain ⟨v, hr, hx⟩ := htests c₁.top.env (hE.typed ht)
    (Nat.lt_of_lt_of_le (CoreOK.dst_lt (m := m₁) (B := B₁) h₁ hc) c₁.top.fits)
    (by rw [hE₁]; exact hk)
  rw [hE₁] at hx
  obtain ⟨top, hS, h₂, hsp, htf, hte⟩ :=
    run_straight hwf₁ oracle (.cons hr .nil) h₁ hc rfl (htm ▸ hx)
  obtain ⟨s₁, hs₁, hb₁, hl₁⟩ := exitTo_lands top [st, sf] _ hS
  obtain ⟨h2, h3⟩ := two_way (I := M.interp) (armOf (applyFn f.env ts fn args ht) = k) st sf
  obtain rfl := Option.some.inj (h2.symm.trans hs₁)
  rw [h3] at hl₁
  exact ⟨top, _, h₂, hsp, htf, hte ▸ hE.fresh (hsz ▸ hd) v, hb₁, hl₁⟩

/-- **The chain that lowers a case**, run in the target: from the rest of a block that dispatches
the case from successor `k`, when the case picks `k` or a later one, silent steps reach where
the source's case leads. -/
theorem chain_silent {n : Nat} {β : Nat → Nat} {f : Frame M} {g₁ : LBody M}
    (hB : BodyOK bound n β g₁ f.func) (hsz : f.env.size = n) {ts : List Ty}
    {ps : List (List Ty)} {fn : Fn M.interp (Exit M.interp ps) ts} {args : List Nat}
    {succs : List LSite} (ht : Typed f.env args ts) (hS : Exec.SitesOK f succs ps) {c : Core M}
    {d : Nat} {k : Nat} {code : List (LInsn M)} {term : LTerm M}
    (hch : Chain n β g₁ fn args succs k code term) :
    k ≤ armOf (applyFn f.env ts fn args ht) →
    ∀ {c₁ : Core M} (h₁ : StateOK m₁ B₁ ⟨c₁, .exec, d, ()⟩), c₁.top.func = g₁ →
      c₁.top.code = code → c₁.top.term = term → EnvRel f.env c₁.top.env → DataRel bound c c₁ →
      ∃ c₂, SilentPlus hwf₁ oracle ⟨⟨c₁, .exec, d, ()⟩, h₁⟩ c₂ ∧
        Match bound ⟨c, modeOf (exitTo f succs (applyFn f.env ts fn args ht) hS), d, ()⟩ c₂.1 := by
  induction hch with
  | none hk =>
    intro hk'
    exact absurd (armOf_lt (applyFn f.env ts fn args ht)) (by omega)
  | @last k s code term hk hs htail hsel =>
    intro hk' c₁ h₁ hf hc htm hE hD
    have harm : armOf (applyFn f.env ts fn args ht) = k := by
      have := armOf_lt (applyFn f.env ts fn args ht)
      omega
    obtain ⟨s', hs', hb, hl⟩ := exitTo_lands f succs (applyFn f.env ts fn args ht) hS
    rw [harm] at hs'
    obtain rfl := Option.some.inj (hs.symm.trans hs')
    refine tail_silent hB hsz h₁ hf hc hE (htm ▸ htail) (fun env' hE' => ?_) hl hD
    have h := hsel env' (hE'.typed ht) (by rw [hE'.applyFn fn ht]; exact harm)
    rwa [hE'.applyFn fn ht] at h
  | @test k test br st sf hd htests harm hk2 harm' =>
    intro hk' c₁ h₁ hf hc htm hE hD
    obtain ⟨top, x₁, h₂, hsp, htf, hE', hb₁, hl₁⟩ :=
      test_steps (hwf₁ := hwf₁) (oracle := oracle) hsz ht hd htests hk' h₁ hc htm hE
    have hrel : SilentRel hwf₁ oracle (Match bound)
        ⟨c, modeOf (exitTo f succs (applyFn f.env ts fn args ht) hS), d, ()⟩
        ⟨⟨{ c₁ with top := top }, modeOf x₁, d, ()⟩, h₂⟩ := by
      by_cases ha : armOf (applyFn f.env ts fn args ht) = k
      · simp only [ha, ↓reduceIte] at hl₁
        exact arm_rel (htf.trans hf) hB hsz hE' ht hS harm ha hl₁ (hD.withTop _ _) h₂
      · simp only [ha, ↓reduceIte] at hl₁
        have ha' : armOf (applyFn f.env ts fn args ht) = k + 1 := by
          have := armOf_lt (applyFn f.env ts fn args ht)
          omega
        exact arm_rel (htf.trans hf) hB hsz hE' ht hS harm' ha' hl₁ (hD.withTop _ _) h₂
    obtain ⟨c₂, hsil, hm⟩ := hrel
    exact ⟨c₂, hsp.trans hsil, hm⟩
  | @next k test br st sf j b hd htests harm hsf hbj hps _ ih =>
    intro hk' c₁ h₁ hf hc htm hE hD
    obtain ⟨top, x₁, h₂, hsp, htf, hE', hb₁, hl₁⟩ :=
      test_steps (hwf₁ := hwf₁) (oracle := oracle) hsz ht hd htests hk' h₁ hc htm hE
    by_cases ha : armOf (applyFn f.env ts fn args ht) = k
    · simp only [ha, ↓reduceIte] at hl₁
      obtain ⟨c₂, hsil, hm⟩ :=
        arm_rel (hwf₁ := hwf₁) (oracle := oracle) (htf.trans hf) hB hsz hE' ht hS harm ha hl₁
          (hD.withTop _ _) h₂
      exact ⟨c₂, hsp.trans hsil, hm⟩
    · simp only [ha, ↓reduceIte] at hl₁
      subst hsf
      obtain ⟨F, rfl, hFf, hFc, hFt, hFe⟩ :=
        lands_via (by rw [htf, hf]; exact hbj) hps hl₁
      obtain ⟨c₂, hsp₂, hm⟩ := ih (by omega) (c₁ := { c₁ with top := F }) h₂
        (hFf.trans (htf.trans hf)) hFc hFt (hFe ▸ hE') (hD.withTop _ _)
      exact ⟨c₂, hsp.trans (.step (stepAt_jump hwf₁ oracle h₂) rfl rfl hsp₂.silent), hm⟩

end

end

end Strata.Dyn.CasesSound
