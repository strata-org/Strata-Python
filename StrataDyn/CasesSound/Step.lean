/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.CasesSound.Cert
public import StrataDyn.Exec.Trace

set_option autoImplicit false

/-!
# What the simulation of a case lowering needs of the machine

* **Stores.**  `EnvRel`: the target's store holds the source's on every slot of the source's
  store.  It gives the same operands (`EnvRel.applyFn`, `EnvRel.lookupAll`), and is kept by
  binding the same slot in both stores (`EnvRel.set`) and by binding a slot above the source's
  store in the target (`EnvRel.fresh`).
* **Edges.**  `Lands` says where an edge leads as a function of the values it passes, its
  arguments' and then its payload's: binding a block's parameters (`bindL`), or leaving the body
  with the one value.  `exitTo_lands` gives it for the machine's transfer.  The lowering passes as
  arguments what the source passes as a payload, and the two land alike.
* **Straight-line code.**  `RunsTo` says that instructions return values at once, each bound
  before the next runs, and which store they leave.  Instructions that return in every store that
  holds the source's, into slots above it, run from any such store to one (`EnvRel.runsTo`);
  they keep the slots they do not define (`RunsTo.keeps`) and leave their values in those they
  do (`RunsTo.holds`).
* **Steps.**  `stepAt_returns` and `stepAt_exits` are the machine's step at an instruction that
  returns at once and at a terminator that exits at once.  `run_straight` puts them together:
  the machine runs straight-line code and then a terminator that exits at once by steps that
  change neither the world nor the choices (`SilentPlus`), and leaves the transfer pending.
-/

namespace Strata.Dyn.CasesSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-! ## Stores -/

section
variable {env env₁ : Array (Dyn M.interp)}

/-- The store `env₁` holds what `env` holds, on every slot of `env`. -/
def EnvRel (env env₁ : Array (Dyn M.interp)) : Prop := ∀ v, v < env.size → env₁[v]? = env[v]?

/-- A slot of the smaller store is a slot of the larger. -/
private theorem EnvRel.lt (h : EnvRel env env₁) {v : Nat} (hv : v < env.size) : v < env₁.size := by
  have h₁ := h v hv
  rw [Array.getElem?_eq_getElem hv] at h₁
  exact (Array.getElem?_eq_some_iff.mp h₁).1

/-- Binding the same slot to the same value in both stores. -/
theorem EnvRel.set (h : EnvRel env env₁) (v : Nat) (d : Dyn M.interp) :
    EnvRel (env.setIfInBounds v d) (env₁.setIfInBounds v d) := by
  intro w hw
  rw [Array.size_setIfInBounds] at hw
  rw [Array.getElem?_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hvw : v = w
  · subst hvw
    simp only [↓reduceIte, hw, h.lt hw]
  · simp only [hvw, ↓reduceIte]
    exact h w hw

/-- Binding, in the larger store, a slot that the smaller does not have. -/
theorem EnvRel.fresh (h : EnvRel env env₁) {w : Nat} (hw : env.size ≤ w) (d : Dyn M.interp) :
    EnvRel env (env₁.setIfInBounds w d) := by
  intro v hv
  rw [Array.getElem?_setIfInBounds_ne (Nat.ne_of_gt (Nat.lt_of_lt_of_le hv hw))]
  exact h v hv

/-- A value bound at a tag in the smaller store is bound at it in the larger. -/
private theorem EnvRel.hasTy (h : EnvRel env env₁) {v : Nat} {t : Ty} (hv : HasTy env v t) :
    HasTy env₁ v t := by
  have he := h v hv.1
  have hv₁ := h.lt hv.1
  rw [Array.getElem?_eq_getElem hv.1, Array.getElem?_eq_getElem hv₁] at he
  refine ⟨hv₁, fun _ => ?_⟩
  rw [Option.some.inj he]
  exact hv.2 hv.1

/-- Operands bound at their tags in the smaller store are bound at them in the larger. -/
theorem EnvRel.typed (h : EnvRel env env₁) :
    ∀ {vs : List Nat} {ts : List Ty}, Typed env vs ts → Typed env₁ vs ts
  | [], [], _ => trivial
  | _ :: _, _ :: _, ht => ⟨h.hasTy ht.1, h.typed ht.2⟩
  | [], _ :: _, ht => ht.elim
  | _ :: _, [], ht => ht.elim

/-- Operands bound at their tags are bound. -/
private theorem typed_allBound : ∀ {vs : List Nat} {ts : List Ty}, Typed env vs ts → AllBound env vs
  | [], [], _ => trivial
  | _ :: _, _ :: _, ht => ⟨ht.1.1, typed_allBound ht.2⟩
  | [], _ :: _, ht => ht.elim
  | _ :: _, [], ht => ht.elim

/-- Operands of the smaller store hold the same values in the larger. -/
private theorem EnvRel.same (h : EnvRel env env₁) :
    ∀ {vs : List Nat}, AllBound env vs → All₂ (fun v₁ v => env₁[v₁]? = env[v]?) vs vs
  | [], _ => .nil
  | _ :: _, hb => .cons (h _ hb.1) (h.same hb.2)

/-- A function of operands of the smaller store has the same value on the larger. -/
theorem EnvRel.applyFn (h : EnvRel env env₁) {R : Type} {ts : List Ty} (f : Fn M.interp R ts)
    {vs : List Nat} (ht : Typed env vs ts) (ht₁ : Typed env₁ vs ts) :
    applyFn env₁ ts f vs ht₁ = applyFn env ts f vs ht :=
  applyFn_congr (h.same (typed_allBound ht)) ts f ht₁ ht

/-- Operands of the smaller store have the same values in the larger. -/
theorem EnvRel.lookupAll (h : EnvRel env env₁) {vs : List Nat} (hb : AllBound env vs)
    (hb₁ : AllBound env₁ vs) : lookupAll env₁ vs hb₁ = lookupAll env vs hb :=
  lookupAll_congr (h.same hb) hb₁ hb

/-- A slot bound to a value of tag `t` is bound at `t`. -/
theorem hasTy_set {v : Nat} (hv : v < env.size) {t : Ty} (x : M.interp t) :
    HasTy (env.setIfInBounds v ⟨t, x⟩) v t := by
  have hv₁ : v < (env.setIfInBounds v ⟨t, x⟩).size := by
    rw [Array.size_setIfInBounds]
    exact hv
  refine ⟨hv₁, fun _ => ?_⟩
  rw [Array.getElem_setIfInBounds_self]

/-- A slot bound to a value holds it at its tag. -/
theorem getT_set {v : Nat} {t : Ty} (x : M.interp t)
    (h : HasTy (env.setIfInBounds v ⟨t, x⟩) v t) :
    getT (env.setIfInBounds v ⟨t, x⟩) v t h = x := by
  have he : (env.setIfInBounds v ⟨t, x⟩)[v]'h.1 = ⟨t, x⟩ := Array.getElem_setIfInBounds_self ..
  have key : ∀ (d : Dyn M.interp) (p : d.1 = t), d = ⟨t, x⟩ →
      cast (congrArg M.interp p) d.2 = x := by
    intro d p e
    subst e
    rfl
  exact key _ (h.2 h.1) he

/-- Bind the parameters `ps` to the values `ds`, in order, as far as both go. -/
def bindL : Array (Dyn M.interp) → Exec.Ctx → List (Dyn M.interp) → Array (Dyn M.interp)
  | env, [], _ => env
  | env, _ :: _, [] => env
  | env, (p, _) :: ps, d :: ds => bindL (env.setIfInBounds p d) ps ds

/-- Binding parameters keeps the store's size. -/
theorem size_bindL : ∀ (env : Array (Dyn M.interp)) (ps : Exec.Ctx) (ds : List (Dyn M.interp)),
    (bindL env ps ds).size = env.size
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | _, (_, _) :: ps, _ :: ds => (size_bindL _ ps ds).trans Array.size_setIfInBounds

/-- Binding the same parameters to the same values in both stores. -/
theorem EnvRel.bindL : ∀ {env env₁ : Array (Dyn M.interp)} (_ : EnvRel env env₁) (ps : Exec.Ctx)
    (ds : List (Dyn M.interp)), EnvRel (bindL env ps ds) (bindL env₁ ps ds)
  | _, _, h, [], _ => h
  | _, _, h, _ :: _, [] => h
  | _, _, h, (p, _) :: ps, d :: ds => (h.set p d).bindL ps ds

/-- The machine's binding of a block's parameters, to an edge's arguments and then its payload,
binds them to the list of both. -/
theorem bindSite_eq :
    ∀ (env : Array (Dyn M.interp)) {ts : List Ty} (ps : Exec.Ctx) (ds : List (Dyn M.interp))
      (xs : Args M.interp ts) (h : ∀ p ∈ ps, p.1 < env.size),
      bindSite env ps ds xs h = bindL env ps (ds ++ Args.toList xs)
  | _, _, [], _, _, _ => rfl
  | env, _, (p, _) :: ps, d :: ds, xs, h => by
    rw [bindSite, bindSite_eq, List.cons_append, bindL, Array.setIfInBounds_def,
      dite_eq_left (h _ List.mem_cons_self)]
  | env, _, (p, _) :: ps, [], .cons x xs, h => by
    rw [bindSite, bindSite_eq, List.nil_append, List.nil_append, Args.toList, bindL,
      Array.setIfInBounds_def, dite_eq_left (h _ List.mem_cons_self)]
  | _, _, (_, _) :: _, [], .nil, _ => rfl

end

/-! ## Straight-line code -/

/-- Run in the store `env`, the instructions `code` return the values `vals` at once, each
bound before the next runs, and leave the store `env'`. -/
inductive RunsTo : Array (Dyn M.interp) → List (LInsn M) → List (Dyn M.interp) →
    Array (Dyn M.interp) → Prop
  | nil {env : Array (Dyn M.interp)} : RunsTo env [] [] env
  | cons {env env' : Array (Dyn M.interp)} {i : LInsn M} {code : List (LInsn M)}
      {x : Dyn M.interp} {vals : List (Dyn M.interp)} :
      Returns env i x → RunsTo (env.setIfInBounds i.dst x) code vals env' →
      RunsTo env (i :: code) (x :: vals) env'

/-- Instructions that return `vals` at once in every store that holds `env`, and define slots
that `env` does not have, run from a store that holds `env` to one that does. -/
theorem EnvRel.runsTo {env : Array (Dyn M.interp)} :
    ∀ {env₁ : Array (Dyn M.interp)} {code : List (LInsn M)} {vals : List (Dyn M.interp)},
      EnvRel env env₁ → (∀ env', EnvRel env env' → All₂ (Returns env') code vals) →
      (∀ i ∈ code, env.size ≤ i.dst) → ∃ env₂, RunsTo env₁ code vals env₂ ∧ EnvRel env env₂
  | env₁, [], vals, hE, hsel, _ => by
    obtain rfl : vals = [] := by cases hsel _ hE; rfl
    exact ⟨env₁, .nil, hE⟩
  | env₁, i :: code, vals, hE, hsel, hfr => by
    obtain ⟨v, vals, rfl⟩ : ∃ v vals₁, vals = v :: vals₁ := by
      cases hsel _ hE with
      | cons _ _ => exact ⟨_, _, rfl⟩
    have hr : Returns env₁ i v := by
      cases hsel _ hE with
      | cons h _ => exact h
    obtain ⟨env₂, hrun, hE₂⟩ := (hE.fresh (hfr i List.mem_cons_self) v).runsTo
      (fun env' hE' => by
        cases hsel env' hE' with
        | cons _ h => exact h)
      fun j hj => hfr j (List.mem_cons_of_mem _ hj)
    exact ⟨env₂, .cons hr hrun, hE₂⟩

/-- Instructions that run keep the slots that they do not define. -/
private theorem RunsTo.keeps {env env' : Array (Dyn M.interp)} {code : List (LInsn M)}
    {vals : List (Dyn M.interp)} (h : RunsTo env code vals env') {u : Nat}
    (hu : u ∉ code.map LInsn.dst) : env'[u]? = env[u]? := by
  induction h with
  | nil => rfl
  | cons _ _ ih =>
    exact (ih fun hm => hu (List.mem_cons_of_mem _ hm)).trans
      (Array.getElem?_setIfInBounds_ne fun (e : _ = u) => hu (e ▸ List.mem_cons_self))

/-- Instructions that run and define each slot once leave, in the slots that they define, the
values that they return, where these are slots of the store. -/
theorem RunsTo.holds {env env' : Array (Dyn M.interp)} {code : List (LInsn M)}
    {vals : List (Dyn M.interp)} (h : RunsTo env code vals env')
    (hnd : (code.map LInsn.dst).Nodup) (hb : ∀ u ∈ code.map LInsn.dst, u < env'.size) :
    All₂ (fun u v => env'[u]? = some v) (code.map LInsn.dst) vals := by
  induction h with
  | nil => exact .nil
  | cons _ h ih =>
    obtain ⟨hu, hnd⟩ := List.nodup_cons.mp hnd
    refine .cons ?_ (ih hnd fun u hu => hb u (List.mem_cons_of_mem _ hu))
    have e := h.keeps hu
    rw [Array.getElem?_setIfInBounds_self, Array.getElem?_eq_getElem (hb _ List.mem_cons_self)] at e
    split at e
    · exact (Array.getElem?_eq_getElem (hb _ List.mem_cons_self)).trans e
    · exact nomatch e

/-! ## Exits and edges -/

/-- An exit picks one of the successors. -/
theorem armOf_lt {I : Ty → Type} : ∀ {ps : List (List Ty)} (e : Exit I ps), armOf e < ps.length
  | _, .here _ => Nat.succ_pos _
  | _, .there e => Nat.succ_lt_succ (armOf_lt e)

/-- An exit along a successor without a payload passes no value. -/
theorem valsOf_nil {I : Ty → Type} :
    ∀ {ps : List (List Ty)} (e : Exit I ps), ps[armOf e]? = some [] → valsOf e = []
  | _, .here .nil, _ => rfl
  | _, .here (.cons _ _), h => nomatch h
  | _, .there e, h => valsOf_nil e h

/-- The lowered successors, at the position an exit picks. -/
theorem SitesLow.get {n : Nat} {β : Nat → Nat} {g₁ : LBody M} :
    ∀ {ps : List (List Ty)} {ss ss₁ : List LSite}, SitesLow n β g₁ ps ss ss₁ →
      ∀ e : Exit M.interp ps, ∃ p s s₁, ps[armOf e]? = some p ∧ ss[armOf e]? = some s ∧
        ss₁[armOf e]? = some s₁ ∧ SiteLow n β g₁ p s s₁
  | _, _, _, .cons h _, .here _ => ⟨_, _, _, rfl, rfl, rfl, h⟩
  | _, _, _, .cons _ hs, .there e => hs.get e

/-- Where an edge to `tgt` from frame `f` that passes the values `ds` leads: a frame of the body
at the block, with its parameters bound to `ds`, or out of the body with the one value. -/
def Lands (f : Frame M) (tgt : LTarget) (ds : List (Dyn M.interp)) : Next M → Prop
  | .frame F => ∃ i b, tgt = .block i ∧ f.func.blocks[i]? = some b ∧ F.func = f.func ∧
      F.code = b.insns ∧ F.term = b.term ∧ F.env = bindL f.env b.params ds
  | .leave v => tgt = .exit ∧ ds = [v]

/-- Taking an edge lands where its arguments' values and then its payload's lead. -/
private theorem take_lands (f : Frame M) :
    ∀ (s : LSite) {ts : List Ty} (xs : Args M.interp ts) (h : CanTake f s ts),
      Lands f s.target (lookupAll f.env s.args h.1 ++ Args.toList xs) (take f s xs h)
  | ⟨.block i, _⟩, _, _, h =>
    ⟨i, _, rfl, Array.getElem?_eq_getElem h.2.1, rfl, rfl, rfl, bindSite_eq ..⟩
  | ⟨.exit, _⟩, _, xs, h => ⟨rfl, single_spec _ xs h.2⟩

/-- **Leaving along the successor an exit picks** lands where that successor's arguments' values
and then the exit's values lead. -/
theorem exitTo_lands (f : Frame M) :
    ∀ {ps : List (List Ty)} (ss : List LSite) (e : Exit M.interp ps) (h : Exec.SitesOK f ss ps),
      ∃ s, ss[armOf e]? = some s ∧ ∃ hb : AllBound f.env s.args,
        Lands f s.target (lookupAll f.env s.args hb ++ valsOf e) (exitTo f ss e h)
  | _, s :: _, .here xs, _ => ⟨s, rfl, _, take_lands f s xs _⟩
  | _, _ :: ss, .there e, _ => exitTo_lands f ss e _
  | _, [], .here _, h => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)
  | _, [], .there _, h => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)

/-- The pending transition of a transfer. -/
def modeOf : Next M → Mode M
  | .frame g => .jump g
  | .leave v => .ret v

/-! ## Steps -/

section
variable {m : LModule M} {B : Ty} (hwf : WF m) (oracle : Nat → Nat)

omit hwf in
/-- A transfer leaves the frames and the data, with the transfer pending. -/
theorem transfer_eq (c : Core M) (n : Next M) (hn : NextOK m c.top n)
    (hK : ContsOK m B c.top.func.ret c.conts) (d : Nat) (ev : Event) :
    ∃ h, transfer c n hn hK d ev = .next ev ⟨c, modeOf n, d, ()⟩ h := by
  cases n <;> exact ⟨_, rfl⟩

/-- **A pending edge**: one step enters the frame it leads to. -/
theorem stepAt_jump {c : Core M} {to : Frame M} {d : Nat}
    (h : StateOK m B ⟨c, .jump to, d, ()⟩) :
    stepAt hwf oracle ⟨⟨c, .jump to, d, ()⟩, h⟩ =
      .running ⟨⟨{ c with top := to }, .exec, d, ()⟩, h⟩ :=
  rfl

/-- **A terminator that exits at once**: one step leaves the transfer along the successor it
picks pending. -/
theorem stepAt_exits {c : Core M} {d : Nat} (h : StateOK m B ⟨c, .exec, d, ()⟩)
    (hc : c.top.code = []) {ps : List (List Ty)} {succs : List LSite} {e : Exit M.interp ps}
    (he : Exits c.top.env c.top.term ps succs e) :
    ∃ hS h₁, stepAt hwf oracle ⟨⟨c, .exec, d, ()⟩, h⟩ =
      .running ⟨⟨c, modeOf (exitTo c.top succs e hS), d, ()⟩, h₁⟩ := by
  obtain ⟨⟨func, code, term, env, blk, pc, fits⟩, conts, heap, world⟩ := c
  simp only at hc he
  subst hc
  cases he with
  | case ht =>
    simp only [stepAt, step, exec, execCode, execTerm]
    obtain ⟨h₁, he₁⟩ := transfer_eq (B := B) _ _ (h.caseNext hwf rfl rfl _ (h.termReady rfl rfl).2)
      h.2 d (.instr (Frame.pos ⟨func, [], _, env, blk, pc, fits⟩))
    exact ⟨_, h₁, congrArg StepR.config he₁⟩
  | sem ht hx =>
    simp only [stepAt, step, exec, execCode, execTerm]
    rw [hx]
    simp only [settle]
    obtain ⟨h₁, he₁⟩ := transfer_eq (B := B) _ _
      ((h.termInst (m := m) rfl rfl).exit hwf e) h.2 d
      (.instr (Frame.pos ⟨func, [], _, env, blk, pc, fits⟩))
    exact ⟨_, h₁, congrArg StepR.config he₁⟩

/-- **An instruction that returns at once**: one step binds its value and continues. -/
theorem stepAt_returns {c : Core M} {d : Nat} (h : StateOK m B ⟨c, .exec, d, ()⟩) {i : LInsn M}
    {code : List (LInsn M)} (hc : c.top.code = i :: code) {x : Dyn M.interp}
    (hr : Returns c.top.env i x) :
    ∃ top h₁, stepAt hwf oracle ⟨⟨c, .exec, d, ()⟩, h⟩ =
        .running ⟨⟨{ c with top := top }, .exec, d, ()⟩, h₁⟩ ∧
      top.func = c.top.func ∧ top.code = code ∧ top.term = c.top.term ∧
      top.env = c.top.env.setIfInBounds i.dst x := by
  obtain ⟨⟨func, code₀, term, env, blk, pc, fits⟩, conts, heap, world⟩ := c
  simp only at hc hr
  subst hc
  have hd : i.dst < env.size := Nat.lt_of_lt_of_le (CoreOK.dst_lt h rfl) fits
  cases hr with
  | pure ht =>
    simp only [stepAt, step, exec, execCode, Core.next, StepR.config]
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    simp only [LInsn.dst] at hd ⊢
    rw [Array.setIfInBounds_def, dite_eq_left hd]
  | sem ht hx =>
    simp only [stepAt, step, exec, execCode]
    rw [hx]
    simp only [settle, StepR.config, Frame.bind, resDyn]
    refine ⟨_, _, rfl, rfl, rfl, rfl, ?_⟩
    simp only [LInsn.dst] at hd ⊢
    rw [Array.setIfInBounds_def, dite_eq_left hd]

/-- One step and then silent steps, none of which changes the world or the choices. -/
def SilentPlus (c c₂ : Cfg m B) : Prop :=
  ∃ c₁, stepAt hwf oracle c = .running c₁ ∧ c₁.1.core.world = c.1.core.world ∧
    c₁.1.drawn = c.1.drawn ∧ Silent hwf oracle c₁ c₂

variable {hwf oracle}

/-- One or more silent steps are silent steps. -/
theorem SilentPlus.silent {c c₂ : Cfg m B} (h : SilentPlus hwf oracle c c₂) :
    Silent hwf oracle c c₂ :=
  let ⟨_, hs, hw, hd, hq⟩ := h
  .step hs hw hd hq

/-- One or more silent steps, then silent steps. -/
theorem SilentPlus.trans {c c₁ c₂ : Cfg m B} (h : SilentPlus hwf oracle c c₁)
    (h₁ : Silent hwf oracle c₁ c₂) : SilentPlus hwf oracle c c₂ :=
  let ⟨_, hs, hw, hd, hq⟩ := h
  ⟨_, hs, hw, hd, hq.trans h₁⟩

variable (hwf oracle)

/-- **Straight-line code**: instructions that return at once and then a terminator that exits at
once are silent steps, which bind the instructions' values and leave the transfer along the
successor the exit picks pending. -/
theorem run_straight {env env' : Array (Dyn M.interp)} {code : List (LInsn M)}
    {vals : List (Dyn M.interp)} (hrun : RunsTo env code vals env') {d : Nat}
    {ps : List (List Ty)} {succs : List LSite} {e : Exit M.interp ps} :
    ∀ {c : Core M} (h : StateOK m B ⟨c, .exec, d, ()⟩), c.top.code = code → c.top.env = env →
      Exits env' c.top.term ps succs e →
      ∃ top hS h₁, SilentPlus hwf oracle ⟨⟨c, .exec, d, ()⟩, h⟩
          ⟨⟨{ c with top := top }, modeOf (exitTo top succs e hS), d, ()⟩, h₁⟩ ∧
        top.func = c.top.func ∧ top.env = env' := by
  induction hrun with
  | nil =>
    intro c h hc he hex
    obtain ⟨hS, h₁, hstep⟩ := stepAt_exits hwf oracle h hc (he ▸ hex)
    exact ⟨c.top, hS, h₁, ⟨_, hstep, rfl, rfl, .refl _⟩, rfl, he⟩
  | cons hr _ ih =>
    intro c h hc he hex
    obtain ⟨top, h₁, hstep, htf, htc, htt, hte⟩ := stepAt_returns hwf oracle h hc (he ▸ hr)
    obtain ⟨top₂, hS, h₂, hsp, htf₂, hte₂⟩ :=
      ih (c := { c with top := top }) h₁ htc (he ▸ hte) (htt ▸ hex)
    exact ⟨top₂, hS, h₂, ⟨_, hstep, rfl, rfl, hsp.silent⟩, htf₂.trans htf, hte₂⟩

end

end

end Strata.Dyn.CasesSound
