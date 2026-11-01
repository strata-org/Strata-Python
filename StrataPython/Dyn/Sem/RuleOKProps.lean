/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.RuleOK
public import StrataDyn.Exec.EffectsProps

set_option autoImplicit false

/-!
# Properties of `RuleOK`

Key theorems: `runRule_ok`, `runTotal_ok`, `runRuleFree_ok`, `runTotalFree_ok` and
`runRuleIf_ok`, which give `RuleOK` for every rule that runs a `PyM` computation; `RuleOK.lift`,
which lifts `RuleOK` to a higher effect; and `ImplOK.within`, which gives `ImplWithin` from
`ImplOK`, at the spec `pySpec`, which has the laws (`pySpec_laws`).

The definitions are in `RuleOK.lean`: `RuleOK`, with `StartWithin` and `AnyStart`, `ImplOK`,
`ImplWithin` and `pySpec`.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec Strata.Dyn.Exec.Effects

@[expose] public section

section
variable {σ : Type} [Store σ] [Decode σ] {rs : List (List Ty × Ty)} {ps : List (List Ty)}
  {S R : Type}

variable {V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)}

/-- A result, as a continuation, when `Q` holds of every result. -/
private theorem contOK_ret {e : Level} {α : Type} (s : Start) {Q : Typing → α → Prop}
    (hQ : ∀ g a, Q g a) (a : α) :
    ContOK V s e Q (fun _ _ => True) (.ret a) :=
  ⟨fun g => Spec.sat_ret.mpr (hQ g a), fun _ => trivial⟩

/-- A jump, as a continuation, when `V` allows every exit. -/
private theorem contOK_jump {e : Level} {α : Type} (s : Start) {Q : Typing → α → Prop}
    (hX : ∀ g x, V.Exit g x) (x : Out (Dec σ) ps S) :
    ContOK V s e Q (fun _ _ => True) (.stop (.jump x)) :=
  ⟨fun g => Spec.sat_jump.mpr (hX g x), fun _ => trivial⟩

/-- A gap, as a continuation. -/
private theorem contOK_gap {e : Level} {α : Type} (s : Start) {Q : Typing → α → Prop}
    (msg : String) :
    ContOK (rs := rs) (ps := ps) (S := S) V s e Q (fun _ _ => True) (semanticGap msg) :=
  ⟨fun _ => Spec.sat_fault, fun _ => trivial⟩

/-- The handles of a rule without regions. -/
private theorem handlesOK_nil (s : Start) :
    HandlesOK (rs := rs) (ps := ps) (S := S) V s #[] := fun _ h => absurd h (Nat.not_lt_zero _)

/-- A rule that reads the start of the store and runs `k` from it satisfies `V` from every
typing, and is within `e` from the world at its start. -/
private theorem ruleOK_start {e : Level} {Q : Typing → R → Prop}
    (k : Start → BTree σ rs ps S R) (hk : ∀ s, ContOK V s e Q (fun _ _ => True) (k s)) :
    RuleOK V Q e (do let st ← getThe (ObjStore σ); k (startOf st)) := by
  refine ⟨fun g => Spec.sat_update.mpr fun w hw => ⟨hw, (hk _).1 g⟩,
    .inl ⟨_, rfl, fun _ w₁ w₂ h => ?_, fun w N => (hk _).2 N⟩⟩
  dsimp only [bind, Sem.bind]
  have hs : startOf (HasPart.get w₁ : ObjStore σ) = startOf (HasPart.get w₂ : ObjStore σ) := by
    simp only [startOf]; exact congrArg _ h.1
  rw [hs]

/-- **A rule that runs a `PyM` computation satisfies `V` and is within its effect**, for every `V`
with the laws that allows every exit, and every `Q` that holds of every result. -/
theorem runRule_ok {e : Level} {fr : Bool} {α : Type} (m : PyM σ e fr α) (tg : Tags σ)
    (hc : PyCertLaws rs tg V) (Q : Typing → α → Prop) (hQ : ∀ g a, Q g a)
    (hX : ∀ g x, V.Exit g x) (err : Target (Out (Dec σ) ps S) [Value]) :
    RuleOK V Q e
      (@runRule σ _ _ (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) e α fr err #[] m) :=
  ruleOK_start _ fun s => m.2.1 rs ps S tg V hc s #[] (handlesOK_nil s) e (Nat.le_refl _) Q _
    pure (jump err) (contOK_ret s hQ) (fun _ => contOK_jump s hX _)

/-- **A rule of an operation that can't raise, that runs a `PyM` computation, satisfies `V` and
is within its effect**, for every `V` with the laws, and every `Q` that holds of every result. -/
theorem runTotal_ok {e : Level} {fr : Bool} {α : Type} (op : String) (m : PyM σ e fr α)
    (tg : Tags σ) (hc : PyCertLaws rs tg V) (Q : Typing → α → Prop) (hQ : ∀ g a, Q g a) :
    RuleOK V Q e
      (@runTotal σ _ _ (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) e α fr op #[] m) :=
  ruleOK_start _ fun s => m.2.1 rs ps S tg V hc s #[] (handlesOK_nil s) e (Nat.le_refl _) Q _
    pure (fun _ => semanticGap s!"an exception in an operation that can't raise: {op}")
    (contOK_ret s hQ) (fun _ => contOK_gap s _)

/-- A rule whose computation needs no start, from every start: what `StartFree` gives. -/
private theorem ruleOK_free {e : Level} {α : Type} {Q : Typing → R → Prop} (m : PyM σ e true α)
    (tg : Tags σ) (k : α → BTree σ rs ps S R) (ke : Value → BTree σ rs ps S R)
    (hm : ∀ s, ContOK V s e Q (fun _ _ => True)
      (@m.1 (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) #[] s _ k ke)) :
    RuleOK V Q e (@m.1 (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) #[] ⟨0⟩ _ k ke) := by
  refine ⟨(hm ⟨0⟩).1, .inr fun s N => ?_⟩
  have h2 : StartFree @m.1 := m.2.2 rfl
  unfold StartFree at h2
  rw [@h2 (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) #[] ⟨0⟩ s _ k ke]
  exact (hm s).2 N

/-- **A rule that runs a `PyM` computation that needs no start satisfies `V` and is within its
effect from every start**, under the hypotheses of `runRule_ok`. -/
theorem runRuleFree_ok {e : Level} {α : Type} (m : PyM σ e true α) (tg : Tags σ)
    (hc : PyCertLaws rs tg V) (Q : Typing → α → Prop) (hQ : ∀ g a, Q g a)
    (hX : ∀ g x, V.Exit g x) (err : Target (Out (Dec σ) ps S) [Value]) :
    RuleOK V Q e
      (@runRuleFree σ _ _ (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) e α err #[] m) :=
  ruleOK_free m tg _ _ fun s => m.2.1 rs ps S tg V hc s #[] (handlesOK_nil s) e (Nat.le_refl _)
    Q _ pure (jump err) (contOK_ret s hQ) (fun _ => contOK_jump s hX _)

/-- **A rule of an operation that can't raise, that runs a `PyM` computation that needs no
start, satisfies `V` and is within its effect from every start**, under the hypotheses of
`runTotal_ok`. -/
theorem runTotalFree_ok {e : Level} {α : Type} (op : String) (m : PyM σ e true α)
    (tg : Tags σ) (hc : PyCertLaws rs tg V) (Q : Typing → α → Prop) (hQ : ∀ g a, Q g a) :
    RuleOK V Q e
      (@runTotalFree σ _ _ (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) e α op #[] m) :=
  ruleOK_free m tg _ _ fun s => m.2.1 rs ps S tg V hc s #[] (handlesOK_nil s) e (Nat.le_refl _)
    Q _ pure (fun _ => semanticGap s!"an exception in an operation that can't raise: {op}")
    (contOK_ret s hQ) (fun _ => contOK_gap s _)

/-- **A rule that runs one of two `PyM` computations, chosen by a condition on its operands,
satisfies `V` and is within its effect**, as `runRule_ok` and `runRuleFree_ok` give for each. -/
theorem runRuleIf_ok {e : Level} {α : Type} (cond : Bool) (m : PyM σ e false α)
    (mFree : PyM σ e true α) (tg : Tags σ) (hc : PyCertLaws rs tg V) (Q : Typing → α → Prop)
    (hQ : ∀ g a, Q g a) (hX : ∀ g x, V.Exit g x) (err : Target (Out (Dec σ) ps S) [Value]) :
    RuleOK V Q e
      (@runRuleIf σ _ _ (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) e α cond err #[] m mFree) := by
  unfold runRuleIf
  split
  · exact runRule_ok m tg hc Q hQ hX err
  · exact runRuleFree_ok mFree tg hc Q hQ hX err

/-- `RuleOK` at a lower effect gives it at a higher one. -/
theorem RuleOK.lift {e e' : Level} {Q : Typing → R → Prop} {t : BTree σ rs ps S R}
    (he : e.le e') (h : RuleOK V Q e t) : RuleOK V Q e' t :=
  match h with
  | ⟨hS, .inl ⟨k, ht, hk, hw⟩⟩ =>
    ⟨hS, .inl ⟨k, ht, fun hp => hk (Level.eq_pure (hp ▸ he)), fun w N => Within.lift he (k w) (hw w N)⟩⟩
  | ⟨hS, .inr ha⟩ => ⟨hS, .inr fun s N => Within.lift he t (ha s N)⟩

end

section
variable {σ : Type} [Store σ] [Decode σ] {rs : List (List Ty × Ty)} {ps : List (List Ty)}
  {S : Type}

/-- `pySpec` has the laws. -/
theorem pySpec_laws (tg : Tags σ) : PyCertLaws rs tg (pySpec tg rs ps S) := by
  letI : TagOf σ Value := tg.value
  letI : Refs σ (Modules σ) := modulesRefs tg.value
  letI : SigOf σ [Value, Value] (Except Value Value) := @funcSig σ _ _ (BEff σ rs) (bInst rs tg)
  refine ⟨⟨fun _ _ _ => trivial, fun G v o h => ?_, fun _ _ _ => trivial,
    fun _ _ _ _ => refsOK_nil rfl, fun _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩,
    ⟨fun _ _ _ _ _ => trivial, fun G _ _ o _ => ?_⟩,
    ⟨fun _ _ h => h.1, fun _ _ _ h hp => ⟨hp, h.2⟩⟩, ⟨fun _ _ h => h.2, fun _ _ _ h hp => ⟨h.1, hp⟩⟩,
    ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩, ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩,
    ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩, ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩⟩
  · change G.Valid o.loc tg.value.tag at h
    have hl : ∀ {α β : Type} (e : α = β) (c : Ref σ α), (cast (congrArg (Ref σ) e) c).loc = c.loc := by
      intro _ _ e c; subst e; rfl
    show G.Valid (cast (congrArg (Ref σ) tg.value.ok) o).loc _
    rw [hl tg.value.ok]
    exact h
  · have hx : ∀ x : Except Value Value, RefsOK (σ := σ) G x := by
      intro x; cases x <;> exact refsOK_nil rfl
    exact hx _

end

/-- `ImplOK` gives `ImplWithin`: its `Within` half holds at `pySpec`. -/
theorem ImplOK.within {interp : Interp} {tags : (σ : Type) → [Store σ] → @Tags σ _ ⟨interp σ⟩}
    {e : Level} {o : OpImpl interp (fun σ _ => World σ)} (h : ImplOK interp tags e o) :
    ImplWithin interp e o := by
  intro σ _ targs
  letI : Decode σ := ⟨interp σ⟩
  have h' := h σ targs (pySpec (tags σ) _ _ _) (pySpec_laws (tags σ)) (fun _ _ => trivial)
    (fun _ _ => True) (fun _ _ => trivial)
  unfold ImplWithinAt
  revert h'
  generalize o.fn σ targs = impl
  cases impl with
  | pure _ => intro h; exact h.elim
  | sem f => exact FnAll.imp fun _ => VarAll.imp fun _ h => h.2
  | loop f g => exact fun ⟨h₁, h₂⟩ => ⟨FnAll.imp (fun _ => VarAll.imp fun _ h => h.2) h₁,
      FnAll.imp (fun _ => VarAll.imp fun _ h st => (h st).2) h₂⟩

end

end StrataPython.Dyn.Sem
