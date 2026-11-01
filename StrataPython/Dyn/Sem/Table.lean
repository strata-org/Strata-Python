/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Rules.Gaps
public import StrataPython.Dyn.Sem.RuleTheorems
public import StrataDyn.Exec.CertModelProps
public import StrataDyn.Exec.EffectsProps
public import StrataDyn.Exec.CertTactic
public import StrataPython.Dyn.Sem.Rules.Values
public import StrataPython.Dyn.Sem.Rules.Ops
public import StrataPython.Dyn.Sem.Rules.Containers
public import StrataPython.Dyn.Sem.Rules.Globals
public meta import StrataPython.Dyn.Env
public meta import StrataDyn.DDM

set_option autoImplicit false

/-!
# Python's table

`PySem` is the table of every rule of Python's environment, over the world `World`.
`#py_rule_theorems` proves of each rule that it stays within its operation's declared effect
(`PySem.ok.<op>`), and gives the certificate of it at Python's accounts (`PySem.cert.<op>`):
the rule reaches only the cells and closures it is given.  The declared effects are those of
`Py.env`'s instructions (`pyDeclaredEffect`).

Key definitions and theorems:
* `pyAcct` and `pyAccounts`, where the machine's values and Python's world hold refs, and
  `pyCertLaws`, which says that their spec has the laws that the rule monad relies on;
* `ImplOK.cert`, which turns a rule's `ImplOK` into its certificate;
* `PySem.okOf.py.globalCell` and `PySem.certOf.py.globalCell`, the own proofs of the rule written
  directly in `Sem`;
* `PySem.certified`: Python's table is certified (`Model.Certified`), which ref-to-reg's soundness
  theorem takes.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

public section
#dyn_sem_table PySem for Py (world := World)
end

#dyn_coverage Py

open Strata.Dyn.Exec.Effects

@[expose] public section

open Lean Elab Command in
/-- `#py_declared_effects` defines `pyDeclaredEffect (op : String) : Level`, the declared effect
of each instruction `py.name` of `Py.env`, read from the environment when the command runs: one
string arm per instruction that is not `writes`, so that a proof computes an effect by `rfl`. -/
elab "#py_declared_effects" : command => do
  let arms := Py.names.filterMap fun n =>
    match Py.env.get? n with
    | some (.insn (isig := σ) _) =>
      let t := Strata.Dyn.ToDDM.nameText n
      let lvl : Option Lean.Name := match σ.effect with
        | .pure => some `pure | .reads => some `reads | .calls => some `calls | .writes => none
      if t.startsWith "py." then lvl.map (t, ·) else none
    | _ => none
  let alts ← arms.toArray.mapM fun (t, l) =>
    `(Lean.Parser.Term.matchAltExpr| | $(Syntax.mkStrLit t) => $(mkIdent (`Strata.Dyn.Exec.Effects.Level ++ l)))
  elabCommand (← `(command|
    /-- The declared effect of the operation `op` of `Py.env`, written `py.name`: `writes` if no
    instruction of that name declares another. -/
    def $(mkIdent `pyDeclaredEffect) (op : String) : Strata.Dyn.Exec.Effects.Level :=
      match op with $alts:matchAlt* | _ => .writes))

#py_declared_effects

/-- The tags of `PyLang` in `PySem`. -/
def pyTags (σ : Type) [Store σ] : @Tags σ _ ⟨PySem.interp σ⟩ :=
  letI : Decode σ := ⟨PySem.interp σ⟩
  ⟨⟨PySem.T.py.Value, rfl⟩, ⟨Ty.ref PySem.T.py.Value, rfl⟩,
    ⟨PySem.T.base.Except PySem.T.py.Value PySem.T.py.Value, rfl⟩⟩

/-- Where the refs of a value of Python's tag `t` are: heads `0` and `1` are a ref's and a
closure's, `7` is Base's `Sequence` and `8` its `Except`; every other head, `py.Value` and
`py.Completion` included, holds no ref. -/
def pyAcct : (t : Ty) → PySem.interp Run t → List Loc
  | .app 0 [a], x => [.cell x.loc a]
  | .app 1 [.list ts, r], f =>
    if (PySem.model.at.fnOf (ts := ts) (r := r) f).captured = 0 then []
    else [.caps (PySem.model.at.fnOf (ts := ts) (r := r) f).captured]
  | .app 7 [a], xs => xs.toList.flatMap (pyAcct a)
  | .app 8 [e, a], x => match x with
    | .error v => pyAcct e v
    | .ok v => pyAcct a v
  | _, _ => []
termination_by structural t => t

/-- **Python's accounts**: a value's refs by `pyAcct`, the world's by the `Refs` instances of its
store and module table, and no ref in a rule's state. -/
def pyAccounts : Accounts PySem.model.at where
  acct := pyAcct
  world w :=
    letI : Decode Run := ⟨PySem.interp Run⟩
    Refs.refs (σ := Run) w.store ++ @Refs.refs Run _ _ (modulesRefs (pyTags Run).value) w.modules
  st _ _ := []
  ref t x := by simp only [pyAcct, RunModel.locOf, cast_eq]
  fn ts r x := by simp only [pyAcct]
  unit := rfl
  bool _ := rfl
  int _ := rfl
  float _ := rfl
  str _ := rfl

end

@[expose] public section

/-- A `Value` of `PySem` holds no ref: its account is empty. -/
theorem pyAcct_value (v : PySem.interp Run PySem.T.py.Value) : pyAcct PySem.T.py.Value v = [] := rfl

/-- A `Value` is valid in every typing. -/
theorem valOK_value (G : Typing) (v : PySem.interp Run PySem.T.py.Value) :
    pyAccounts.ValOK G PySem.T.py.Value v := by
  show G.AllValid (pyAcct PySem.T.py.Value v)
  rw [pyAcct_value]
  exact Typing.allValid_nil G

/-- **Python's accounts have the laws that the rule monad relies on**, at every operation shape:
a `Value` holds no ref, a call's closure and a new cell are the engine's, and each part of the
world holds its refs in the world's account. -/
theorem pyCertLaws (rs : List (List Ty × Ty)) (ps : List (List Ty)) {St : Type}
    (StOK : Typing → St → Prop) :
    letI : Decode Run := ⟨PySem.interp Run⟩
    PyCertLaws rs (pyTags Run) (pyAccounts.spec rs ps StOK) := by
  letI : Decode Run := ⟨PySem.interp Run⟩
  letI : TagOf Run Value := (pyTags Run).value
  letI : Refs Run (Modules Run) := modulesRefs (pyTags Run).value
  letI : SigOf Run [Value, Value] (Except Value Value) :=
    @funcSig Run _ _ (BEff Run rs) (bInst rs (pyTags Run))
  have hl : ∀ {α β : Type} (e : α = β) (c : Ref Run α), (cast (congrArg (Ref Run) e) c).loc = c.loc := by
    intro _ _ e c; subst e; rfl
  have hexc : ∀ (G : Typing) (x : Except Value Value), RefsOK (σ := Run) G x := by
    intro _ x; cases x <;> exact refsOK_nil rfl
  have hargs : ∀ (G : Typing)
      (p : Payload ([PySem.T.py.Value, PySem.T.py.Value].map (PySem.interp Run))),
      pyAccounts.ArgsOK G (Args.ofPayload [PySem.T.py.Value, PySem.T.py.Value] p) :=
    fun G ⟨x, y⟩ => ⟨valOK_value G x, valOK_value G y, trivial⟩
  have hworld : ∀ (G : Typing) (w : World Run), (pyAccounts.spec rs ps StOK).World G w ↔
      RefsOK (σ := Run) G w.store ∧ RefsOK (σ := Run) G w.modules := fun G w =>
    Typing.allValid_append
  refine ⟨⟨fun _ _ _ => ?_, fun G v o h => ?_, fun _ _ h => h, fun _ _ _ _ => refsOK_nil rfl,
    fun _ _ _ h _ => ⟨h, ?_⟩, fun _ _ _ h _ => ⟨h, fun _ _ => ?_⟩⟩,
    ?_,
    ⟨fun G w h => ((hworld G w).mp h).1, fun G w p h hp => (hworld G _).mpr ⟨hp, ((hworld G w).mp h).2⟩⟩,
    ⟨fun G w h => ((hworld G w).mp h).2, fun G w p h hp => (hworld G _).mpr ⟨((hworld G w).mp h).1, hp⟩⟩,
    ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩, ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩,
    ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩, ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩⟩
  · exact valOK_value _ _
  · show G.Valid (cast (congrArg (Ref Run) (pyTags Run).value.ok) o).loc _
    rw [hl (pyTags Run).value.ok]
    exact h
  · exact valOK_value _ _
  · exact valOK_value _ _
  · exact ⟨fun G f a hf _ => ⟨refsOK_fn.mp hf, hargs G _⟩, fun G _ _ _ _ => hexc G _⟩

/-- `ImplOK` gives `Accounts.ImplOK` at `pyAccounts`, for a state validity that holds of every
state, when the rule's results and exits hold no ref. -/
theorem ImplOK.implOK {e : Level} {o : OpImpl PySem.interp (fun σ _ => World σ)}
    (h : ImplOK PySem.interp pyTags e o) (targs : Vector Ty o.typeArgc)
    (hres : ∀ (G : Typing) x, pyAccounts.ResOK G (o.shape targs).ret x)
    (hexit : ∀ (G : Typing) (x : Exit (PySem.interp Run) (o.shape targs).succs),
      pyAccounts.ExitOK G x)
    (StOK : Typing → o.St Run targs → Prop) (hSt : ∀ G s, StOK G s) :
    pyAccounts.ImplOK StOK (o.shape targs) (o.fn Run targs) := by
  letI : Decode Run := ⟨PySem.interp Run⟩
  have hX : ∀ G (x : Out (PySem.interp Run) (o.shape targs).succs (o.St Run targs)),
      pyAccounts.OutOK StOK G x := fun G x => match x with
    | .exit x => hexit G x
    | .again s => hSt G s
  have h' := h Run targs (pyAccounts.spec _ _ StOK) (pyCertLaws _ _ StOK) hX
    (fun G x => pyAccounts.ResOK G _ x) hres
  revert h'
  generalize o.fn Run targs = impl
  cases impl with
  | pure _ => intro h; exact h.elim
  | sem f => exact fun hf G =>
      pyAccounts.fnOK_of_fnAll (fun _ => pyAccounts.varOK_of_varAll (fun _ ht => ht.1 G) G) G hf
  | loop f g => exact fun ⟨hf, hg⟩ => ⟨fun G => pyAccounts.fnOK_of_fnAll
      (fun _ => pyAccounts.varOK_of_varAll (fun _ ht => ht.1 G) G) G hf,
    fun G => pyAccounts.fnOK_of_fnAll
      (fun _ => pyAccounts.varOK_of_varAll (fun _ ht st _ => (ht st).1 G) G) G hg⟩

/-- **A rule's theorem gives its certificate at Python's model**: `ImplOK` gives
`Model.OpCertified` at every position, when the rule's results and exits hold no ref (`hres`,
`hexit`); its state's account is empty. -/
theorem ImplOK.cert {e : Level} {o : OpImpl PySem.interp (fun σ _ => World σ)}
    (h : ImplOK PySem.interp pyTags e o)
    (hres : ∀ targs (G : Typing) x, pyAccounts.ResOK G (o.shape targs).ret x)
    (hexit : ∀ targs (G : Typing) (x : Exit (PySem.interp Run) (o.shape targs).succs),
      pyAccounts.ExitOK G x)
    (k : Nat) : PySem.model.OpCertified pyAccounts k o := fun targs =>
  h.implOK targs (hres targs) (hexit targs) _ fun G _ _ => Typing.allValid_nil G

/-! ## The rules written in `Sem` directly -/

section
variable {σ : Type} [Store σ] [Decode σ] {rs : List (List Ty × Ty)} {ps : List (List Ty)}
  {S : Type}

/-- **`globalCell` satisfies every spec that has the laws**, with its result a valid cell: the cell
that the module table holds, or the new one, which it adds to the table. -/
theorem globalCell_sat (tg : Tags σ) (V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S))
    (hc : PyCertLaws rs tg V) (module name : String) (Q : Typing → Ref σ Value → Prop)
    (hQ : ∀ g (r : Ref σ Value), g.Valid r.loc tg.value.tag → Q g r) (g : Typing) :
    V.Sat Q g (@Rules.globalCell σ _ _ (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) module name) := by
  letI : Refs σ (Modules σ) := modulesRefs tg.value
  letI : TagOf σ Value := tg.value
  dsimp only [Rules.globalCell, bind, Sem.bind, Sem.bindAfter, pure, newRef, getThe,
      MonadStateOf.get, Sem.instMonadStateOf]
  refine Spec.sat_update.mpr fun w hw => ⟨hw, ?_⟩
  dsimp only
  split
  · rename_i r hr
    exact Spec.sat_ret.mpr (hQ _ _ (valid_of_cell? tg.value (hc.modules.1 g w hw) hr))
  · simp only [modifyGetThe_eq]
    refine Spec.sat_vis.mpr ⟨hc.heap.1 g _ (refsOK_nil rfl), fun g₁ _ o ho => ?_⟩
    have hv := hc.heap.2 g₁ _ o ho
    refine Spec.Sat.bind (Spec.sat_update.mpr fun w₁ hw₁ => ⟨hc.store.2 g₁ w₁ _ hw₁ ?_, ?_⟩)
    · split
      · intro l hl
        rw [refs_alloc, show Refs.refs (σ := σ) (Rules.moduleObj (σ := σ) module) = [] from rfl,
          List.append_nil] at hl
        exact hc.store.1 g₁ w₁ hw₁ l hl
      · exact hc.store.1 g₁ w₁ hw₁
    · refine Spec.sat_ret.mpr (Spec.Sat.bind (Spec.sat_update.mpr fun w₂ hw₂ =>
        ⟨hc.modules.2 g₁ w₂ _ hw₂ (refsOK_withCell tg.value _ _ _ (hc.modules.1 g₁ w₂ hw₂) hv), ?_⟩))
      exact Spec.sat_ret.mpr (Spec.sat_ret.mpr (hQ _ _ hv))

end

/-- `globalCell`'s certificate at Python's model: its result is a valid cell. -/
theorem PySem.certOf.py.globalCell (k : Nat) :
    PySem.model.OpCertified pyAccounts k PySem.impl.py.globalCell := by
  intro targs G
  dsimp only [PySem.impl.py.globalCell, Accounts.ImplOK, Accounts.FnOK, Accounts.VarOK]
  intro a0 _ a1 _
  letI : Decode Run := ⟨PySem.interp Run⟩
  exact globalCell_sat (pyTags Run) _ (pyCertLaws _ _ _) a0 a1 _
    (fun g r h => by
      show g.AllValid [Loc.cell r.loc PySem.T.py.Value]
      exact Typing.allValid_singleton.mpr h) G

/-- `globalCell` stays within its declared effect, `pure`: its result is the cell that the world
holds or that it makes, and it changes only the module table and, for a module's first global,
the store. -/
theorem PySem.okOf.py.globalCell :
    ImplWithin PySem.interp (pyDeclaredEffect "py.globalCell") PySem.impl.py.globalCell := by
  intro σ _ _
  letI : Decode σ := ⟨PySem.interp σ⟩
  intro a0 a1
  refine .inl ⟨_, rfl, fun _ w₁ w₂ h => ?_, fun w N => ?_⟩
  · have hcell :
        (HasPart.get w₁ : Modules σ).cell? a0 a1 = (HasPart.get w₂ : Modules σ).cell? a0 a1 :=
      h.2.2.2.2 a0 a1
    have hnew : ((HasPart.get w₁ : Modules σ).map[a0]?).isNone =
        ((HasPart.get w₂ : Modules σ).map[a0]?).isNone := by
      have := congrArg Option.isNone (h.2.2.2.1 a0)
      simp only [Option.isNone_map] at this
      exact this
    dsimp only [Sem.bind]
    rw [hcell, hnew]
  · dsimp only [bind, Sem.bind, Sem.bindAfter, Rules.globalCell, pure, newRef, getThe,
      MonadStateOf.get, Sem.instMonadStateOf]
    change Within spec (startOf w.store) .pure _ N _
    split
    · trivial
    · simp only [modifyGetThe_eq]
      refine fun o => ⟨fun _ w₂ => ?_, fun _ w₂ w₃ h => ⟨?_, ?_⟩, fun w₂ =>
        ⟨fun _ w₃ => ?_, fun _ w₃ w₄ h => ⟨?_, rfl⟩, fun _ => trivial⟩⟩
      · change Same (startOf w.store) w₂ { w₂ with store :=
          if ((HasPart.get w : Modules σ).map[a0]?).isNone = true then
            (w₂.store.alloc (Rules.moduleObj a0)).1 else w₂.store }
        split
        · exact same_allocObj _ _ w₂
        · exact ⟨Nat.le_refl _, fun _ _ _ h => h, Modules.Extends.refl _, rfl, rfl⟩
      · change ImmEq (startOf w.store)
          { w₂ with store := if ((HasPart.get w : Modules σ).map[a0]?).isNone = true then
            (w₂.store.alloc (Rules.moduleObj a0)).1 else w₂.store }
          { w₃ with store := if ((HasPart.get w : Modules σ).map[a0]?).isNone = true then
            (w₃.store.alloc (Rules.moduleObj a0)).1 else w₃.store }
        split
        · exact immEq_allocObj _ h
        · exact h
      · have hs : (HasPart.get w₂ : ObjStore σ).size = (HasPart.get w₃ : ObjStore σ).size := h.1
        dsimp only
        rw [hs]
        rfl
      · exact ⟨Nat.le_refl _, fun _ _ _ h => h, Modules.extends_withCell _ _ _ _ _, rfl, rfl⟩
      · exact immEq_withCell h _ _ _ _
end

public section
#py_rule_theorems PySem for Py (effects := pyDeclaredEffect) (tags := pyTags)
  (accounts := pyAccounts)
end

public section

set_option maxRecDepth 20000 in
/-- **Python's table is certified**: each of its rules reaches only the cells and closures it is
given, at Python's accounts.  A rule of `#py_rule_theorems` has its certificate `PySem.cert.<op>`;
`dyn_cert` proves the other wrappers: the pure ones and Base's. -/
theorem PySem.certified : PySem.model.Certified pyAccounts := by
  apply Model.certified_of_ops
  show PySem.model.OpsCertified pyAccounts 0 PySem.ops.toList
  simp (config := { zeta := true }) only [PySem.ops, List.toList_toArray, Model.OpsCertified]
  repeat' apply And.intro
  all_goals first | trivial | py_op_cert | dyn_cert [pyAccounts, pyAcct]

end

end StrataPython.Dyn.Sem
