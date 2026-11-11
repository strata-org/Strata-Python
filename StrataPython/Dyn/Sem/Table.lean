/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Rules.Comprehensions
public import StrataPython.Dyn.Sem.RuleTheorems
public import StrataDyn.Exec.CertModelProps
public import StrataDyn.Exec.EffectsProps
public import StrataDyn.Exec.CertTactic
public import StrataPython.Dyn.Sem.Rules.Values
public import StrataPython.Dyn.Sem.Rules.Ops
public import StrataPython.Dyn.Sem.Rules.Containers
public import StrataPython.Dyn.Sem.Rules.Globals
public import StrataPython.Dyn.Sem.Rules.Closures
public import StrataPython.Dyn.Sem.Rules.Calls
public import StrataPython.Dyn.Sem.Rules.Attrs
public import StrataPython.Dyn.Sem.Rules.Exceptions
public import StrataPython.Dyn.Sem.Rules.Iter
public import StrataPython.Dyn.Sem.Rules.Strings
public import StrataPython.Dyn.Sem.Contracts.Locations
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
* `PySem.okOf.py.globalCell`, `PySem.certOf.py.globalCell`, `PySem.okOf.py.mkClosure` and
  `PySem.certOf.py.mkClosure`, the own proofs of the two rules written directly in `Sem`;
* `PySem.certified`: Python's table is certified (`Model.Certified`), which ref-to-reg's soundness
  theorem takes.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

public section
-- The compiler specializes every piece's step machines into `py.call`'s implementation, which
-- takes more than the default budget.
set_option maxHeartbeats 1000000 in
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

/-- The tags of Python's types whose values hold no ref: `Value` and the comprehensions'
accumulators. -/
def pyNoRef : List Ty := [PySem.T.py.Value, PySem.T.py.ListAcc, PySem.T.py.SetAcc, PySem.T.py.DictAcc]

/-- The tags of `PyLang` in `PySem`. -/
def pyTags (σ : Type) [Store σ] : @Tags σ _ ⟨PySem.interp σ⟩ :=
  letI : Decode σ := ⟨PySem.interp σ⟩
  ⟨⟨PySem.T.py.Value, rfl⟩, ⟨Ty.ref PySem.T.py.Value, rfl⟩,
    ⟨PySem.T.base.Except PySem.T.py.Value PySem.T.py.Value, rfl⟩, pyNoRef⟩

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

/-- The arguments of a region whose parameters all have one of the tags of `pyNoRef` hold no ref,
so they are valid in every typing. -/
theorem argsOK_noRef (G : Typing) : {ts : List Ty} → (a : Args (PySem.interp Run) ts) →
    (∀ t ∈ ts, t ∈ pyNoRef) → pyAccounts.ArgsOK G a
  | [], .nil, _ => trivial
  | t :: _, .cons x xs, h => by
    refine ⟨?_, argsOK_noRef G xs fun t' ht' => h t' (List.mem_cons_of_mem _ ht')⟩
    show G.AllValid (pyAcct t x)
    have ht := h t List.mem_cons_self
    simp only [pyNoRef, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> exact Typing.allValid_nil G

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
    ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩, ⟨fun _ _ _ => refsOK_nil rfl, fun _ _ _ h _ => h⟩,
    fun G _ a h => argsOK_noRef G a h⟩
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
      · refine .inr ?_
        change Same (startOf w.store) w₂ { w₂ with store :=
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
      · exact .inr ⟨Nat.le_refl _, fun _ _ _ h => h, Modules.extends_withCell _ _ _ _ _, rfl, rfl⟩
      · exact immEq_withCell h _ _ _ _

/-- **`mkClosure` satisfies the machine's spec at Python's accounts**, for every state validity:
it binds valid cells into a valid code pointer, reads the module's `__name__` cell, and allocates a
function object whose closure is valid, so the store stays valid. -/
theorem mkClosure_implOK (targs : Vector Ty PySem.impl.py.mkClosure.typeArgc)
    (StOK : Typing → PySem.impl.py.mkClosure.St Run targs → Prop) :
    pyAccounts.ImplOK StOK (PySem.impl.py.mkClosure.shape targs) (PySem.impl.py.mkClosure.fn Run targs) := by
  dsimp only [PySem.impl.py.mkClosure, Accounts.ImplOK, Accounts.FnOK]
  intro G a0 h0 a1 _ a2 _
  refine pyAccounts.fnOK_ofPayload _ G _ _ fun vs hvs => ?_
  dsimp only [Accounts.VarOK, Accounts.TreeOK, Rules.mkClosure]
  letI : Decode Run := ⟨PySem.interp Run⟩
  letI : Refs Run (Modules Run) := modulesRefs (pyTags Run).value
  have hworld : ∀ (G : Typing) (w : World Run), (pyAccounts.spec [] [] StOK).World G w ↔
      RefsOK (σ := Run) G w.store ∧ RefsOK (σ := Run) G w.modules := fun G w =>
    Typing.allValid_append
  -- The function object of a valid closure keeps the store valid.
  have halloc : ∀ G₂ (g : FnRef Run [Value, Value] (Except Value Value)) m,
      G₂.CapValid g.captured →
      (pyAccounts.spec [] [] StOK).Sat (fun S₁ x => pyAccounts.ResOK S₁ (some PySem.T.py.Value) x) G₂
        (modifyGetThe (ObjStore Run) fun st => (Value.obj st.size, (st.alloc (Rules.funcObj g a1 m)).fst)) := by
    intro G₂ g m hg
    rw [modifyGetThe_eq (ε := MEff (PySem.interp Run) Run (World Run) []) (P := ObjStore Run)]
    refine Spec.sat_update.mpr fun w' hw' => ⟨(hworld G₂ _).mpr ⟨fun l hl => ?_, ((hworld G₂ w').mp hw').2⟩,
      Spec.sat_ret.mpr (valOK_value _ _)⟩
    change l ∈ Refs.refs (σ := Run) ((HasPart.get w' : ObjStore Run).alloc (Rules.funcObj g a1 m)).1 at hl
    rw [refs_alloc, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ((hworld G₂ w').mp hw').1 l hl
    · exact refsOK_fn.mpr hg l hl
  refine Accounts.bindAll_sat (s := _) pyAccounts StOK _ _ _ vs _ G ?_ hvs fun G₁ _ g hg => ?_
  · have h' := pyAccounts.fn (targs[0].elems ++ [PySem.T.py.Value, PySem.T.py.Value])
      (PySem.T.base.Except PySem.T.py.Value PySem.T.py.Value) a0
    have hc := Typing.capValid_of_allValid ((congrArg G.AllValid h').mp h0)
    simp only [RunModel.fnOf] at hc
    exact (congrArg G.CapValid (Accounts.captured_cast
      (Ty.decodeList_eq_map Run (PySem.H Run) (targs[0].elems ++ [PySem.T.py.Value, PySem.T.py.Value]))
      rfl a0)).mp hc
  · dsimp only [Rules.moduleName, bind, Sem.bind, Sem.bindAfter, getThe, MonadStateOf.get,
      Sem.instMonadStateOf, pure]
    refine Spec.sat_update.mpr fun w hw => ⟨hw, ?_⟩
    dsimp only
    split
    · rename_i r hr
      have hv := valid_of_cell? (pyTags Run).value ((hworld G₁ w).mp hw).2 hr
      refine Spec.sat_vis.mpr ⟨hv, fun G₂ he _ _ => ?_⟩
      simp only [Sem.bind]
      split <;> exact halloc G₂ g _ (Typing.CapValid.mono he hg)
    · exact halloc G₁ g _ hg

/-- `mkClosure` stays within its declared effect: its binds change nothing that `Within` counts, and
the function object that it allocates is new. -/
theorem PySem.okOf.py.mkClosure :
    ImplWithin PySem.interp (pyDeclaredEffect "py.mkClosure") PySem.impl.py.mkClosure := by
  intro σ _ targs
  letI : Decode σ := ⟨PySem.interp σ⟩
  intro a0 a1 a2
  refine FnAll_ofPayload _ _ _ fun vs => ?_
  dsimp only [PySem.impl.py.mkClosure, VarAll, Rules.mkClosure, bind]
  refine .inr fun s N => Strata.Dyn.Exec.Effects.bindAll_within (σ := σ) (s := _) _ s _ _ _ _ vs _ N
    fun g => ?_
  dsimp only [Rules.moduleName, bind, Sem.bind, Sem.bindAfter, getThe, MonadStateOf.get,
    Sem.instMonadStateOf, pure]
  have hne : pyDeclaredEffect "py.mkClosure" ≠ .pure := by decide
  refine ⟨fun _ w => .inr (Same.refl s w), fun h => absurd h hne, fun w => ?_⟩
  rw [Strata.Dyn.Exec.Effects.Within.after_eq]
  dsimp only
  split
  · refine ⟨fun h => absurd h hne, fun v => ?_⟩
    dsimp only [Sem.bind]
    split
    all_goals
      simp only [modifyGetThe_eq]
      exact ⟨fun _ w => .inr (same_allocObj s _ w),
        fun _ _ _ h => ⟨immEq_allocObj _ h, congrArg (fun n => Sem.ret (Value.obj n)) h.1⟩,
        fun _ => trivial⟩
  · simp only [modifyGetThe_eq]
    exact ⟨fun _ w => .inr (same_allocObj s _ w),
      fun _ _ _ h => ⟨immEq_allocObj _ h, congrArg (fun n => Sem.ret (Value.obj n)) h.1⟩,
      fun _ => trivial⟩

/-- `mkClosure`'s certificate at Python's model. -/
theorem PySem.certOf.py.mkClosure (k : Nat) :
    PySem.model.OpCertified pyAccounts k PySem.impl.py.mkClosure := fun targs =>
  mkClosure_implOK targs _

end

public section
/-! The call bracket's marker is in `Depth`, so `Within` at `calls` bounds the changes outside a
bracket only if nothing but the bracket's edges changes the marker, and nothing else reads it
(`docs/PythonToDyn.md` §13).  No operation names `Depth`'s instance, the class field that hands it
to a rule, the world's constructor, the marker's field, or the bracket's test of it, other than
through the primitives that keep the marker (`withDepth`, `withPyDepth`, `depthGet`) or change it
at a bracket's edges (`bracketed`, `callClosureT`), the bracket itself, the effects' statement
(`spec`, whose `inCall` field reads the marker but is itself forbidden, and the proposition
`Within`), and the other parts' instances.  And no operation calls a closure
other than through `callClosureT`, which lowers the marker for the callee.  The definitions below
the rule monad, listed here, are the ones whose code the walk alone checks; the rules generic in
their monad (`#py_rule_shapes`) are not among them.  The walk, and its choice of which definitions
are below the rule monad, are trusted: no theorem proves that it misses no write or read of the
marker. -/
/--
info: #py_part_writers: StrataPython.Dyn.Sem.PySem.ops reaches 185 definitions below the rule monad, which name StrataPython.Dyn.Sem.PyLang, StrataPython.Dyn.Sem.World, Strata.Dyn.Exec.Sem, StrataPython.Dyn.Sem.Depth, StrataPython.Dyn.Sem.PyM or a constant whose type does:
StrataPython.Dyn.Sem.BEff
StrataPython.Dyn.Sem.BTree
StrataPython.Dyn.Sem.ContOK
StrataPython.Dyn.Sem.Depth.c
StrataPython.Dyn.Sem.Depth.py
StrataPython.Dyn.Sem.Handles
StrataPython.Dyn.Sem.HandlesOK
StrataPython.Dyn.Sem.Prim.addrHash
StrataPython.Dyn.Sem.Prim.alloc
StrataPython.Dyn.Sem.Prim.allocDict
StrataPython.Dyn.Sem.Prim.allocDictFrom
StrataPython.Dyn.Sem.Prim.allocDictOf
StrataPython.Dyn.Sem.Prim.allocExc
StrataPython.Dyn.Sem.Prim.allocInstance
StrataPython.Dyn.Sem.Prim.allocList
StrataPython.Dyn.Sem.Prim.allocObj
StrataPython.Dyn.Sem.Prim.allocSet
StrataPython.Dyn.Sem.Prim.allocSetOf
StrataPython.Dyn.Sem.Prim.allocWith
StrataPython.Dyn.Sem.Prim.builtinGet
StrataPython.Dyn.Sem.Prim.callClosure
StrataPython.Dyn.Sem.Prim.callFunc
StrataPython.Dyn.Sem.Prim.choicesAt
StrataPython.Dyn.Sem.Prim.choose
StrataPython.Dyn.Sem.Prim.classOf
StrataPython.Dyn.Sem.Prim.classSetMro
StrataPython.Dyn.Sem.Prim.classSetMroNew
StrataPython.Dyn.Sem.Prim.classSetName
StrataPython.Dyn.Sem.Prim.dictClear
StrataPython.Dyn.Sem.Prim.dictDelete
StrataPython.Dyn.Sem.Prim.dictDeleteNew
StrataPython.Dyn.Sem.Prim.dictDeleteWith
StrataPython.Dyn.Sem.Prim.dictEntryAt
StrataPython.Dyn.Sem.Prim.dictFind
StrataPython.Dyn.Sem.Prim.dictLocate
StrataPython.Dyn.Sem.Prim.dictOf
StrataPython.Dyn.Sem.Prim.dictPopitem
StrataPython.Dyn.Sem.Prim.dictPopitemNew
StrataPython.Dyn.Sem.Prim.dictPopitemWith
StrataPython.Dyn.Sem.Prim.dictSet
StrataPython.Dyn.Sem.Prim.dictSetNew
StrataPython.Dyn.Sem.Prim.dictSetWith
StrataPython.Dyn.Sem.Prim.dictTable
StrataPython.Dyn.Sem.Prim.excSet
StrataPython.Dyn.Sem.Prim.funcSetAnnotations
StrataPython.Dyn.Sem.Prim.funcSetName
StrataPython.Dyn.Sem.Prim.globalGet
StrataPython.Dyn.Sem.Prim.globalGetT
StrataPython.Dyn.Sem.Prim.handledGet
StrataPython.Dyn.Sem.Prim.hashValue
StrataPython.Dyn.Sem.Prim.immHash
StrataPython.Dyn.Sem.Prim.immView
StrataPython.Dyn.Sem.Prim.iterSet
StrataPython.Dyn.Sem.Prim.keyClassOf
StrataPython.Dyn.Sem.Prim.layoutOf
StrataPython.Dyn.Sem.Prim.listChange
StrataPython.Dyn.Sem.Prim.listChangeNew
StrataPython.Dyn.Sem.Prim.markWalk
StrataPython.Dyn.Sem.Prim.modifyObj
StrataPython.Dyn.Sem.Prim.modifyOwnPayload
StrataPython.Dyn.Sem.Prim.modifyPayload
StrataPython.Dyn.Sem.Prim.moduleAdd
StrataPython.Dyn.Sem.Prim.modulesGet
StrataPython.Dyn.Sem.Prim.mutSet
StrataPython.Dyn.Sem.Prim.numBinary
StrataPython.Dyn.Sem.Prim.numUnary
StrataPython.Dyn.Sem.Prim.objClass
StrataPython.Dyn.Sem.Prim.objDict
StrataPython.Dyn.Sem.Prim.objEnsureDict
StrataPython.Dyn.Sem.Prim.objGet
StrataPython.Dyn.Sem.Prim.objView
StrataPython.Dyn.Sem.Prim.ofArith
StrataPython.Dyn.Sem.Prim.ownData
StrataPython.Dyn.Sem.Prim.ownDict
StrataPython.Dyn.Sem.Prim.ownSet
StrataPython.Dyn.Sem.Prim.partView
StrataPython.Dyn.Sem.Prim.probeOf
StrataPython.Dyn.Sem.Prim.raiseFailure
StrataPython.Dyn.Sem.Prim.raiseNew
StrataPython.Dyn.Sem.Prim.reprCheck
StrataPython.Dyn.Sem.Prim.setAdd
StrataPython.Dyn.Sem.Prim.setAddNew
StrataPython.Dyn.Sem.Prim.setAddWith
StrataPython.Dyn.Sem.Prim.setClear
StrataPython.Dyn.Sem.Prim.setClearNew
StrataPython.Dyn.Sem.Prim.setCopy
StrataPython.Dyn.Sem.Prim.setDiscard
StrataPython.Dyn.Sem.Prim.setDiscardNew
StrataPython.Dyn.Sem.Prim.setDiscardWith
StrataPython.Dyn.Sem.Prim.setExactOf
StrataPython.Dyn.Sem.Prim.setFreeze
StrataPython.Dyn.Sem.Prim.setFreezeNew
StrataPython.Dyn.Sem.Prim.setHandled
StrataPython.Dyn.Sem.Prim.setId
StrataPython.Dyn.Sem.Prim.setLocate
StrataPython.Dyn.Sem.Prim.setMerge
StrataPython.Dyn.Sem.Prim.setMergeNew
StrataPython.Dyn.Sem.Prim.setMergeWith
StrataPython.Dyn.Sem.Prim.setPop
StrataPython.Dyn.Sem.Prim.setPopNew
StrataPython.Dyn.Sem.Prim.setPopWith
StrataPython.Dyn.Sem.Prim.setRead
StrataPython.Dyn.Sem.Prim.setReadAt
StrataPython.Dyn.Sem.Prim.setReplace
StrataPython.Dyn.Sem.Prim.setReplaceNew
StrataPython.Dyn.Sem.Prim.setReserve
StrataPython.Dyn.Sem.Prim.setReserveNew
StrataPython.Dyn.Sem.Prim.setSlotAt
StrataPython.Dyn.Sem.Prim.setSubtract
StrataPython.Dyn.Sem.Prim.setSubtractNew
StrataPython.Dyn.Sem.Prim.setSubtractWith
StrataPython.Dyn.Sem.Prim.setSymUpdate
StrataPython.Dyn.Sem.Prim.setSymUpdateNew
StrataPython.Dyn.Sem.Prim.setSymUpdateWith
StrataPython.Dyn.Sem.Prim.setTrim
StrataPython.Dyn.Sem.Prim.setTrimNew
StrataPython.Dyn.Sem.Prim.setViewOf
StrataPython.Dyn.Sem.Prim.slotCount
StrataPython.Dyn.Sem.Prim.slotCount._f
StrataPython.Dyn.Sem.Prim.slotGet
StrataPython.Dyn.Sem.Prim.slotPut
StrataPython.Dyn.Sem.Prim.stateSet
StrataPython.Dyn.Sem.Prim.strIterNext
StrataPython.Dyn.Sem.Prim.strTable
StrataPython.Dyn.Sem.Prim.walkGuard
StrataPython.Dyn.Sem.Prim.withRepr
StrataPython.Dyn.Sem.Prim.writeOut
StrataPython.Dyn.Sem.Proved
StrataPython.Dyn.Sem.PyFn
StrataPython.Dyn.Sem.PyLang.call
StrataPython.Dyn.Sem.PyLang.guard
StrataPython.Dyn.Sem.PyLang.handled
StrataPython.Dyn.Sem.PyLang.heap
StrataPython.Dyn.Sem.PyLang.modules
StrataPython.Dyn.Sem.PyLang.out
StrataPython.Dyn.Sem.PyLang.store
StrataPython.Dyn.Sem.PyLang.tagExcept
StrataPython.Dyn.Sem.PyLang.tagValue
StrataPython.Dyn.Sem.PyM
StrataPython.Dyn.Sem.PyM.bind'
StrataPython.Dyn.Sem.PyM.failure
StrataPython.Dyn.Sem.PyM.gap
StrataPython.Dyn.Sem.PyM.instMonad
StrataPython.Dyn.Sem.PyM.instMonadExceptValue
StrataPython.Dyn.Sem.PyM.lift
StrataPython.Dyn.Sem.PyM.pure'
StrataPython.Dyn.Sem.PyM.region
StrataPython.Dyn.Sem.PyM.relax
StrataPython.Dyn.Sem.PyM.throw'
StrataPython.Dyn.Sem.PyM.tryCatch'
StrataPython.Dyn.Sem.Rules.globalCell
StrataPython.Dyn.Sem.Rules.mkClosure
StrataPython.Dyn.Sem.Rules.moduleName
StrataPython.Dyn.Sem.StartFree
StrataPython.Dyn.Sem.TreeOK
StrataPython.Dyn.Sem.bInst
StrataPython.Dyn.Sem.callBuiltinWith
StrataPython.Dyn.Sem.callBuiltinWith._f
StrataPython.Dyn.Sem.callsRecord
StrataPython.Dyn.Sem.contOf
StrataPython.Dyn.Sem.instPyCallsPyMCallsValue
StrataPython.Dyn.Sem.instPyMachinesPyMWritesTrueValuePyLoopState
StrataPython.Dyn.Sem.instPyNewPyMFalseValue
StrataPython.Dyn.Sem.instPyNewPyMWritesTrueValue
StrataPython.Dyn.Sem.instPyPurePyMValue
StrataPython.Dyn.Sem.instPyReadsPyMValueOfAtLeastReads
StrataPython.Dyn.Sem.instPyWritesPyMWritesValue
StrataPython.Dyn.Sem.isNamedTypeError
StrataPython.Dyn.Sem.loopCont
StrataPython.Dyn.Sem.machinesResume
StrataPython.Dyn.Sem.machinesResume._f
StrataPython.Dyn.Sem.machinesStart
StrataPython.Dyn.Sem.machinesStart._f
StrataPython.Dyn.Sem.modelInvariant
StrataPython.Dyn.Sem.regionHandle
StrataPython.Dyn.Sem.resolveBuiltin
StrataPython.Dyn.Sem.runLoop
StrataPython.Dyn.Sem.runLoopFree
StrataPython.Dyn.Sem.runRule
StrataPython.Dyn.Sem.runRuleFree
StrataPython.Dyn.Sem.runRuleIf
StrataPython.Dyn.Sem.runTotal
StrataPython.Dyn.Sem.runTotalFree
StrataPython.Dyn.Sem.treeOf
StrataPython.Dyn.Sem.writesRecord
-/
#guard_msgs in
#py_part_writers PySem (lang := PyLang)
  (forbidden := [World.instHasPart_depth, PyLang.depth, World.mk, Depth.bracket,
    Strata.Dyn.Exec.HasInCall.inCall, Strata.Dyn.Exec.Effects.WorldSpec.inCall, Strata.Dyn.Exec.HasCall.callReq])
  (trusted := [Prim.bracketed, Prim.callClosureT, Prim.withDepth, Prim.withPyDepth, Prim.depthGet,
    instHasInCallWorld, Strata.Dyn.Exec.HasBracket.mreq, spec, Strata.Dyn.Exec.Effects.Within,
    World.instHasPart_depth, World.instHasPart_store, World.instHasPart_modules, World.instHasPart_handled,
    World.instHasPart_guard, World.instHasPart_out])
  (below := [PyLang, World, Strata.Dyn.Exec.Sem, Depth, PyM])

/-! No Python rule blocks or fails: a case the rules don't model stops with a gap, and a Python rule
never stops with `Fault.blocked` (which `assume` gives) or `Fault.failure`, so that a verifier never
reads a path CPython takes as one that can't happen.  The one operation that reaches
`Fault.failure` is the language-neutral `base.unreachable`, for code that no run reaches: the dead
arms of a completion dispatch, the code after a `NameError` that always raises, and the stubs of a
module whose translation has diagnostics, which is never run.  The check trusts that operation's
entry in the table, not the helper, so that no Python rule can call the helper. -/
#py_part_writers PySem (lang := PyLang)
  (forbidden := [Strata.Dyn.Exec.Fault.failure, Strata.Dyn.Exec.Fault.blocked])
  (trusted := [StrataPython.Dyn.Sem.PySem.impl.base.unreachable])


/-! Every rule but two runs a definition that is generic in its monad, at `PyM`, with the record's
instances alone, which the walks above check.  `globalCell` and `mkClosure` work on the machine's
cells and closures, which the record doesn't hand out. -/
#py_rule_shapes Py (exceptions := [py.globalCell, py.mkClosure])

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
