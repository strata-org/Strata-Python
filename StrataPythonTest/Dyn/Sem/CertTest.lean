/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
public import StrataDyn.RefToRegSound.RefToReg
-- `#guard` runs Python's accounts as compiled code.
meta import StrataPython.Dyn.Sem.Table

set_option autoImplicit false

/-!
# Python's table is certified, and ref-to-reg's soundness applies to it

* `refToReg_sound_python` is `refToReg_sound_cell` at Python's table, with its certificate
  `PySem.certified`: its only open hypothesis about the pass is `PromotionOK`.
* What Python's accounts accept and reject, on concrete trees at `pyAccounts.spec` and concrete
  typings: a read of a valid cell is accepted; a read of a cell at another tag, and a call of a
  closure whose captures cell the typing doesn't know, are rejected.  A rule that reads a cell
  through a retyped ref is rejected at every typing in which the cell is valid, and the certificate
  tactic fails on it.
* What Python's accounts hold: a world's global cells, and a function value's captures cell.
-/

namespace StrataPython.Dyn.Sem.CertTest

open Strata.Dyn Strata.Dyn.Exec Strata.Dyn.RefToRegSound StrataPython.Dyn.Sem

public section

/-- The initial world holds no ref: no global cell, and no function object. -/
theorem pyAccounts_w0 : pyAccounts.world PySem.model.at.w0 = [] := by
  decide

/-- **A target that promotes the cells of a Python program improves on it under every oracle, up
to a bad cell**, as `refToReg_sound_cell` gives at Python's table: if the module `m` links and
validates against `PySem.model` with function `f` at index `i`, and `PromotionOK` relates the
linked source to a well-formed linked target `lm₁`, then a start of `f` in `m`, on arguments that
hold no ref, has a start at index `i` in `lm₁`, and for every observation of the world the
target's run refines the source's under every oracle: the same, or the source faults with a bad
cell after what the target shows.  Any other fault or gap of the source, a failed call included,
the target shows too.  The run starts from the initial snapshot. -/
theorem refToReg_sound_python {α : Type} {m : Module Py.env α} {f : Name}
    {lm : LModule PySem.model.at} {hw : WF lm} {i : Nat}
    (hp : prepare PySem.model m f = .ok ⟨lm, hw, i⟩) {lm₁ : LModule PySem.model.at}
    (hw₁ : WF lm₁) (hcert : PromotionOK lm lm₁)
    (args : List (Dyn PySem.model.at.interp)) (hargs : ∀ d ∈ args, pyAcct d.1 d.2 = [])
    {B : Ty} {c : Core PySem.model.at} {h : CoreOK lm B c}
    (hs : startCore hw i args .initial = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hw₁ i args .initial = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : PySem.model.at.W → O),
        Exec.OracleRefines hw hw₁ obs Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩ ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ :=
  refToReg_sound_cell PySem.model pyAccounts PySem.certified hp hw₁ hcert pyAccounts_w0 args hargs
    hs

/-- The spec of an operation with no regions, successors or state. -/
abbrev V0 := pyAccounts.spec [] [] (St := Empty) fun _ _ => True

/-- A typing in which cell `0` holds `py.Value`s. -/
def valueAt0 : Typing := { cell := fun l => if l = 0 then some PySem.T.py.Value else none }

/-- A typing in which cell `0` holds `base.Int`s. -/
def intAt0 : Typing := { cell := fun l => if l = 0 then some PySem.T.base.Int else none }

/-- A read of cell `0` as a `py.Value`, then nothing. -/
def readCell0 : Tree PySem.model.at.interp Run PySem.model.at.W [] [] Empty Unit :=
  .vis (.get PySem.T.py.Value 0) fun _ => .ret ()

/-- A call of function `0` through the captures cell `3`, on two `None`s. -/
def callCaps3 : Tree PySem.model.at.interp Run PySem.model.at.W [] [] Empty Unit :=
  .vis (.call ([PySem.T.py.Value, PySem.T.py.Value], PySem.T.py.Value) 0 3 (.none, .none))
    fun _ => .ret ()

-- A read of a cell that the typing gives the tag of `py.Value` is accepted.
example : V0.Sat (fun _ _ => True) valueAt0 readCell0 :=
  Spec.sat_vis.mpr ⟨rfl, fun _ _ _ _ => Spec.sat_ret.mpr trivial⟩

-- At a typing in which cell `0` holds `Int`, a read of cell `0` as `py.Value` is rejected.
example : ¬ V0.Sat (fun _ _ => True) intAt0 readCell0 := fun h => by
  have hp : intAt0.cell 0 = some PySem.T.py.Value := (Spec.sat_vis.mp h).1
  exact absurd hp (by decide)

-- A call of a closure whose captures cell the typing doesn't know is rejected.
example : ¬ V0.Sat (fun _ _ => True) {} callCaps3 := fun h => by
  obtain ⟨hcap, _⟩ := (Spec.sat_vis.mp h).1
  rcases hcap with h0 | ⟨_, h3⟩
  · exact absurd h0 (by decide)
  · exact nomatch h3

/-- A rule's read of the `py.Value` cell `r` through a ref retyped to `Int` (`⟨r.raw⟩`). -/
def retypedRead (r : Ref Run Value) :
    Tree PySem.model.at.interp Run PySem.model.at.W [] [] Empty Int :=
  letI : Decode Run := ⟨PySem.model.at.interp⟩
  letI : TagOf Run Int := ⟨PySem.T.base.Int, rfl⟩
  @readRef Run _ _ (MEff PySem.model.at.interp Run PySem.model.at.W [])
    (Out PySem.model.at.interp [] Empty) HasHeap.mreq Int _ ⟨r.raw⟩

-- A rule that reads a cell through a retyped ref has no certificate: at every typing in which `r`
-- holds `py.Value`s, the machine's spec rejects its read at `Int` (`Accounts.sat_retyped_cell`).
example (r : Ref Run Value) (S : Typing) (hr : S.Valid r.loc PySem.T.py.Value) :
    ¬ V0.Sat (fun _ _ => True) S (retypedRead r) :=
  Accounts.sat_retyped_cell pyAccounts _ _ hr (by decide) (.inl rfl) _

-- So the certificate tactic fails on it, and a table with such a rule doesn't build.
example : True := by
  fail_if_success
    have _ : V0.Sat (fun _ _ => True) valueAt0 (retypedRead ⟨⟨0, trivial⟩⟩) := by
      dyn_cert [pyAccounts, pyAcct]
  trivial

/-- The initial world with a global cell `x` of a module `m`, at location `0`. -/
def wCell0 : PySem.model.at.W :=
  { PySem.model.at.w0 with modules := PySem.model.at.w0.modules.withCell "m" "x" 2 ⟨0, trivial⟩ }

-- Python's accounts list the module table's cells as the world's refs.
#guard pyAccounts.world wCell0 == [.cell 0 PySem.T.py.Value]
-- So that world is possible at a typing that gives cell `0` the tag of `py.Value`, and not at the
-- empty typing.
example : valueAt0.AllValid [.cell 0 PySem.T.py.Value] := by
  simp [Typing.AllValid, Typing.LocValid, Typing.Valid, valueAt0]
example : ¬ ({} : Typing).AllValid [.cell 0 PySem.T.py.Value] := by
  simp [Typing.AllValid, Typing.LocValid, Typing.Valid]

/-- A function value whose captures cell is `3`. -/
def fnCaps3 : PySem.model.at.interp (.app 1 [.list [PySem.T.py.Value], PySem.T.py.Value]) :=
  ⟨0, 3, trivial⟩

-- Python's accounts list a function value's captures cell, so the empty typing rejects it.
example : pyAcct _ fnCaps3 = [.caps 3] := by decide
example : ¬ pyAccounts.ValOK {} _ fnCaps3 := by
  show ¬ Typing.AllValid {} (pyAcct _ fnCaps3)
  rw [show pyAcct _ fnCaps3 = [.caps 3] by decide]
  simp [Typing.AllValid, Typing.LocValid, Typing.CapValid]

/--
info: 'StrataPython.Dyn.Sem.PySem.certified' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PySem.certified

/--
info: 'StrataPython.Dyn.Sem.CertTest.refToReg_sound_python' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refToReg_sound_python

/-! ## The rules' meaning, for twins

A twin is an abstract interpreter's copy of a rule, which it proves to cover the rule by unfolding
the rule's primitives at `PyM`. So every definition of the concrete record's primitives (`Prim.*`)
and of the rule monad (`PyM.*`) has a body that an importer sees: none is an axiom to it (which a
definition without `@[expose]` is), opaque, or implemented by other code, and none is irreducible
but through its unfolding equation (a definition by well-founded recursion). One primitive is
unfolded as an example. -/

open Lean Meta in
#eval show MetaM Unit from do
  let env ← getEnv
  let pres := [`StrataPython.Dyn.Sem.Prim, `StrataPython.Dyn.Sem.PyM]
  let mut n := 0
  for (name, ci) in env.constants.toList do
    let user := (privateToUserName? name).getD name
    -- The definitions themselves, not the auxiliary definitions that Lean makes for them.
    unless pres.contains user.getPrefix && !user.isInternalDetail do continue
    -- Structures, their constructors and projections have no body to unfold.
    unless ci matches .defnInfo _ | .thmInfo _ | .axiomInfo _ | .opaqueInfo _ do continue
    -- A proof is not computed, and an importer sees a theorem as an axiom.
    if ← isProp ci.type then continue
    n := n + 1
    unless ci matches .defnInfo _ do throwError "{user} has no body that an importer sees"
    -- A definition by well-founded recursion is irreducible, but its unfolding equation computes it.
    if (← getReducibilityStatus name) == .irreducible && (← getUnfoldEqnFor? name).isNone then
      throwError "{user} is irreducible"
    if (Compiler.getImplementedBy? env name).isSome then throwError "{user} is implemented by other code"
  if n < 10 then throwError "only {n} definitions found"

/-- `undefName?` at `PyM` is the tree that answers at once, by unfolding. -/
example {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε] (hs : Handles ε E)
    (s : Start) {β : Type} (k : Option String → Sem ε E β) (ke : Value → Sem ε E β) (v : Value) :
    (PyPure.undefName? (m := PyM σ .pure true) v).1 hs s k ke =
      k (match v with | .undef n => some n | _ => none) := rfl

end

end StrataPython.Dyn.Sem.CertTest
