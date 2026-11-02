/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Dyn.Sem.Table
meta import StrataPython.Dyn.Sem.Table
public meta import Lean.Elab.Term

meta section
open Lean Elab Term in
/-- `depth% i`: the raw projection of the field `depth` of the instance `i`. -/
elab "depth% " i:term : term => do
  let e ← elabTerm i none
  return Expr.proj ``StrataPython.Dyn.Sem.PyLang 3 e
end

set_option autoImplicit false

/-!
# `#py_part_writers`

Writes of the call bracket's marker that `#py_part_writers` must reject, each reached from its own
list of operations: a two-step forge written as private definitions (raise the marker, then run a
body inside a bracket with no call), and the marker written through an abbreviation of `Depth`, a
generic wrapper, a `partial`, an `opaque` and an `@[implemented_by]` definition, and `id Depth`;
the depth part taken out of the instance by a `match`, `casesOn`, a `let` pattern, `rec` and a raw
projection; a language instance whose depth part is the rule's own, hidden in the arguments of a
forbidden operand; and an axiom named only in a type.  The axiom is the case under test: the check
must reject a definition that nothing shows.  Then reads of the marker: through `depthGet` with its
field, `Depth`'s derived equality or `sizeOf`, the bracket's own test, and the trusted statement of
the effects; and a call of a closure that doesn't lower the marker for the callee.
-/

namespace StrataPython.Dyn.Sem.PartWritersTest

open Strata.Dyn.Exec

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- The marker raised by one. -/
def raise (d : Depth) : Depth := { d with bracket := d.bracket + 1 }

/-- Step 1 of the forge: raise the marker, and change nothing else. -/
private def raiseOnly : Sem ε E Unit := modifyThe Depth raise

/-- Step 2: a body inside a bracket, without the bracket's own edges. -/
private def inBracket (body : Sem ε E Unit) : Sem ε E Unit := HasBracket.bracket "x" body

/-- The forge: raise the marker, then write the output with no call. -/
def forged : Sem ε E Unit := do
  raiseOnly
  inBracket (modifyThe Output fun o => ⟨o.pieces.push "x"⟩)

def Forge.ops : List (Sem ε E Unit) := [forged]

/-- `Depth` under another name. -/
abbrev D := Depth
def viaAbbrev : Sem ε E Unit := modifyThe D raise
def Abbrev.ops : List (Sem ε E Unit) := [viaAbbrev]

/-- A wrapper generic in the part. -/
def bump (P : Type) [HasPart ε.W P] (f : P → P) : Sem ε E Unit := modifyThe P f
def viaWrapper : Sem ε E Unit := bump Depth raise
def Wrapper.ops : List (Sem ε E Unit) := [viaWrapper]

/-- `Depth` as `id Depth`. -/
def viaId : Sem ε E Unit := @modifyThe (id Depth) (Sem ε E) (inferInstanceAs (MonadStateOf Depth (Sem ε E))) raise
def Id.ops : List (Sem ε E Unit) := [viaId]

/-- The depth part taken out of the instance by a `match`. -/
def viaMatch (inst : PyLang σ ε) : Sem ε E Unit :=
  match inst with
  | { depth := d, .. } => @modifyThe Depth _ (@Sem.instMonadStateOf _ _ _ d) raise
def Match.ops [inst : PyLang σ ε] : List (Sem ε E Unit) := [viaMatch inst]

/-- By `PyLang.casesOn`. -/
def viaCases (inst : PyLang σ ε) : Sem ε E Unit :=
  PyLang.casesOn (motive := fun _ => Sem ε E Unit) inst
    fun _ _ _ d _ _ _ _ _ _ _ _ => @modifyThe Depth _ (@Sem.instMonadStateOf _ _ _ d) raise
def Cases.ops [inst : PyLang σ ε] : List (Sem ε E Unit) := [viaCases inst]

/-- By a `let` pattern. -/
def viaLetPat (inst : PyLang σ ε) : Sem ε E Unit :=
  let { depth := d, .. } := inst
  @modifyThe Depth _ (@Sem.instMonadStateOf _ _ _ d) raise
def LetPat.ops [inst : PyLang σ ε] : List (Sem ε E Unit) := [viaLetPat inst]

/-- By `PyLang.rec`, which has no compiled code. -/
noncomputable def viaRec (inst : PyLang σ ε) : Sem ε E Unit :=
  PyLang.rec (motive := fun _ => Sem ε E Unit)
    (fun _ _ _ d _ _ _ _ _ _ _ _ => @modifyThe Depth _ (@Sem.instMonadStateOf _ _ _ d) raise) inst
noncomputable def Rec.ops [inst : PyLang σ ε] : List (Sem ε E Unit) := [viaRec inst]

/-- By a raw projection. -/
def viaProj (inst : PyLang σ ε) : Sem ε E Unit :=
  @modifyThe Depth _ (@Sem.instMonadStateOf _ _ _ (depth% inst)) raise
def Proj.ops [inst : PyLang σ ε] : List (Sem ε E Unit) := [viaProj inst]
/-- A language instance whose depth part raises the marker on every write, built from the
instance's own parts and handed to a trusted primitive.  The custom part hides in the arguments of
an operand whose head is the forbidden `PyLang.depth`. -/
@[reducible] def sneakyInst [inst : PyLang σ ε] : PyLang σ ε :=
  PyLang.mk PyLang.store PyLang.modules PyLang.handled
    (@PyLang.depth σ _ _ ε (PyLang.mk PyLang.store PyLang.modules PyLang.handled
      { get := fun w => (PyLang.depth (self := inst)).get w
        set := fun w d => (PyLang.depth (self := inst)).set w (raise d) }
      PyLang.guard PyLang.out PyLang.heap PyLang.call PyLang.bracket (PyLang.tagValue ε) (PyLang.tagCell ε)
      (PyLang.tagExcept ε)))
    PyLang.guard PyLang.out PyLang.heap PyLang.call PyLang.bracket (PyLang.tagValue ε) (PyLang.tagCell ε)
    (PyLang.tagExcept ε)
def viaMk [inst : PyLang σ ε] : Sem ε E Unit :=
  @Subtype.val _ _ (Prim.withDepth (σ := σ) (e := .calls) (fr := true) (by decide) 0 (PyM.pure' ()))
    ε E (sneakyInst (inst := inst)) #[] ⟨0⟩ Unit pure (fun _ => pure ())
def Mk.ops [PyLang σ ε] : List (Sem ε E Unit) := [viaMk (σ := σ)]

/-- A read of the marker, through the trusted `depthGet`. -/
def viaRead : PyM σ .reads true Bool := do
  let d ← Prim.depthGet
  pure (d.bracket != 0)
def Read.ops : List (PyM σ .reads true Bool) := [viaRead]

/-- A read of the marker through `Depth`'s derived equality. -/
def viaDecEq : PyM σ .reads true Bool := do
  let d ← Prim.depthGet
  pure (d == { py := d.py, c := d.c })
def DecEq.ops : List (PyM σ .reads true Bool) := [viaDecEq]

/-- A read of the marker through `sizeOf`, which has no compiled code. -/
noncomputable def viaSizeOf : PyM σ .reads true Nat := do
  let d ← Prim.depthGet
  pure (sizeOf d)
noncomputable def SizeOf.ops : List (PyM σ .reads true Nat) := [viaSizeOf]

end

/-- A read of the marker through the bracket's own test, on the whole world. -/
def viaInCall {σ : Type} [Store σ] : StateM (World σ) Bool := do return HasInCall.inCall (← get)
def InCall.ops {σ : Type} [Store σ] : List (StateM (World σ) Bool) := [viaInCall]

/-- A read of the marker through the trusted statement of the effects. -/
def viaSpec {σ : Type} [Store σ] : StateM (World σ) Bool := do return (spec (σ := σ)).inCall (← get)
def SpecInCall.ops {σ : Type} [Store σ] : List (StateM (World σ) Bool) := [viaSpec]

/-- A call of a closure that doesn't lower the marker for the callee. -/
def viaCallFn {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]
    (f : FnRef σ [Value, Value] (Except Value Value)) : Sem ε E (Except Value Value) :=
  callFn f (Value.none, Value.none)
def CallFn.ops {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]
    (f : FnRef σ [Value, Value] (Except Value Value)) : List (Sem ε E (Except Value Value)) :=
  [viaCallFn f]

/-- An axiom, named only in a type, whose definition nothing shows. -/
axiom AxTy : Type
def viaAxiom : List AxTy → StateM Depth Unit := fun _ => pure ()
def Axiom.ops : List (StateM Depth Unit) := [viaAxiom []]

/-- A partial definition, whose body proofs don't see. -/
partial def viaPartial (n : Nat) : StateM Depth Unit :=
  if n = 0 then modifyThe Depth raise else viaPartial (n - 1)
def Partial.ops : List (StateM Depth Unit) := [viaPartial 0]

/-- An opaque definition with a value. -/
opaque viaOpaque : Nat → StateM Depth Unit := fun _ => modifyThe Depth raise
def Opaque.ops : List (StateM Depth Unit) := [viaOpaque 0]

/-- Compiled code that is other code than the definition. -/
def writeImpl : StateM Depth Unit := modifyThe Depth raise
@[implemented_by writeImpl] def viaImpl : StateM Depth Unit := pure ()
def Impl.ops : List (StateM Depth Unit) := [viaImpl]

/-- A rule that blocks: `assume` stops a run that fails it with `Fault.blocked`. -/
def viaAssume {ε : Strata.Dyn.Exec.Eff} {E : Type} : Strata.Dyn.Exec.Sem ε E Unit :=
  Strata.Dyn.Exec.assume false "blocked"
def Blocks.ops {ε : Strata.Dyn.Exec.Eff} {E : Type} : List (Strata.Dyn.Exec.Sem ε E Unit) :=
  [viaAssume]

/-- A rule that fails: `semanticFailure` stops with `Fault.failure`. -/
def viaFailure {ε : Strata.Dyn.Exec.Eff} {E : Type} : Strata.Dyn.Exec.Sem ε E Unit :=
  Strata.Dyn.Exec.semanticFailure "failed"
def Fails.ops {ε : Strata.Dyn.Exec.Eff} {E : Type} : List (Strata.Dyn.Exec.Sem ε E Unit) :=
  [viaFailure]

/-- A rule that reaches the helper of the language-neutral `base.unreachable`, which fails. -/
def viaUnreachable {ε : Strata.Dyn.Exec.Eff} {E : Type} (b : Bool) : Strata.Dyn.Exec.Sem ε E Empty :=
  if b then Strata.Dyn.Exec.BaseRules.unreachable else Strata.Dyn.Exec.semanticGap "x"
def Unreachable.ops {ε : Strata.Dyn.Exec.Eff} {E : Type} : List (Strata.Dyn.Exec.Sem ε E Empty) :=
  [viaUnreachable true]

end StrataPython.Dyn.Sem.PartWritersTest

open StrataPython.Dyn.Sem StrataPython.Dyn.Sem.PartWritersTest

/-- The arguments of Python's check, for each list of operations. -/
macro "#check_parts " t:ident : command => `(command|
  #py_part_writers $t (lang := PyLang)
    (forbidden := [World.instHasPart_depth, PyLang.depth, World.mk, Depth.bracket,
      Strata.Dyn.Exec.HasInCall.inCall, Strata.Dyn.Exec.Effects.WorldSpec.inCall,
      Strata.Dyn.Exec.HasCall.callReq])
    (trusted := [Prim.bracketed, Prim.callClosureT, Prim.withDepth, Prim.withPyDepth, Prim.depthGet,
      instHasInCallWorld, Strata.Dyn.Exec.HasBracket.mreq, spec, Strata.Dyn.Exec.Effects.Within,
      -- The test's own `raise`, so that each case is rejected for its own way of writing the marker.
      PartWritersTest.raise,
      World.instHasPart_depth, World.instHasPart_store, World.instHasPart_modules,
      World.instHasPart_handled, World.instHasPart_guard, World.instHasPart_out]))

/--
error: #py_part_writers: Forge.ops reaches raiseOnly (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Forge.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.forged → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.raiseOnly), which names PyLang.depth outside the trusted primitives
-/
#guard_msgs in #check_parts Forge

/--
error: #py_part_writers: Abbrev.ops reaches viaAbbrev (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Abbrev.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaAbbrev), which names PyLang.depth outside the trusted primitives
-/
#guard_msgs in #check_parts Abbrev

/--
error: #py_part_writers: Wrapper.ops reaches viaWrapper (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Wrapper.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaWrapper), which names PyLang.depth outside the trusted primitives
-/
#guard_msgs in #check_parts Wrapper

/--
error: #py_part_writers: Id.ops reaches viaId._aux_5 (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Id.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaId → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaId._aux_5), which names PyLang.depth outside the trusted primitives
-/
#guard_msgs in #check_parts Id

/--
error: #py_part_writers: Partial.ops reaches viaPartial (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Partial.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaPartial), an opaque or partial definition whose code proofs don't see
-/
#guard_msgs in #check_parts Partial

/--
error: #py_part_writers: Opaque.ops reaches viaOpaque (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Opaque.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaOpaque), an opaque or partial definition whose code proofs don't see
-/
#guard_msgs in #check_parts Opaque

/--
error: #py_part_writers: Impl.ops reaches viaImpl (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Impl.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaImpl), whose compiled code is other code than its definition, or which has none
-/
#guard_msgs in #check_parts Impl


/--
error: #py_part_writers: Match.ops reaches viaMatch.match_1 (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Match.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaMatch → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaMatch.match_1), which names PyLang.casesOn outside the trusted primitives
-/
#guard_msgs in #check_parts Match

/--
error: #py_part_writers: Cases.ops reaches viaCases (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Cases.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaCases), which names PyLang.casesOn outside the trusted primitives
-/
#guard_msgs in #check_parts Cases

/--
error: #py_part_writers: LetPat.ops reaches viaMatch.match_1 (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.LetPat.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaLetPat → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaMatch.match_1), which names PyLang.casesOn outside the trusted primitives
-/
#guard_msgs in #check_parts LetPat

/--
error: #py_part_writers: Rec.ops reaches Rec.ops (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Rec.ops), whose compiled code is other code than its definition, or which has none
-/
#guard_msgs in #check_parts Rec

/--
error: #py_part_writers: Proj.ops reaches viaProj (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Proj.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaProj), which names StrataPython.Dyn.Sem.PyLang.proj outside the trusted primitives
-/
#guard_msgs in #check_parts Proj

/--
error: #py_part_writers: Axiom.ops reaches AxTy (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Axiom.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.AxTy), an axiom of this package
-/
#guard_msgs in #check_parts Axiom

/--
error: #py_part_writers: Mk.ops reaches sneakyInst (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Mk.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaMk → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.sneakyInst), which names PyLang.depth outside the trusted primitives
-/
#guard_msgs in #check_parts Mk

/--
error: #py_part_writers: Read.ops reaches viaRead (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Read.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaRead), which names Depth.bracket outside the trusted primitives
-/
#guard_msgs in #check_parts Read

/--
error: #py_part_writers: InCall.ops reaches viaInCall (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.InCall.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaInCall), which names Strata.Dyn.Exec.HasInCall.inCall outside the trusted primitives
-/
#guard_msgs in #check_parts InCall

/--
error: #py_part_writers: CallFn.ops reaches Strata.Dyn.Exec.callFn (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.CallFn.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaCallFn → Strata.Dyn.Exec.callFn), which names Strata.Dyn.Exec.HasCall.callReq outside the trusted primitives
-/
#guard_msgs in #check_parts CallFn

/--
error: #py_part_writers: DecEq.ops reaches instDecidableEqDepth.decEq.match_1 (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.DecEq.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaDecEq → StrataPython.Dyn.Sem.instDecidableEqDepth → StrataPython.Dyn.Sem.instDecidableEqDepth.decEq → StrataPython.Dyn.Sem.instDecidableEqDepth.decEq.match_1), which names Depth.casesOn outside the trusted primitives
-/
#guard_msgs in #check_parts DecEq

/--
error: #py_part_writers: SizeOf.ops reaches SizeOf.ops (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.SizeOf.ops), whose compiled code is other code than its definition, or which has none
-/
#guard_msgs in #check_parts SizeOf

/--
error: #py_part_writers: SpecInCall.ops reaches viaSpec (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.SpecInCall.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaSpec), which names Strata.Dyn.Exec.Effects.WorldSpec.inCall outside the trusted primitives
-/
#guard_msgs in #check_parts SpecInCall

/-- The arguments of the check that no Python rule blocks or fails, as `Table.lean` runs it. -/
macro "#check_faults " t:ident : command => `(command|
  #py_part_writers $t (lang := PyLang)
    (forbidden := [Strata.Dyn.Exec.Fault.failure, Strata.Dyn.Exec.Fault.blocked])
    (trusted := [StrataPython.Dyn.Sem.PySem.impl.base.unreachable]))

/--
error: #py_part_writers: Blocks.ops reaches Strata.Dyn.Exec.assume (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Blocks.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaAssume → Strata.Dyn.Exec.assume), which names Strata.Dyn.Exec.Fault.blocked outside the trusted primitives
-/
#guard_msgs in #check_faults Blocks

/--
error: #py_part_writers: Fails.ops reaches Strata.Dyn.Exec.semanticFailure (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Fails.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaFailure → Strata.Dyn.Exec.semanticFailure), which names Strata.Dyn.Exec.Fault.failure outside the trusted primitives
-/
#guard_msgs in #check_faults Fails

/--
error: #py_part_writers: Unreachable.ops reaches Strata.Dyn.Exec.semanticFailure (_private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.Unreachable.ops → _private.StrataPythonTest.Dyn.Sem.PartWritersTest.0.StrataPython.Dyn.Sem.PartWritersTest.viaUnreachable → Strata.Dyn.Exec.BaseRules.unreachable → Strata.Dyn.Exec.semanticFailure), which names Strata.Dyn.Exec.Fault.failure outside the trusted primitives
-/
#guard_msgs in #check_faults Unreachable
