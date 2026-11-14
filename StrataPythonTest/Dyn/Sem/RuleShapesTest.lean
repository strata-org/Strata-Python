/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
import StrataDyn.DSL
meta import StrataPython.Dyn.Sem.Table

set_option autoImplicit false

/-!
# `#py_rule_shapes`

Rules that `#py_rule_shapes` must reject: a computation written inline at `PyM`, a rule written
directly in `Sem`, a generic definition given an instance that isn't declared, a generic
definition given a `PyM` computation as an argument (written inline, or under a name of its own),
a definition whose own type names `PyM`, and a region that the rule makes itself, alone or next to
a handle of the operation's own region; a handle of a term made from a region, one whose input or
output works at the rule monad, and one given by a definition; and the ways
around a check of names alone: a computation typed by an abbreviation of `PyM`, an equation of
the monad with `PyM`, an instance of the record declared next to the rule, a class outside the
record, regions from a definition, a trusted primitive passed to a generic definition, and a
generic definition that reads the marker of a `Depth` it is given; a definition whose result is
`PyM` under a plain definition, one that takes no monad, a monad other than `PyM`, a second monad,
an instance given a level and a runner given a test that are computed from a `PyM` computation;
and an exception whose rule has the generic shape.  A rule that runs a generic definition or a
record primitive passes, and so does one with a handle of its operation's own region.
-/

namespace StrataPython.Dyn.Sem.RuleShapesTest

open Strata.Dyn Strata.Dyn.Exec StrataPython.Dyn.Sem

/-- Instructions over Python's values, one per shape. -/
public environment PyS extends Py where
  namespace ps
  open py
  insn generic (x : Value) (^err (exc : Value)) : Value
  insn primitive (^err (exc : Value)) : Value
  insn inline (x : Value) (^err (exc : Value)) : Value
  insn direct (x : Value) : Value
  insn handInst (x : Value) (^err (exc : Value)) : Value
  insn pymArg (x : Value) (^err (exc : Value)) : Value
  insn pymType (x : Value) (^err (exc : Value)) : Value
  insn hidden (x : Value) (^err (exc : Value)) : Value
  insn handles (x : Value) (^err (exc : Value)) : Value
  insn ownRegion (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn mixedHandles (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn notOwnRegion (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn monadicInput (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn monadicOutput (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn handleDef (&body (x : Value) : raising base.Unit) (^err (exc : Value)) : Value
  insn abbrevArg (x : Value) (^err (exc : Value)) : Value
  insn eqArg (x : Value) (^err (exc : Value)) : Value
  insn ownInst (x : Value) (^err (exc : Value)) : Value
  insn otherClass (x : Value) (^err (exc : Value)) : Value
  insn handlesDef (x : Value) (^err (exc : Value)) : Value
  insn trustedPrim (x : Value) (^err (exc : Value)) : Value
  insn readMarker (x : Value) (^err (exc : Value)) : Value
  insn plainResult (x : Value) (^err (exc : Value)) : Value
  insn noMonad (x : Value) (^err (exc : Value)) : Value
  insn otherMonad (x : Value) (^err (exc : Value)) : Value
  insn secondMonad (x : Value) (^err (exc : Value)) : Value
  insn instanceArg (x : Value) (^err (exc : Value)) : Value
  insn runnerArg (x : Value) (^err (exc : Value)) : Value
  insn listed (x : Value) (^err (exc : Value)) : Value
  end ps

#dyn_types PyS

/-- `x`, through a monad that it doesn't know. -/
def same {m : Type → Type 1} {V : Type} [PyPure m V] (x : m V) : m V := x

/-- `x`, typed at `PyM` although it takes a monad. -/
def atPyM {σ : Type} [Store σ] [Decode σ] {m : Type → Type 1} [PyPure m Value]
    (_x : PyM σ .pure true Value) : m Value := pure (Value.int 0)

/-- `PyM` under other names. -/
abbrev HiddenM (σ : Type) [Store σ] [Decode σ] : Type 1 := PyM σ .writes true Value
abbrev HiddenN (σ : Type) [Store σ] [Decode σ] : Type → Type 1 := PyM σ .writes true
abbrev HiddenC (σ : Type) [Store σ] [Decode σ] : Type 1 := PyM σ .calls true Value
abbrev DepthM (σ : Type) [Store σ] [Decode σ] : Type 1 := PyM σ .reads true Depth

/-- A definition generic in its monad that takes an equation of its monad with `PyM`. -/
def castIt {σ : Type} [Store σ] [Decode σ] {m : Type → Type 1} [PyPure m Value]
    (h : HiddenN σ = m) : m Value :=
  h ▸ (do Prim.setHandled .none; pure .none : PyM σ .writes true Value)

/-- `PyM` under plain definitions, which no check unfolds. -/
def PlainC (σ : Type) [Store σ] [Decode σ] : Type 1 := PyM σ .calls true Value
def PlainF (σ : Type) [Store σ] [Decode σ] : Type → Type 1 := PyM σ .pure true

set_option linter.unusedVariables false in
/-- Takes a monad that it never uses; its result is `PyM` under a plain definition. -/
def bracketAlias {m : Type → Type 1} {σ : Type} (s : Store σ) (d : Decode σ) : @PlainC σ s d :=
  (Prim.bracketed "x" (do Prim.setHandled .none; pure Value.none) : PyM σ .calls true Value)

/-- Takes no monad; its result is `PyM` under a plain definition. -/
def noM (σ : Type) [Store σ] [Decode σ] : PlainC σ := (PyM.gap "x" : PyM σ .calls true Value)

/-- Takes two monads, and runs a computation in the second. -/
def sameN {m n : Type → Type 1} [PyPure m Value] {α : Type} (x : n α) : n α := x

/-- A level computed from a `PyM` computation. -/
def lvlOf {σ : Type} [Store σ] [Decode σ] (_ : PyM σ .pure true Value) : Effects.Level := .pure

/-- A test computed from a `PyM` computation. -/
def condOf {σ : Type} [Store σ] [Decode σ] (_ : PyM σ .pure true Value) : Bool := true

/-- A class outside the record. -/
class Sneak (m : Type → Type 1) where
  sneak : m Unit

/-- Generic in its monad, over the class outside the record. -/
def viaSneak {m : Type → Type 1} [PyPure m Value] [Sneak m] : m Value := do
  Sneak.sneak
  pure (PyPure.imm (m := m) (Imm.bool true))

/-- Generic in its monad: the marker of the depth that `x` gives, as an `int`. -/
def markerOf {m : Type → Type 1} [PyPure m Value] (x : m Depth) : m Value := do
  let d ← x
  pure (PyPure.imm (m := m) (Imm.int d.bracket))

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε]

/-- The instance of the record at `PyM`, as a definition, not an instance. -/
@[instance_reducible] def handMade : PyCalls (PyM σ .calls true) Value := inferInstance

/-- `bool(x)`, through a generic definition. -/
@[dyn_sem PyS.generic] def generic (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.notValue (m := PyM σ .calls true) x)

/-- A new `{}`, through a record primitive. -/
@[dyn_sem PyS.primitive] def primitive (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (PyPure.allocDict (m := PyM σ .reads true))

/-- `bool(x)`, with the computation written inline at `PyM`. -/
@[dyn_sem PyS.inline] def inline (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (do
    let b ← Proto.truthy (m := PyM σ .calls true) x
    pure (.bool b))

/-- `x`, directly in `Sem`. -/
@[dyn_sem PyS.direct] def direct (x : Value) : Sem ε E Value := pure x

/-- `bool(x)`, with a hand-made instance of the record. -/
@[dyn_sem PyS.handInst] def handInst (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (@Proto.notValue (PyM σ .calls true) Value handMade x)

/-- A gap at `PyM`, passed to a generic definition. -/
@[dyn_sem PyS.pymArg] def pymArg (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (same (m := PyM σ .pure true) (PyM.gap "x"))

/-- A definition whose type names `PyM`. -/
@[dyn_sem PyS.pymType] def pymType (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (atPyM (σ := σ) (m := PyM σ .pure true) (PyM.gap "x"))

/-- A gap at `PyM`, under a name of its own. -/
def hiddenGap : PyM σ .pure true Value := PyM.gap "x"

/-- A `PyM` computation under its own name, passed to a generic definition. -/
@[dyn_sem PyS.hidden] def hidden (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (same (m := PyM σ .pure true) hiddenGap)

/-- `bool(x)`, with a region that the rule makes itself. -/
@[dyn_sem PyS.handles] def handles (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[fun _ => pure (.ok .none)] (Proto.notValue (m := PyM σ .calls true) x)

/-- `bool(None)`, with a handle of the operation's own region, which passes. -/
@[dyn_sem PyS.ownRegion] def ownRegion (body : Region ε [Value] (Except Value Unit))
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[regionHandle body oneValue fun _ => .none]
    (Proto.notValue (m := PyM σ .calls true) .none)

/-- `bool(None)`, with a handle of the operation's own region and a region that the rule makes
itself. -/
@[dyn_sem PyS.mixedHandles] def mixedHandles (body : Region ε [Value] (Except Value Unit))
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[regionHandle body oneValue fun _ => .none,
    fun _ => pure (.ok .none)] (Proto.notValue (m := PyM σ .calls true) .none)

/-- `bool(None)`, with a handle of a region that is not a variable of the rule, but a term made
from one. -/
@[dyn_sem PyS.notOwnRegion] def notOwnRegion (body : Region ε [Value] (Except Value Unit))
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[regionHandle (id body) oneValue fun _ => .none]
    (Proto.notValue (m := PyM σ .calls true) .none)

/-- `bool(None)`, with a handle of the operation's own region whose input works at the rule
monad. -/
@[dyn_sem PyS.monadicInput] def monadicInput (body : Region ε [Value] (Except Value Unit))
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err
    #[regionHandle body (fun a => if condOf (σ := σ) (PyM.gap "x") then a[0]? else none)
      fun _ => .none]
    (Proto.notValue (m := PyM σ .calls true) .none)

/-- `bool(None)`, with a handle of the operation's own region whose output works at the rule
monad. -/
@[dyn_sem PyS.monadicOutput] def monadicOutput (body : Region ε [Value] (Except Value Unit))
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err
    #[regionHandle body oneValue
      fun _ => if condOf (σ := σ) (PyM.gap "x") then .none else .none]
    (Proto.notValue (m := PyM σ .calls true) .none)

/-- A handle of a region, under a name of its own. -/
def handleOf (body : Region ε [Value] (Except Value Unit)) :
    Array Value → Sem ε E (Except Value Value) :=
  regionHandle body oneValue fun _ => .none

/-- `bool(None)`, with a handle of the operation's own region given by a definition, which the
check doesn't unfold. -/
@[dyn_sem PyS.handleDef] def handleDef (body : Region ε [Value] (Except Value Unit))
    (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[handleOf body] (Proto.notValue (m := PyM σ .calls true) .none)

/-- A write of the handled exception, typed by an abbreviation of `PyM`. -/
def hiddenWrite : HiddenM σ := do Prim.setHandled .none; pure .none

/-- A computation typed by an abbreviation of `PyM`, passed to a generic definition. -/
@[dyn_sem PyS.abbrevArg] def abbrevArg (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (same (m := PyM σ .writes true) (hiddenWrite (σ := σ)))

/-- A generic definition given an equation of its monad with `PyM`. -/
@[dyn_sem PyS.eqArg] def eqArg (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (castIt (σ := σ) (m := PyM σ .writes true) rfl)

/-- An instance of the record declared next to the rule, whose `allocDict` writes. -/
@[instance_reducible] instance (priority := low) ownWrites : PyPure (PyM σ .writes true) Value :=
  { (inferInstance : PyPure (PyM σ .writes true) Value) with
    allocDict := do Prim.setHandled .none; PyPure.allocDict (m := PyM σ .writes true) }

/-- A record primitive through that instance. -/
@[dyn_sem PyS.ownInst] def ownInst (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (@PyPure.allocDict (PyM σ .writes true) Value ownWrites)

/-- The class outside the record, at `PyM`, writing. -/
instance sneakPyM : Sneak (PyM σ .writes true) := ⟨Prim.setHandled .none⟩

/-- A generic definition over the class outside the record. -/
@[dyn_sem PyS.otherClass] def otherClass (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (viaSneak (m := PyM σ .writes true))

/-- Regions from a definition. -/
def ownHandles {ε' : Eff} {E' : Type} : Handles ε' E' := #[fun _ => pure (.ok .none)]

/-- `bool(x)`, with regions from a definition. -/
@[dyn_sem PyS.handlesDef] def handlesDef (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err ownHandles (Proto.notValue (m := PyM σ .calls true) x)

/-- The trusted bracket, run outside `callBuiltin`, typed by an abbreviation. -/
def bracketWrite : HiddenC σ := Prim.bracketed "x" (do Prim.setHandled .none; pure Value.none)

/-- The bracket passed to a generic definition. -/
@[dyn_sem PyS.trustedPrim] def trustedPrim (_x : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (same (m := PyM σ .calls true) (bracketWrite (σ := σ)))

/-- The trusted `depthGet`, typed by an abbreviation. -/
def depthAt : DepthM σ := Prim.depthGet

/-- A rule that returns the call bracket's marker. -/
@[dyn_sem PyS.readMarker] def readMarker (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (markerOf (m := PyM σ .reads true) (depthAt (σ := σ)))

/-- A definition that takes a monad but whose result is `PyM` under a plain definition. -/
@[dyn_sem PyS.plainResult] def plainResult (_x : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (bracketAlias (m := PyM σ .calls true) (σ := σ) inferInstance inferInstance)

/-- A definition that takes no monad. -/
@[dyn_sem PyS.noMonad] def noMonad (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (noM σ)

/-- A generic definition at a monad other than `PyM`. -/
@[dyn_sem PyS.otherMonad] def otherMonad (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[]
    (@PyPure.allocDict (PlainF σ) Value (inferInstanceAs (PyPure (PyM σ .pure true) Value)))

/-- A generic definition given a second monad, `PyM`, besides its own. -/
@[dyn_sem PyS.secondMonad] def secondMonad (_x : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree err #[] (sameN (m := PyM σ .pure true) (n := PyM σ .writes true) (hiddenWrite (σ := σ)))

/-- A record instance given a level computed from a `PyM` computation, with the runner's own level
a plain constant. -/
@[dyn_sem PyS.instanceArg] def instanceArg (_x : Value) (err : Target E [Value]) :
    Sem ε E Value :=
  runRuleFree (e := .pure) err #[] (PyPure.allocDict (m := PyM σ (lvlOf (σ := σ) (PyM.gap "x")) true))

/-- A runner given a test computed from a `PyM` computation. -/
@[dyn_sem PyS.runnerArg] def runnerArg (_x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleIf (condOf (σ := σ) (PyM.gap "x")) err #[] (PyPure.allocDict (m := PyM σ .reads false))
    (PyPure.allocDict (m := PyM σ .reads true))

/-- `bool(x)`, through a generic definition, but listed as an exception. -/
@[dyn_sem PyS.listed] def listed (x : Value) (err : Target E [Value]) : Sem ε E Value :=
  runRuleFree err #[] (Proto.notValue (m := PyM σ .calls true) x)

/-- An output write in `Sem`, under a name like those a table gives its wrappers. -/
def Shapes.impl.write : Sem ε E Value := do
  modifyThe Output fun o => ⟨o.pieces.push "x"⟩
  pure .none

/-- A rule that the shape check accepts, one that it rejects, and the write. -/
def Shapes.ops (err : Target E [Value]) : List (Sem ε E Value) :=
  [generic (σ := σ) .none err, inline (σ := σ) .none err, Shapes.impl.write (σ := σ)]
end

/--
error: #py_rule_shapes: the rule of ps.inline (inline) is not a runner of a definition generic in its monad: bind takes an instance of a class outside the record: Bind
  m
---
error: #py_rule_shapes: the rule of ps.direct (direct) is not a runner of a definition generic in its monad: its body is pure, not a runner
---
error: #py_rule_shapes: the rule of ps.handInst (handInst) is not a runner of a definition generic in its monad: Proto.notValue: an instance argument is not one of the record's: handMade
---
error: #py_rule_shapes: the rule of ps.pymArg (pymArg) is not a runner of a definition generic in its monad: same takes an argument in its monad: m
  V
---
error: #py_rule_shapes: the rule of ps.pymType (pymType) is not a runner of a definition generic in its monad: atPyM's type names the rule monad
---
error: #py_rule_shapes: the rule of ps.hidden (hidden) is not a runner of a definition generic in its monad: same takes an argument in its monad: m
  V
---
error: #py_rule_shapes: the rule of ps.handles (handles) is not a runner of a definition generic in its monad: its regions are not the operation's own: #[fun
    x =>
  pure (Except.ok Value.none)]
---
error: #py_rule_shapes: the rule of ps.mixedHandles (mixedHandles) is not a runner of a definition generic in its monad: its regions are not the operation's own: #[regionHandle
    body oneValue fun x => Value.none,
  fun x => pure (Except.ok Value.none)]
---
error: #py_rule_shapes: the rule of ps.notOwnRegion (notOwnRegion) is not a runner of a definition generic in its monad: its regions are not the operation's own: #[regionHandle
    (id body) oneValue fun x => Value.none]
---
error: #py_rule_shapes: the rule of ps.monadicInput (monadicInput) is not a runner of a definition generic in its monad: its regions are not the operation's own: #[regionHandle
    body (fun a => if condOf (PyM.gap "x") = true then a[0]? else none) fun x => Value.none]
---
error: #py_rule_shapes: the rule of ps.monadicOutput (monadicOutput) is not a runner of a definition generic in its monad: its regions are not the operation's own: #[regionHandle
    body oneValue fun x => if condOf (PyM.gap "x") = true then Value.none else Value.none]
---
error: #py_rule_shapes: the rule of ps.handleDef (handleDef) is not a runner of a definition generic in its monad: its regions are not the operation's own: #[handleOf
    body]
---
error: #py_rule_shapes: the rule of ps.abbrevArg (abbrevArg) is not a runner of a definition generic in its monad: same takes an argument in its monad: m
  V
---
error: #py_rule_shapes: the rule of ps.eqArg (eqArg) is not a runner of a definition generic in its monad: castIt's type names the rule monad
---
error: #py_rule_shapes: the rule of ps.ownInst (ownInst) is not a runner of a definition generic in its monad: PyPure.allocDict: an instance argument is not one of the record's: ownWrites
---
error: #py_rule_shapes: the rule of ps.otherClass (otherClass) is not a runner of a definition generic in its monad: viaSneak takes an instance of a class outside the record: Sneak
  m
---
error: #py_rule_shapes: the rule of ps.handlesDef (handlesDef) is not a runner of a definition generic in its monad: its regions are not the operation's own: ownHandles
---
error: #py_rule_shapes: the rule of ps.trustedPrim (trustedPrim) is not a runner of a definition generic in its monad: same takes an argument in its monad: m
  V
---
error: #py_rule_shapes: the rule of ps.readMarker (readMarker) is not a runner of a definition generic in its monad: markerOf's type names the rule monad
---
error: #py_rule_shapes: the rule of ps.plainResult (plainResult) is not a runner of a definition generic in its monad: bracketAlias's result is not in its monad: PlainC
  σ
---
error: #py_rule_shapes: the rule of ps.noMonad (noMonad) is not a runner of a definition generic in its monad: noM takes no monad
---
error: #py_rule_shapes: the rule of ps.otherMonad (otherMonad) is not a runner of a definition generic in its monad: PyPure.allocDict's monad is not PyM
---
error: #py_rule_shapes: the rule of ps.secondMonad (secondMonad) is not a runner of a definition generic in its monad: an argument of sameN works at the rule monad: PyM
  σ✝ Effects.Level.writes true
---
error: #py_rule_shapes: the rule of ps.instanceArg (instanceArg) is not a runner of a definition generic in its monad: PyPure.allocDict: an argument of the instance instPyPurePyMValue works at the rule monad: lvlOf
  (PyM.gap "x")
---
error: #py_rule_shapes: the rule of ps.runnerArg (runnerArg) is not a runner of a definition generic in its monad: an argument of runRuleIf works at the rule monad: condOf
  (PyM.gap "x")
---
error: #py_rule_shapes: the rule of ps.listed is listed as an exception, but it runs a definition generic in its monad
-/
#guard_msgs in
#py_rule_shapes PyS (exceptions := [ps.listed])

/-- error: #py_rule_shapes: ps.nothing is not an instruction of PyS -/
#guard_msgs in
#py_rule_shapes PyS (exceptions := [ps.nothing])

end StrataPython.Dyn.Sem.RuleShapesTest

open StrataPython.Dyn.Sem StrataPython.Dyn.Sem.RuleShapesTest

/-! The walk's list of the definitions below the rule monad has the rule that the shape check
rejects and the write, which no table made, but not the rule that the check accepts.  The record's
instances are trusted here, so that the list stays short. -/
/--
info: #py_part_writers: StrataPython.Dyn.Sem.RuleShapesTest.Shapes.ops reaches 18 definitions below the rule monad, which name StrataPython.Dyn.Sem.PyLang, StrataPython.Dyn.Sem.World, Strata.Dyn.Exec.Sem, StrataPython.Dyn.Sem.Depth or a constant whose type does:
StrataPython.Dyn.Sem.BEff
StrataPython.Dyn.Sem.BTree
StrataPython.Dyn.Sem.ContOK
StrataPython.Dyn.Sem.Handles
StrataPython.Dyn.Sem.HandlesOK
StrataPython.Dyn.Sem.Proved
StrataPython.Dyn.Sem.PyFn
StrataPython.Dyn.Sem.PyLang.out
StrataPython.Dyn.Sem.PyM
StrataPython.Dyn.Sem.PyM.bind'
StrataPython.Dyn.Sem.PyM.pure'
StrataPython.Dyn.Sem.RuleShapesTest.Shapes.impl.write
StrataPython.Dyn.Sem.RuleShapesTest.inline
StrataPython.Dyn.Sem.StartFree
StrataPython.Dyn.Sem.TreeOK
StrataPython.Dyn.Sem.bInst
StrataPython.Dyn.Sem.runRuleFree
StrataPython.Dyn.Sem.treeOf
-/
#guard_msgs in
#py_part_writers Shapes (lang := PyLang)
  (forbidden := [World.instHasPart_depth, PyLang.depth, World.mk, Depth.bracket])
  (trusted := [Prim.bracketed, Prim.callClosureT, Prim.withDepth, Prim.withPyDepth, Prim.depthGet,
    instHasInCallWorld, Strata.Dyn.Exec.HasBracket.mreq, spec, Strata.Dyn.Exec.Effects.Within,
    World.instHasPart_depth, World.instHasPart_store, World.instHasPart_modules,
    World.instHasPart_handled, World.instHasPart_guard, World.instHasPart_out,
    instPyPurePyMValue, instPyReadsPyMValueOfAtLeastReads, instPyCallsPyMCallsValue])
  (below := [PyLang, World, Strata.Dyn.Exec.Sem, Depth])
