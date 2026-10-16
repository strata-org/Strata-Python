/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Build
public import StrataPython.Mantle.Env
-- Emitting instructions over `Py.env` needs the signature representation at
-- code-generation time.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Emitting Python

`PyM` emits a Python function over `Py.env`, on top of `Mantle.Build`.  It carries the
enclosing handler: every raising operation passes it as its `err` successor.

The sections below group the operations.

A function body is emitted inside `buildFunc`, which installs the handler that returns a
failure to the caller before the body runs.  Misusing blocks is an error, as in
`Mantle.Build`, and `buildFunc` fails if one was recorded or the function is not well formed.
Block parameters are not decided here: locals stay in cells until ref-to-reg.

An emitter that takes a body to emit, such as `withHandler` or `forEach`, runs it in any
`MonadPy` monad: `PyM` itself, or the translator's `TransM` above it.
-/

namespace StrataPython.Mantle.PyBuild

open Strata.Mantle

public section

/-- What Python carries on top of the generic builder. -/
structure Frame where
  /-- Where a failing operation transfers.  Never absent: `buildFunc` installs a handler
  that returns the failure to the caller before the body is emitted.  Its arguments are
  pre-bound, and `err` supplies the exception after them. -/
  handler : BlockValue
  /-- The cell holding each local in scope. -/
  locals : Build.StrMap ValId := ∅

/-- Emitting a Python function, with `α` the annotation a front end threads through —
`SourceRange` in the translator, `Unit` in a test. -/
abbrev PyM (α : Type) := StateT Frame (BuildM Py.env α)

/-- A monad that emits Python by running `PyM α`: `PyM α` itself, or a reader or state layer
over one, such as the translator's `TransM`. -/
class MonadPy (α : outParam Type) (m : Type → Type) where
  /-- Run a `PyM` action. -/
  liftPy {β : Type} : PyM α β → m β

export MonadPy (liftPy)

variable {α β : Type} {m : Type → Type}

instance : MonadPy α (PyM α) := ⟨id⟩

instance {ρ : Type} [MonadPy α m] : MonadPy α (ReaderT ρ m) := ⟨fun x _ => liftPy x⟩

instance {σ : Type} [Monad m] [MonadPy α m] : MonadPy α (StateT σ m) :=
  ⟨fun x s => do return (← liftPy x, s)⟩

/-! ## The enclosing handler -/

/-- Where a failing operation currently reports. -/
def handler : PyM α BlockValue := (·.handler) <$> get

/-- The enclosing handler with the exception `e` passed: where raising `e` transfers. -/
def raiseTo (e : ValId) : PyM α BlockValue := do
  let h ← handler
  return { h with args := h.args.push e }

/-- Emit `act` with failures going to `k`, whose arguments are pre-bound, restoring the old
handler afterwards, so handlers nest as `try`s do. -/
def withHandlerTo [Monad m] [MonadPy α m] (k : BlockValue) (act : m β) : m β := do
  let saved ← liftPy (handler (α := α))
  liftPy (modify ({ · with handler := k }) : PyM α Unit)
  let r ← act
  liftPy (modify ({ · with handler := saved }) : PyM α Unit)
  return r

/-- Emit `act` with failures going to the block `l`, which takes only the exception. -/
def withHandler [Monad m] [MonadPy α m] (l : Label) (act : m β) : m β :=
  withHandlerTo (Build.goto l) act

/-! ## Annotations

Every emitter below takes an optional annotation; without one it uses the default the
builder carries.  `withInfo` is how a translator sets that default once for everything a
source construct emits. -/

/-- Emit `act` with `info` as the default annotation, restoring the old one afterwards. -/
def withInfo (info : α) (act : PyM α β) : PyM α β :=
  fun env => Build.withInfo info (act env)

/-- The annotation to use: `info` if given, the current default otherwise. -/
def resolveInfo (info : Option α) : PyM α α := Build.resolveInfo (env := Py.env) info

/-- Emit the base constant `c`, named after `name`. -/
def emitConst (name : Name) (c : Const) (info : Option α := none) : PyM α ValId :=
  Build.emitConst (env := Py.env) name c info

/-! ## Operations

One emitter per result type and failure behaviour.  Every Python operation is monomorphic,
so `typeArgs` is always `ta[]`, which `infer_type_args` fills in. -/

/-- An operation that cannot fail and produces a Python value. -/
def emitTotal {isig : InsnSig Py.env} (name : Name) (r : InsnRef Py.env isig)
    (args : Array ValId) (info : Option α := none)
    (typeArgs : KindedTypeArgsFor r (some Py.Value.ty) := by infer_type_args) : PyM α ValId :=
  Build.emitApply name Py.Value.ty r args (info := info) (typeArgs := typeArgs)

/-- A raising operation producing a Python value: its `err` successor is the enclosing
handler. -/
def emitFailing {isig : InsnSig Py.env} (name : Name) (r : InsnRef Py.env isig)
    (args : Array ValId) (info : Option α := none)
    (typeArgs : KindedTypeArgsFor r (some Py.Value.ty) := by infer_type_args) : PyM α ValId := do
  Build.emitApply name Py.Value.ty r args #[← handler] (info := info) (typeArgs := typeArgs)

/-- An operation that cannot fail and only acts: its result is `()`. -/
def emitEffect {isig : InsnSig Py.env} (name : Name) (r : InsnRef Py.env isig)
    (args : Array ValId) (info : Option α := none)
    (typeArgs : KindedTypeArgsFor r (some Base.Unit.ty) := by infer_type_args) : PyM α ValId :=
  Build.emitApply name Base.Unit.ty r args (info := info) (typeArgs := typeArgs)

/-- A raising operation that only acts: its result is `()`, and its `err` successor is the
enclosing handler. -/
def emitActing {isig : InsnSig Py.env} (name : Name) (r : InsnRef Py.env isig)
    (args : Array ValId) (info : Option α := none)
    (typeArgs : KindedTypeArgsFor r (some Base.Unit.ty) := by infer_type_args) : PyM α ValId := do
  Build.emitApply name Base.Unit.ty r args #[← handler] (info := info) (typeArgs := typeArgs)

/-- An operation producing a base `Bool`, which is what a `branch` takes. -/
def emitTest {isig : InsnSig Py.env} (name : Name) (r : InsnRef Py.env isig)
    (args : Array ValId) (info : Option α := none)
    (typeArgs : KindedTypeArgsFor r (some Base.Bool.ty) := by infer_type_args) : PyM α ValId :=
  Build.emitApply name Base.Bool.ty r args (info := info) (typeArgs := typeArgs)

/-- `bool(v)`: the base `Bool` a `branch` takes.  It can fail — `__bool__` and `__len__`
are arbitrary code — so its `err` successor is the enclosing handler. -/
def truthy (v : ValId) (info : Option α := none) : PyM α ValId := do
  Build.emitApply (env := Py.env) (.str .base "cond") Base.Bool.ty Py.truthy #[v]
    #[← handler] (info := info)

/-- Whether the exception `exc` matches `except type`: the base `Bool` a `branch` takes.  It
fails for a `type` that is not an exception class, so its `err` successor is the enclosing
handler. -/
def excMatch (exc type : ValId) (info : Option α := none) : PyM α ValId := do
  Build.emitApply (env := Py.env) (.str .base "match") Base.Bool.ty Py.excMatch #[exc, type]
    #[← handler] (info := info)

/-! ## Literals

Each is a base constant and the operation that boxes it. -/

def intLit (i : Int) (info : Option α := none) : PyM α ValId := do
  emitTotal (.str .base "int") Py.intLit #[← emitConst (.str .base "c") (.int i) info] info

def floatLit (f : Float) (info : Option α := none) : PyM α ValId := do
  emitTotal (.str .base "float") Py.floatLit
      #[← emitConst (.str .base "c") (.float f) info] info

def strLit (s : String) (info : Option α := none) : PyM α ValId := do
  emitTotal (.str .base "str") Py.strLit #[← emitConst (.str .base "c") (.str s) info] info

def boolLit (b : Bool) (info : Option α := none) : PyM α ValId := do
  emitTotal (.str .base "bool") Py.boolLit #[← emitConst (.str .base "c") (.bool b) info] info

def bytesLit (s : String) (info : Option α := none) : PyM α ValId := do
  emitTotal (.str .base "bytes") Py.bytesLit #[← emitConst (.str .base "c") (.str s) info] info

def noneLit (info : Option α := none) : PyM α ValId := emitTotal (.str .base "none") Py.noneLit
    #[] info

def ellipsisLit (info : Option α := none) : PyM α ValId :=
  emitTotal (.str .base "ellipsis") Py.ellipsisLit #[] info

/-! ## Blocks and values

`Mantle.Build`'s operations, at `Py.env`. -/

/-- The stem of the values named after the Python name `x`: the one segment `x`. -/
def stem (x : String) : Name := .str .base x

/-- The stem of the cell holding the Python name `x`: the two segments `x` and `cell`. -/
def cellStem (x : String) : Name := .str (stem x) "cell"

/-- The stem of the cell holding the default of the parameter `x`: the segments `x` and
`default`. -/
def defaultStem (x : String) : Name := .str (stem x) "default"

/-- A fresh Python value, named after `name`. -/
def freshVal (name : Name) : PyM α (ValDecl Py.env) :=
  Build.freshVal (env := Py.env) (α := α) name Py.Value.ty

/-- A label for a block not yet emitted: `base.n`. -/
def freshLabel (base : String := Build.blockBase) : PyM α Label :=
  Build.freshLabel (env := Py.env) (α := α) base

/-- Open the block called `label`, taking `params`.  Opening a block while another is open
is an error. -/
def startBlock (label : Label) (params : Array (ValDecl Py.env) := #[]) : PyM α Unit :=
  Build.startBlock (α := α) label params

/-- Open a fresh block, labelled `base.n`, and hand back its label. -/
def startFreshBlock (params : Array (ValDecl Py.env) := #[])
    (base : String := Build.blockBase) : PyM α Label :=
  Build.startFreshBlock (α := α) params base

/-- Open the block called `label`, taking one fresh value of type `t` named after `name`, and
hand back that value: a handler's exception, a join's result. -/
def startBlockWith (label : Label) (name : Name) (t : TypeExpr Py.env := Py.Value.ty) :
    PyM α ValId :=
  Build.startBlockWith (α := α) label name t

/-- Whether a block is open, so that instructions can be emitted. -/
def isOpen : PyM α Bool := do return (← getThe (Build.State Py.env α)).body.label.isSome

/-- Close the open block with `term`.  With no block open, it is an error. -/
def finishBlock (term : Terminator Py.env α) (info : Option α := none) : PyM α Unit :=
  Build.finishBlock term info

/-- Close the open block with `jump k`. -/
def jump (k : BlockValue) (info : Option α := none) : PyM α Unit :=
  Build.jump (env := Py.env) k info

/-- Close the open block with `branch cond t f`. -/
def branch (cond : ValId) (t f : BlockValue) (info : Option α := none) : PyM α Unit :=
  Build.branch (env := Py.env) cond t f info

/-- Close the open block with `unreachable`. -/
def unreachable (info : Option α := none) : PyM α Unit :=
  Build.unreachable (env := Py.env) info

/-! ## Attributes -/

/-- `obj.name`, which can raise. -/
def getAttr (obj : ValId) (name : String) (info : Option α := none) : PyM α ValId := do
  emitFailing (stem name) Py.attr #[obj, ← emitConst (.str .base "attr") (.str name) info]
    info

/-- `obj.name = val`, which can raise. -/
def setAttr (obj : ValId) (name : String) (val : ValId) (info : Option α := none) :
    PyM α ValId := do
  emitActing (stem name) Py.setAttr
    #[obj, ← emitConst (.str .base "attr") (.str name) info, val] info

/-- `del obj.name`, which can raise. -/
def delAttr (obj : ValId) (name : String) (info : Option α := none) : PyM α ValId := do
  emitActing (stem name) Py.delAttr #[obj, ← emitConst (.str .base "attr") (.str name) info]
    info

/-! ## Closures

A code pointer is a constant naming a function of the *module*; a closure pairs it with the
cells it captures.  A module-level function is the case with no cells. -/

/-- Emit a code pointer to `target`, a function the module defines: the constant
`.func target`. -/
def emitFunc (target : Name) (info : Option α := none) : PyM α ValId :=
  Build.emitFunc (env := Py.env) target info

/-- A callable value: the code, and the cells it captures. -/
def mkClosure (code : ValId) (cells : Array ValId) (info : Option α := none) : PyM α ValId :=
  emitTotal (.str .base "clo") Py.mkClosure (#[code] ++ cells) info

/-- A callable value for a module-level function, which captures nothing. -/
def funcValue (target : Name) (info : Option α := none) : PyM α ValId := do
  mkClosure (← emitFunc target info) #[] info

/-! ## Locals

A local is a cell: an assignment writes it and a read reads it.  A cell holds `undef` until
its first assignment, so a read before assignment can be checked. -/

/-- The cell of a local in scope, if it is one. -/
def cellOf? (name : String) : PyM α (Option ValId) := (·.locals.find? name) <$> get

/-- A fresh cell holding `v`, named after `name`. -/
def newCell (name : Name) (v : ValId) (info : Option α := none) : PyM α ValId :=
  Build.emitApply (env := Py.env) name Py.cell.ty Base.refNew #[v] (info := info)

/-- Make a cell for `name`, holding "not yet assigned", and record it. -/
def declareLocal (name : String) (info : Option α := none) : PyM α ValId := do
  let nameConst ← emitConst (.str .base "n") (.str name) info
  let undef ← emitTotal (stem name) Py.undef #[nameConst] info
  let cell ← newCell (cellStem name) undef info
  modify fun e => { e with locals := e.locals.insert name cell }
  return cell

/-- Record `cell`, a captured cell the function takes as a parameter, as the cell of `name`. -/
def captureCell (name : String) (cell : ValId) : PyM α Unit :=
  modify fun e => { e with locals := e.locals.insert name cell }

/-- Read a cell.  `name` is only what the result is called. -/
def readCell (cell : ValId) (name : Name) (info : Option α := none) : PyM α ValId :=
  Build.emitApply (env := Py.env) name Py.Value.ty Base.refGet #[cell] (info := info)

/-- Write a cell. -/
def writeCell (cell : ValId) (v : ValId) (info : Option α := none) : PyM α ValId :=
  Build.emitApply (env := Py.env) (.str .base "set") Base.Unit.ty Base.refSet #[cell, v]
    (info := info) (typeArgs := ta[Py.Value])

/-! ## Globals and imports

A global is a cell too, named by its module and its name rather than recorded in the frame.
`loadGlobal` reads a name, falling back to the builtins; `requireGlobal` is the cell's checked
read without that fallback, as `del` needs. -/

/-- The cell of the global `name` of `module`. -/
def globalCell (module name : String) (info : Option α := none) : PyM α ValId := do
  let m ← emitConst (.str .base "m") (.str module) info
  let n ← emitConst (.str .base "n") (.str name) info
  Build.emitApply (env := Py.env) (cellStem name) Py.cell.ty Py.globalCell #[m, n]
    (info := info)

/-- The global `name`'s value, raising `NameError` if it is unassigned, without the builtins
fallback: the check of `DELETE_NAME` and `DELETE_GLOBAL`.  Reads use `loadGlobal`. -/
def requireGlobal (module name : String) (info : Option α := none) : PyM α ValId := do
  let v ← readCell (← globalCell module name info) (stem name) info
  let excType ← emitConst (.str .base "e") (.str "NameError") info
  let msg ← emitConst (.str .base "msg") (.str s!"name '{name}' is not defined") info
  emitFailing (stem name) Py.requireDefined #[v, excType, msg] info

/-- Read the name `name` in `module`: its global, else its builtin, else `NameError`. -/
def loadGlobal (module name : String) (info : Option α := none) : PyM α ValId := do
  let m ← emitConst (.str .base "m") (.str module) info
  let n ← emitConst (.str .base "n") (.str name) info
  emitFailing (stem name) Py.loadGlobal #[m, n] info

/-- Write the global `name` of `module`. -/
def writeGlobal (module name : String) (v : ValId) (info : Option α := none) :
    PyM α ValId := do
  writeCell (← globalCell module name info) v info

/-- The module object for `module`, a fully qualified name, imported if need be. -/
def importModule (module : String) (info : Option α := none) : PyM α ValId := do
  emitFailing (.str .base "mod") Py.importModule
      #[← emitConst (.str .base "m") (.str module) info] info

/-- `from module import name`, read once. -/
def importFrom (module name : String) (info : Option α := none) : PyM α ValId := do
  let m ← emitConst (.str .base "m") (.str module) info
  let n ← emitConst (.str .base "n") (.str name) info
  emitFailing (stem name) Py.importFrom #[m, n] info

/-! ## Regions -/

/-- `py.forEach iterable`, its `err` successor the enclosing handler.  The body region takes
the item, emitted by `body` with failures going to the region's own handler, which returns
them as `error`.  Falling off the end of `body` returns `ok ()`. -/
def forEach [Monad m] [MonadPy α m] (iterable : ValId) (body : ValId → m Unit)
    (info : Option α := none) : m Unit := do
  let _ : MonadLiftT (BuildM Py.env α) m := ⟨fun x => liftPy (α := α) (monadLift x)⟩
  let each : m (Region Py.env α) := do
    let item ← liftPy (freshVal (α := α) (stem "item"))
    Prod.fst <$> Build.regionWith #[item] (base := "each") do
      let propagate ← liftPy (freshLabel (α := α) "propagate")
      withHandler propagate (body item.id)
      liftPy (α := α) do
        if ← isOpen then
          let u ← Build.emitApply (env := Py.env) (α := α) (stem "unit") Base.Unit.ty
            Base.Unit.unit #[]
          let ok ← Build.emitApply (env := Py.env) (α := α) (stem "ok")
            (Py.raising.ty Base.Unit.ty) Base.Except.ok #[u]
          Build.ret (env := Py.env) (α := α) ok
        let exc ← startBlockWith propagate (stem "exc")
        let e ← Build.emitApply (env := Py.env) (α := α) (stem "exc")
          (Py.raising.ty Base.Unit.ty) Base.Except.error #[exc]
        Build.ret (env := Py.env) (α := α) e
  let h ← liftPy (handler (α := α))
  discard <| Build.emitApplyWith (stem "each") Base.Unit.ty Py.forEach #[iterable] #[h]
    #[each] info

/-! ## Completions

How a block that a `finally` protects finished, as a value.  A `finally` body is emitted
once, takes the pending completion as its parameter, and ends by dispatching on it; `Py`'s
module docstring shows the shape. -/

/-- A fresh completion-typed value: what a `finally` or dispatch block takes. -/
def freshComp (name : Name) : PyM α (ValDecl Py.env) :=
  Build.freshVal (env := Py.env) (α := α) name Py.Completion.ty

/-- Build a completion: apply one constructor of `py.Completion`, which takes no type
arguments. -/
def emitComp {isig : InsnSig Py.env} (ctor : InsnRef Py.env isig) (args : Array ValId)
    (info : Option α := none)
    (typeArgs : KindedTypeArgsFor ctor (some Py.Completion.ty) := by infer_type_args) :
    PyM α ValId :=
  Build.emitApply (.str .base "comp") Py.Completion.ty ctor args (info := info)
    (typeArgs := typeArgs)

def compNormal (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionNormal #[] info

def compReturn (v : ValId) (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionReturn #[v] info

def compRaise (e : ValId) (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionRaise #[e] info

def compBreak (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionBreak #[] info

def compContinue (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionContinue #[] info

/-! ### Dispatching a completion

`py.Completion.case` passes each payload to the successor for its constructor, so a payload
is in scope exactly where it exists. -/

/-- Emit the dispatch for the pending completion `c`, ending the open block.

One `py.Completion.case`, one successor per constructor, in `py.Completion`'s declaration
order.  `onRaise` and `onReturn` each receive their payload as a parameter; `onNormal`,
`onBreak` and `onContinue` carry nothing and so take none. -/
def dispatch (c : ValId) (onRaise onReturn onBreak onContinue onNormal : Label)
    (info : Option α := none) : PyM α Unit :=
  Build.terminate (env := Py.env) Py.Completion.case #[c]
    #[Build.goto onNormal, Build.goto onReturn, Build.goto onRaise, Build.goto onBreak,
      Build.goto onContinue] (info := info)

/-! ### Dispatching to blocks

`dispatchArms` is `dispatch` with each successor's block, or its target, given with it. -/

/-- What one successor of a dispatch does.  `β` is its payload: `ValId` for `return` and
`raise`, `Unit` for the others. -/
inductive Arm (m : Type → Type) (β : Type) where
  /-- Go straight to `l`, which takes the payload if there is one. -/
  | to (l : Label)
  /-- A fresh block labelled `base.n`, taking the payload.  `emit` emits its body, given the
  payload, and must finish the block: leaving it open is an error. -/
  | block (base : String) (emit : β → m Unit)
  /-- A fresh block labelled `unreachable.n` that is `unreachable`: a `break` or `continue`
  with no enclosing loop. -/
  | unreachable

/-- The successors of a dispatch, one per constructor of `py.Completion`.  `break` and
`continue` default to `unreachable`. -/
structure Arms (m : Type → Type) where
  normal : Arm m Unit
  «return» : Arm m ValId
  raise : Arm m ValId
  «break» : Arm m Unit := .unreachable
  «continue» : Arm m Unit := .unreachable

/-- The label `a` transfers to: its own, or a fresh one for the block it emits. -/
def Arm.target [Monad m] [MonadPy α m] {β : Type} : Arm m β → m Label
  | .to l => pure l
  | .block base _ => liftPy (freshLabel (α := α) base)
  | .unreachable => liftPy (freshLabel (α := α) "unreachable")

/-- Emit `a`'s block, if it has one.  `start` opens it and hands back the payload. -/
def Arm.emitAt [Monad m] [MonadPy α m] {β : Type} (a : Arm m β) (start : m β) : m Unit :=
  match a with
  | .to _ => pure ()
  | .block _ emit => do emit (← start)
  | .unreachable => do
    let _ ← start
    liftPy (PyBuild.unreachable (α := α))

/-- Emit the dispatch for the completion `c`, ending the open block, then the blocks its
successors emit, in `py.Completion`'s declaration order.  The `return` and `raise` blocks take
their payload, named `val` and `exc`. -/
def dispatchArms [Monad m] [MonadPy α m] (c : ValId) (arms : Arms m) : m Unit := do
  let normal ← arms.normal.target
  let ret ← arms.return.target
  let raise ← arms.raise.target
  let brk ← arms.break.target
  let cont ← arms.continue.target
  liftPy (dispatch (α := α) c raise ret brk cont normal)
  arms.normal.emitAt (liftPy (startBlock (α := α) normal))
  arms.return.emitAt (liftPy (startBlockWith (α := α) ret (.str .base "val")))
  arms.raise.emitAt (liftPy (startBlockWith (α := α) raise (.str .base "exc")))
  arms.break.emitAt (liftPy (startBlock (α := α) brk))
  arms.continue.emitAt (liftPy (startBlock (α := α) cont))

/-! ### A protected block, and `try`/`finally` -/

/-- Emit `body` so that it leaves to `k` with a completion however it finishes, `k` being a
block that takes one.

* A failure goes to a fresh block `handlerBase.n`, emitted after `body`, which makes the
  exception a `raise` completion.
* Falling off the end passes a `normal` completion.
* A `return`, `break` or `continue` is `body`'s own: it jumps to `k` with its completion. -/
def protect [Monad m] [MonadPy α m] (k : Label) (body : m Unit) (handlerBase : String) :
    m Unit := do
  let caught ← liftPy (freshLabel (α := α) handlerBase)
  withHandler caught body
  if ← liftPy (isOpen (α := α)) then
    liftPy (α := α) do jump (Build.goto k #[← compNormal])
  liftPy (α := α) do
    let e ← startBlockWith caught (.str .base "exc")
    jump (Build.goto k #[← compRaise e])

/-- Emit `try: body finally: final` by completion (§7.2 of `docs/PythonToMantle.md`), ending
the open block.

`body fin` is the protected block, under `protect fin`: a failure becomes a `raise`
completion in `finRaise.n`, falling off the end is `normal`, and a `return`, `break` or
`continue` jumps to `fin` with its completion.  `final prev` is the `finally` body, emitted
once in `fin.n`, which takes the pending completion.  It runs after `pushPending`, so on the
exceptional path the pending exception is the one being handled, as in CPython; `prev` is the
one handled before, which every way out of `final` restores with `popExcept`.

* A failure in `final` supersedes the pending completion: `superseded.n` restores `prev`,
  then raises to the handler around the `try`.
* A `return`, `break` or `continue` in `final` is its own, and must restore `prev` itself.
* If `final` finishes normally, `prev` is restored and the pending completion is dispatched
  to the arms `arms` gives, which do from outside the `try` what the completion would have
  done.

Returns whether `final` finished normally, so the dispatch was emitted. -/
def tryFinally [Monad m] [MonadPy α m] (body : Label → m Unit) (final : ValId → m Unit)
    (arms : m (Arms m)) : m Bool := do
  let outer ← liftPy (handler (α := α))
  let fin ← liftPy (freshLabel (α := α) "fin")
  protect fin (body fin) "finRaise"
  let (pending, prev, superseded) ← liftPy (α := α) do
    let pending ← startBlockWith fin (.str .base "pending") Py.Completion.ty
    let prev ← emitTotal (.str .base "prev") Py.pushPending #[pending]
    return (pending, prev, ← freshLabel "superseded")
  let pop := liftPy (α := α) (discard <| emitEffect (.str .base "pop") Py.popExcept #[prev])
  withHandler superseded (final prev)
  let finished ← liftPy (isOpen (α := α))
  if finished then
    pop
    dispatchArms pending (← arms)
  let e ← liftPy (startBlockWith (α := α) superseded (.str .base "exc"))
  pop
  liftPy (jump (α := α) { outer with args := outer.args.push e })
  return finished

/-! ## Leaving a function

A Python function returns `Except Value Value`, so returning a value is `ok` and
propagating a failure is `error`, each applied at `Value, Value`.  Both finish the open
block. -/

/-- `return v`. -/
def emitReturn (v : ValId) (info : Option α := none) : PyM α Unit := do
  let i ← resolveInfo info
  let r ← Build.emitApply (env := Py.env) (.str .base "ret") Py.failing.ty Base.Except.ok
    #[v] (info := some i)
  Build.ret (env := Py.env) r (some i)

/-- `return None`, which is what falling off the end does. -/
def emitReturnNone (info : Option α := none) : PyM α Unit := do
  emitReturn (← noneLit info) info

/-- Return the failure `e` to the caller. -/
def emitPropagate (e : ValId) (info : Option α := none) : PyM α Unit := do
  let i ← resolveInfo info
  let r ← Build.emitApply (env := Py.env) (.str .base "exc") Py.failing.ty Base.Except.error
    #[e] (info := some i)
  Build.ret (env := Py.env) r (some i)

/-! ## A whole function -/

/-- `buildFuncTyped` below, also returning the result of `body`, on failure too, as
`Build.run` does. -/
def buildFuncTypedWith (name : Name) (params : Array (Name × TypeExpr Py.env)) (info : α)
    (body : Array ValId → PyM α β) :
    Except (Build.Failure β) ({fn : Func Py.env α // fn.WF} × β) :=
  Build.run name Py.failing.ty info do
    let ps ← params.mapM fun (p, t) => Build.freshVal p t
    let propagate ← Build.freshLabel "propagate"
    let _ ← Build.startFreshBlock ps "entry"
    let (r, _) ← (body (ps.map (·.id))).run { handler := Build.goto propagate }
    -- The handler, emitted last: it takes the exception and hands it back.
    let exc ← Build.freshVal (.str .base "exc") Py.Value.ty
    Build.startBlock propagate #[exc]
    let _ ← (emitPropagate exc.id).run { handler := Build.goto propagate }
    return r

/-- Emit a Python function whose parameters have the given types, and check it.

`buildFunc` is the form whose parameters are all Python values.  This one also takes
others, such as a closure's captured cells, which arrive as `Ref Value` parameters.

Before `body` runs, the handler is in place: it takes the exception and returns it to the
caller.  `body` must finish every block it opens: ending with a block open is an error, and
so is any other error `Mantle.Build` records.  It fails with the `Build.Failure` if there is
one or the function is not well formed.  The entry block is labelled `entry.0` and the
handler `propagate.0`. -/
def buildFuncTyped (name : Name) (params : Array (Name × TypeExpr Py.env)) (info : α)
    (body : Array ValId → PyM α Unit) :
    Except (Build.Failure Unit) {fn : Func Py.env α // fn.WF} :=
  Prod.fst <$> buildFuncTypedWith name params info body

/-- Emit a Python function, every parameter a Python value, and check it. -/
def buildFunc (name : Name) (params : Array String) (info : α)
    (body : Array ValId → PyM α Unit) :
    Except (Build.Failure Unit) {fn : Func Py.env α // fn.WF} :=
  buildFuncTyped name (params.map (stem ·, Py.Value.ty)) info body

/-- The stub of the function `buildFuncTyped name params` would build, `Build.stub` at its
signature. -/
def stubFunc (name : Name) (params : Array (Name × TypeExpr Py.env)) (info : α) :
    {fn : Func Py.env α // fn.WF} :=
  Build.stub name params Py.failing.ty info

end

end StrataPython.Mantle.PyBuild
