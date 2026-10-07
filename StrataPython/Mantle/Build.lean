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

The operations:

* `handler`, `withHandler`, `withHandlerTo`: read and replace the enclosing handler, as a
  `try` does;
* `withInfo`, `resolveInfo`: the default annotation;
* `emitConst`, `emitTotal`, `emitFailing`, `emitActing`, `emitTest`, `truthy`: emit a
  constant or an operation;
* `intLit`, `floatLit`, `strLit`, `boolLit`, `bytesLit`, `noneLit`: a boxed literal;
* `getAttr`: `obj.name`;
* `freshVal`, `freshLabel`, `startBlock`, `startBlockWith`, `startFreshBlock`, `isOpen`,
  `finishBlock`, `jump`, `branch`, `unreachable`: `Mantle.Build`'s, over `Py.env`;
* `emitFunc`, `mkClosure`, `funcValue`: code pointers and closures;
* `cellOf?`, `declareLocal`, `readCell`, `writeCell`: locals, each a `Ref Value` cell;
* `globalCell`, `readGlobal`, `writeGlobal`, `importModule`, `importFrom`: globals and
  imports;
* `freshComp`, `compNormal`, `compReturn`, `compRaise`, `compBreak`, `compContinue`,
  `dispatch`, `dispatchArms`: completions, for `finally`;
* `protect`, `tryFinally`: a protected block and `try`/`finally`, by completion;
* `emitReturn`, `emitReturnNone`, `emitPropagate`: leave the function;
* `buildFunc`, `buildFuncTyped`, `buildFuncTypedWith`: emit a whole function.

A function body is emitted inside `buildFunc`, which installs the handler that returns a
failure to the caller before the body runs.  Misusing blocks is an error, as in
`Mantle.Build`, and `buildFunc` fails if one was recorded.  Block parameters are not decided
here: locals stay in cells until ref-to-reg.

The emitters that take a body to emit (`withHandler`, `dispatchArms`, `protect`,
`tryFinally`) run it in any `MonadPy` monad: `PyM` itself, or the translator's `TransM` above
it.
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
def emitConst (name : String) (c : Const) (info : Option α := none) : PyM α ValId :=
  Build.emitConst (env := Py.env) name c info

/-! ## Operations

One emitter per result type and failure behaviour.  Every Python operation is monomorphic,
so `typeArgs` is always `#v[]`. -/

/-- An operation that cannot fail and produces a Python value. -/
def emitTotal {isig : InsnSig Py.env} (name : String) (r : InsnRef Py.env isig)
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc) (args : Array ValId)
    (info : Option α := none) : PyM α ValId :=
  Build.emitApply name Py.Value.ty r typeArgs args (info := info)

/-- A raising operation producing a Python value: its `err` successor is the enclosing
handler. -/
def emitFailing {isig : InsnSig Py.env} (name : String) (r : InsnRef Py.env isig)
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc) (args : Array ValId)
    (info : Option α := none) : PyM α ValId := do
  Build.emitApply name Py.Value.ty r typeArgs args #[← handler] (info := info)

/-- A raising operation that only acts: its result is `()`, and its `err` successor is the
enclosing handler. -/
def emitActing {isig : InsnSig Py.env} (name : String) (r : InsnRef Py.env isig)
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc) (args : Array ValId)
    (info : Option α := none) : PyM α ValId := do
  Build.emitApply name Base.Unit.ty r typeArgs args #[← handler] (info := info)

/-- An operation producing a base `Bool`, which is what a `branch` takes. -/
def emitTest {isig : InsnSig Py.env} (name : String) (r : InsnRef Py.env isig)
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc) (args : Array ValId)
    (info : Option α := none) : PyM α ValId :=
  Build.emitApply name Base.Bool.ty r typeArgs args (info := info)

/-- `bool(v)`: the base `Bool` a `branch` takes.  It can fail — `__bool__` and `__len__`
are arbitrary code — so its `err` successor is the enclosing handler. -/
def truthy (v : ValId) (info : Option α := none) : PyM α ValId := do
  Build.emitApply (env := Py.env) "cond" Base.Bool.ty Py.truthy #v[] #[v]
    #[← handler] (info := info)

/-! ## Literals

Each is a base constant and the operation that boxes it. -/

def intLit (i : Int) (info : Option α := none) : PyM α ValId := do
  emitTotal "int" Py.intLit #v[] #[← emitConst "c" (.int i) info] info

def floatLit (f : Float) (info : Option α := none) : PyM α ValId := do
  emitTotal "float" Py.floatLit #v[] #[← emitConst "c" (.float f) info] info

def strLit (s : String) (info : Option α := none) : PyM α ValId := do
  emitTotal "str" Py.strLit #v[] #[← emitConst "c" (.str s) info] info

def boolLit (b : Bool) (info : Option α := none) : PyM α ValId := do
  emitTotal "bool" Py.boolLit #v[] #[← emitConst "c" (.bool b) info] info

def bytesLit (s : String) (info : Option α := none) : PyM α ValId := do
  emitTotal "bytes" Py.bytesLit #v[] #[← emitConst "c" (.str s) info] info

def noneLit (info : Option α := none) : PyM α ValId := emitTotal "none" Py.noneLit #v[] #[] info

/-! ## Blocks and values

`Mantle.Build`'s operations, at `Py.env`. -/

/-- A fresh Python value, named after `name`. -/
def freshVal (name : String) : PyM α (ValDecl Py.env) :=
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
def startBlockWith (label : Label) (name : String) (t : TypeExpr Py.env 0 := Py.Value.ty) :
    PyM α ValId :=
  Build.startBlockWith (α := α) label name t

/-- Whether a block is open, so that instructions can be emitted. -/
def isOpen : PyM α Bool := do return (← getThe (Build.State Py.env α)).label.isSome

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
  emitFailing name Py.attr #v[] #[obj, ← emitConst "attr" (.str name) info] info

/-! ## Closures

A code pointer is a constant naming a function of the *module*; a closure pairs it with the
cells it captures.  A module-level function is the case with no cells. -/

/-- Emit a code pointer to `target`, a function the module defines: the constant
`.func target`. -/
def emitFunc (target : Name) (info : Option α := none) : PyM α ValId :=
  Build.emitFunc (env := Py.env) target info

/-- A callable value: the code, and the cells it captures. -/
def mkClosure (code : ValId) (cells : Array ValId) (info : Option α := none) : PyM α ValId :=
  emitTotal "clo" Py.mkClosure #v[] (#[code] ++ cells) info

/-- A callable value for a module-level function, which captures nothing. -/
def funcValue (target : Name) (info : Option α := none) : PyM α ValId := do
  mkClosure (← emitFunc target info) #[] info

/-! ## Locals

A local is a cell: an assignment writes it and a read reads it.  A cell holds `undef` until
its first assignment, so a read before assignment can be checked. -/

/-- The cell of a local in scope, if it is one. -/
def cellOf? (name : String) : PyM α (Option ValId) := (·.locals.find? name) <$> get

/-- Make a cell for `name`, holding "not yet assigned", and record it. -/
def declareLocal (name : String) (info : Option α := none) : PyM α ValId := do
  let nameConst ← emitConst "n" (.str name) info
  let undef ← emitTotal name Py.undef #v[] #[nameConst] info
  let cell ← Build.emitApply (env := Py.env) (name ++ ".cell") Py.cell.ty Base.refNew
    #v[Py.Value.ty] #[undef] (info := info)
  modify fun e => { e with locals := e.locals.insert name cell }
  return cell

/-- Read a cell.  `name` is only what the result is called. -/
def readCell (cell : ValId) (name : String) (info : Option α := none) : PyM α ValId :=
  Build.emitApply (env := Py.env) name Py.Value.ty Base.refGet #v[Py.Value.ty] #[cell]
    (info := info)

/-- Write a cell. -/
def writeCell (cell : ValId) (v : ValId) (info : Option α := none) : PyM α ValId :=
  Build.emitApply (env := Py.env) "set" Base.Unit.ty Base.refSet #v[Py.Value.ty] #[cell, v]
    (info := info)

/-! ## Globals and imports

A global is a cell too, named by its module and its name rather than recorded in the frame.
`readGlobal` is the checked read; a read that falls back to a builtin is `readCell` of
`globalCell`, then `isDefined` and a branch. -/

/-- The cell of the global `name` of `module`. -/
def globalCell (module name : String) (info : Option α := none) : PyM α ValId := do
  let m ← emitConst "m" (.str module) info
  let n ← emitConst "n" (.str name) info
  Build.emitApply (env := Py.env) (name ++ ".cell") Py.cell.ty Py.globalCell #v[] #[m, n]
    (info := info)

/-- Read the global `name` of `module`, raising `NameError` if it is not assigned. -/
def readGlobal (module name : String) (info : Option α := none) : PyM α ValId := do
  let v ← readCell (← globalCell module name info) name info
  let excType ← emitConst "e" (.str "NameError") info
  let msg ← emitConst "msg" (.str s!"name '{name}' is not defined") info
  emitFailing name Py.requireDefined #v[] #[v, excType, msg] info

/-- Write the global `name` of `module`. -/
def writeGlobal (module name : String) (v : ValId) (info : Option α := none) :
    PyM α ValId := do
  writeCell (← globalCell module name info) v info

/-- The module object for `module`, a fully qualified name, imported if need be. -/
def importModule (module : String) (info : Option α := none) : PyM α ValId := do
  emitFailing "mod" Py.importModule #v[] #[← emitConst "m" (.str module) info] info

/-- `from module import name`, read once. -/
def importFrom (module name : String) (info : Option α := none) : PyM α ValId := do
  let m ← emitConst "m" (.str module) info
  let n ← emitConst "n" (.str name) info
  emitFailing name Py.importFrom #v[] #[m, n] info

/-! ## Completions

How a block that a `finally` protects finished, as a value.  A `finally` body is emitted
once, takes the pending completion as its parameter, and ends by dispatching on it; `Py`'s
module docstring shows the shape. -/

/-- A fresh completion-typed value: what a `finally` or dispatch block takes. -/
def freshComp (name : String) : PyM α (ValDecl Py.env) :=
  Build.freshVal (env := Py.env) (α := α) name Py.Completion.ty

/-- Build a completion: apply one constructor of `py.Completion`, which takes no type
arguments. -/
def emitComp {isig : InsnSig Py.env} (ctor : InsnRef Py.env isig)
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc) (args : Array ValId)
    (info : Option α := none) : PyM α ValId :=
  Build.emitApply "comp" Py.Completion.ty ctor typeArgs args (info := info)

def compNormal (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionNormal #v[] #[] info

def compReturn (v : ValId) (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionReturn #v[] #[v] info

def compRaise (e : ValId) (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionRaise #v[] #[e] info

def compBreak (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionBreak #v[] #[] info

def compContinue (info : Option α := none) : PyM α ValId :=
  emitComp Py.Completion.completionContinue #v[] #[] info

/-! ### Dispatching a completion

`py.Completion.case` passes each payload to the successor for its constructor, so a payload
is in scope exactly where it exists. -/

/-- Emit the dispatch for the pending completion `c`, ending the open block.

One `py.Completion.case`, one successor per constructor, in `py.Completion`'s declaration
order.  `onRaise` and `onReturn` each receive their payload as a parameter; `onNormal`,
`onBreak` and `onContinue` carry nothing and so take none. -/
def dispatch (c : ValId) (onRaise onReturn onBreak onContinue onNormal : Label)
    (info : Option α := none) : PyM α Unit :=
  Build.terminate (env := Py.env) Py.Completion.case #v[] #[c]
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
  arms.return.emitAt (liftPy (startBlockWith (α := α) ret "val"))
  arms.raise.emitAt (liftPy (startBlockWith (α := α) raise "exc"))
  arms.break.emitAt (liftPy (startBlock (α := α) brk))
  arms.continue.emitAt (liftPy (startBlock (α := α) cont))

/-! ### A protected block, and `try`/`finally` -/

/-- Emit `body` so that it leaves to `k` with a completion however it finishes, `k` being a
block that takes one.

* A failure goes to a fresh block `handlerBase.n`, emitted after `body`, which makes the
  exception a `raise` completion.  The block takes `carry`, pre-bound by the failing site,
  before the exception, and ignores them; a policy chaining `__context__` would read them.
* Falling off the end passes the completion `normal` gives, `normal` by default.
* A `return`, `break` or `continue` is `body`'s own: it jumps to `k` with its completion. -/
def protect [Monad m] [MonadPy α m] (k : Label) (body : m Unit)
    (carry : Array (ValDecl Py.env) := #[]) (normal : m ValId := liftPy (compNormal (α := α)))
    (handlerBase : String := "caught") : m Unit := do
  let caught ← liftPy (freshLabel (α := α) handlerBase)
  withHandlerTo (Build.goto caught (carry.map (·.id))) body
  if ← liftPy (isOpen (α := α)) then
    let c ← normal
    liftPy (jump (α := α) (Build.goto k #[c]))
  liftPy (α := α) do
    let carried ← carry.mapM fun d => Build.freshVal (env := Py.env) (α := α) "carried" d.type
    let e ← freshVal "exc"
    startBlock caught (carried.push e)
    jump (Build.goto k #[← compRaise e.id])

/-- Emit `try: body finally: final` by completion (§7.2 of `docs/PythonToMantle.md`), ending
the open block.

`body fin` is the protected block, under `protect fin`: a failure becomes a `raise`
completion in `finRaise.n`, falling off the end is `normal`, and a `return`, `break` or
`continue` jumps to `fin` with its completion.  `final` is the `finally` body, emitted once in
`fin.n`, which takes the pending completion.  If it finishes normally, the pending completion
is dispatched to `arms`, which do from outside the `try` what the completion would have
done.

A failure in `final` supersedes the pending completion.  Without `superseded`, `final` runs
under the enclosing handler, so the failure simply goes there.  With it, `final` is itself
protected: a failure goes to `superseded.n`, which also takes the pending completion and
makes the failure a `raise` completion, and both ends of `final` reach one dispatch block,
`disp.n`, taking the completion of the whole statement. -/
def tryFinally [Monad m] [MonadPy α m] (body : Label → m Unit) (final : m Unit)
    (arms : Arms m) (superseded : Bool := false) : m Unit := do
  let fin ← liftPy (freshLabel (α := α) "fin")
  protect fin (body fin) (handlerBase := "finRaise")
  let pending ← liftPy (startBlockWith (α := α) fin "pending" Py.Completion.ty)
  if superseded then
    let disp ← liftPy (freshLabel (α := α) "disp")
    protect disp final (carry := #[⟨pending, Py.Completion.ty⟩]) (normal := pure pending)
      (handlerBase := "superseded")
    dispatchArms (← liftPy (startBlockWith (α := α) disp "comp" Py.Completion.ty)) arms
  else
    final
    if ← liftPy (isOpen (α := α)) then dispatchArms pending arms

/-! ## Leaving a function

A Python function returns `Except Value Value`, so returning a value is `ok` and
propagating a failure is `error`, each applied at `Value, Value`.  Both finish the open
block. -/

/-- `return v`. -/
def emitReturn (v : ValId) (info : Option α := none) : PyM α Unit := do
  let i ← resolveInfo info
  let r ← Build.emitApply (env := Py.env) "ret" Py.failing.ty Base.Except.ok
    #v[Py.Value.ty, Py.Value.ty] #[v] (info := some i)
  Build.ret (env := Py.env) r (some i)

/-- `return None`, which is what falling off the end does. -/
def emitReturnNone (info : Option α := none) : PyM α Unit := do
  emitReturn (← noneLit info) info

/-- Return the failure `e` to the caller. -/
def emitPropagate (e : ValId) (info : Option α := none) : PyM α Unit := do
  let i ← resolveInfo info
  let r ← Build.emitApply (env := Py.env) "exc" Py.failing.ty Base.Except.error
    #v[Py.Value.ty, Py.Value.ty] #[e] (info := some i)
  Build.ret (env := Py.env) r (some i)

/-! ## A whole function -/

/-- `buildFuncTyped` below, also returning the result of `body`, and the errors recorded
rather than failing on them. -/
def buildFuncTypedWith (name : Name) (params : Array (String × TypeExpr Py.env 0)) (info : α)
    (body : Array ValId → PyM α β) : Build.Built (Func Py.env α × β) :=
  Build.run name Py.failing.ty info do
    let ps ← params.mapM fun (p, t) => Build.freshVal p t
    let propagate ← Build.freshLabel "propagate"
    let _ ← Build.startFreshBlock ps "entry"
    let (r, _) ← (body (ps.map (·.id))).run { handler := Build.goto propagate }
    -- The handler, emitted last: it takes the exception and hands it back.
    let exc ← Build.freshVal "exc" Py.Value.ty
    Build.startBlock propagate #[exc]
    let _ ← (emitPropagate exc.id).run { handler := Build.goto propagate }
    return r

/-- Emit a Python function whose parameters have the given types.

`buildFunc` is the form whose parameters are all Python values.  This one also takes
others, such as a closure's captured cells, which arrive as `Ref Value` parameters.

Before `body` runs, the handler is in place: it takes the exception and returns it to the
caller.  `body` must finish every block it opens: ending with a block open is an error, and
so is any other error `Mantle.Build` records.  It fails with the `Errors` if there is one.
The entry block is labelled `entry.0` and the handler `propagate.0`. -/
def buildFuncTyped (name : Name) (params : Array (String × TypeExpr Py.env 0)) (info : α)
    (body : Array ValId → PyM α Unit) : Except Build.Errors (Func Py.env α) :=
  Prod.fst <$> (buildFuncTypedWith name params info body).toExcept

/-- Emit a Python function, every parameter a Python value. -/
def buildFunc (name : Name) (params : Array String) (info : α)
    (body : Array ValId → PyM α Unit) : Except Build.Errors (Func Py.env α) :=
  buildFuncTyped name (params.map (·, Py.Value.ty)) info body

end

end StrataPython.Mantle.PyBuild
