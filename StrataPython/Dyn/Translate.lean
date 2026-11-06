/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Build
public import StrataPython.Dyn.Scope
public import StrataDyn.WF
public import StrataDyn.Attr
public import StrataPython.Dyn.Shape
public import Lean.Data.Position
import StrataPython.Dyn.Termination
import Strata.Util.ListUtilsProps
import Std.Data.HashSet.Lemmas
import StrataDyn.FloatText
-- Emitting instructions over `Py.env` needs the signature representation at
-- code-generation time.
import StrataDyn.Env.WF
import StrataDyn.DomDiag

set_option autoImplicit false

/-!
# Python to Dyn

`translate` lowers a parsed Python module to a checked `Dyn.Module` over `Py.env`, as the
design doc, `docs/PythonToDyn.md`, describes.  It returns the module and its diagnostics.
A result with a diagnostic is a failure.

* The module body is the function `m.<module>`, with no parameters.  It first writes
  `__name__` and `__doc__`.  A `def` is a function named after its `__qualname__`, `m.f.g` for
  `f.<locals>.g`.  Its parameters are the cells it captures, then `args` (a tuple) and
  `kwargs` (a dict).
* Names are classified by `PyScope.analyze`.  A function's locals are cells declared in its
  entry block.  A module global is the cell `py.globalCell m x`, and a read of it is
  `py.loadGlobal m x`, which falls back to the builtin `x` at run time.
* Every instruction carries the source range of the Python node it lowers.
* A construct outside the supported subset is a diagnostic at its range.  A rejected
  expression is `py.unsupported`, a rejected statement emits nothing, and a rejected
  function (`async def`, a generator) is a stub that returns `py.unsupported`.
* An error the builder records is a bug in the translator: an `internal error` diagnostic at
  the range of the function it was emitting.  So is a node CPython's parser never produces,
  such as the target of "a, b += 1": an `internal error` at the node's range.  So is a
  function that is not well formed.  A function whose build failed either way is a stub
  (`Build.stub`), so the module is still checked; it is for diagnostics only.

## Supported constructs

The design doc's §11 lists what is lowered; `StrataPythonTest/Dyn/dyn_tests.txt` marks
each test program as supported or not.

## Adding a construct

1. Replace its rejection in `transStmt` or `transExpr` with a case that lowers it.
2. Read and write names with `readName` and `writeName`.
3. Emit operations with the `PyBuild` emitters, through `build`.  Open blocks with
   `freshLabel`, with the types they take, and `startBlock`, and end them with `jump` or
   `branch` to a target made from a block.  Start a join block only if `targeted` holds for
   it.
4. Run a body that `break`, `continue` or `return` leaves under `withExit`.
5. Add a program to `StrataPythonTest/Dyn/dyn_tests/`, list it in
   `StrataPythonTest/Dyn/dyn_tests.txt`, and write its golden `NAME.expected.dyn`
   beside it with `DYN_UPDATE=1`.  Mark the other tests it now translates `yes` in that
   list.  Give it a `NAME.symtable` and `NAME.expected.scope` too, as `AGENTS.md` describes,
   and regenerate the ref-to-reg goldens of every changed golden.
   `lake exe pydyn dyn FILE.py` prints the diagnostics and the module for one file.

`whileStmt` is a short example, tested by `m_while.py` and `t04_while.py`.

## Size lemmas

The size lemmas next to some helpers, such as `sizeOf_params_default_lt`, are in this file,
not in a `TranslateProps.lean`, because the translator's termination proofs need them.
-/

namespace StrataPython.Dyn.PyTranslate

open Strata.Dyn
open StrataPython.Dyn.PyBuild
open StrataPython.Dyn.PyScope (Table Scope ScopeId NameScope Diagnostic ParamKind mangle
  formatRange starredIndex?)
open StrataPython (stmt expr constant operator unaryop cmpop arguments arg keyword alias
  opt_expr excepthandler withitem match_case comprehension)
open StrataDDM (SourceRange)

public section

/-! ## Results -/

/-- A translated module and its diagnostics: the scope pass's syntax errors, then each
rejected construct, in source order. -/
structure Result where
  /-- The module, checked.  A function whose build failed, or that is not well formed, is a
  stub whose body is `unreachable`, and a diagnostic reports it. -/
  module : Module Py.env Info
  diagnostics : Array Diagnostic

/-- Whether the translation succeeded: no diagnostic. -/
def Result.ok (r : Result) : Bool := r.diagnostics.isEmpty

/-- `n`, dotted. -/
def nameText : Name → String
  | .base => "_"
  | .str .base s => s
  | .num .base i => toString i
  | .str p s => s!"{nameText p}.{s}"
  | .num p i => s!"{nameText p}.{i}"

/-- A diagnostic as one comment line: `-- unsupported: match is not supported at 4:4-4:22`. -/
def formatDiagnostic (fileMap : Option Lean.FileMap) (d : Diagnostic) : String :=
  s!"-- {d.kind.text}: {d.message} at {formatRange fileMap d.range}"

end -- public section

/-! ## Translator state -/

/-- A construct that `break`, `continue` and `return` leave through, innermost last. -/
inductive Exit where
  /-- A loop: `break` jumps to `brk`, `continue` to `cont`. -/
  | loop (brk cont : BlockRef Py.env [])
  /-- The body of an `except` clause or a `finally`, left through `leaveHandler`: `prev` is
  the exception handled before, `name` the name the clause binds and where, and `outer` the
  handler around the `try`. -/
  | handler (prev : ValId) (name : Option (String × SourceRange)) (outer : PyTarget [Py.Value])
  /-- A `try` with a `finally`, or a `with`: a `return`, `break` or `continue` jumps to `fin`
  with its completion, and the dispatch after the `finally` body or `__exit__` carries it
  on. -/
  | cleanup (fin : BlockRef Py.env [Py.Completion])

/-- The parts of a class statement that a class body's declared shape needs besides the body:
the private name where the class statement runs, and its bases, keywords and decorators. -/
structure ClassParts where
  outerPrivate : Option String
  bases : Array (expr SourceRange)
  keywords : Array (keyword SourceRange)
  decorators : Array (expr SourceRange)

/-- A `def` whose function is emitted after the current one. -/
structure FuncJob where
  name : Name
  scope : ScopeId
  /-- `table.scopes[scope]`. -/
  cur : Scope
  /-- The parameters; `none` for a class body, which takes the namespace as `args[0]`. -/
  args : Option (arguments SourceRange)
  body : Array (stmt SourceRange)
  range : SourceRange
  /-- The rejected construct, for a function emitted as a stub. -/
  stub : Option String
  /-- For a class body, what its declared shape needs besides the body. -/
  classParts : Option ClassParts := none

/-- What is fixed while one function is translated. -/
structure Ctx where
  table : Table
  /-- The Python module name, such as `a.b`. -/
  module : String
  /-- The module name as a Dyn name: the prefix of every function name. -/
  moduleName : Name
  scope : ScopeId
  /-- `table.scopes[scope]`, the scope being translated. -/
  cur : Scope
  /-- In a class body, its namespace (§6.7). -/
  classNs : Option ValId := none
  /-- The module body sets up `__annotations__` (§6.1), so the name has a value. -/
  moduleAnnotations : Bool := false
  /-- The class body whose namespace is `classNs` sets up `__annotations__` too. -/
  classAnnotations : Bool := false
  /-- In an `except` body, the exception it handles: what a bare `raise` raises again. -/
  handled : Option ValId := none

/-- What translation accumulates.  The first three fields are module-wide; `exits`,
`targeted` and `inits` belong to the function being emitted. -/
structure TState where
  diagnostics : Array Diagnostic := #[]
  pending : Array FuncJob := #[]
  funcNames : Std.HashSet Name := {}
  exits : Array Exit := #[]
  /-- The labels some emitted transfer names. -/
  targeted : Std.HashSet Label := {}
  /-- The `__init__`s of the class body being emitted: each `def`'s range, its function, and
  whether it keeps its first parameter, so that its `self.x: T` declare fields of the
  instance. -/
  inits : Array (SourceRange × Name × Bool) := #[]

/-- Translating one Python function. -/
abbrev TransM := ReaderT Ctx (StateT TState (PyM Info))

variable {β : Type}

/-- Run a `PyBuild` action. -/
def build (x : PyM Info β) : TransM β := monadLift x

/-- Run `act` with `r` as the default annotation. -/
def withRange (r : SourceRange) (act : TransM β) : TransM β := do
  let ctx ← read
  let s ← get
  let (b, s') ← build (PyBuild.withInfo { range := r } ((act.run ctx).run s))
  set s'
  return b

/-- Run `act` with `e` pushed on the exits stack. -/
def withExit (e : Exit) (act : TransM β) : TransM β := do
  let saved := (← get).exits
  modify fun s => { s with exits := s.exits.push e }
  let r ← act
  modify fun s => { s with exits := saved }
  return r

/-! ## Diagnostics -/

/-- Record a bug in the translator, `what`, at `range`. -/
def internalError (what : String) (range : SourceRange) : TransM Unit :=
  let d : Diagnostic := { kind := .internal, message := what, range }
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- Record that `what` is not supported at `range`. -/
def reject (what : String) (range : SourceRange) : TransM Unit :=
  let d : Diagnostic := { kind := .unsupported, message := s!"{what} is not supported", range }
  modify fun s => { s with diagnostics := s.diagnostics.push d }

/-- `py.unsupported "what"`: the value of an expression already rejected. -/
def standIn (what : String) : TransM ValId := do
  let n ← build (strLit what)
  build (emitTotal (.str .base "unsupported") Py.unsupported.ref #[n])

/-- Reject the expression `what` at `range`; its value is `py.unsupported "what"`. -/
def unsupportedValue (what : String) (range : SourceRange) : TransM ValId := do
  reject what range
  standIn what

/-! ## Blocks -/

/-- Whether a block is open, so that instructions can be emitted. -/
def isOpen : TransM Bool := build PyBuild.isOpen

/-- Whether some transfer names `l`. -/
def targeted {ps : List (TypeExpr Py.env)} (l : BlockRef Py.env ps) : TransM Bool :=
  return (← get).targeted.contains l.label

def recordTarget {ps : List (TypeExpr Py.env)} (k : PyTarget ps) : TransM Unit :=
  modify fun s => { s with targeted := s.targeted.insert k.rawUnchecked.label }

/-- End the open block with `jump k`. -/
def jump (k : PyTarget []) : TransM Unit := do
  recordTarget k
  build (PyBuild.jump k)

/-- End the open block with `branch c t f`. -/
def branch (c : ValId) (t f : PyTarget []) : TransM Unit := do
  recordTarget t
  recordTarget f
  build (PyBuild.branch c t f)

/-! ## Names

`place` classifies a name in the current scope from the scope table; `readName` and
`writeName` lower the read and the write for each class (§5.1). -/

/-- Where a name lives in the current scope. -/
inductive Place where
  /-- A local or cell variable of the function, held in this cell. -/
  | cell (c : ValId)
  /-- A module global, or a builtin. -/
  | global
  /-- A variable of an enclosing function, held in this captured cell. -/
  | free (c : ValId)
  /-- In a class body, a name of its namespace `ns`, else a global (`LOAD_NAME`). -/
  | nsName (ns : ValId)
  /-- In a class body, a name of its namespace `ns`, else the free variable in the captured
  cell `c` (`LOAD_FROM_DICT_OR_DEREF`). -/
  | nsFree (ns c : ValId)
  /-- A local or free variable with no cell in the frame. -/
  | unresolved

/-- The current scope. -/
def curScope : TransM Scope := return (← read).cur

/-- `name`, mangled in the current scope. -/
def mangled (name : String) : TransM String := do
  return mangle (← curScope).privateName name

/-- Where the scope that binds a name keeps it, for a name that is free in an inlined
comprehension. -/
inductive EnclosingHold where
  /-- A global or a builtin. -/
  | global
  /-- In a local cell of the frame. -/
  | cell
  /-- In a cell that the frame captured. -/
  | free
  /-- The scope table lacks a scope or a parent that it should have: a bug. -/
  | missing

/-- How the scope `id?` holds the mangled `name`.  If the scope is an inlined comprehension
where `name` is free, its parent decides instead, and so on up the table: each parent comes
before its scope. -/
def enclosingHold (t : Table) (name : String) : Option ScopeId → EnclosingHold
  | none => .missing
  | some id =>
    if hid : id < t.scopes.size then
      let sc := t.scopes[id]
      match sc.kind, ((sc.symbol? name).map (·.scope) : Option NameScope) with
      | .module, _ => .global
      | .inlinedComprehension, some .free =>
        match hp : sc.parent with
        | some q =>
          have hlt : q < id := t.parent_lt hid hp
          enclosingHold t name (some q)
        | none => .missing
      | _, some .«local» | _, some .cell =>
        if sc.kind == .classBody then
          if !((sc.symbol? name).any (·.uses.freeClass)) then .global else .free
        else .cell
      | _, some .free => .free
      | _, _ => .global
    else .missing
termination_by id? => id?.getD 0

/-- Classify `name`, which must be mangled, as the scope `start` encloses it, for a name
an inlined comprehension does not bind.  An enclosing comprehension that binds it holds it in
its cell; a function holds it in its local or captured cell.  The comprehension skips a
class's names, so in a class body it is the cell the body captures, if it is free there or
`free_class`, and a global otherwise. -/
def enclosingPlace (name : String) (start : Option ScopeId) : TransM Place := do
  match enclosingHold (← read).table name start with
  | .global => return .global
  | .missing => return .unresolved
  | .cell => return ((← build (cellOf? name)).map .cell).getD .unresolved
  | .free => return ((← build (cellOf? name)).map .free).getD .unresolved

/-- Classify `name`, which must be mangled. -/
def place (name : String) : TransM Place := do
  let sc ← curScope
  if sc.kind == .module then return .global
  if sc.kind == .inlinedComprehension then
    return ← match ((sc.symbol? name).map (·.scope) : Option NameScope) with
    | some .«local» | some .cell => do
      match ← build (cellOf? name) with
      | some c => pure (.cell c)
      | none => pure .unresolved
    | some .free => enclosingPlace name sc.parent
    | _ => pure .global
  if let some ns := (← read).classNs then
    return ← match ((sc.symbol? name).map (·.scope) : Option NameScope) with
    | some .globalExplicit => pure .global
    | some .free => do
      match ← build (cellOf? name) with
      | some c => pure (.nsFree ns c)
      | none => pure .unresolved
    | _ => pure (.nsName ns)
  match ((sc.symbol? name).map (·.scope) : Option NameScope) with
  | some .«local» | some .cell =>
    match ← build (cellOf? name) with
    | some c => return .cell c
    | none => return .unresolved
  | some .free =>
    match ← build (cellOf? name) with
    | some c => return .free c
    | none => return .unresolved
  | some .globalExplicit | some .globalImplicit | none => return .global

/-- `py.requireDefined v excType msg`. -/
def requireDefined (v : ValId) (name excType msg : String) : TransM ValId := do
  let e ← build (emitConst (.str .base "e") (.str excType))
  let m ← build (emitConst (.str .base "msg") (.str msg))
  build (emitFailing (stem name) Py.requireDefined.ref #[v, e, m])

/-- Read the local `name`'s cell `c`, raising `UnboundLocalError` if it is unassigned. -/
def readLocal (c : ValId) (name : String) : TransM ValId := do
  let v ← build (readCell c (stem name))
  requireDefined v name "UnboundLocalError"
    s!"cannot access local variable '{name}' where it is not associated with a value"

/-- The module attributes CPython defines that the translation has no value for: unlike
`__name__` and `__doc__`, the module body does not write them, so `loadGlobal` would find the
`builtins` module's value or raise `NameError`.  A read or `del` of one is rejected. -/
def moduleDunders : List String :=
  ["__annotations__", "__builtins__", "__cached__", "__file__", "__loader__", "__package__",
   "__path__", "__spec__"]

/-- Whether `x` is a module attribute the translation has no value for: one of
`moduleDunders`, except `__annotations__` in a module or class body that sets it up. -/
def unmodelled (x : String) : TransM Bool := do
  let ctx ← read
  let annotated := ctx.moduleAnnotations || (ctx.classNs.isSome && ctx.classAnnotations)
  return moduleDunders.contains x && !(x == "__annotations__" && annotated)

/-- Read the free variable `name`'s captured cell `c`, raising `NameError` if it is
unassigned. -/
def readFree (c : ValId) (name : String) : TransM ValId := do
  let v ← build (readCell c (stem name))
  requireDefined v name "NameError" (s!"cannot access free variable '{name}' where it is " ++
    "not associated with a value in enclosing scope")

/-- `name` in the class namespace `ns`, or `fallback` if it is absent: `ns[name]`, with a
`KeyError` as absence, as CPython's `LOAD_NAME` reads a namespace. -/
def readNs (ns : ValId) (name : String) (fallback : TransM ValId) : TransM ValId := do
  let key ← build (strLit name)
  let n ← build (emitConst (.str .base "n") (.str name))
  let miss ← build (emitTotal (stem name) Py.undef.ref #[n])
  let v ← build (emitFailing (stem name) Py.getOptionalItem.ref #[ns, key, miss])
  let join ← build (freshLabel [Py.Value] "join")
  let absent ← build (freshLabel [] "absent")
  branch (← build (emitTest (.str .base "found") Py.isDefined.ref #[v])) (join.goto.bind (value v))
    absent.goto
  build (startBlock absent)
  jump (join.goto.bind (value (← fallback)))
  Val.id <$> build (startBlockWith join (stem name))

/-- Read the name `name` at `range`. -/
def readName (name : String) (range : SourceRange) : TransM ValId := do
  let name ← mangled name
  match ← place name with
  | .cell c => readLocal c name
  | .global => globalRead name
  | .free c => readFree c name
  | .nsName ns => readNs ns name (globalRead name)
  | .nsFree ns c => readNs ns name (readFree c name)
  | .unresolved => unsupportedValue "unresolved local" range
where
  /-- The global `x`, with the module attributes the translation has no value for rejected. -/
  globalRead (x : String) : TransM ValId := do
    if ← unmodelled x then unsupportedValue s!"module attribute {x}" range
    else build (loadGlobal (← read).module x)

/-- Write `v` to the name `name` at `range`. -/
def writeName (name : String) (v : ValId) (range : SourceRange) : TransM Unit := do
  let name ← mangled name
  match ← place name with
  | .cell c | .free c | .nsFree _ c => discard <| build (writeCell c v)
  | .global =>
    -- Rebinding `__builtins__` changes the builtins of the functions defined after it.
    if name == "__builtins__" then reject s!"module attribute {name}" range
    else discard <| build (writeGlobal (← read).module name v)
  | .nsName ns =>
    let key ← build (strLit name)
    discard <| build (emitActing (.str .base "store") Py.setItem.ref #[ns, key, v])
  | .unresolved => reject "unresolved local" range

/-- `del name` at `range`: raise as a read does, but without the builtins fallback, then
unassign the name.  In a class body, delete it from the namespace, any failure raising
`NameError`. -/
def deleteName (name : String) (range : SourceRange) : TransM Unit := do
  let name ← mangled name
  let undef := do
    build (emitTotal (stem name) Py.undef.ref #[← build (emitConst (.str .base "n") (.str name))])
  match ← place name with
  | .cell c =>
    discard <| readLocal c name
    discard <| build (writeCell c (← undef))
  | .global =>
    if ← unmodelled name then reject s!"module attribute {name}" range
    else
      let m := (← read).module
      discard <| build (requireGlobal m name)
      discard <| build (writeGlobal m name (← undef))
  | .free c | .nsFree _ c =>
    discard <| readFree c name
    discard <| build (writeCell c (← undef))
  | .nsName ns =>
    -- As CPython's `DELETE_NAME`, any failure of `del ns[name]` raises `NameError`.
    let key ← build (strLit name)
    let failed ← build (freshLabel [Py.Value] "undefined")
    let done ← build (freshLabel [] "deleted")
    discard <| build (withHandler failed (emitActing (.str .base "del") Py.delItem.ref #[ns, key]))
    jump done.goto
    discard <| build (startBlockWith failed (.str .base "exc"))
    discard <| requireDefined (← undef) name "NameError" s!"name '{name}' is not defined"
    build unreachable
    build (startBlock done)
  | .unresolved => reject "unresolved local" range

/-- `SETUP_ANNOTATIONS`: `__annotations__ = {}`, unless the class namespace or the module's
globals already have one.  Like CPython, it ignores how the scope binds the name. -/
def setupAnnotations : TransM Unit := do
  let ns? := (← read).classNs
  let v ← match ns? with
    | some ns => do
      let key ← build (strLit "__annotations__")
      let n ← build (emitConst (.str .base "n") (.str "__annotations__"))
      let miss ← build (emitTotal (stem "__annotations__") Py.undef.ref #[n])
      build (emitFailing (stem "__annotations__") Py.getOptionalItem.ref #[ns, key, miss])
    | none => do
      let cell ← build (globalCell (← read).module "__annotations__")
      build (readCell cell (stem "__annotations__"))
  let found ← build (freshLabel [] "annotated")
  let make ← build (freshLabel [] "annotations")
  branch (← build (emitTest (.str .base "found") Py.isDefined.ref #[v])) found.goto make.goto
  build (startBlock make)
  let d ← build (emitFailing (.str .base "dict") Py.mkDict.ref #[])
  match ns? with
  | some ns =>
    let key ← build (strLit "__annotations__")
    discard <| build (emitActing (.str .base "store") Py.setItem.ref #[ns, key, d])
  | none => discard <| build (writeGlobal (← read).module "__annotations__" d)
  jump found.goto
  build (startBlock found)

/-- `LOAD_NAME __annotations__`: the class namespace's, else the module's.  Like CPython, it
ignores how the scope binds the name. -/
def annotationsDict : TransM ValId := do
  let load := do build (loadGlobal (← read).module "__annotations__")
  match (← read).classNs with
  | some ns => readNs ns "__annotations__" load
  | none => load

/-! ## Operators -/

/-- The raising operation `r` on `a` and `b`. -/
def binary {isig : InsnSig Py.env} (name : String) (r : InsnRef Py.env isig) (a b : ValId)
    (typeArgs : TypeArgsOf r (some Py.Value) := by infer_type_args) : TransM ValId :=
  build (emitFailing (stem name) r #[a, b] (typeArgs := typeArgs))

/-- `a op b` for a binary operator. -/
def binOp (op : operator SourceRange) (a b : ValId) : TransM ValId :=
  match op with
  | .Add _ => binary "add" Py.add.ref a b
  | .Sub _ => binary "sub" Py.sub.ref a b
  | .Mult _ => binary "mult" Py.mult.ref a b
  | .MatMult _ => binary "matMult" Py.matMult.ref a b
  | .Div _ => binary "div" Py.div.ref a b
  | .FloorDiv _ => binary "floorDiv" Py.floorDiv.ref a b
  | .Mod _ => binary "mod" Py.mod.ref a b
  | .Pow _ => binary "pow" Py.pow.ref a b
  | .LShift _ => binary "lShift" Py.lShift.ref a b
  | .RShift _ => binary "rShift" Py.rShift.ref a b
  | .BitAnd _ => binary "bitAnd" Py.bitAnd.ref a b
  | .BitOr _ => binary "bitOr" Py.bitOr.ref a b
  | .BitXor _ => binary "bitXor" Py.bitXor.ref a b

/-- `a op= b`, the in-place form of `binOp`. -/
def inPlaceOp (op : operator SourceRange) (a b : ValId) : TransM ValId :=
  match op with
  | .Add _ => binary "iAdd" Py.iAdd.ref a b
  | .Sub _ => binary "iSub" Py.iSub.ref a b
  | .Mult _ => binary "iMult" Py.iMult.ref a b
  | .MatMult _ => binary "iMatMult" Py.iMatMult.ref a b
  | .Div _ => binary "iDiv" Py.iDiv.ref a b
  | .FloorDiv _ => binary "iFloorDiv" Py.iFloorDiv.ref a b
  | .Mod _ => binary "iMod" Py.iMod.ref a b
  | .Pow _ => binary "iPow" Py.iPow.ref a b
  | .LShift _ => binary "iLShift" Py.iLShift.ref a b
  | .RShift _ => binary "iRShift" Py.iRShift.ref a b
  | .BitAnd _ => binary "iBitAnd" Py.iBitAnd.ref a b
  | .BitOr _ => binary "iBitOr" Py.iBitOr.ref a b
  | .BitXor _ => binary "iBitXor" Py.iBitXor.ref a b

/-- `a op b` for a comparison operator. -/
def cmpOp (op : cmpop SourceRange) (a b : ValId) : TransM ValId :=
  match op with
  | .Eq _ => binary "eq" Py.eq.ref a b
  | .NotEq _ => binary "notEq" Py.notEq.ref a b
  | .Lt _ => binary "lt" Py.lt.ref a b
  | .LtE _ => binary "ltE" Py.ltE.ref a b
  | .Gt _ => binary "gt" Py.gt.ref a b
  | .GtE _ => binary "gtE" Py.gtE.ref a b
  | .Is _ => build (emitTotal (.str .base "is") Py.is_.ref #[a, b])
  | .IsNot _ => build (emitTotal (.str .base "isNot") Py.isNot.ref #[a, b])
  | .In _ => binary "in" Py.in_.ref a b
  | .NotIn _ => binary "notIn" Py.notIn.ref a b

/-! ## Literals -/

/-- The string whose code units are the octets of `b`, as `py.bytesLit` takes. -/
def bytesText (b : ByteArray) : String := String.ofList (b.toList.map (Char.ofNat ·.toNat))

/-- A literal. -/
def literal (c : constant SourceRange) (range : SourceRange) : TransM ValId :=
  match c with
  | .ConPos _ ⟨_, n⟩ => build (intLit n)
  | .ConNeg _ ⟨_, n⟩ => build (intLit (-(n : Int)))
  | .ConString _ ⟨_, s⟩ => build (strLit s)
  | .ConFloat _ ⟨_, s⟩ =>
    match parseFloat? s with
    | some f => build (floatLit f)
    | none => unsupportedValue s!"float literal {s}" range
  | .ConTrue _ => build (boolLit true)
  | .ConFalse _ => build (boolLit false)
  | .ConNone _ => build noneLit
  | .ConBytes _ ⟨_, b⟩ => build (bytesLit (bytesText b))
  | .ConEllipsis _ => build ellipsisLit
  | .ConComplex .. => unsupportedValue "complex literal" range

/-! ## Rejected constructs -/

/-- The name of a statement `transStmt` rejects. -/
def stmtName : stmt SourceRange → String
  | .TypeAlias .. => "type alias"
  | .AsyncFor .. => "async for"
  | .AsyncWith .. => "async with"
  | .Match .. => "match"
  | .TryStar .. => "try/except*"
  | _ => "statement"

/-- An annotation that `paramAnnotations args` returns is smaller than `args`. -/
private theorem sizeOf_paramAnnotations_lt {args : arguments SourceRange}
    {x : String × expr SourceRange} (hx : x ∈ paramAnnotations args) :
    sizeOf x.2 < sizeOf args := by
  cases args with
  | mk_arguments _ posOnly pos varPos kwOnly _ varKw _ =>
  simp only [paramAnnotations, Array.mem_filterMap, Array.mem_append, Option.mem_toArray] at hx
  obtain ⟨⟨r, ⟨r₁, n⟩, ⟨r₂, a⟩, tc⟩, ha, hx⟩ := hx
  cases a with
  | none => simp at hx
  | some a =>
    simp only [Option.map_some, Option.some.injEq] at hx
    subst hx
    have hArg : sizeOf a < sizeOf (arg.mk_arg r ⟨r₁, n⟩ ⟨r₂, some a⟩ tc) := by simp; omega
    rcases ha with (((h | h) | h) | h) | h
    · have hMem := Array.sizeOf_lt_of_mem h; simp [sizeOf_ann]; omega
    · have hMem := Array.sizeOf_lt_of_mem h; simp [sizeOf_ann]; omega
    · obtain ⟨_, v⟩ := varPos; subst h; simp [sizeOf_ann]; omega
    · have hMem := Array.sizeOf_lt_of_mem h; simp [sizeOf_ann]; omega
    · obtain ⟨_, v⟩ := varKw; subst h; simp [sizeOf_ann]; omega

mutual

/-- Whether the statements hold an annotated assignment outside a nested function or class:
CPython's `find_ann`, which decides `SETUP_ANNOTATIONS`. -/
def findAnn (ss : Array (stmt SourceRange)) : Bool :=
  ss.attach.any fun ⟨s, h⟩ =>
    have _hmem := Array.sizeOf_lt_of_mem h
    findAnnIn s
termination_by sizeOf ss

/-- Whether the statement `s` holds an annotated assignment outside a nested function or
class, as `findAnn`. -/
def findAnnIn (s : stmt SourceRange) : Bool :=
  match s with
  | .AnnAssign .. => true
  | .For _ _ _ b o _ | .AsyncFor _ _ _ b o _ | .While _ _ b o | .If _ _ b o =>
    findAnn b.val || findAnn o.val
  | .With _ _ b _ | .AsyncWith _ _ b _ => findAnn b.val
  | .Try _ b hs o f | .TryStar _ b hs o f =>
    findAnn b.val ||
      hs.val.attach.any (fun ⟨.ExceptHandler _ _ _ hb, h⟩ =>
        have _hmem := Array.sizeOf_lt_of_mem h
        findAnn hb.val) ||
      findAnn o.val || findAnn f.val
  | .Match _ _ cases =>
    cases.val.attach.any fun ⟨.mk_match_case _ _ _ b, h⟩ =>
      have _hmem := Array.sizeOf_lt_of_mem h
      findAnn b.val
  | _ => false
termination_by sizeOf s

end

/-! ## Functions

A `def` is bound where it runs, and its function is emitted after the current one, from a
`FuncJob`. -/

/-- A parameter, with its default. -/
structure ParamWithDefault where
  name : String
  kind : ParamKind
  default : Option (expr SourceRange)

/-- The parameters of `args`, in signature order. -/
def params (args : arguments SourceRange) : Array ParamWithDefault :=
  let .mk_arguments _ posOnly pos varPos kwOnly kwDefaults varKw defaults := args
  let name : arg SourceRange → String := fun (.mk_arg _ ⟨_, n⟩ _ _) => n
  let positional := posOnly.val.map (·, ParamKind.posOnly) ++ pos.val.map (·, .positional)
  let firstDefault := positional.size - defaults.val.size
  positional.mapIdx (fun i (a, kind) =>
      { name := name a, kind
        default := if i ≥ firstDefault then defaults.val[i - firstDefault]? else none }) ++
    (varPos.val.map fun a => { name := name a, kind := .varPositional, default := none }).toArray ++
    kwOnly.val.mapIdx (fun j a =>
      { name := name a, kind := .kwOnly
        default := match kwDefaults.val[j]? with
          | some (.some_expr _ d) => some d
          | _ => none }) ++
    (varKw.val.map fun a => { name := name a, kind := .varKeyword, default := none }).toArray

/-- The default of a parameter of `args` is smaller than `args`. -/
private theorem sizeOf_params_default_lt {args : arguments SourceRange} {p : ParamWithDefault}
    (hp : p ∈ params args) {d : expr SourceRange} (hd : p.default = some d) :
    sizeOf d < sizeOf args := by
  cases args with
  | mk_arguments _ posOnly pos varPos kwOnly kwDefaults varKw defaults =>
  simp only [params, Array.mem_append, Array.mem_mapIdx] at hp
  rcases hp with ((⟨i, _, rfl⟩ | hv) | ⟨j, _, rfl⟩) | hk
  · simp only at hd
    split at hd
    · have hlt := Array.sizeOf_lt_of_mem (Array.mem_of_getElem? hd)
      simp only [arguments.mk_arguments.sizeOf_spec, sizeOf_ann] at hlt ⊢; omega
    · simp at hd
  · cases h : varPos.val <;> simp [h] at hv; subst hv; simp at hd
  · simp only at hd
    split at hd
    · rename_i h
      have hlt := Array.sizeOf_lt_of_mem (Array.mem_of_getElem? h)
      simp at hd; subst hd
      simp only [arguments.mk_arguments.sizeOf_spec, sizeOf_ann, opt_expr.some_expr.sizeOf_spec]
        at hlt ⊢
      omega
    · simp at hd
  · cases h : varKw.val <;> simp [h] at hk; subst hk; simp at hd

/-- Whether a default is a constant, which the prologue evaluates in place. -/
def isConstantDefault : expr SourceRange → Bool
  | .Constant _ (.ConComplex ..) _ => false
  | .Constant .. => true
  | .UnaryOp _ (.USub _) (.Constant _ (.ConPos ..) _) => true
  | .UnaryOp _ (.USub _) (.Constant _ (.ConFloat ..) _) => true
  | _ => false

public section

/-- The `k`-th candidate for a fresh name made from `first`: `first`, then `first.1`,
`first.2`, … -/
@[expose] def candidate (first : Name) : Nat → Name
  | 0 => first
  | k + 1 => .num first (k + 1)

/-- The first candidate made from `first` that `taken` does not contain.  One of the first
`taken.size + 1` candidates is free (`freshName_not_mem`), so the last case does not
happen. -/
@[expose] def freshName (taken : Std.HashSet Name) (first : Name) : Name :=
  match (List.range (taken.size + 1)).find? (fun k => !taken.contains (candidate first k)) with
  | some k => candidate first k
  | none => candidate first taken.size

/-- `freshName`, with a search that stops at the first free candidate. -/
@[expose] def freshNameFast (taken : Std.HashSet Name) (first : Name) : Name :=
  go 0 (taken.size + 1)
where
  /-- The first free candidate among the `n` candidates from the `k`-th one, or
  `candidate first taken.size` if none is free. -/
  go (k : Nat) : (n : Nat) → Name
    | 0 => candidate first taken.size
    | n + 1 => if taken.contains (candidate first k) then go (k + 1) n else candidate first k

/-- The search of `freshNameFast` over the `n` candidates from the `k`-th one gives the first
free one, as `find?` over the same candidates does, or `candidate first taken.size` if none is
free. -/
private theorem freshNameFast_go (taken : Std.HashSet Name) (first : Name) (n k : Nat) :
    freshNameFast.go taken first k n =
      match (List.range' k n).find? (fun j => !taken.contains (candidate first j)) with
      | some j => candidate first j
      | none => candidate first taken.size := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [freshNameFast.go, ih, List.range'_succ, List.find?_cons]
    cases taken.contains (candidate first k) <;> rfl

/-- `freshName` and `freshNameFast` are the same function, so the compiled code can run
`freshNameFast`, which stops at the first free candidate. -/
@[csimp] theorem freshName_eq_fast : @freshName = @freshNameFast := by
  funext taken first
  -- The two sides may use different copies of the same `match`.
  simp only [freshName, freshNameFast, freshNameFast_go, List.range_eq_range'] <;>
    (generalize (List.range' 0 (taken.size + 1)).find?
        (fun k => !taken.contains (candidate first k)) = o
     cases o <;> rfl)

end -- public section

/-- A fresh function name for the scope whose `__qualname__` is `qualname`: `m.f.g` for
`f.<locals>.g`, or `m.f.g.k` if that is taken. -/
def allocName (qualname : String) : TransM Name := do
  let parts := (qualname.splitOn ".").filter (· != "<locals>")
  let first := parts.foldl (init := (← read).moduleName) Name.str
  let n := freshName (← get).funcNames first
  modify fun s => { s with funcNames := s.funcNames.insert n }
  return n

/-- The parameters whose default is not a constant, in signature order: each is evaluated
at the definition into a default cell, which the closure captures (§5.3). -/
def defaultCellParams (args : arguments SourceRange) : Array ParamWithDefault :=
  (params args).filter (·.default.any (!isConstantDefault ·))

/-- The scope that the `def`, `class`, `lambda` or comprehension at `range` opens: a child of
the current scope.  Inside an inlined comprehension, the current scope is the comprehension's,
as in the scope pass, and the scopes opened in it are its children. -/
def childScope? (range : SourceRange) : TransM (Option ScopeId) :=
  return (← read).table.childAt? (← read).scope range

/-- The frame's key for a class's own `__class__` cell, which its methods capture.  It is not a
Python name: a class nested in a method also captures the method's `__class__`, which its
body reads. -/
def classCellKey : String := ".__class__"

/-- The cells a scope's closure captures: its free variables, and in a class body also the
names it binds that a method reads from an enclosing function (`free_class`), in order of
first use, then the class's `__class__` cell if a method needs it. -/
def capturedVars (s : Scope) : Array String :=
  let vars := s.symbols.filterMap fun sym =>
    if sym.scope == .free || sym.uses.freeClass then some sym.name else none
  if s.kind == .classBody && s.needsClassCell then vars.push classCellKey else vars

/-- Whether some scope may rebind the global `super`: then CPython calls it with no arguments.
A module-level comprehension variable named `super` counts too, on the safe side. -/
def superRebound : TransM Bool := do
  return (← read).table.scopes.any fun sc => (sc.symbol? "super").any fun sym =>
    (sc.kind == .module && sym.scope == .«local») ||
      (sym.scope == .globalExplicit && (sym.uses.assigned || sym.uses.imported))

/-- The scope `sc`, or the first scope enclosing it that is not an inlined comprehension, or
`none` if a parent is missing. -/
def pastComprehensions (t : Table) (sc : Scope) : Option Scope :=
  if sc.kind != .inlinedComprehension then some sc
  else match sc.parent with
    | none => none
    | some p => go p
where
  go (p : ScopeId) : Option Scope :=
    if hp : p < t.scopes.size then
      let ps := t.scopes[p]
      if ps.kind != .inlinedComprehension then some ps
      else match hq : ps.parent with
        | none => none
        | some q =>
          have hlt : q < p := t.parent_lt hp hq
          go q
    else none
  termination_by p

/-- The first positional parameter of the function the current code runs in, skipping
inlined comprehensions: the object a zero-argument `super()` binds. -/
def firstParam? : TransM (Option String) := do
  let some sc := pastComprehensions (← read).table (← read).cur | return none
  if !(sc.kind matches .function | .lambda) then return none
  return (sc.params.find? fun p => p.kind matches .posOnly | .positional).map (·.name)

/-- The default cells of a function with arguments `args`, by name. -/
def funcDefaults : Option (arguments SourceRange) → Array String
  | some a => (defaultCellParams a).map (·.name)
  | none => #[]

/-- The cell parameters of the function of scope `cur` with arguments `args`, a class body's
if `none`: the cells it captures, in `capturedVars` order, then its default cells.  A class's
own `__class__` cell is captured under `classCellKey`, named like any cell. -/
def funcCells (cur : Scope) (args : Option (arguments SourceRange)) :
    Array (Name × TypeExpr Py.env) :=
  (capturedVars cur).map (fun x => (cellStem (if x == classCellKey then "__class__" else x),
      Py.cell)) ++
    (funcDefaults args).map (defaultStem ·, Py.cell)

/-- The parameters of the function of scope `cur` with arguments `args`: its cells
(`funcCells`), then `args` and `kwargs`. -/
def funcParams (cur : Scope) (args : Option (arguments SourceRange)) :
    Array (Name × TypeExpr Py.env) :=
  funcCells cur args ++ #[(stem "args", Py.Value), (stem "kwargs", Py.Value)]

/-- Queue the function of scope `cur` at `sr` and return its closure, capturing the cells of
`capturedVars cur` from the frame, then `extra`.  A class body is named `m.C.<body>`.  Each
scope is queued once, as each AST node is lowered once and has its own range; `emitQueued`
reports a scope queued twice as an internal error. -/
def queueFunc (sr : SourceRange) (scope : ScopeId) (cur : Scope)
    (args : Option (arguments SourceRange)) (body : Array (stmt SourceRange))
    (stub : Option String) (extra : Array ValId)
    (classParts : Option ClassParts := none) :
    TransM (Option ValId) := do
  let mut cells := #[]
  let here ← curScope
  for x in capturedVars cur do
    -- A method's `__class__` is its class's own cell.
    let key := if x == "__class__" && here.kind == .classBody && here.needsClassCell then
      classCellKey else x
    match ← build (cellOf? key) with
    | some c => cells := cells.push c
    | none =>
      -- An unbound `nonlocal` is free with no cell; the scope pass already reported it.
      if (← read).table.syntaxErrors.isEmpty then
        internalError s!"no cell for the free variable '{x}'" sr
      return none
  let fname ← allocName (if args.isNone then s!"{cur.qualname}.<body>" else cur.qualname)
  let job : FuncJob := { name := fname, scope, cur, args, body, range := sr, stub, classParts }
  modify fun s => { s with pending := s.pending.push job }
  let params := (funcParams cur args).map (·.2)
  let cellTypes := (funcCells cur args).map (·.2)
  some <$> build (mkClosure (← build (emitFunc fname params)) cellTypes (cells ++ extra))

/-- `f` with the decorators `decs`, already evaluated, applied bottom to top. -/
def decorate (decs : Array ValId) (f : ValId) : TransM ValId := do
  let mut f := f
  for d in decs.reverse do
    let t ← build (emitTotal (.str .base "args") Py.mkTuple.ref #[f])
    let kw ← build (emitTotal (.str .base "kwargs") Py.mkKwargs.ref #[])
    f ← build (emitFailing (.str .base "decorated") Py.call.ref #[d, t, kw])
  return f

/-! ## Assignment targets -/

/-- Report the target `t`, which the translator does not lower and CPython rejects at compile
time.  It reports nothing if the scope pass already reports a syntax error at `t`, and an
internal error otherwise: the parser rejects every other such target. -/
def badTarget (t : expr SourceRange) : TransM Unit := do
  if (← read).table.syntaxErrors.any (·.range == t.ann) then return
  internalError "a target CPython rejects" t.ann


/-- An assignment target whose object and key are evaluated (§6.1). -/
inductive Lhs where
  | name (name : String) (range : SourceRange)
  | attr (obj : ValId) (name : String)
  | item (obj key : ValId)
  /-- `obj[lo:hi:step]`, with `None` for an absent bound. -/
  | slice (obj : ValId) (bounds : Array ValId)

/-! ## Expressions -/

/-- What an inlined comprehension builds. -/
inductive CompKind where
  | list | set | dict

/-- More elements than this make CPython build a set or a dict run one element at a time
(`STACK_USE_GUIDELINE`), hashing each as it is evaluated. -/
def stackUseGuideline : Nat := 30

/-- The pairs in one chunk of a dict display's run: CPython's `compiler_dict` cuts a run when
the 17th pair arrives, as 16 pairs exceed `stackUseGuideline`. -/
def dictChunk : Nat := 17

/-- `xs` cut into chunks of `n` elements; the last may be shorter. -/
def chunks {α : Type} (n : Nat) (xs : Array α) : Array (Array α) :=
  (Array.range ((xs.size + n - 1) / n)).map fun i => xs.extract (i * n) (i * n + n)

/-- The elements of a display before its first `*x`, and the rest. -/
def splitStarred (vs : Array (expr SourceRange)) :
    Array (expr SourceRange) × Array (expr SourceRange) :=
  let n := (vs.findIdx? fun | .Starred .. => true | _ => false).getD vs.size
  (vs.extract 0 n, vs.extract n vs.size)

/-- The elements of a display before its first `*x`, then the rest, are the display. -/
private theorem splitStarred_append (vs : Array (expr SourceRange)) :
    (splitStarred vs).1 ++ (splitStarred vs).2 = vs := by
  simp only [splitStarred, Array.extract_append_extract, Nat.zero_min]
  apply Array.extract_eq_self_of_le
  omega

/-- The elements of a display before and after its first `*x` are elements of the display. -/
private theorem mem_of_mem_splitStarred {vs : Array (expr SourceRange)} {x : expr SourceRange}
    (h : x ∈ (splitStarred vs).1 ∨ x ∈ (splitStarred vs).2) : x ∈ vs := by
  rw [← splitStarred_append vs, Array.mem_append]; exact h

/-- Build a dict from `entries` in order, as CPython's `compiler_dict` does.  Each run of
pairs is cut by `cut`, and `chunk` builds one chunk.  For a `**d` entry `e`, `star? e` is the
action that evaluates `d`, and `combine acc d` adds it.  The first chunk is the dict itself; a
later one is built, then combined into it. -/
def dictFromEntries {γ : Type} (entries : Array γ) (star? : γ → Option (TransM ValId))
    (cut : Array γ → Array (Array γ)) (chunk : Array γ → TransM ValId)
    (combine : ValId → ValId → TransM ValId) : TransM ValId := do
  let mut acc : Option ValId := none
  let mut pending : Array γ := #[]
  for e in entries do
    match star? e with
    | none => pending := pending.push e
    | some d =>
      let a ← flush acc pending
      pending := #[]
      acc := some (← combine a (← d))
  flush acc pending
where
  /-- The dict so far, with the pending run added. -/
  flush (acc : Option ValId) (pending : Array γ) : TransM ValId := do
    let mut acc := acc
    for c in cut pending do
      let d ← chunk c
      acc := some (← match acc with | none => pure d | some a => combine a d)
    match acc with
    | some a => return a
    | none => chunk #[]

mutual

/-- Lower an expression to the value it produces. -/
def transExpr (e : expr SourceRange) : TransM ValId := withRange e.ann do
  match e with
  | .Constant sr c _ => literal c sr
  | .Name sr ⟨_, n⟩ _ => readName n sr
  | .BinOp _ l op r => do
    let a ← transExpr l
    binOp op a (← transExpr r)
  | .UnaryOp _ op x => do
    let v ← transExpr x
    match op with
    | .Not _ => build (emitFailing (.str .base "not") Py.not_.ref #[v])
    | .USub _ => build (emitFailing (.str .base "neg") Py.uSub.ref #[v])
    | .UAdd _ => build (emitFailing (.str .base "pos") Py.uAdd.ref #[v])
    | .Invert _ => build (emitFailing (.str .base "invert") Py.invert.ref #[v])
  | .Compare _ l ops rs => compare l ops.val rs.val
  | .Call _ f args kws => call f args.val kws.val
  | .BoolOp _ op vs => boolOp (op matches .And _) vs.val
  | .NamedExpr _ (.Name nsr ⟨_, n⟩ _) v => do
    let x ← transExpr v
    writeName n x nsr
    return x
  | .NamedExpr sr .. => unsupportedValue "assignment expression" sr
  | .Lambda sr args body => do
    match ← closure sr args #[.Return body.ann ⟨body.ann, some body⟩] #[] none false false with
    | some f => return f
    | none => standIn "lambda"
  | .IfExp _ c a b => ifExp c a b
  | .Dict _ ks vs => dictDisplay ks.val vs.val
  | .Set _ vs => setDisplay vs.val
  | .List _ vs _ => listDisplay vs.val
  | .Tuple _ vs _ => tupleDisplay vs.val
  | .ListComp sr elt gens => compExpr sr .list elt none gens.val
  | .SetComp sr elt gens => compExpr sr .set elt none gens.val
  | .DictComp sr k v gens => compExpr sr .dict k (some v) gens.val
  | .GeneratorExp sr .. => unsupportedValue "generator expression" sr
  | .Await sr .. => unsupportedValue "await" sr
  | .Yield sr .. => unsupportedValue "yield" sr
  | .YieldFrom sr .. => unsupportedValue "yield from" sr
  | .JoinedStr _ vs => fString vs.val
  | .FormattedValue _ v conv spec => formatted v conv spec.val
  | .Interpolation sr .. | .TemplateStr sr .. => unsupportedValue "t-string" sr
  | .Attribute _ v ⟨_, a⟩ _ => do
    let o ← match v with
      | c@(.Call _ f args kws) => do
        match ← zeroArgSuper? f args.val kws.val with
        -- CPython's `LOAD_SUPER_ATTR`, but not for `__class__`, nor if the module names `super`.
        | some sr =>
          let named := ((← read).table.module.symbol? "super").isSome
          superCall sr (a != "__class__" && !named)
        | none => transExpr c
      | other => transExpr other
    build (getAttr o (← mangled a))
  | .Subscript _ v k _ => do
    let o ← transExpr v
    match k with
    | .Slice _ lo hi st =>
      let bs ← bounds lo.val hi.val st.val
      build (emitFailing (.str .base "slice") Py.getSlice.ref (#[o] ++ bs))
    | k => build (emitFailing (.str .base "item") Py.getItem.ref #[o, ← transExpr k])
  | .Starred sr .. => unsupportedValue "starred expression" sr
  | .Slice _ lo hi st => do
    build (emitTotal (.str .base "slice") Py.mkSlice.ref (← bounds lo.val hi.val st.val))
termination_by sizeOf e

/-- `l op₀ r₀ op₁ r₁ …`.  A chain evaluates each operand once and stops at the first false
comparison; its value is the last comparison's. -/
def compare (l : expr SourceRange) (ops : Array (cmpop SourceRange))
    (rs : Array (expr SourceRange)) : TransM ValId := do
  let a ← transExpr l
  have hzip := sizeOf_zip_le ops rs
  if h : (ops.zip rs).size = 1 then
    have hget := Array.sizeOf_getElem (ops.zip rs) 0 (by omega)
    have hsnd := sizeOf_snd_lt (ops.zip rs)[0]
    return ← cmpOp (ops.zip rs)[0].1 a (← transExpr (ops.zip rs)[0].2)
  let join ← build (freshLabel [Py.Value] "join")
  let to (v : ValId) := join.goto.bind (value v)
  jump (to (← chainLinks a (ops.zip rs) to))
  Val.id <$> build (startBlockWith join (.str .base "cmp"))
termination_by sizeOf l + sizeOf ops + sizeOf rs + 1

/-- The links `op₀ r₀ op₁ r₁ …` of a comparison chain whose left operand `a` is evaluated,
in CPython's order: each operand is evaluated once.  Every link but the last is tested, and
a false one jumps to `exit` of its result.  Returns the last link's result. -/
def chainLinks (a : ValId) (links : Array (cmpop SourceRange × expr SourceRange))
    (exit : ValId → PyTarget []) : TransM ValId := do
  let mut lhs := a
  let mut last := a
  for h : i in [:links.size] do
    have hget := Array.sizeOf_getElem links i (by get_elem_tactic)
    have hsnd := sizeOf_snd_lt links[i]
    let b ← transExpr links[i].2
    last ← cmpOp links[i].1 lhs b
    if i + 1 < links.size then
      let t ← build (truthy last)
      let next ← build (freshLabel [] "cmp")
      branch t next.goto (exit last)
      build (startBlock next)
    lhs := b
  return last
termination_by sizeOf links

/-- `f"a{x}b"`: `strConcat` of the parts, as CPython's `BUILD_STRING`.  Every part is a
`str`: a literal, or a formatted field.  A lone part is itself, as in CPython. -/
def fString (vs : Array (expr SourceRange)) : TransM ValId := do
  if h : vs.size = 1 then transExpr vs[0]
  else build (emitTotal (.str .base "fstr") Py.strConcat.ref (← vs.mapM transExpr))
termination_by sizeOf vs

/-- An f-string field `{v!c:spec}`, as CPython's `FORMAT_VALUE`: `v`, then `spec` (`""` if
absent), then the conversion `!s`, `!r` or `!a`, then `fmtValue`. -/
def formatted (v : expr SourceRange) (conv : StrataPython.int SourceRange)
    (spec : Option (expr SourceRange)) : TransM ValId := do
  let x ← transExpr v
  let sp ← match spec with
    | some s => transExpr s
    | none => build (strLit "")
  let x ← match conv with
    | .IntNeg .. => pure x
    | .IntPos sr ⟨_, c⟩ =>
      match Char.ofNat c with
      | 's' => build (emitFailing (.str .base "str") Py.toStr.ref #[x])
      | 'r' => build (emitFailing (.str .base "repr") Py.repr.ref #[x])
      | 'a' => build (emitFailing (.str .base "ascii") Py.ascii.ref #[x])
      | _ => unsupportedValue "f-string conversion" sr  -- the parser gives no other
  build (emitFailing (.str .base "fmt") Py.fmtValue.ref #[x, sp])
termination_by sizeOf v + sizeOf spec + 1

/-- The bounds `lo`, `hi` and `st` of a slice, in order, `None` for an absent one. -/
def bounds (lo hi st : Option (expr SourceRange)) : TransM (Array ValId) :=
  return #[← bound lo, ← bound hi, ← bound st]
termination_by sizeOf lo + sizeOf hi + sizeOf st + 1

/-- A bound of a slice, `None` if it is absent. -/
def bound : Option (expr SourceRange) → TransM ValId
  | some b => transExpr b
  | none => build noneLit
termination_by b => sizeOf b

/-- `a and b …` (`isAnd`) or `a or b …`, as a value: each operand but the last is tested, and
the first that decides the result is the result. -/
def boolOp (isAnd : Bool) (vs : Array (expr SourceRange)) : TransM ValId := do
  let join ← build (freshLabel [Py.Value] "join")
  for h : i in [:vs.size] do
    let v ← transExpr vs[i]
    let decided := join.goto.bind (value v)
    if i + 1 < vs.size then
      let t ← build (truthy v)
      let next ← build (freshLabel [] (if isAnd then "and" else "or"))
      if isAnd then branch t next.goto decided else branch t decided next.goto
      build (startBlock next)
    else
      jump decided
  Val.id <$> build (startBlockWith join (.str .base "bool"))
termination_by sizeOf vs

/-- `a if c else b`, as a value.  `c` is a condition. -/
def ifExp (c a b : expr SourceRange) : TransM ValId := do
  let thenL ← build (freshLabel [] "then")
  let elseL ← build (freshLabel [] "else")
  let join ← build (freshLabel [Py.Value] "join")
  transCond c thenL.goto elseL.goto
  build (startBlock thenL)
  jump (join.goto.bind (value (← transExpr a)))
  build (startBlock elseL)
  jump (join.goto.bind (value (← transExpr b)))
  Val.id <$> build (startBlockWith join (.str .base "ifexp"))
termination_by sizeOf c + sizeOf a + sizeOf b + 2

/-- Lower `e` as a condition: end the open block with a jump to `t` if `e` is true and to `f`
otherwise, as CPython's `compiler_jump_if` does.  `not`, `and`, `or`, `x if c else y` and a
chained comparison become branches, so each operand's truth is tested at most once. -/
def transCond (e : expr SourceRange) (t f : PyTarget []) : TransM Unit := withRange e.ann do
  match e with
  | .UnaryOp _ (.Not _) x => transCond x f t
  | .BoolOp _ op ⟨_, vs⟩ =>
    let isAnd := op matches .And _
    for h : i in [:vs.size] do
      if i + 1 < vs.size then
        let next ← build (freshLabel [] (if isAnd then "and" else "or"))
        if isAnd then transCond vs[i] next.goto f else transCond vs[i] t next.goto
        build (startBlock next)
      else
        transCond vs[i] t f
  | .IfExp _ c a b =>
    let thenL ← build (freshLabel [] "then")
    let elseL ← build (freshLabel [] "else")
    transCond c thenL.goto elseL.goto
    build (startBlock thenL)
    transCond a t f
    build (startBlock elseL)
    transCond b t f
  | .Compare _ l ops rs =>
    have hzip := sizeOf_zip_le ops.val rs.val
    let last ← chainLinks (← transExpr l) (ops.val.zip rs.val) fun _ => f
    branch (← build (truthy last)) t f
  | other => branch (← build (truthy (← transExpr other))) t f
termination_by sizeOf e + 1

/-- `[a, *x, b]`: `BUILD_LIST` of the elements before the first `*x`, then `LIST_EXTEND` for
each `*x` and `LIST_APPEND` for each later element, as CPython does.  The values `pre`, already
evaluated, come first. -/
def listDisplay (vs : Array (expr SourceRange)) (pre : Array ValId := #[]) :
    TransM ValId := do
  let first ← (splitStarred vs).1.attach.mapM fun ⟨x, hx⟩ =>
    have hmem := Array.sizeOf_lt_of_mem (mem_of_mem_splitStarred (.inl hx))
    transExpr x
  let l ← build (emitTotal (.str .base "list") Py.mkList.ref (pre ++ first))
  for hv : v in (splitStarred vs).2 do
    have hmem := Array.sizeOf_lt_of_mem (mem_of_mem_splitStarred (.inr hv))
    match v, hmem with
    | .Starred _ x _, hmem =>
      discard <| build (emitActing (.str .base "extend") Py.listExtend.ref #[l, ← transExpr x])
    | v, hmem =>
      let x ← transExpr v
      discard <| build (emitEffect (.str .base "append") Py.listAppend.ref #[l, x])
  return l
termination_by sizeOf vs

/-- `(a, b)`: `BUILD_TUPLE`.  With a `*x`, a list display then `INTRINSIC_LIST_TO_TUPLE`, as
CPython does.  The values `pre`, already evaluated, come first. -/
def tupleDisplay (vs : Array (expr SourceRange)) (pre : Array ValId := #[]) :
    TransM ValId := do
  if (splitStarred vs).2.isEmpty then
    build (emitTotal (.str .base "tuple") Py.mkTuple.ref (pre ++ (← vs.mapM transExpr)))
  else
    build (emitTotal (.str .base "tuple") Py.listToTuple.ref #[← listDisplay vs pre])
termination_by sizeOf vs + 1

/-- `{a, *x, b}`: as `listDisplay`, with `BUILD_SET`, `SET_UPDATE` and `SET_ADD`.  A set of
more than `stackUseGuideline` elements starts empty, as in CPython. -/
def setDisplay (vs : Array (expr SourceRange)) : TransM ValId := do
  let parts := if vs.size > stackUseGuideline then (#[], vs) else splitStarred vs
  have hparts : ∀ x, x ∈ parts.1 ∨ x ∈ parts.2 → x ∈ vs := by
    intro x hx; simp only [parts] at hx; split at hx
    · simpa using hx
    · exact mem_of_mem_splitStarred hx
  let first ← parts.1.attach.mapM fun ⟨x, hx⟩ =>
    have hmem := Array.sizeOf_lt_of_mem (hparts x (.inl hx))
    transExpr x
  let st ← build (emitFailing (.str .base "set") Py.mkSet.ref first)
  for hv : v in parts.2 do
    have hmem := Array.sizeOf_lt_of_mem (hparts v (.inr hv))
    match v, hmem with
    | .Starred _ x _, hmem =>
      discard <| build (emitActing (.str .base "update") Py.setUpdate.ref #[st, ← transExpr x])
    | v, hmem => discard <| build (emitActing (.str .base "add") Py.setAdd.ref #[st, ← transExpr v])
  return st
termination_by sizeOf vs

/-- `{k: v, **d}`, as CPython builds it: a run of pairs is cut into chunks of `dictChunk`,
each built by `pairs`, and each later chunk and each `**d` is `DICT_UPDATE`. -/
def dictDisplay (ks : Array (opt_expr SourceRange)) (vs : Array (expr SourceRange)) :
    TransM ValId :=
  dictFromEntries (ks.zip vs).attach
    (fun ⟨(k, d), h⟩ => match k with
      | .some_expr .. => none
      | .missing_expr .. =>
        have hmem := Array.sizeOf_lt_of_mem (Array.of_mem_zip h).2
        some (transExpr d))
    (chunks dictChunk) pairs
    (fun a d => build (emitFailing (.str .base "update") Py.dictUpdate.ref #[a, d]))
termination_by sizeOf ks + sizeOf vs + 2
where
  /-- `BUILD_MAP` of the pairs `k: v` of `c`, key before value.  More than
  `stackUseGuideline / 2` pairs start an empty dict and add each pair (`MAP_ADD`). -/
  pairs (c : Array {e // e ∈ ks.zip vs}) : TransM ValId := do
    let kvs : Array ({k : expr SourceRange // sizeOf k < sizeOf ks} ×
        {v : expr SourceRange // sizeOf v < sizeOf vs}) := c.filterMap fun ⟨(k, v), h⟩ =>
      match hk : k with
      | .some_expr _ k =>
        some (⟨k, by
                have hmem := Array.sizeOf_lt_of_mem (Array.of_mem_zip h).1
                subst hk; simp at hmem; omega⟩,
              ⟨v, Array.sizeOf_lt_of_mem (Array.of_mem_zip h).2⟩)
      | .missing_expr .. => none
    if 2 * kvs.size > stackUseGuideline then
      let d ← build (emitFailing (.str .base "dict") Py.mkDict.ref #[])
      for (⟨k, hk⟩, ⟨v, hv⟩) in kvs do
        let kv ← transExpr k
        let vv ← transExpr v
        discard <| build (emitActing (.str .base "set") Py.dictSet.ref #[d, kv, vv])
      return d
    let mut args := #[]
    for (⟨k, hk⟩, ⟨v, hv⟩) in kvs do
      args := args.push (← transExpr k)
      args := args.push (← transExpr v)
    build (emitFailing (.str .base "dict") Py.mkDict.ref args)
  termination_by sizeOf ks + sizeOf vs + 1

/-- `f(a, *x, k=v, **m)`: `py.call f args kwargs`, evaluating the callee, the positional
arguments, then the keyword arguments, as CPython does.  `args` is a tuple display; a lone
`*x` is evaluated in place and made a tuple by `argsTuple` after the keyword arguments.
`kwargs` is runs of `k=v` pairs, each a total `mkKwargs`, and `DICT_MERGE` (`dictMerge`)
for each `**m`. -/
def call (f : expr SourceRange) (args : Array (expr SourceRange))
    (kws : Array (keyword SourceRange)) : TransM ValId := do
  if let some sr ← zeroArgSuper? f args kws then return ← superCall sr false
  let fv ← transExpr f
  let lone ← if h : args.size = 1 then
      match hx : args[0] with
      | .Starred _ x _ =>
        have hsize : sizeOf x < sizeOf args := by
          have hget := Array.sizeOf_getElem args 0 (by omega); rw [hx] at hget; simp at hget; omega
        some <$> transExpr x
      | _ => pure none
    else pure none
  let t? ← if lone.isSome then pure none else some <$> tupleDisplay args
  let d ← kwargsDict fv kws
  let t ← match t?, lone with
    | some t, _ => pure t
    | none, some x => build (emitFailing (.str .base "args") Py.argsTuple.ref #[fv, x])
    | none, none => build (emitTotal (.str .base "args") Py.mkTuple.ref #[])
  build (emitFailing (.str .base "call") Py.call.ref #[fv, t, d])
termination_by sizeOf f + sizeOf args + sizeOf kws + 2

/-- The evaluation of the target `t`, or `none` if `t` is not a name, an attribute or a
subscript: `o` for `o.a`, then `o` and `k` for `o[k]`.  The attribute name is mangled, as in
a read. -/
def target? : expr SourceRange → Option (TransM Lhs)
  | .Name sr ⟨_, n⟩ _ => some (pure (.name n sr))
  | .Attribute _ v ⟨_, a⟩ _ => some do return .attr (← transExpr v) (← mangled a)
  | .Subscript _ v k _ => some do
    let o ← transExpr v
    match k with
    | .Slice _ lo hi st => return .slice o (← bounds lo.val hi.val st.val)
    | k => return .item o (← transExpr k)
  | _ => none
termination_by t => sizeOf t

/-- Read the target `l`, as `x op= e` does. -/
def readLhs : Lhs → TransM ValId
  | .name n r => readName n r
  | .attr o a => build (getAttr o a)
  | .item o k => build (emitFailing (.str .base "item") Py.getItem.ref #[o, k])
  | .slice o bs => build (emitFailing (.str .base "slice") Py.getSlice.ref (#[o] ++ bs))

/-- Write `v` to the target `l`.  A name is written at `range`, the statement's.  A slice is
written by `setItem` of a `mkSlice`, as CPython's `STORE_SLICE` does. -/
def writeLhs (l : Lhs) (v : ValId) (range : SourceRange) : TransM Unit :=
  match l with
  | .name n _ => writeName n v range
  | .attr o a => discard <| build (setAttr o a v)
  | .item o k => discard <| build (emitActing (.str .base "store") Py.setItem.ref #[o, k, v])
  | .slice o bs => do
    let k ← build (emitTotal (.str .base "slice") Py.mkSlice.ref bs)
    discard <| build (emitActing (.str .base "store") Py.setItem.ref #[o, k, v])

/-- The assignment of a value to the target `t` at `range`, or the part of `t` the translator
does not lower.  A tuple or list target unpacks the value, with `unpackEx` if an element is
starred, then assigns each element in turn, evaluating its target only then. -/
def assigner (range : SourceRange) (t : expr SourceRange) :
    Except (expr SourceRange) (ValId → TransM Unit) :=
  match t with
  | .Tuple _ ⟨_, ts⟩ _ | .List _ ⟨_, ts⟩ _ => do
    let .ok star := starredIndex? ts | throw t
    let elems ← ts.attach.mapM fun ⟨t, h⟩ =>
      have hmem := Array.sizeOf_lt_of_mem h
      match t with | .Starred _ e _ => assigner range e | e => assigner range e
    let unpack (v : ValId) : TransM ValId := do
      match star with
      | none =>
        let n ← build (emitConst (.str .base "n") (.int ts.size))
        build (emitFailing (.str .base "unpack") Py.unpackSeq.ref #[v, n])
      | some i =>
        let before ← build (emitConst (.str .base "before") (.int i))
        let after ← build (emitConst (.str .base "after") (.int (ts.size - i - 1)))
        build (emitFailing (.str .base "unpack") Py.unpackEx.ref #[v, before, after])
    return fun v => do
      let tup ← unpack v
      for h : i in [:elems.size] do
        let x ← build (emitTotal (.str .base "elem") Py.tupleGet.ref
          #[tup, ← build (emitConst (.str .base "i") (.int i))])
        elems[i] x
  | t => match target? t with
    | some eval => return fun v => do writeLhs (← eval) v range
    | none => throw t
termination_by sizeOf t + 1

/-- A list, set or dict comprehension at `sr` (§6.8), inlined as PEP 709 does.  The
outermost iterable is evaluated in the enclosing scope, then the accumulator is made, then
the comprehension's scope takes over: each iteration variable is a fresh cell, shadowing the
enclosing scope's name until the end, and each `for` clause is a `py.forEach` whose body
region assigns the target, tests the `if`s, and runs the next clause or adds the element. -/
def compExpr (sr : SourceRange) (kind : CompKind) (elt : expr SourceRange)
    (value : Option (expr SourceRange)) (gens : Array (comprehension SourceRange)) :
    TransM ValId := do
  let what := match kind with
    | .list => "list comprehension" | .set => "set comprehension" | .dict => "dict comprehension"
  if gens.any fun (.mk_comprehension _ _ _ _ a) => a.value != 0 then
    return ← unsupportedValue s!"async {what}" sr
  let ctx ← read
  match hg : (gens[0]? : Option (comprehension SourceRange)) with
  | none => internalError s!"{what} without a generator" sr; standIn what
  | some (.mk_comprehension _ _ iter0 _ _) =>
  have hmem := Array.sizeOf_lt_of_mem (Array.mem_of_getElem? hg)
  let some scope ← childScope? sr | return ← unsupportedValue s!"{what} without a scope" sr
  let some cur := ctx.table.scopes[scope]?
    | internalError s!"scope {scope} is not in the table" sr; standIn what
  let it ← transExpr iter0
  let acc ← match kind with
    | .list => build (emitTotal (.str .base "acc") Py.mkList.ref #[])
    | .set => build (emitFailing (.str .base "acc") Py.mkSet.ref #[])
    | .dict => build (emitFailing (.str .base "acc") Py.mkDict.ref #[])
  let saved := (← build (get : PyM Info PyBuild.Frame)).locals
  withReader ({ · with scope, cur, classNs := none }) do
    for x in cur.regionLocals do discard <| build (declareLocal x)
    have hlist := sizeOf_toList_lt gens
    clause acc it gens.toList
  build (modify fun f => { f with locals := saved })
  return acc
termination_by sizeOf elt + sizeOf value + sizeOf gens
where
  /-- The first `for` clause of `gs`, over the evaluated iterable `it`, and the clauses after
  it. -/
  clause (acc it : ValId) (gs : List (comprehension SourceRange)) : TransM Unit := do
    match gs with
    | [] => return
    | .mk_comprehension _ target _ ifs _ :: later =>
    let assign ← match assigner sr target with
      | .ok a => pure a
      | .error t => do badTarget t; pure fun _ => pure ()
    forEach it fun item => do
      assign item
      let skip ← build (freshLabel [] "skip")
      for c in ifs.val do
        let next ← build (freshLabel [] "if")
        transCond c next.goto skip.goto
        build (startBlock next)
      match later with
      | c@(.mk_comprehension _ _ iter _ _) :: rest => clause acc (← transExpr iter) (c :: rest)
      | [] =>
        match kind, value with
        | .dict, some v =>
          let k ← transExpr elt
          let x ← transExpr v
          discard <| build (emitActing (.str .base "set") Py.dictSet.ref #[acc, k, x])
        | .set, _ =>
          discard <| build (emitActing (.str .base "add") Py.setAdd.ref #[acc, ← transExpr elt])
        | _, _ =>
          let x ← transExpr elt
          discard <| build (emitEffect (.str .base "append") Py.listAppend.ref #[acc, x])
      if ← targeted skip then
        jump skip.goto
        build (startBlock skip)
  termination_by sizeOf gs + sizeOf elt + sizeOf value

/-- The range of the name `super` in `f(args, kws)`, if it is a zero-argument `super()` of the
builtin `super`: not a local `super`, nor one a class body binds. -/
def zeroArgSuper? (f : expr SourceRange) (args : Array (expr SourceRange))
    (kws : Array (keyword SourceRange)) : TransM (Option SourceRange) := do
  let .Name sr ⟨_, "super"⟩ _ := f | return none
  if !args.isEmpty || !kws.isEmpty then return none
  match ← place "super" with
  | .global => return some sr
  | .nsName _ =>
    -- A class body reads `super` from its namespace, else the builtin.
    return if ((← curScope).symbol? "super").any (·.uses.assigned) then none else some sr
  | _ => return none

/-- `super()` at `sr` with no arguments: `super(__class__, first)`, `first` being the first
positional parameter of the enclosing function.  `super().x` (`attr`) is CPython's
`LOAD_SUPER_ATTR`, which reads the cell, then `first`; a bare `super()` is a call, which checks
`first`, then the cell, raising `RuntimeError`.  CPython also uses a plain call for
`super().__class__`, and for every `super().x` in a module whose symbol table names `super`.
Where CPython raises `RuntimeError` at run time instead, with no `__class__` cell or no
positional parameter, it is rejected, and so it is if the module may rebind `super`. -/
def superCall (sr : SourceRange) (attr : Bool) : TransM ValId := do
  if ← superRebound then return ← unsupportedValue "super() with super rebound" sr
  let some first ← firstParam? | unsupportedValue "super() without a positional parameter" sr
  let .free c ← place "__class__" | unsupportedValue "super() outside a class" sr
  -- The current cell of the parameter's name, which a comprehension may rebind.
  let some p ← build (cellOf? first) | unsupportedValue "super() without a positional parameter" sr
  let fv ← build (loadGlobal (← read).module "super")
  let (cls, self) ← if attr then do
      let cls ← readFree c "__class__"
      pure (cls, ← readLocal p first)
    else do
      let v ← build (readCell p (stem first))
      let self ← requireDefined v first "RuntimeError" "super(): arg[0] deleted"
      let k ← build (readCell c (stem "__class__"))
      pure (← requireDefined k "__class__" "RuntimeError" "super(): empty __class__ cell", self)
  let t ← build (emitTotal (.str .base "args") Py.mkTuple.ref #[cls, self])
  let d ← build (emitTotal (.str .base "kwargs") Py.mkKwargs.ref #[])
  build (emitFailing (.str .base "super") Py.call.ref #[fv, t, d])

/-- The keyword dict of a call to `fv` with the keyword arguments `kws`: runs of `k=v` pairs,
each a total `mkKwargs`, and `DICT_MERGE` (`dictMerge`) for each `**m`. -/
def kwargsDict (fv : ValId) (kws : Array (keyword SourceRange)) : TransM ValId :=
  dictFromEntries kws.attach
    (fun ⟨kw, h⟩ =>
      have hmem := Array.sizeOf_lt_of_mem h
      match kw, hmem with
      | .mk_keyword _ _ v, hmem =>
        if kw.nameAndValue.1.isSome then none else some (transExpr v))
    (fun run => if run.isEmpty then #[] else #[run])
    (fun run => do
      let mut kvs := #[]
      for ⟨kw, h⟩ in run do
        have hmem := Array.sizeOf_lt_of_mem h
        match kw, hmem with
        | .mk_keyword _ _ v, hmem =>
          kvs := kvs.push (← build (strLit (kw.nameAndValue.1.getD "")))
          kvs := kvs.push (← transExpr v)
      build (emitTotal (.str .base "kwargs") Py.mkKwargs.ref kvs))
    (fun a m => build (emitFailing (.str .base "merge") Py.dictMerge.ref #[fv, a, m]))
termination_by sizeOf kws + 1

/-- The closure of the `def` or `lambda` at `sr`, whose function is queued, or `none` if it is
rejected, as §5.3 builds it: the decorators are evaluated, then the non-constant defaults
into default cells, then the annotations, `returns` last.  The closure captures the cells of
the function's free variables (§6.6), then the default cells.  The annotations are stored in
its `__annotations__`, then the decorators are applied to it bottom to top.  An `async def`
or a generator is queued as a stub. -/
def closure (sr : SourceRange) (args : arguments SourceRange)
    (body : Array (stmt SourceRange)) (decorators : Array (expr SourceRange))
    (returns : Option (expr SourceRange)) (hasTypeParams isAsync : Bool) :
    TransM (Option ValId) := do
  let ctx ← read
  if hasTypeParams then reject "type parameters" sr; return none
  let some scope ← childScope? sr
    | do reject "function without a scope" sr; return none
  let some cur := ctx.table.scopes[scope]?
    | do internalError s!"scope {scope} is not in the table" sr; return none
  let stub ← if isAsync then do reject "async def" sr; pure (some "async def")
    else match cur.generator with
      | some r => do reject "generator function" r; pure (some "generator function")
      | none => pure none
  let decs ← decorators.mapM transExpr
  let mut defaults := #[]
  for hp : p in defaultCellParams args do
    match hd : p.default with
    | some d =>
      have hdef := sizeOf_params_default_lt (Array.mem_of_mem_filter hp) hd
      defaults := defaults.push (← build (newCell (defaultStem p.name) (← transExpr d)))
    | none => pure ()
  -- The annotations, keyed by mangled name, as CPython 3.12 evaluates them at the `def`.
  let mut anns := #[]
  for ha : a in paramAnnotations args do
    have hann := sizeOf_paramAnnotations_lt ha
    anns := anns.push (← build (strLit (← mangled a.1))) |>.push (← transExpr a.2)
  if let some r := returns then
    anns := anns.push (← build (strLit "return")) |>.push (← transExpr r)
  let some f ← queueFunc sr scope cur (some args) body stub defaults | return none
  -- The `self.x: T` of a class body's `__init__` declare fields of the instance (§6.7), unless
  -- a decorator may make its first parameter something else, as `@classmethod` does, or the
  -- body binds that parameter again (`Shape.keepsSelf`).
  if ctx.cur.kind == .classBody && cur.name == "__init__" && stub.isNone then
    if let some job := (← get).pending.back? then
      let keeps := decorators.isEmpty && Shape.keepsSelf ctx.table scope args
      modify fun s => { s with inits := s.inits.push (sr, job.name, keeps) }
  unless anns.isEmpty do
    let d ← build (emitFailing (.str .base "annotations") Py.mkDict.ref anns)
    discard <| build (setAttr f "__annotations__" d)
  some <$> decorate decs f
termination_by sizeOf args + sizeOf decorators + sizeOf returns

end

/-- Delete the target `l`. -/
def deleteLhs : Lhs → TransM Unit
  | .name n r => deleteName n r
  | .attr o a => discard <| build (delAttr o a)
  | .item o k => discard <| build (emitActing (.str .base "del") Py.delItem.ref #[o, k])
  | .slice o bs => do
    let k ← build (emitTotal (.str .base "slice") Py.mkSlice.ref bs)
    discard <| build (emitActing (.str .base "del") Py.delItem.ref #[o, k])

/-- The deletion of the target `t`, or the part of `t` the translator does not lower.  A
tuple or list deletes its elements left to right. -/
def deleter (t : expr SourceRange) : Except (expr SourceRange) (TransM Unit) :=
  match t with
  | .Tuple _ ts _ | .List _ ts _ => do
    let dels ← ts.val.mapM deleter
    return dels.forM id
  | t => match target? t with
    | some eval => return do deleteLhs (← eval)
    | none => throw t
termination_by sizeOf t

/-- Emit the argument-binding prologue (§5.4), writing each parameter's cell.  The defaults are a
tuple with one entry per named parameter: a constant default is evaluated in place, another is
read from its cell in `defaults`, and a parameter without one gets `undef`.  `bindArgs` binds
`args` and `kwargs` to the parameters as CPython does, and each parameter, `*args` and `**kw`
is taken from its result with `tupleGet`. -/
def prologue (ps : Array ParamWithDefault) (defaults : Array (String × ValId))
    (args kwargs : ValId) : TransM Unit := do
  -- As in CPython, a private name is mangled everywhere, its keyword included.
  let ps ← ps.mapM fun p => return { p with name := ← mangled p.name }
  let defaults ← defaults.mapM fun (n, c) => return (← mangled n, c)
  let isPos (p : ParamWithDefault) := p.kind == .posOnly || p.kind == .positional
  let named := ps.filter fun p => isPos p || p.kind == .kwOnly
  let varPos := ps.find? (·.kind == .varPositional)
  let varKw := ps.find? (·.kind == .varKeyword)
  let fillSlot (p : ParamWithDefault) : TransM ValId := do
    match p.default, defaults.find? (·.1 == p.name) with
    | some _, some (_, c) => build (readCell c (defaultStem p.name))
    | some d, none => transExpr d
    | none, _ => build (emitTotal (stem p.name) Py.undef.ref
        #[← build (emitConst (.str .base "n") (.str p.name))])
  let fill ← build (emitTotal (.str .base "defaults") Py.mkTuple.ref (← named.mapM fillSlot))
  let const (c : Const) : TransM ValId := build (emitConst (.str .base "c") c)
  let nPosOnly ← const (.int (ps.filter (·.kind == .posOnly)).size)
  let nPos ← const (.int (ps.filter isPos).size)
  let hasVarPos ← const (.bool varPos.isSome)
  let hasVarKw ← const (.bool varKw.isSome)
  let names ← named.mapM fun p => const (.str p.name)
  let bound ← build (emitFailing (.str .base "bound") Py.bindArgs.ref
    (#[args, kwargs, fill, nPosOnly, nPos, hasVarPos, hasVarKw] ++ names))
  let take (i : Nat) (name : String) : TransM Unit := do
    let v ← build (emitTotal (stem name) Py.tupleGet.ref #[bound, ← const (.int i)])
    writeName name v .none
  for h : i in [:named.size] do take i named[i].name
  if let some p := varPos then take named.size p.name
  if let some p := varKw then take (named.size + if varPos.isSome then 1 else 0) p.name

/-- `def name(args): body` at `sr`: bind `name` to the function's closure. -/
def defStmt (sr : SourceRange) (name : String) (args : arguments SourceRange)
    (body : Array (stmt SourceRange)) (decorators : Array (expr SourceRange))
    (returns : Option (expr SourceRange)) (hasTypeParams isAsync : Bool) : TransM Unit := do
  if let some f ← closure sr args body decorators returns hasTypeParams isAsync then
    writeName name f sr

/-- `class name(bases, kws): body` at `sr` (§6.7): `__build_class__` called on the closure
of the body's function, the name, the bases and the keywords, then the decorators, evaluated
first, applied to the class.  If a method needs `__class__`, its cell is made here, captured
by the body, and set to the class before the decorators run. -/
def classDef (sr : SourceRange) (name : String) (bases : Array (expr SourceRange))
    (kws : Array (keyword SourceRange)) (body : Array (stmt SourceRange))
    (decorators : Array (expr SourceRange)) (hasTypeParams : Bool) : TransM Unit := do
  let ctx ← read
  if hasTypeParams then return ← reject "type parameters" sr
  let some scope ← childScope? sr | return ← reject "class without a scope" sr
  let some cur := ctx.table.scopes[scope]?
    | return ← internalError s!"scope {scope} is not in the table" sr
  let decs ← decorators.mapM transExpr
  let m ← build (emitConst (.str .base "m") (.str "builtins"))
  let n ← build (emitConst (.str .base "n") (.str "__build_class__"))
  let bc ← build (emitFailing (.str .base "__build_class__") Py.qualifiedRef.ref #[m, n])
  let classCell ← if cur.needsClassCell then do
      let n ← build (emitConst (.str .base "n") (.str "__class__"))
      let undef ← build (emitTotal (stem "__class__") Py.undef.ref #[n])
      some <$> build (newCell (cellStem "__class__") undef)
    else pure none
  -- The body captures the cell under `classCellKey`, for this closure only.
  let saved := (← build (get : PyM Info PyBuild.Frame)).locals
  if let some c := classCell then build (captureCell classCellKey c)
  -- The body's function states the class's declared shape (§6.7).
  let f? ← queueFunc sr scope cur none body none #[]
    (some { outerPrivate := ctx.cur.privateName, bases, keywords := kws, decorators })
  build (modify fun fr => { fr with locals := saved })
  let some f := f? | return
  let t ← tupleDisplay bases (pre := #[f, ← build (strLit name)])
  let d ← kwargsDict bc kws
  let cls ← build (emitFailing (stem name) Py.call.ref #[bc, t, d])
  if let some c := classCell then discard <| build (writeCell c cls)
  writeName name (← decorate decs cls) sr

/-! ## Statements -/

/-- Lower an `import` or `from … import` alias, from the scope table's import record. -/
def importAlias (a : alias SourceRange) : TransM Unit := do
  let ctx ← read
  let some imp := (ctx.table.importsIn ctx.scope).find? (·.range == a.ann)
    | reject "import" a.ann
  let v ← match imp.target with
    | .module path => do
      let m ← build (importModule imp.loads)
      if path == imp.loads then pure m else build (importModule path)
    | .member m n => build (importFrom m n)
  writeName imp.name v a.ann

/-- Unbind `name`, bound at `range`, as leaving `except … as name` does with `name = None`,
then `del name`.  That leaves a cell unassigned.  In a class namespace, it stores `None`, then
deletes the key, as CPython's `STORE_NAME` and `DELETE_NAME` do. -/
def unbindName (name : String) (range : SourceRange) : TransM Unit := do
  let m ← mangled name
  match ← place m with
  | .nsName _ =>
    writeName name (← build noneLit) range
    deleteName name range
  | _ =>
    let n ← build (emitConst (.str .base "n") (.str m))
    writeName name (← build (emitTotal (stem m) Py.undef.ref #[n])) range

/-- Make `prev` the exception being handled again. -/
def popExcept (prev : ValId) : TransM Unit :=
  discard <| build (emitEffect (.str .base "pop") Py.popExcept.ref #[prev])

/-- Leave an `except` clause or a `finally` body other than by a failure, as CPython does:
under `outer`, the handler around the `try`, make `prev` the exception being handled again,
then unbind `name` if the clause binds one. -/
def leaveHandler (prev : ValId) (name : Option (String × SourceRange))
    (outer : PyTarget [Py.Value]) :
    TransM Unit :=
  withHandlerTo outer do
    popExcept prev
    if let some (n, r) := name then unbindName n r

/-- Leave by `break` (`brk := true`), `continue`, or `return v` (`ret := some v`), walking the
exits stack from the innermost entry (§4). -/
def exitWalk (brk : Bool) (ret : Option ValId) (range : SourceRange) : TransM Unit := do
  let exits := (← get).exits
  -- The scope pass reports a `break` or `continue` outside a loop.
  if ret.isNone && !exits.any (· matches .loop ..) then
    if (← read).table.syntaxErrors.any (·.range == range) then return
    return ← internalError (if brk then "'break' outside loop" else "'continue' outside loop") range
  for e in exits.reverse do
    match e, ret with
    | .loop b c, none => return ← jump (if brk then b else c).goto
    | .loop .., some _ => pure ()
    | .handler prev name outer, _ => leaveHandler prev name outer
    | .cleanup fin, _ =>
      let c ← build <| match ret with
        | some v => compReturn v
        | none => if brk then compBreak else compContinue
      return ← jump (fin.goto.bind c)
  if let some v := ret then build (emitReturn v)

/-- The arms of the dispatch after a `finally` body or a `with`'s `__exit__`, which do from
outside the statement at `sr` what the completion would have done: `join` is the code after
it, and `outer` the handler around it. -/
def exitArms (join : BlockRef Py.env []) (outer : PyTarget [Py.Value]) (sr : SourceRange) :
    TransM (Arms TransM) := do
  let exits := (← get).exits
  -- `break` or `continue` jumps straight to the loop when it is the innermost entry.
  let loopArm (brk : Bool) : TransM (Arm TransM [] Unit) := do
    if !exits.any (· matches .loop ..) then return .unreachable
    match exits.back? with
    | some (.loop b c) =>
      let k := (if brk then b else c).goto
      recordTarget k
      return .to k
    | _ => return .block (if brk then "brk" else "cont") fun _ => exitWalk brk none sr
  return {
    normal := .to join.goto
    «return» := if (← curScope).kind matches .module | .classBody then .unreachable
      else .block "ret" fun v => exitWalk false (some v.id) sr
    raise := .to outer
    «break» := ← loopArm true
    «continue» := ← loopArm false }

mutual

/-- Lower a statement list, skipping what follows a statement that ends every path. -/
def transStmts (ss : Array (stmt SourceRange)) : TransM Unit := do
  for s in ss do
    if !(← isOpen) then return
    transStmt s
termination_by sizeOf ss

/-- Lower a statement. -/
def transStmt (s : stmt SourceRange) : TransM Unit := withRange s.ann do
  match s with
  | .Expr _ v => discard <| transExpr v
  | .Pass _ | .Global .. | .Nonlocal .. => pure ()
  | .Assign sr ⟨_, targets⟩ v _ =>
    match targets.mapM (assigner sr) with
    | .error t => badTarget t
    | .ok assigns =>
      let x ← transExpr v
      for assign in assigns do assign x
  | .AnnAssign sr target ann ⟨_, value⟩ simple =>
    let some eval := target? target | badTarget target
    match value with
    | none => discard eval
    | some v =>
      let x ← transExpr v
      writeLhs (← eval) x sr
    -- In a module or class body the annotation is evaluated, as in CPython 3.12, and a simple
    -- name's is stored in `__annotations__` (§6.1; §9 Q11 for Python 3.14).
    if (← curScope).kind matches .module | .classBody then
      let t ← transExpr ann
      if let .Name _ ⟨_, n⟩ _ := target then
        if simple.value != 0 then
          let d ← annotationsDict
          let key ← build (strLit (← mangled n))
          discard <| build (emitActing (.str .base "store") Py.setItem.ref #[d, key, t])
  | .AugAssign sr target op v =>
    let some eval := target? target | badTarget target
    let l ← eval
    let cur ← readLhs l
    let rhs ← transExpr v
    writeLhs l (← inPlaceOp op cur rhs) sr
  | .If _ test body orelse => ifStmt test body.val orelse.val
  | .While _ test body orelse => whileStmt test body.val orelse.val
  | .For sr target iter body orelse _ => forStmt sr target iter body.val orelse.val
  | .Break sr => exitWalk true none sr
  | .Continue sr => exitWalk false none sr
  | .Return sr ⟨_, v⟩ =>
    -- The scope pass reports a `return` outside a function.
    if (← curScope).kind matches .module | .classBody then return
    let x ← match v with
      | some e => transExpr e
      | none => build noneLit
    exitWalk false (some x) sr
  | .Import _ ⟨_, aliases⟩ => aliases.forM importAlias
  | .ImportFrom sr ⟨_, m⟩ ⟨_, aliases⟩ ⟨_, level⟩ =>
    if m.isNone || (level.map (·.value)).getD 0 != 0 then reject "relative import" sr
    else if aliases.any (·.name == "*") then reject "import *" sr
    -- Its string annotations would need the annotation's source text (§9, Q11).
    else if (m.map (·.val)) == some "__future__" && aliases.any (·.name == "annotations") then
      reject "from __future__ import annotations" sr
    else aliases.forM importAlias
  | .FunctionDef sr ⟨_, n⟩ args body decs ⟨_, ret⟩ _ tps =>
    defStmt sr n args body.val decs.val ret (!tps.val.isEmpty) false
  | .Assert _ test ⟨_, msg⟩ => assertStmt test msg
  | .Raise _ ⟨_, some e⟩ ⟨_, cause⟩ => raiseStmt e cause
  | .Raise _ ⟨_, none⟩ _ =>
    let e ← match (← read).handled with
      | some exc => pure exc
      | none => build (emitFailing (.str .base "exc") Py.handledExc.ref #[])
    build (PyBuild.jump (← build (raiseTo e)))
  | .With sr ⟨_, items⟩ ⟨_, body⟩ _ =>
    have hlist := sizeOf_toList_lt items
    withStmt sr items.toList body
  | .Try sr ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, final⟩ =>
    if final.isEmpty then tryStmt body handlers orelse
    else tryFinallyStmt sr body handlers orelse final
  | .Delete _ ⟨_, targets⟩ =>
    match targets.mapM deleter with
    | .error t => badTarget t
    | .ok dels => dels.forM id
  | .AsyncFunctionDef sr ⟨_, n⟩ args body decs ⟨_, ret⟩ _ tps =>
    defStmt sr n args body.val decs.val ret (!tps.val.isEmpty) true
  | .ClassDef sr ⟨_, n⟩ bases kws body decs tps =>
    classDef sr n bases.val kws.val body.val decs.val (!tps.val.isEmpty)
  | other => reject (stmtName other) other.ann
termination_by sizeOf s

/-- `if test: body else: orelse` (§6.2).  `elif` is an `if` in `orelse`. -/
def ifStmt (test : expr SourceRange) (body orelse : Array (stmt SourceRange)) :
    TransM Unit := do
  let thenL ← build (freshLabel [] "then")
  let elseL ← build (freshLabel [] "else")
  let join ← build (freshLabel [] "join")
  transCond test thenL.goto elseL.goto
  build (startBlock thenL)
  transStmts body
  if ← isOpen then jump join.goto
  build (startBlock elseL)
  transStmts orelse
  if ← isOpen then jump join.goto
  if ← targeted join then build (startBlock join)
termination_by sizeOf test + sizeOf body + sizeOf orelse + 1

/-- `while test: body else: orelse` (§6.4). -/
def whileStmt (test : expr SourceRange) (body orelse : Array (stmt SourceRange)) :
    TransM Unit := do
  let head ← build (freshLabel [] "head")
  let bodyL ← build (freshLabel [] "body")
  let elseL? ← if orelse.isEmpty then pure none else some <$> build (freshLabel [] "else")
  let exit ← build (freshLabel [] "exit")
  jump head.goto
  build (startBlock head)
  transCond test bodyL.goto (elseL?.getD exit).goto
  build (startBlock bodyL)
  withExit (.loop exit head) (transStmts body)
  if ← isOpen then jump head.goto
  if let some l := elseL? then
    build (startBlock l)
    transStmts orelse
    if ← isOpen then jump exit.goto
  if ← targeted exit then build (startBlock exit)
termination_by sizeOf test + sizeOf body + sizeOf orelse + 1

/-- `assert test, msg` (§6.1): `test` as a condition.  Only the failing side evaluates
`msg`, then raises the `AssertionError` class called on it, or the class itself without a
`msg`, through `toException`, as CPython's `RAISE_VARARGS` does. -/
def assertStmt (test : expr SourceRange) (msg : Option (expr SourceRange)) :
    TransM Unit := do
  let ok ← build (freshLabel [] "ok")
  let fail ← build (freshLabel [] "fail")
  transCond test ok.goto fail.goto
  build (startBlock fail)
  let cls ← build (emitTotal (.str .base "AssertionError") Py.assertionError.ref #[])
  let v ← match msg with
    | none => pure cls
    | some m => do
      let args ← build (emitTotal (.str .base "args") Py.mkTuple.ref #[← transExpr m])
      let kwargs ← build (emitTotal (.str .base "kwargs") Py.mkKwargs.ref #[])
      build (emitFailing (.str .base "call") Py.call.ref #[cls, args, kwargs])
  let e ← build (emitFailing (.str .base "exc") Py.toException.ref #[v])
  build (PyBuild.jump (← build (raiseTo e)))
  build (startBlock ok)

/-- `raise e from cause` (§7.1): evaluate `e`, then `cause`, make `e` an exception with
`toException`, set its cause, and jump to the enclosing handler. -/
def raiseStmt (e : expr SourceRange) (cause : Option (expr SourceRange)) :
    TransM Unit := do
  let v ← transExpr e
  let c ← cause.mapM transExpr
  let x ← build (emitFailing (.str .base "exc") Py.toException.ref #[v])
  if let some c := c then
    discard <| build (emitActing (.str .base "cause") Py.setCause.ref #[x, c])
  build (PyBuild.jump (← build (raiseTo x)))

/-- `try: body except …: … else: orelse` (§7.2).  A failure in `body` goes to `catch`, which
makes the exception the one being handled and tests the clauses in turn.  A failure in a
clause, and an exception that no clause matches, go to `unwind`.  It makes the previous
exception the one being handled again, then raises to the handler around the `try`.  `orelse`
runs after `body`, under that handler. -/
def tryStmt (body : Array (stmt SourceRange)) (handlers : Array (excepthandler SourceRange))
    (orelse : Array (stmt SourceRange)) : TransM Unit := do
  let outer ← build handler
  let catchL ← build (freshLabel [Py.Value] "catch")
  let unwind ← build (freshLabel [Py.Value] "unwind")
  let join ← build (freshLabel [] "join")
  withHandler catchL (transStmts body)
  if ← isOpen then
    transStmts orelse
    if ← isOpen then jump join.goto
  let excV ← build (startBlockWith catchL (.str .base "exc"))
  let exc := excV.id
  let prev ← build (emitTotal (.str .base "prev") Py.pushExcInfo.ref #[exc])
  withHandler unwind do
    for hm : h in handlers do
      have hlt := Array.sizeOf_lt_of_mem hm
      match hh : h with
      | .ExceptHandler hsr ⟨_, type⟩ ⟨_, name⟩ ⟨_, hbody⟩ =>
        have hbodyLt : sizeOf hbody < sizeOf handlers := by subst hh; simp at hlt; omega
        let name := name.map (·.val, hsr)
        let some t := type
          | -- A bare `except:` is last; the scope pass reports one that is not.
            clause exc prev outer join unwind name hbody
            break
        let m ← build (excMatch exc (← transExpr t))
        let bodyL ← build (freshLabel [] "except")
        let next ← build (freshLabel [] "next")
        branch m bodyL.goto next.goto
        build (startBlock bodyL)
        clause exc prev outer join unwind name hbody
        build (startBlock next)
    if ← isOpen then jump (unwind.goto.bind excV)
  let x ← build (startBlockWith unwind (.str .base "exc"))
  popExcept prev
  build (PyBuild.jump (outer.bind x))
  if ← targeted join then build (startBlock join)
termination_by sizeOf body + sizeOf handlers + sizeOf orelse + 1

/-- `try: … finally: final` at `sr` (§7.2), with the `except` clauses and `else` of `tryStmt`
if there are any.  Every way out of the protected part reaches the `finally` body as a
completion, through the `cleanup` exit for `return`, `break` and `continue`.  After the body,
the dispatch does from outside the `try` what the completion would have done.  Inside the
body, a `return`, `break` or `continue` first restores the exception handled before it. -/
def tryFinallyStmt (sr : SourceRange) (body : Array (stmt SourceRange))
    (handlers : Array (excepthandler SourceRange)) (orelse final : Array (stmt SourceRange)) :
    TransM Unit := do
  let outer ← build handler
  let join ← build (freshLabel [] "join")
  let finished ← tryFinally
    (fun fin => withExit (.cleanup fin) do
      if handlers.isEmpty then transStmts body else tryStmt body handlers orelse)
    (fun prev => withReader ({ · with handled := none })
      (withExit (.handler prev none outer) (transStmts final)))
    (exitArms join outer sr)
  if finished then build (startBlock join)
termination_by sizeOf body + sizeOf handlers + sizeOf orelse + sizeOf final + 2

/-- `with item, …: body` at `sr` (§7.3), one item at a time, the first outermost. -/
def withStmt (sr : SourceRange) (items : List (withitem SourceRange))
    (body : Array (stmt SourceRange)) : TransM Unit :=
  match items with
  | [] => transStmts body
  | .mk_withitem _ ctx ⟨_, target⟩ :: rest => do
    let assign? ← match target.mapM (assigner sr) with
      | .error t => return ← badTarget t
      | .ok a => pure a
    let outer ← build handler
    let mgr ← transExpr ctx
    let enter ← build (emitFailing (.str .base "enter") Py.enterMethod.ref #[mgr])
    let exit ← build (emitFailing (.str .base "exit") Py.exitMethod.ref #[mgr])
    let noArgs ← build (emitTotal (.str .base "args") Py.mkTuple.ref #[])
    let kw ← build (emitTotal (.str .base "kwargs") Py.mkKwargs.ref #[])
    let v ← build (emitFailing (.str .base "entered") Py.call.ref #[enter, noArgs, kw])
    let wexc ← build (freshLabel [Py.Value] "wexc")
    let fin ← build (freshLabel [Py.Completion] "fin")
    let join ← build (freshLabel [] "join")
    -- The body, and the assignment to the target, which `__exit__` covers too.
    withExit (.cleanup fin) <| withHandler wexc do
      if let some assign := assign? then assign v
      withStmt sr rest body
    if ← isOpen then jump (fin.goto.bind (← build compNormal))
    -- An exception: `__exit__(type, exc, tb)` while it is the one being handled.
    let exc ← build (startBlockWith wexc (.str .base "exc"))
    let prev ← build (emitTotal (.str .base "prev") Py.pushExcInfo.ref #[exc.id])
    let unwind ← build (freshLabel [Py.Value] "unwind")
    let suppress ← build (freshLabel [] "suppress")
    withHandler unwind do
      let r ← build (emitFailing (.str .base "exited") Py.exitWithExc.ref #[exit, exc.id])
      let b ← build (truthy r)
      branch b suppress.goto (unwind.goto.bind exc)
    build (startBlock suppress)
    popExcept prev
    jump join.goto
    let x ← build (startBlockWith unwind (.str .base "exc"))
    popExcept prev
    build (PyBuild.jump (outer.bind x))
    -- Every other way out, if there is one: `__exit__(None, None, None)`, then the dispatch.
    if ← targeted fin then
      let pending ← build (startBlockWith fin (.str .base "pending"))
      let n ← build noneLit
      let t ← build (emitTotal (.str .base "args") Py.mkTuple.ref #[n, n, n])
      let kw ← build (emitTotal (.str .base "kwargs") Py.mkKwargs.ref #[])
      discard <| build (emitFailing (.str .base "exited") Py.call.ref #[exit, t, kw])
      dispatchArms pending (← exitArms join outer sr)
    build (startBlock join)
termination_by sizeOf items + sizeOf body + 1

/-- The body of an `except` clause handling `exc`, which binds it to `name` if there is one,
then leaves the handler (`leaveHandler`) and jumps to `join`.  `prev` is the exception handled
before, `outer` the handler around the `try`, and `unwind` the block that restores `prev` and
raises again.  With a `name`, a failure first unbinds it, in `clear`. -/
def clause (exc prev : ValId) (outer : PyTarget [Py.Value]) (join : BlockRef Py.env [])
    (unwind : BlockRef Py.env [Py.Value])
    (name : Option (String × SourceRange)) (body : Array (stmt SourceRange)) : TransM Unit :=
  withReader ({ · with handled := some exc }) do
    let clear? ← name.mapM fun (n, r) => do
      writeName n exc r
      build (freshLabel [Py.Value] "clear")
    withExit (.handler prev name outer) (withHandler (clear?.getD unwind) (transStmts body))
    if ← isOpen then
      leaveHandler prev name outer
      jump join.goto
    if let (some clear, some (n, r)) := (clear?, name) then
      let x ← build (startBlockWith clear (.str .base "exc"))
      unbindName n r
      jump (unwind.goto.bind x)
termination_by sizeOf body + 1

/-- `for target in iter: body else: orelse` at `sr` (§6.4).  Only `next` raises to `stop`,
which ends the loop on `StopIteration` and passes any other exception to the enclosing
handler. -/
def forStmt (sr : SourceRange) (target iter : expr SourceRange)
    (body orelse : Array (stmt SourceRange)) : TransM Unit := do
  match assigner sr target with
  | .error t => badTarget t
  | .ok assign =>
    let it ← build (emitFailing (.str .base "iter") Py.getIter.ref #[← transExpr iter])
    let head ← build (freshLabel [] "head")
    let stop ← build (freshLabel [Py.Value] "stop")
    let elseL? ← if orelse.isEmpty then pure none else some <$> build (freshLabel [] "else")
    let exit ← build (freshLabel [] "exit")
    jump head.goto
    build (startBlock head)
    assign (← build (withHandler stop (emitFailing (.str .base "item") Py.next.ref #[it])))
    withExit (.loop exit head) (transStmts body)
    if ← isOpen then jump head.goto
    let e ← build (startBlockWith stop (.str .base "exc"))
    let done ← build (emitTest (.str .base "done") Py.isStopIteration.ref #[e.id])
    let finished := (elseL?.getD exit).goto
    recordTarget finished
    build (PyBuild.branch done finished ((← build handler).bind e))
    if let some l := elseL? then
      build (startBlock l)
      transStmts orelse
      if ← isOpen then jump exit.goto
    if ← targeted exit then build (startBlock exit)
termination_by sizeOf target + sizeOf iter + sizeOf body + sizeOf orelse + 1

end

/-! ## Modules -/

/-- The module's docstring: the value of a first statement that is a string constant. -/
def docstring? (stmts : Array (stmt SourceRange)) : Option String :=
  match stmts[0]? with
  | some (stmt.Expr _ (expr.Constant _ (constant.ConString _ ⟨_, s⟩) _)) => some s
  | _ => none

/-- Run `act` as the body of a function, then return `None` if it falls off the end. -/
def runBody (ctx : Ctx) (st : TState) (range : SourceRange) (act : TransM Unit) :
    PyM Info TState := do
  let body : TransM Unit := withRange range do
    act
    if ← isOpen then build emitReturnNone
  let ((), st') ← (body.run ctx).run { st with exits := #[], targeted := {} }
  return st'

/-- Build the function `name`, taking `params`, with `body`: the checked function and the
translator's state.  If the build fails, the function is its stub, and the state gains an
internal-error diagnostic at `range` for each misuse, or else one saying that the function is
not well formed.  That one names each unreachable block and each use out of scope
(`Func.scopeDiagnostics`). -/
def builtFunc (name : Name) (params : Array (Name × TypeExpr Py.env)) (range : SourceRange)
    (body : Array ValId → PyM Info TState) :
    {fn : Func Py.env Info // fn.WF} × TState :=
  match buildFuncTypedWith name params { range } (fun ps => body ps.toArray) with
  | .ok r => r
  | .error e =>
    let messages :=
      if !e.misuses.isEmpty then e.misuses.map (s!"{nameText name}: {·}")
      else if e.func.Reachable ∧ e.func.Scopable then #[s!"{nameText name} is not well formed"]
      else #[s!"{nameText name} is not well formed: \
        {"; ".intercalate e.func.scopeDiagnostics.toList}"]
    let ds := messages.map fun message => ({ kind := .internal, message, range } : Diagnostic)
    (stubFunc name params { range }, { e.value with diagnostics := e.value.diagnostics ++ ds })

/-- Emit the function `job` queues.  Its parameters are the cells it captures, in
`capturedVars` order, then its default cells, then `args` and `kwargs`.  A class body reads
its namespace from `args[0]`, stores `__module__`, `__qualname__` and its docstring, as
CPython 3.12 does, then runs. -/
def transFunc (ctx : Ctx) (st : TState) (job : FuncJob) :
    {fn : Func Py.env Info // fn.WF} × TState :=
  let ctx := { ctx with scope := job.scope, cur := job.cur }
  let free := capturedVars job.cur
  let defaults := funcDefaults job.args
  let (fn, st) := builtFunc job.name (funcParams job.cur job.args) job.range fun ps =>
    runBody ctx st job.range do
      match job.stub with
      | some what =>
        build (emitReturn (← standIn what))
      | none =>
        let sc ← curScope
        for (x, c) in free.zip ps do build (captureCell x c)
        let defaultCells := defaults.zip (ps.extract free.size (free.size + defaults.size))
        let #[args, kwargs] := ps.extract (free.size + defaults.size)
          | internalError "a function without its args and kwargs parameters" job.range
        match job.args with
        | none =>
          let ns ← build (emitFailing (.str .base "ns") Py.getItem.ref #[args, ← build (intLit 0)])
          let annotated := findAnn job.body
          withReader ({ · with classNs := some ns, classAnnotations := annotated }) do
            writeName "__module__" (← readName "__name__" job.range) job.range
            writeName "__qualname__" (← build (strLit sc.qualname)) job.range
            if annotated then setupAnnotations
            match (job.body[0]? : Option (stmt SourceRange)) with
            | some (.Expr r (.Constant _ (.ConString _ ⟨_, doc⟩) _)) =>
              withRange r do writeName "__doc__" (← build (strLit doc)) r
              transStmts (job.body.extract 1)
            | _ => transStmts job.body
        | some a =>
          for sym in sc.symbols do
            if sym.scope == .«local» || sym.scope == .cell then
              discard <| build (declareLocal sym.name)
          prologue (params a) defaultCells args kwargs
          transStmts job.body
  let attrs := match job.classParts with
    | some c =>
      Shape.classAttrs ctx.table c.outerPrivate job.scope c.bases c.keywords c.decorators job.body
        st.inits
    | none => #[]
  (Func.setInfo fn { fn.val.info with attrs }, { st with inits := #[] })

/-- A set of scope ids below `n` has at most `n` elements. -/
private theorem size_le_of_lt {done : Std.HashSet ScopeId} {n : Nat}
    (h : ∀ x ∈ done, x < n) : done.size ≤ n := by
  have hsub : done.toList ⊆ List.range n := fun x hx =>
    List.mem_range.mpr (h x (Std.HashSet.mem_toList.mp hx))
  have hnd : done.toList.Nodup := Std.HashSet.distinct_toList.imp fun hab => by simpa using hab
  have hlen := List.subset_nodup_length hnd hsub
  simpa [Std.HashSet.length_toList] using hlen

/-- Emit the functions queued in `st` from position `i` on, after `funcs`, in queue order;
an emitted function may queue more.  `done` holds the scopes already emitted, all in the
scope table (`hdone`).  A job whose scope was emitted already, or is not in the table, is an
internal error, and is skipped: each scope is queued once.  Return the functions and the
state after the last. -/
def emitQueued (ctx : Ctx) (done : Std.HashSet ScopeId)
    (hdone : ∀ x ∈ done, x < ctx.table.scopes.size) (st : TState) (i : Nat)
    (funcs : Array {fn : Func Py.env Info // fn.WF}) :
    Array {fn : Func Py.env Info // fn.WF} × TState :=
  if h : i < st.pending.size then
    let job := st.pending[i]
    if hj : job.scope < ctx.table.scopes.size ∧ job.scope ∉ done then
      let (f, st') := transFunc ctx st job
      have hdone' : ∀ x ∈ done.insert job.scope, x < ctx.table.scopes.size := by
        intro x hx
        rcases Std.HashSet.mem_insert.mp hx with heq | hx
        · simp at heq; exact heq ▸ hj.1
        · exact hdone x hx
      emitQueued ctx (done.insert job.scope) hdone' st' (i + 1) (funcs.push f)
    else
      let what := if job.scope < ctx.table.scopes.size then "is queued twice"
        else "has no scope in the table"
      let d : Diagnostic :=
        { kind := .internal, range := job.range, message := s!"{nameText job.name} {what}" }
      emitQueued ctx done hdone { st with diagnostics := st.diagnostics.push d } (i + 1) funcs
  else (funcs, st)
termination_by (ctx.table.scopes.size - done.size, st.pending.size - i)
decreasing_by
  · have hle := size_le_of_lt hdone'
    have hins : (done.insert job.scope).size = done.size + 1 := by
      rw [Std.HashSet.size_insert]; simp [hj.2]
    apply Prod.Lex.left; rw [hins]; omega
  · apply Prod.Lex.right; omega

/-- The module `name` with no functions and no ghosts. -/
def emptyModule (name : Name) (info : Info) : Module Py.env Info :=
  ⟨{ name, funcs := #[], info },
    ⟨by simp [Module.Raw.funcNames, Array.mapK_eq_map_fun], by simp, by simp,
      by simp [Module.Raw.ghostNames, Module.Raw.funcNames, Array.mapK_eq_map_fun], by simp,
      by simp [Module.Raw.GhostRefsIn], by simp [Module.Raw.GhostOrderIn]⟩⟩

/-- The module `name` of the checked functions `funcs`, and an internal-error diagnostic at
`range` for each function named twice, of which the first is kept.  The translator only
references functions it emits, so the module's check does not fail; if it did, the module
would be empty, with a diagnostic. -/
def assemble (name : Name) (funcs : Array {fn : Func Py.env Info // fn.WF})
    (range : SourceRange) : Module Py.env Info × Array Diagnostic := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut distinct := #[]
  let mut ds := #[]
  for f in funcs do
    if seen.contains f.val.name then
      ds := ds.push { kind := .internal, message := s!"{nameText f.val.name} is emitted twice",
                      range }
    else
      seen := seen.insert f.val.name
      distinct := distinct.push f
  match Module.ofChecked name distinct { range } with
  | .ok m => return (m, ds)
  | .error bad =>
    let message := s!"{nameText name} references a function it does not define: \
      {", ".intercalate (bad.map nameText).toList}"
    return (emptyModule name { range }, ds.push { kind := .internal, message, range })

/-- The Dyn name of the Python module `m`: one segment per dotted component. -/
def moduleNameOf (m : String) : Name :=
  (m.splitOn ".").foldl (init := .base) fun n s => n.str s

public section

/-- Translate the Python module `moduleName`, whose statements are `stmts`. -/
def translate (moduleName : String) (stmts : Array (stmt SourceRange)) : Result := Id.run do
  let table := PyScope.analyze stmts
  let mname := moduleNameOf moduleName
  let range : SourceRange := match stmts[0]?, stmts.back? with
    | some a, some b => ⟨a.ann.start, b.ann.stop⟩
    | _, _ => .none
  let some cur := table.scopes[0]?
    | return { module := emptyModule mname { range }
               diagnostics := #[{ kind := .internal, message := "no module scope", range }] }
  let ctx : Ctx :=
    { table, module := moduleName, moduleName := mname, scope := 0, cur,
      moduleAnnotations := findAnn stmts }
  let bodyName := mname.str "<module>"
  let st : TState := { funcNames := ({} : Std.HashSet Name).insert bodyName }
  let (body, st) := builtFunc bodyName #[] range fun _ =>
    runBody ctx st range do
      writeName "__name__" (← build (strLit moduleName)) .none
      if findAnn stmts then setupAnnotations
      match docstring? stmts, stmts[0]? with
      | some s, some d =>
        -- As CPython's `STORE_NAME __doc__`, on the docstring's line, instead of the statement.
        withRange d.ann do writeName "__doc__" (← build (strLit s)) .none
        transStmts (stmts.extract 1)
      | _, _ =>
        writeName "__doc__" (← build noneLit) .none
        transStmts stmts
  let (funcs, st) := emitQueued ctx {} (by simp) st 0 #[body]
  let (module, ds) := assemble mname funcs range
  -- The scope pass's internal errors are bugs, reported like the translator's.
  let internal := table.diagnostics.filter (·.kind == .internal)
  let diagnostics := (table.syntaxErrors ++ internal ++ st.diagnostics ++ ds).insertionSort
    fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  return { module, diagnostics }

end -- public section

end StrataPython.Dyn.PyTranslate
