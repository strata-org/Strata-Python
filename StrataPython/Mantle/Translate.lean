/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Mantle.Build
public import StrataPython.Mantle.Scope
public import StrataMantle.WF
public import Lean.Data.Position
-- Emitting instructions over `Py.env` needs the signature representation at
-- code-generation time.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Python to Mantle

`translate` lowers a parsed Python module to a `Mantle.Module.Raw` over `Py.env`, as the
design doc, `docs/PythonToMantle.md`, describes.  It returns the module and its diagnostics.
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
  such as the target of "a, b += 1": an `internal error` at the node's range.

## Supported constructs

The design doc's §11 lists what is lowered; `StrataPythonTest/Mantle/mantle_tests.txt` marks
each test program as supported or not.

## Adding a construct

1. Replace its rejection in `transStmt` or `transExpr` with a case that lowers it.
2. Read and write names with `readName` and `writeName`.
3. Emit operations with the `PyBuild` emitters, through `build`.  Open blocks with
   `freshLabel` and `startBlock`, and end them with `jump` or `branch`.  Start a join block
   only if `targeted` holds for its label.
4. Run a body that `break`, `continue` or `return` leaves under `withExit`.
5. Add a program to `StrataPythonTest/Mantle/mantle_tests/`, list it in
   `StrataPythonTest/Mantle/mantle_tests.txt`, and write its golden `NAME.expected.mantle`
   beside it with `MANTLE_UPDATE=1`.  Mark the other tests it now translates `yes` in that
   list.  Give it a `NAME.symtable` and `NAME.expected.scope` too, as `AGENTS.md` describes.
   `lake exe pymantle mantle FILE.py` prints the diagnostics and the module for one file.

`whileStmt` is a short example, tested by `m_while.py` and `t04_while.py`.
-/

namespace StrataPython.Mantle.PyTranslate

open Strata.Mantle
open StrataPython.Mantle.PyBuild
open StrataPython.Mantle.PyScope (Table Scope ScopeId NameScope Diagnostic ParamKind mangle
  formatRange starredIndex?)
open StrataPython (stmt expr constant operator unaryop cmpop arguments arg keyword alias
  opt_expr excepthandler withitem match_case comprehension)
open StrataDDM (SourceRange)

public section

/-! ## Results -/

/-- A translated module and its diagnostics: the scope pass's syntax errors, then each
rejected construct, in source order. -/
structure Result where
  module : Module.Raw Py.env SourceRange
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
  | loop (brk cont : Label)
  /-- The body of an `except` clause or a `finally`, left through `leaveHandler`: `prev` is
  the exception handled before, `name` the name the clause binds and where, and `outer` the
  handler around the `try`. -/
  | handler (prev : ValId) (name : Option (String × SourceRange)) (outer : BlockValue)
  /-- A `try` with a `finally`, or a `with`: a `return`, `break` or `continue` jumps to `fin`
  with its completion, and the dispatch after the `finally` body or `__exit__` carries it
  on. -/
  | cleanup (fin : Label)

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

/-- What is fixed while one function is translated. -/
structure Ctx where
  table : Table
  /-- The Python module name, such as `a.b`. -/
  module : String
  /-- The module name as a Mantle name: the prefix of every function name. -/
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

/-- What translation accumulates.  The first three fields are module-wide; `exits` and
`targeted` belong to the function being emitted. -/
structure TState where
  diagnostics : Array Diagnostic := #[]
  pending : Array FuncJob := #[]
  funcNames : Std.HashSet Name := {}
  exits : Array Exit := #[]
  /-- The labels some emitted transfer names. -/
  targeted : Std.HashSet Label := {}

/-- Translating one Python function. -/
abbrev TransM := ReaderT Ctx (StateT TState (PyM SourceRange))

variable {β : Type}

/-- Run a `PyBuild` action. -/
def build (x : PyM SourceRange β) : TransM β := monadLift x

/-- Run `act` with `r` as the default annotation. -/
def withRange (r : SourceRange) (act : TransM β) : TransM β := do
  let ctx ← read
  let s ← get
  let (b, s') ← build (PyBuild.withInfo r ((act.run ctx).run s))
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
  build (emitTotal (.str .base "unsupported") Py.unsupported #v[] #[n])

/-- Reject the expression `what` at `range`; its value is `py.unsupported "what"`. -/
def unsupportedValue (what : String) (range : SourceRange) : TransM ValId := do
  reject what range
  standIn what

/-! ## Blocks -/

/-- Whether a block is open, so that instructions can be emitted. -/
def isOpen : TransM Bool := build PyBuild.isOpen

/-- Whether some transfer names `l`. -/
def targeted (l : Label) : TransM Bool := return (← get).targeted.contains l

def recordTarget (l : Label) : TransM Unit :=
  modify fun s => { s with targeted := s.targeted.insert l }

/-- End the open block with `jump l(args)`. -/
def jump (l : Label) (args : Array ValId := #[]) : TransM Unit := do
  recordTarget l
  build (PyBuild.jump (Build.goto l args))

/-- End the open block with `branch c t(targs) f(fargs)`. -/
def branch (c : ValId) (t f : Label) (targs fargs : Array ValId := #[]) : TransM Unit := do
  recordTarget t
  recordTarget f
  build (PyBuild.branch c (Build.goto t targs) (Build.goto f fargs))

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

/-- Classify `name`, which must be mangled, as the scope `start` encloses it, for a name
an inlined comprehension does not bind.  An enclosing comprehension that binds it holds it in
its cell; a function holds it in its local or captured cell.  The comprehension skips a
class's names, so in a class body it is the cell the body captures, if it is free there or
`free_class`, and a global otherwise. -/
def enclosingPlace (name : String) (start : Option ScopeId) : TransM Place := do
  let table := (← read).table
  let mut id? := start
  for _ in [:table.scopes.size] do
    let some id := id? | return .global
    let some sc := table.scopes[id]? | return .global
    match sc.kind, ((sc.symbol? name).map (·.scope) : Option NameScope) with
    | .module, _ => return .global
    | .inlinedComprehension, some .free => id? := sc.parent
    | _, some .«local» | _, some .cell =>
      if sc.kind == .classBody then
        if !((sc.symbol? name).any (·.uses.freeClass)) then return .global
        return match ← build (cellOf? name) with
          | some c => .free c
          | none => .unresolved
      return match ← build (cellOf? name) with
        | some c => .cell c
        | none => .unresolved
    | _, some .free =>
      return match ← build (cellOf? name) with
        | some c => .free c
        | none => .unresolved
    | _, _ => return .global
  return .global

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
  build (emitFailing (stem name) Py.requireDefined #v[] #[v, e, m])

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
  let miss ← build (emitTotal (stem name) Py.undef #v[] #[n])
  let v ← build (emitFailing (stem name) Py.getOptionalItem #v[] #[ns, key, miss])
  let join ← build (freshLabel "join")
  let absent ← build (freshLabel "absent")
  branch (← build (emitTest (.str .base "found") Py.isDefined #v[] #[v])) join absent #[v]
  build (startBlock absent)
  jump join #[← fallback]
  build (startBlockWith join (stem name))

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
    discard <| build (emitActing (.str .base "store") Py.setItem #v[] #[ns, key, v])
  | .unresolved => reject "unresolved local" range

/-- `del name` at `range`: raise as a read does, but without the builtins fallback, then
unassign the name.  In a class body, delete it from the namespace, any failure raising
`NameError`. -/
def deleteName (name : String) (range : SourceRange) : TransM Unit := do
  let name ← mangled name
  let undef := do
    build (emitTotal (stem name) Py.undef #v[] #[← build (emitConst (.str .base "n") (.str name))])
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
    let failed ← build (freshLabel "undefined")
    let done ← build (freshLabel "deleted")
    discard <| build (withHandler failed (emitActing (.str .base "del") Py.delItem #v[] #[ns, key]))
    jump done
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
      let miss ← build (emitTotal (stem "__annotations__") Py.undef #v[] #[n])
      build (emitFailing (stem "__annotations__") Py.getOptionalItem #v[] #[ns, key, miss])
    | none => do
      let cell ← build (globalCell (← read).module "__annotations__")
      build (readCell cell (stem "__annotations__"))
  let found ← build (freshLabel "annotated")
  let make ← build (freshLabel "annotations")
  branch (← build (emitTest (.str .base "found") Py.isDefined #v[] #[v])) found make
  build (startBlock make)
  let d ← build (emitFailing (.str .base "dict") Py.mkDict #v[] #[])
  match ns? with
  | some ns =>
    let key ← build (strLit "__annotations__")
    discard <| build (emitActing (.str .base "store") Py.setItem #v[] #[ns, key, d])
  | none => discard <| build (writeGlobal (← read).module "__annotations__" d)
  jump found
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
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc := by exact #v[]) : TransM ValId :=
  build (emitFailing (stem name) r typeArgs #[a, b])

/-- `a op b` for a binary operator. -/
def binOp (op : operator SourceRange) (a b : ValId) : TransM ValId :=
  match op with
  | .Add _ => binary "add" Py.add a b
  | .Sub _ => binary "sub" Py.sub a b
  | .Mult _ => binary "mult" Py.mult a b
  | .MatMult _ => binary "matMult" Py.matMult a b
  | .Div _ => binary "div" Py.div a b
  | .FloorDiv _ => binary "floorDiv" Py.floorDiv a b
  | .Mod _ => binary "mod" Py.mod a b
  | .Pow _ => binary "pow" Py.pow a b
  | .LShift _ => binary "lShift" Py.lShift a b
  | .RShift _ => binary "rShift" Py.rShift a b
  | .BitAnd _ => binary "bitAnd" Py.bitAnd a b
  | .BitOr _ => binary "bitOr" Py.bitOr a b
  | .BitXor _ => binary "bitXor" Py.bitXor a b

/-- `a op= b`, the in-place form of `binOp`. -/
def inPlaceOp (op : operator SourceRange) (a b : ValId) : TransM ValId :=
  match op with
  | .Add _ => binary "iAdd" Py.iAdd a b
  | .Sub _ => binary "iSub" Py.iSub a b
  | .Mult _ => binary "iMult" Py.iMult a b
  | .MatMult _ => binary "iMatMult" Py.iMatMult a b
  | .Div _ => binary "iDiv" Py.iDiv a b
  | .FloorDiv _ => binary "iFloorDiv" Py.iFloorDiv a b
  | .Mod _ => binary "iMod" Py.iMod a b
  | .Pow _ => binary "iPow" Py.iPow a b
  | .LShift _ => binary "iLShift" Py.iLShift a b
  | .RShift _ => binary "iRShift" Py.iRShift a b
  | .BitAnd _ => binary "iBitAnd" Py.iBitAnd a b
  | .BitOr _ => binary "iBitOr" Py.iBitOr a b
  | .BitXor _ => binary "iBitXor" Py.iBitXor a b

/-- `a op b` for a comparison operator. -/
def cmpOp (op : cmpop SourceRange) (a b : ValId) : TransM ValId :=
  match op with
  | .Eq _ => binary "eq" Py.eq a b
  | .NotEq _ => binary "notEq" Py.notEq a b
  | .Lt _ => binary "lt" Py.lt a b
  | .LtE _ => binary "ltE" Py.ltE a b
  | .Gt _ => binary "gt" Py.gt a b
  | .GtE _ => binary "gtE" Py.gtE a b
  | .Is _ => build (emitTotal (.str .base "is") Py.is_ #v[] #[a, b])
  | .IsNot _ => build (emitTotal (.str .base "isNot") Py.isNot #v[] #[a, b])
  | .In _ => binary "in" Py.in_ a b
  | .NotIn _ => binary "notIn" Py.notIn a b

/-! ## Literals -/

/-- The `Float` a Python float literal denotes. -/
def parseFloat? (s : String) : Option Float :=
  (Lean.Syntax.decodeScientificLitVal? s).map fun (m, e, x) => OfScientific.ofScientific m e x

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

mutual

/-- The range of the first `yield` or `yield from` an expression evaluates in its own scope. -/
partial def exprYield? : expr SourceRange → Option SourceRange
  | .Yield sr _ | .YieldFrom sr _ => some sr
  | .Lambda _ (.mk_arguments _ _ _ _ _ kwDefaults _ defaults) _ =>
    (defaults.val ++
      kwDefaults.val.filterMap (fun | .some_expr _ d => some d | _ => none)).findSome? exprYield?
  -- A comprehension's outermost iterable is evaluated in the enclosing scope.
  | .ListComp _ _ gens | .SetComp _ _ gens | .DictComp _ _ _ gens | .GeneratorExp _ _ gens =>
    gens.val[0]?.bind fun (.mk_comprehension _ _ iter _ _) => exprYield? iter
  | .Constant .. | .Name .. => none
  | .BoolOp _ _ vs | .Set _ vs | .List _ vs _ | .Tuple _ vs _ | .JoinedStr _ vs
  | .TemplateStr _ vs => vs.val.findSome? exprYield?
  | .NamedExpr _ a b | .BinOp _ a _ b | .Subscript _ a b _ => #[a, b].findSome? exprYield?
  | .UnaryOp _ _ x | .Await _ x | .Starred _ x _ | .Attribute _ x _ _ => exprYield? x
  | .IfExp _ a b c => #[a, b, c].findSome? exprYield?
  | .Dict _ ks vs =>
    (ks.val.filterMap (fun | .some_expr _ k => some k | _ => none) ++ vs.val).findSome?
      exprYield?
  | .Compare _ l _ rs => (#[l] ++ rs.val).findSome? exprYield?
  | .Call _ f as ks => (#[f] ++ as.val ++ ks.val.map (·.value)).findSome? exprYield?
  | .FormattedValue _ v _ s | .Interpolation _ v _ _ s =>
    (#[v] ++ s.val.toArray).findSome? exprYield?
  | .Slice _ a b c => (a.val.toArray ++ b.val.toArray ++ c.val.toArray).findSome? exprYield?

/-- The range of the first `yield` a statement evaluates in its own scope. -/
partial def stmtYield? : stmt SourceRange → Option SourceRange
  | .FunctionDef _ _ args _ decs ret _ _ | .AsyncFunctionDef _ _ args _ decs ret _ _ =>
    let .mk_arguments _ posOnly pos varPos kwOnly kwDefaults varKw defaults := args
    -- CPython 3.12's order: the positional annotations before the positional-only ones.
    let params := pos.val ++ posOnly.val ++ varPos.val.toArray ++ kwOnly.val ++ varKw.val.toArray
    let anns := params.filterMap fun (.mk_arg _ _ a _) => a.val
    (decs.val ++ defaults.val ++
      kwDefaults.val.filterMap (fun | .some_expr _ d => some d | _ => none) ++ anns ++
      ret.val.toArray).findSome? exprYield?
  | .ClassDef _ _ bases kws _ decs _ =>
    (decs.val ++ bases.val ++ kws.val.map (·.value)).findSome? exprYield?
  | .Return _ v => v.val.bind exprYield?
  | .Raise _ v c => (v.val.toArray ++ c.val.toArray).findSome? exprYield?
  | .Delete _ ts => ts.val.findSome? exprYield?
  | .Assign _ ts v _ => (ts.val.push v).findSome? exprYield?
  | .AugAssign _ t _ v => #[t, v].findSome? exprYield?
  | .AnnAssign _ t a v _ => (#[t, a] ++ v.val.toArray).findSome? exprYield?
  | .For _ t it b o _ | .AsyncFor _ t it b o _ =>
    (#[t, it].findSome? exprYield?).orElse fun _ => bodiesYield? #[b.val, o.val]
  | .While _ c b o | .If _ c b o =>
    (exprYield? c).orElse fun _ => bodiesYield? #[b.val, o.val]
  | .With _ items b _ | .AsyncWith _ items b _ =>
    (items.val.findSome? fun (.mk_withitem _ c v) =>
      (exprYield? c).orElse fun _ => v.val.bind exprYield?).orElse fun _ => bodiesYield? #[b.val]
  | .Match _ s cases =>
    (exprYield? s).orElse fun _ => cases.val.findSome? fun (.mk_match_case _ _ g b) =>
      (g.val.bind exprYield?).orElse fun _ => bodiesYield? #[b.val]
  | .Try _ b hs o f | .TryStar _ b hs o f =>
    (bodiesYield? #[b.val]).orElse fun _ =>
      (hs.val.findSome? fun (.ExceptHandler _ t _ hb) =>
        (t.val.bind exprYield?).orElse fun _ => bodiesYield? #[hb.val]).orElse fun _ =>
          bodiesYield? #[o.val, f.val]
  | .Assert _ t m => (#[t] ++ m.val.toArray).findSome? exprYield?
  | .Expr _ v => exprYield? v
  | .TypeAlias .. | .Import .. | .ImportFrom .. | .Global .. | .Nonlocal .. | .Pass _
  | .Break _ | .Continue _ => none

/-- The first `yield` among statement lists. -/
partial def bodiesYield? (bodies : Array (Array (stmt SourceRange))) : Option SourceRange :=
  bodies.findSome? fun b => b.findSome? stmtYield?

end

/-- Whether the statements hold an annotated assignment outside a nested function or class:
CPython's `find_ann`, which decides `SETUP_ANNOTATIONS`. -/
partial def findAnn (ss : Array (stmt SourceRange)) : Bool :=
  ss.any fun
    | .AnnAssign .. => true
    | .For _ _ _ b o _ | .AsyncFor _ _ _ b o _ | .While _ _ b o | .If _ _ b o =>
      findAnn b.val || findAnn o.val
    | .With _ _ b _ | .AsyncWith _ _ b _ => findAnn b.val
    | .Try _ b hs o f | .TryStar _ b hs o f =>
      findAnn b.val || hs.val.any (fun (.ExceptHandler _ _ _ hb) => findAnn hb.val) ||
        findAnn o.val || findAnn f.val
    | .Match _ _ cases => cases.val.any fun (.mk_match_case _ _ _ b) => findAnn b.val
    | _ => false

/-! ## Functions

A `def` is bound where it runs, and its function is emitted after the current one, from a
`FuncJob`. -/

/-- A parameter, with its default. -/
structure ParamWithDefault where
  name : String
  kind : ParamKind
  default : Option (expr SourceRange)

/-- The parameters of `args`, in signature order. -/
def params (args : arguments SourceRange) : Array ParamWithDefault := Id.run do
  let .mk_arguments _ posOnly pos varPos kwOnly kwDefaults varKw defaults := args
  let nPos := posOnly.val.size + pos.val.size
  let firstDefault := nPos - defaults.val.size
  let mut out : Array ParamWithDefault := #[]
  let positional := posOnly.val.map (·, ParamKind.posOnly) ++ pos.val.map (·, .positional)
  for h : i in [:positional.size] do
    let (.mk_arg _ ⟨_, name⟩ _ _, kind) := positional[i]
    let default := if i ≥ firstDefault then defaults.val[i - firstDefault]? else none
    out := out.push { name, kind, default }
  if let some (.mk_arg _ ⟨_, name⟩ _ _) := varPos.val then
    out := out.push { name, kind := .varPositional, default := none }
  for h : j in [:kwOnly.val.size] do
    let .mk_arg _ ⟨_, name⟩ _ _ := kwOnly.val[j]
    let default := match kwDefaults.val[j]? with
      | some (.some_expr _ d) => some d
      | _ => none
    out := out.push { name, kind := .kwOnly, default }
  if let some (.mk_arg _ ⟨_, name⟩ _ _) := varKw.val then
    out := out.push { name, kind := .varKeyword, default := none }
  return out

/-- Whether a default is a constant, which the prologue evaluates in place. -/
def isConstantDefault : expr SourceRange → Bool
  | .Constant _ (.ConComplex ..) _ => false
  | .Constant .. => true
  | .UnaryOp _ (.USub _) (.Constant _ (.ConPos ..) _) => true
  | .UnaryOp _ (.USub _) (.Constant _ (.ConFloat ..) _) => true
  | _ => false

/-- A fresh function name for the scope whose `__qualname__` is `qualname`: `m.f.g` for
`f.<locals>.g`, or `m.f.g.k` if that is taken. -/
def allocName (qualname : String) : TransM Name := do
  let parts := (qualname.splitOn ".").filter (· != "<locals>")
  let first := parts.foldl (init := (← read).moduleName) Name.str
  let taken := (← get).funcNames
  let mut n := first
  let mut k := 1
  while taken.contains n do
    n := .num first k
    k := k + 1
  modify fun s => { s with funcNames := s.funcNames.insert n }
  return n

/-- The parameters whose default is not a constant, in signature order: each is evaluated
at the definition into a default cell, which the closure captures (§5.3). -/
def defaultCellParams (args : arguments SourceRange) : Array ParamWithDefault :=
  (params args).filter (·.default.any (!isConstantDefault ·))

/-- The scope that the `def`, `class`, `lambda` or comprehension at `range` opens.  It is a
child of the current scope, or, inside an inlined comprehension, of the scope enclosing it,
as a `lambda` in a comprehension is. -/
def childScope? (range : SourceRange) : TransM (Option ScopeId) := do
  let table := (← read).table
  let mut id? := some (← read).scope
  for _ in [:table.scopes.size] do
    let some id := id? | return none
    if let some c := table.childAt? id range then return some c
    id? := match table.scopes[id]? with
      | some sc => if sc.kind == .inlinedComprehension then sc.parent else none
      | none => none
  return none

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

/-- The first positional parameter of the function the current code runs in, skipping
inlined comprehensions: the object a zero-argument `super()` binds. -/
def firstParam? : TransM (Option String) := do
  let table := (← read).table
  let mut sc := (← read).cur
  for _ in [:table.scopes.size] do
    if sc.kind != .inlinedComprehension then break
    let some p := sc.parent | return none
    let some ps := table.scopes[p]? | return none
    sc := ps
  if !(sc.kind matches .function | .lambda) then return none
  return (sc.params.find? fun p => p.kind matches .posOnly | .positional).map (·.name)

/-- Queue the function of scope `cur` at `sr` and return its closure, capturing the cells of
`capturedVars cur` from the frame, then `extra`.  A class body is named `m.C.<body>`. -/
def queueFunc (sr : SourceRange) (scope : ScopeId) (cur : Scope)
    (args : Option (arguments SourceRange)) (body : Array (stmt SourceRange))
    (stub : Option String) (extra : Array ValId) : TransM (Option ValId) := do
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
  let job : FuncJob := { name := fname, scope, cur, args, body, range := sr, stub }
  modify fun s => { s with pending := s.pending.push job }
  some <$> build (mkClosure (← build (emitFunc fname)) (cells ++ extra))

/-- `f` with the decorators `decs`, already evaluated, applied bottom to top. -/
def decorate (decs : Array ValId) (f : ValId) : TransM ValId := do
  let mut f := f
  for d in decs.reverse do
    let t ← build (emitTotal (.str .base "args") Py.mkTuple #v[] #[f])
    let kw ← build (emitTotal (.str .base "kwargs") Py.mkKwargs #v[] #[])
    f ← build (emitFailing (.str .base "decorated") Py.call #v[] #[d, t, kw])
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

mutual

/-- Lower an expression to the value it produces. -/
partial def transExpr (e : expr SourceRange) : TransM ValId := withRange e.ann do
  match e with
  | .Constant sr c _ => literal c sr
  | .Name sr ⟨_, n⟩ _ => readName n sr
  | .BinOp _ l op r => do
    let a ← transExpr l
    binOp op a (← transExpr r)
  | .UnaryOp _ op x => do
    let v ← transExpr x
    match op with
    | .Not _ => build (emitFailing (.str .base "not") Py.not_ #v[] #[v])
    | .USub _ => build (emitFailing (.str .base "neg") Py.uSub #v[] #[v])
    | .UAdd _ => build (emitFailing (.str .base "pos") Py.uAdd #v[] #[v])
    | .Invert _ => build (emitFailing (.str .base "invert") Py.invert #v[] #[v])
  | .Compare _ l ops rs => compare l ops.val rs.val
  | .Call _ f args kws => call f args.val kws.val
  | .BoolOp _ op vs => boolOp (op matches .And _) vs.val
  | .NamedExpr _ (.Name nsr ⟨_, n⟩ _) v => do
    let x ← transExpr v
    writeName n x nsr
    return x
  | .NamedExpr sr .. => unsupportedValue "assignment expression" sr
  | .Lambda sr args body => do
    match ← closure sr args #[.Return body.ann ⟨body.ann, some body⟩] #[] false false with
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
      | .Call _ f args kws => do
        match ← zeroArgSuper? f args.val kws.val with
        -- CPython's `LOAD_SUPER_ATTR`, but not for `__class__`, nor if the module names `super`.
        | some sr =>
          let named := ((← read).table.module.symbol? "super").isSome
          superCall sr (a != "__class__" && !named)
        | none => transExpr v
      | _ => transExpr v
    build (getAttr o (← mangled a))
  | .Subscript _ v k _ => do
    let o ← transExpr v
    match k with
    | .Slice _ lo hi st =>
      let bs ← bounds #[lo.val, hi.val, st.val]
      build (emitFailing (.str .base "slice") Py.getSlice #v[] (#[o] ++ bs))
    | k => build (emitFailing (.str .base "item") Py.getItem #v[] #[o, ← transExpr k])
  | .Starred sr .. => unsupportedValue "starred expression" sr
  | .Slice _ lo hi st => do
    build (emitTotal (.str .base "slice") Py.mkSlice #v[] (← bounds #[lo.val, hi.val, st.val]))

/-- `l op₀ r₀ op₁ r₁ …`.  A chain evaluates each operand once and stops at the first false
comparison; its value is the last comparison's. -/
partial def compare (l : expr SourceRange) (ops : Array (cmpop SourceRange))
    (rs : Array (expr SourceRange)) : TransM ValId := do
  let a ← transExpr l
  let links := ops.zip rs
  if h : links.size = 1 then
    let (op, r) := links[0]
    return ← cmpOp op a (← transExpr r)
  let join ← build (freshLabel "join")
  jump join #[← chainLinks a links join (#[·])]
  build (startBlockWith join (.str .base "cmp"))

/-- The links `op₀ r₀ op₁ r₁ …` of a comparison chain whose left operand `a` is evaluated,
in CPython's order: each operand is evaluated once.  Every link but the last is tested, and
a false one jumps to `exit` with `args` of its result.  Returns the last link's result. -/
partial def chainLinks (a : ValId) (links : Array (cmpop SourceRange × expr SourceRange))
    (exit : Label) (args : ValId → Array ValId) : TransM ValId := do
  let mut lhs := a
  let mut last := a
  for h : i in [:links.size] do
    let (op, r) := links[i]
    let b ← transExpr r
    last ← cmpOp op lhs b
    if i + 1 < links.size then
      let t ← build (truthy last)
      let next ← build (freshLabel "cmp")
      branch t next exit #[] (args last)
      build (startBlock next)
    lhs := b
  return last

/-- `f"a{x}b"`: `strConcat` of the parts, as CPython's `BUILD_STRING`.  Every part is a
`str`: a literal, or a formatted field.  A lone part is itself, as in CPython. -/
partial def fString (vs : Array (expr SourceRange)) : TransM ValId := do
  if h : vs.size = 1 then transExpr vs[0]
  else build (emitTotal (.str .base "fstr") Py.strConcat #v[] (← vs.mapM transExpr))

/-- An f-string field `{v!c:spec}`, as CPython's `FORMAT_VALUE`: `v`, then `spec` (`""` if
absent), then the conversion `!s`, `!r` or `!a`, then `fmtValue`. -/
partial def formatted (v : expr SourceRange) (conv : StrataPython.int SourceRange)
    (spec : Option (expr SourceRange)) : TransM ValId := do
  let x ← transExpr v
  let sp ← match spec with
    | some s => transExpr s
    | none => build (strLit "")
  let x ← match conv with
    | .IntNeg .. => pure x
    | .IntPos sr ⟨_, c⟩ =>
      match Char.ofNat c with
      | 's' => build (emitFailing (.str .base "str") Py.toStr #v[] #[x])
      | 'r' => build (emitFailing (.str .base "repr") Py.repr #v[] #[x])
      | 'a' => build (emitFailing (.str .base "ascii") Py.ascii #v[] #[x])
      | _ => unsupportedValue "f-string conversion" sr  -- the parser gives no other
  build (emitFailing (.str .base "fmt") Py.fmtValue #v[] #[x, sp])

/-- The bounds of a slice, in order, `None` for an absent one. -/
partial def bounds (bs : Array (Option (expr SourceRange))) : TransM (Array ValId) :=
  bs.mapM fun
    | some b => transExpr b
    | none => build noneLit

/-- `a and b …` (`isAnd`) or `a or b …`, as a value: each operand but the last is tested, and
the first that decides the result is the result. -/
partial def boolOp (isAnd : Bool) (vs : Array (expr SourceRange)) : TransM ValId := do
  let join ← build (freshLabel "join")
  for h : i in [:vs.size] do
    let v ← transExpr vs[i]
    if i + 1 < vs.size then
      let t ← build (truthy v)
      let next ← build (freshLabel (if isAnd then "and" else "or"))
      if isAnd then branch t next join #[] #[v] else branch t join next #[v]
      build (startBlock next)
    else
      jump join #[v]
  build (startBlockWith join (.str .base "bool"))

/-- `a if c else b`, as a value.  `c` is a condition. -/
partial def ifExp (c a b : expr SourceRange) : TransM ValId := do
  let thenL ← build (freshLabel "then")
  let elseL ← build (freshLabel "else")
  let join ← build (freshLabel "join")
  transCond c thenL elseL
  build (startBlock thenL)
  jump join #[← transExpr a]
  build (startBlock elseL)
  jump join #[← transExpr b]
  build (startBlockWith join (.str .base "ifexp"))

/-- Lower `e` as a condition: end the open block with a jump to `t` if `e` is true and to `f`
otherwise, as CPython's `compiler_jump_if` does.  `not`, `and`, `or`, `x if c else y` and a
chained comparison become branches, so each operand's truth is tested at most once. -/
partial def transCond (e : expr SourceRange) (t f : Label) : TransM Unit := withRange e.ann do
  match e with
  | .UnaryOp _ (.Not _) x => transCond x f t
  | .BoolOp _ op vs =>
    let isAnd := op matches .And _
    let vs := vs.val
    for h : i in [:vs.size] do
      if i + 1 < vs.size then
        let next ← build (freshLabel (if isAnd then "and" else "or"))
        if isAnd then transCond vs[i] next f else transCond vs[i] t next
        build (startBlock next)
      else
        transCond vs[i] t f
  | .IfExp _ c a b =>
    let thenL ← build (freshLabel "then")
    let elseL ← build (freshLabel "else")
    transCond c thenL elseL
    build (startBlock thenL)
    transCond a t f
    build (startBlock elseL)
    transCond b t f
  | .Compare _ l ops rs =>
    let last ← chainLinks (← transExpr l) (ops.val.zip rs.val) f fun _ => #[]
    branch (← build (truthy last)) t f
  | _ => branch (← build (truthy (← transExpr e))) t f

/-- `[a, *x, b]`: `BUILD_LIST` of the elements before the first `*x`, then `LIST_EXTEND` for
each `*x` and `LIST_APPEND` for each later element, as CPython does.  The values `pre`, already
evaluated, come first. -/
partial def listDisplay (vs : Array (expr SourceRange)) (pre : Array ValId := #[]) :
    TransM ValId := do
  let (first, rest) := splitStarred vs
  let l ← build (emitTotal (.str .base "list") Py.mkList #v[] (pre ++ (← first.mapM transExpr)))
  for v in rest do
    match v with
    | .Starred _ x _ =>
      discard <| build (emitActing (.str .base "extend") Py.listExtend #v[] #[l, ← transExpr x])
    | v =>
      let x ← transExpr v
      discard <| build (emitEffect (.str .base "append") Py.listAppend #v[] #[l, x])
  return l

/-- `(a, b)`: `BUILD_TUPLE`.  With a `*x`, a list display then `INTRINSIC_LIST_TO_TUPLE`, as
CPython does.  The values `pre`, already evaluated, come first. -/
partial def tupleDisplay (vs : Array (expr SourceRange)) (pre : Array ValId := #[]) :
    TransM ValId := do
  if (splitStarred vs).2.isEmpty then
    build (emitTotal (.str .base "tuple") Py.mkTuple #v[] (pre ++ (← vs.mapM transExpr)))
  else
    build (emitTotal (.str .base "tuple") Py.listToTuple #v[] #[← listDisplay vs pre])

/-- `{a, *x, b}`: as `listDisplay`, with `BUILD_SET`, `SET_UPDATE` and `SET_ADD`.  A set of
more than `stackUseGuideline` elements starts empty, as in CPython. -/
partial def setDisplay (vs : Array (expr SourceRange)) : TransM ValId := do
  let (first, rest) := if vs.size > stackUseGuideline then (#[], vs) else splitStarred vs
  let st ← build (emitFailing (.str .base "set") Py.mkSet #v[] (← first.mapM transExpr))
  for v in rest do
    match v with
    | .Starred _ x _ =>
      discard <| build (emitActing (.str .base "update") Py.setUpdate #v[] #[st, ← transExpr x])
    | v => discard <| build (emitActing (.str .base "add") Py.setAdd #v[] #[st, ← transExpr v])
  return st

/-- Build a dict from `entries` in order, as CPython's `compiler_dict` does.  Each run of
pairs is cut by `cut`, and `chunk` builds one chunk; a `**d` entry is `combine acc d`.  The
first chunk is the dict itself; a later one is built, then combined into it. -/
partial def dictFromEntries {γ : Type} (entries : Array γ) (star? : γ → Option (expr SourceRange))
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
      acc := some (← combine a (← transExpr d))
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

/-- `{k: v, **d}`, as CPython builds it: a run of pairs is cut into chunks of `dictChunk`,
each built by `pairs`, and each later chunk and each `**d` is `DICT_UPDATE`. -/
partial def dictDisplay (ks : Array (opt_expr SourceRange)) (vs : Array (expr SourceRange)) :
    TransM ValId :=
  dictFromEntries (ks.zip vs) unpacked (chunks dictChunk) pairs
    (fun a d => build (emitFailing (.str .base "update") Py.dictUpdate #v[] #[a, d]))
where
  /-- The `d` of a `**d` entry. -/
  unpacked : opt_expr SourceRange × expr SourceRange → Option (expr SourceRange)
    | (.some_expr .., _) => none
    | (_, d) => some d
  /-- `BUILD_MAP` of the pairs `k: v` of `c`, key before value.  More than
  `stackUseGuideline / 2` pairs start an empty dict and add each pair (`MAP_ADD`). -/
  pairs (c : Array (opt_expr SourceRange × expr SourceRange)) : TransM ValId := do
    let kvs := c.filterMap fun | (.some_expr _ k, v) => some (k, v) | _ => none
    if 2 * kvs.size > stackUseGuideline then
      let d ← build (emitFailing (.str .base "dict") Py.mkDict #v[] #[])
      for (k, v) in kvs do
        let kv ← transExpr k
        let vv ← transExpr v
        discard <| build (emitActing (.str .base "set") Py.dictSet #v[] #[d, kv, vv])
      return d
    let mut args := #[]
    for (k, v) in kvs do
      args := args.push (← transExpr k)
      args := args.push (← transExpr v)
    build (emitFailing (.str .base "dict") Py.mkDict #v[] args)

/-- `f(a, *x, k=v, **m)`: `py.call f args kwargs`, evaluating the callee, the positional
arguments, then the keyword arguments, as CPython does.  `args` is a tuple display; a lone
`*x` is evaluated in place and made a tuple by `argsTuple` after the keyword arguments.
`kwargs` is runs of `k=v` pairs, each a total `mkKwargs`, and `DICT_MERGE` (`dictMerge`)
for each `**m`. -/
partial def call (f : expr SourceRange) (args : Array (expr SourceRange))
    (kws : Array (keyword SourceRange)) : TransM ValId := do
  if let some sr ← zeroArgSuper? f args kws then return ← superCall sr false
  let fv ← transExpr f
  let lone ← match args with
    | #[.Starred _ x _] => some <$> transExpr x
    | _ => pure none
  let t? ← if lone.isSome then pure none else some <$> tupleDisplay args
  let d ← kwargsDict fv kws
  let t ← match t?, lone with
    | some t, _ => pure t
    | none, some x => build (emitFailing (.str .base "args") Py.argsTuple #v[] #[fv, x])
    | none, none => build (emitTotal (.str .base "args") Py.mkTuple #v[] #[])
  build (emitFailing (.str .base "call") Py.call #v[] #[fv, t, d])

/-- The evaluation of the target `t`, or `none` if `t` is not a name, an attribute or a
subscript: `o` for `o.a`, then `o` and `k` for `o[k]`.  The attribute name is mangled, as in
a read. -/
partial def target? : expr SourceRange → Option (TransM Lhs)
  | .Name sr ⟨_, n⟩ _ => some (pure (.name n sr))
  | .Attribute _ v ⟨_, a⟩ _ => some do return .attr (← transExpr v) (← mangled a)
  | .Subscript _ v k _ => some do
    let o ← transExpr v
    match k with
    | .Slice _ lo hi st => return .slice o (← bounds #[lo.val, hi.val, st.val])
    | k => return .item o (← transExpr k)
  | _ => none

/-- Read the target `l`, as `x op= e` does. -/
partial def readLhs : Lhs → TransM ValId
  | .name n r => readName n r
  | .attr o a => build (getAttr o a)
  | .item o k => build (emitFailing (.str .base "item") Py.getItem #v[] #[o, k])
  | .slice o bs => build (emitFailing (.str .base "slice") Py.getSlice #v[] (#[o] ++ bs))

/-- Write `v` to the target `l`.  A name is written at `range`, the statement's.  A slice is
written by `setItem` of a `mkSlice`, as CPython's `STORE_SLICE` does. -/
partial def writeLhs (l : Lhs) (v : ValId) (range : SourceRange) : TransM Unit :=
  match l with
  | .name n _ => writeName n v range
  | .attr o a => discard <| build (setAttr o a v)
  | .item o k => discard <| build (emitActing (.str .base "store") Py.setItem #v[] #[o, k, v])
  | .slice o bs => do
    let k ← build (emitTotal (.str .base "slice") Py.mkSlice #v[] bs)
    discard <| build (emitActing (.str .base "store") Py.setItem #v[] #[o, k, v])

/-- The assignment of a value to the target `t` at `range`, or the part of `t` the translator
does not lower.  A tuple or list target unpacks the value, with `unpackEx` if an element is
starred, then assigns each element in turn, evaluating its target only then. -/
partial def assigner (range : SourceRange) (t : expr SourceRange) :
    Except (expr SourceRange) (ValId → TransM Unit) :=
  match t with
  | .Tuple _ ts _ | .List _ ts _ => do
    let ts := ts.val
    let .ok star := starredIndex? ts | throw t
    let elems ← ts.mapM fun | .Starred _ e _ => assigner range e | e => assigner range e
    let unpack (v : ValId) : TransM ValId := do
      match star with
      | none =>
        let n ← build (emitConst (.str .base "n") (.int ts.size))
        build (emitFailing (.str .base "unpack") Py.unpackSeq #v[] #[v, n])
      | some i =>
        let before ← build (emitConst (.str .base "before") (.int i))
        let after ← build (emitConst (.str .base "after") (.int (ts.size - i - 1)))
        build (emitFailing (.str .base "unpack") Py.unpackEx #v[] #[v, before, after])
    return fun v => do
      let tup ← unpack v
      for h : i in [:elems.size] do
        let x ← build (emitTotal (.str .base "elem") Py.tupleGet #v[]
          #[tup, ← build (emitConst (.str .base "i") (.int i))])
        elems[i] x
  | t => match target? t with
    | some eval => return fun v => do writeLhs (← eval) v range
    | none => throw t

/-- A list, set or dict comprehension at `sr` (§6.8), inlined as PEP 709 does.  The
outermost iterable is evaluated in the enclosing scope, then the accumulator is made, then
the comprehension's scope takes over: each iteration variable is a fresh cell, shadowing the
enclosing scope's name until the end, and each `for` clause is a `py.forEach` whose body
region assigns the target, tests the `if`s, and runs the next clause or adds the element. -/
partial def compExpr (sr : SourceRange) (kind : CompKind) (elt : expr SourceRange)
    (value : Option (expr SourceRange)) (gens : Array (comprehension SourceRange)) :
    TransM ValId := do
  let what := match kind with
    | .list => "list comprehension" | .set => "set comprehension" | .dict => "dict comprehension"
  if gens.any fun (.mk_comprehension _ _ _ _ a) => a.value != 0 then
    return ← unsupportedValue s!"async {what}" sr
  let ctx ← read
  let some (.mk_comprehension _ _ iter0 _ _) := (gens[0]? : Option (comprehension SourceRange))
    | internalError s!"{what} without a generator" sr; standIn what
  let some scope ← childScope? sr | return ← unsupportedValue s!"{what} without a scope" sr
  let some cur := ctx.table.scopes[scope]?
    | internalError s!"scope {scope} is not in the table" sr; standIn what
  let it ← transExpr iter0
  let acc ← match kind with
    | .list => build (emitTotal (.str .base "acc") Py.mkList #v[] #[])
    | .set => build (emitFailing (.str .base "acc") Py.mkSet #v[] #[])
    | .dict => build (emitFailing (.str .base "acc") Py.mkDict #v[] #[])
  let saved := (← build (get : PyM SourceRange PyBuild.Frame)).locals
  withReader ({ · with scope, cur, classNs := none }) do
    for x in cur.regionLocals do discard <| build (declareLocal x)
    clause acc it 0
  build (modify fun f => { f with locals := saved })
  return acc
where
  /-- The `for` clause `i`, over the evaluated iterable `it`, and the clauses after it. -/
  clause (acc it : ValId) (i : Nat) : TransM Unit := do
    let some (.mk_comprehension _ target _ ifs _) := (gens[i]? : Option (comprehension SourceRange))
      | return
    let assign ← match assigner sr target with
      | .ok a => pure a
      | .error t => do badTarget t; pure fun _ => pure ()
    forEach it fun item => do
      assign item
      let skip ← build (freshLabel "skip")
      for c in ifs.val do
        let next ← build (freshLabel "if")
        transCond c next skip
        build (startBlock next)
      match (gens[i + 1]? : Option (comprehension SourceRange)) with
      | some (.mk_comprehension _ _ iter _ _) => clause acc (← transExpr iter) (i + 1)
      | none =>
        match kind, value with
        | .dict, some v =>
          let k ← transExpr elt
          let x ← transExpr v
          discard <| build (emitActing (.str .base "set") Py.dictSet #v[] #[acc, k, x])
        | .set, _ =>
          discard <| build (emitActing (.str .base "add") Py.setAdd #v[] #[acc, ← transExpr elt])
        | _, _ =>
          let x ← transExpr elt
          discard <| build (emitEffect (.str .base "append") Py.listAppend #v[] #[acc, x])
      if ← targeted skip then
        jump skip
        build (startBlock skip)

/-- The range of the name `super` in `f(args, kws)`, if it is a zero-argument `super()` of the
builtin `super`: not a local `super`, nor one a class body binds. -/
partial def zeroArgSuper? (f : expr SourceRange) (args : Array (expr SourceRange))
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
partial def superCall (sr : SourceRange) (attr : Bool) : TransM ValId := do
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
  let t ← build (emitTotal (.str .base "args") Py.mkTuple #v[] #[cls, self])
  let d ← build (emitTotal (.str .base "kwargs") Py.mkKwargs #v[] #[])
  build (emitFailing (.str .base "super") Py.call #v[] #[fv, t, d])

/-- The keyword dict of a call to `fv` with the keyword arguments `kws`: runs of `k=v` pairs,
each a total `mkKwargs`, and `DICT_MERGE` (`dictMerge`) for each `**m`. -/
partial def kwargsDict (fv : ValId) (kws : Array (keyword SourceRange)) : TransM ValId :=
  dictFromEntries kws (fun kw => if kw.nameAndValue.1.isSome then none else some kw.value)
    (fun run => if run.isEmpty then #[] else #[run])
    (fun run => do
      let mut kvs := #[]
      for kw in run do
        kvs := kvs.push (← build (strLit (kw.nameAndValue.1.getD "")))
        kvs := kvs.push (← transExpr kw.value)
      build (emitTotal (.str .base "kwargs") Py.mkKwargs #v[] kvs))
    (fun a m => build (emitFailing (.str .base "merge") Py.dictMerge #v[] #[fv, a, m]))

/-- The closure of the `def` or `lambda` at `sr`, whose function is queued, or `none` if it is
rejected, as §5.3 builds it: the decorators are evaluated, then the non-constant defaults
into default cells.  The closure captures the cells of the function's free variables
(§6.6), then the default cells.  The decorators are applied to it bottom to top.  An
`async def` or a generator is queued as a stub. -/
partial def closure (sr : SourceRange) (args : arguments SourceRange)
    (body : Array (stmt SourceRange)) (decorators : Array (expr SourceRange))
    (hasTypeParams isAsync : Bool) : TransM (Option ValId) := do
  let ctx ← read
  if hasTypeParams then reject "type parameters" sr; return none
  let some scope ← childScope? sr
    | do reject "function without a scope" sr; return none
  let some cur := ctx.table.scopes[scope]?
    | do internalError s!"scope {scope} is not in the table" sr; return none
  let stub ← if isAsync then do reject "async def" sr; pure (some "async def")
    else match bodiesYield? #[body] with
      | some r => do reject "generator function" r; pure (some "generator function")
      | none => pure none
  let decs ← decorators.mapM transExpr
  let mut defaults := #[]
  for p in defaultCellParams args do
    if let some d := p.default then
      defaults := defaults.push (← build (newCell (defaultStem p.name) (← transExpr d)))
  let some f ← queueFunc sr scope cur (some args) body stub defaults | return none
  some <$> decorate decs f

end

/-- Delete the target `l`. -/
def deleteLhs : Lhs → TransM Unit
  | .name n r => deleteName n r
  | .attr o a => discard <| build (delAttr o a)
  | .item o k => discard <| build (emitActing (.str .base "del") Py.delItem #v[] #[o, k])
  | .slice o bs => do
    let k ← build (emitTotal (.str .base "slice") Py.mkSlice #v[] bs)
    discard <| build (emitActing (.str .base "del") Py.delItem #v[] #[o, k])

/-- The deletion of the target `t`, or the part of `t` the translator does not lower.  A
tuple or list deletes its elements left to right. -/
partial def deleter (t : expr SourceRange) : Except (expr SourceRange) (TransM Unit) :=
  match t with
  | .Tuple _ ts _ | .List _ ts _ => do
    let dels ← ts.val.mapM deleter
    return dels.forM id
  | t => match target? t with
    | some eval => return do deleteLhs (← eval)
    | none => throw t

/-- Emit the argument-binding prologue (§5.4), writing each parameter's cell.  A constant
default is evaluated in place; another is read from its cell in `defaults`.  The checks run
in CPython's order: a duplicate value, an unexpected keyword, too many positional
arguments, a missing argument. -/
def prologue (ps : Array ParamWithDefault) (defaults : Array (String × ValId))
    (args kwargs : ValId) : TransM Unit := do
  let fn := (← read).cur.qualname
  -- As in CPython, a private name is mangled everywhere, its keyword included.
  let ps ← ps.mapM fun p => return { p with name := ← mangled p.name }
  let defaults ← defaults.mapM fun (n, c) => return (← mangled n, c)
  let pos := ps.filter fun p => p.kind == .posOnly || p.kind == .positional
  let varPos := ps.find? (·.kind == .varPositional)
  let kwOnly := ps.filter (·.kind == .kwOnly)
  let varKw := ps.find? (·.kind == .varKeyword)
  let fillSlot (p : ParamWithDefault) : TransM ValId := do
    match p.default, defaults.find? (·.1 == p.name) with
    | some _, some (_, c) => build (readCell c (defaultStem p.name))
    | some d, none => transExpr d
    | none, _ => build (emitTotal (stem p.name) Py.undef #v[]
        #[← build (emitConst (.str .base "n") (.str p.name))])
  let discardKey (key : ValId) : TransM Unit :=
    discard <| build (emitEffect (.str .base "discard") Py.dictDiscard #v[] #[kwargs, key])
  let typeError (val : ValId) (limit : Option Int) (msg : String) : TransM Unit := do
    let lim ← limit.mapM fun l => build (emitConst (.str .base "limit") (.int l))
    let e ← build (emitConst (.str .base "e") (.str "TypeError"))
    let m ← build (emitConst (.str .base "msg") (.str msg))
    match lim with
    | some l => discard <| build (emitActing (.str .base "check") Py.requireAtMost #v[]
        #[val, l, e, m])
    | none => discard <| build (emitActing (.str .base "check") Py.requireUndefined #v[]
        #[val, e, m])
  let nargs ← if !pos.isEmpty || varPos.isNone then
      some <$> build (emitTotal (.str .base "nargs") Py.tupleLen #v[] #[args])
    else pure none
  let mut bound : Array (ParamWithDefault × ValId) := #[]
  let mut dups : Array (ParamWithDefault × ValId × ValId) := #[]
  if let some n := nargs then
    if !pos.isEmpty then
      let fill ← build (emitTotal (.str .base "fill") Py.mkTuple #v[] (← pos.mapM fillSlot))
      let none₁ ← build noneLit
      let tail ← build (emitFailing (.str .base "tail") Py.getSlice #v[] #[fill, n, none₁, none₁])
      let pad ← build (emitFailing (.str .base "pad") Py.add #v[] #[args, tail])
      for h : i in [:pos.size] do
        let p := pos[i]
        let idx ← build (intLit i)
        let fromPos ← build (emitFailing (.str .base "pos") Py.getItem #v[] #[pad, idx])
        if p.kind == .posOnly then
          bound := bound.push (p, fromPos)
        else
          let key ← build (strLit p.name)
          let got ← build (emitTotal (stem p.name) Py.dictGet #v[] #[kwargs, key, fromPos])
          let inKw ← build (emitFailing (.str .base "inKw") Py.in_ #v[] #[key, kwargs])
          discardKey key
          bound := bound.push (p, got)
          dups := dups.push (p, idx, inKw)
  if let some p := varPos then
    let idx ← build (intLit pos.size)
    let none₁ ← build noneLit
    let rest ← build (emitFailing (stem p.name) Py.getSlice #v[] #[args, idx, none₁, none₁])
    writeName p.name rest .none
  for p in kwOnly do
    let key ← build (strLit p.name)
    let miss ← fillSlot p
    let got ← build (emitTotal (stem p.name) Py.dictGet #v[] #[kwargs, key, miss])
    discardKey key
    bound := bound.push (p, got)
  if let some n := nargs then
    for (p, idx, inKw) in dups do
      let filled ← build (emitFailing (.str .base "filled") Py.lt #v[] #[idx, n])
      let both ← build (emitFailing (.str .base "both") Py.mult #v[] #[inKw, filled])
      typeError both (some 0) s!"{fn}() got multiple values for argument '{p.name}'"
  if varKw.isNone then
    let kwName ← build (emitConst (.str .base "n") (.str "kwargs"))
    let miss ← build (emitTotal (.str .base "kw") Py.undef #v[] #[kwName])
    let left ← build (emitTotal (.str .base "kw") Py.dictFirstKey #v[] #[kwargs, miss])
    typeError left none s!"{fn}() got an unexpected keyword argument \{}"
  if varPos.isNone then
    if let some n := nargs then
      let required := (pos.filter (·.default.isNone)).size
      let plural := if pos.size == 1 then "argument" else "arguments"
      let takes := if required == pos.size then s!"{pos.size} positional {plural}"
        else s!"from {required} to {pos.size} positional {plural}"
      typeError n (some pos.size) s!"{fn}() takes {takes} but \{} \{was} given"
  for (p, got) in bound do
    if p.default.isSome then writeName p.name got .none
    else
      let kind := if p.kind == .kwOnly then "keyword-only" else "positional"
      let v ← requireDefined got p.name "TypeError"
        s!"{fn}() missing 1 required {kind} argument: '{p.name}'"
      writeName p.name v .none
  if let some p := varKw then writeName p.name kwargs .none

/-- `def name(args): body` at `sr`: bind `name` to the function's closure. -/
def defStmt (sr : SourceRange) (name : String) (args : arguments SourceRange)
    (body : Array (stmt SourceRange)) (decorators : Array (expr SourceRange))
    (hasTypeParams isAsync : Bool) : TransM Unit := do
  if let some f ← closure sr args body decorators hasTypeParams isAsync then
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
  let bc ← build (emitFailing (.str .base "__build_class__") Py.qualifiedRef #v[] #[m, n])
  let classCell ← if cur.needsClassCell then do
      let n ← build (emitConst (.str .base "n") (.str "__class__"))
      let undef ← build (emitTotal (stem "__class__") Py.undef #v[] #[n])
      some <$> build (newCell (cellStem "__class__") undef)
    else pure none
  -- The body captures the cell under `classCellKey`, for this closure only.
  let saved := (← build (get : PyM SourceRange PyBuild.Frame)).locals
  if let some c := classCell then build (captureCell classCellKey c)
  let f? ← queueFunc sr scope cur none body none #[]
  build (modify fun fr => { fr with locals := saved })
  let some f := f? | return
  let t ← tupleDisplay bases (pre := #[f, ← build (strLit name)])
  let d ← kwargsDict bc kws
  let cls ← build (emitFailing (stem name) Py.call #v[] #[bc, t, d])
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
    writeName name (← build (emitTotal (stem m) Py.undef #v[] #[n])) range

/-- Make `prev` the exception being handled again. -/
def popExcept (prev : ValId) : TransM Unit :=
  discard <| build (emitEffect (.str .base "pop") Py.popExcept #v[] #[prev])

/-- Leave an `except` clause or a `finally` body other than by a failure, as CPython does:
under `outer`, the handler around the `try`, make `prev` the exception being handled again,
then unbind `name` if the clause binds one. -/
def leaveHandler (prev : ValId) (name : Option (String × SourceRange)) (outer : BlockValue) :
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
    | .loop b c, none => return ← jump (if brk then b else c)
    | .loop .., some _ => pure ()
    | .handler prev name outer, _ => leaveHandler prev name outer
    | .cleanup fin, _ =>
      let c ← build <| match ret with
        | some v => compReturn v
        | none => if brk then compBreak else compContinue
      return ← jump fin #[c]
  if let some v := ret then build (emitReturn v)

/-- The arms of the dispatch after a `finally` body or a `with`'s `__exit__`, which do from
outside the statement at `sr` what the completion would have done: `join` is the code after
it, and `outer` the handler around it. -/
def exitArms (join : Label) (outer : BlockValue) (sr : SourceRange) : TransM (Arms TransM) := do
  let exits := (← get).exits
  -- `break` or `continue` jumps straight to the loop when it is the innermost entry.
  let loopArm (brk : Bool) : TransM (Arm TransM Unit) := do
    if !exits.any (· matches .loop ..) then return .unreachable
    match exits.back? with
    | some (.loop b c) =>
      let l := if brk then b else c
      recordTarget l
      return .to l
    | _ => return .block (if brk then "brk" else "cont") fun _ => exitWalk brk none sr
  return {
    normal := .to join
    «return» := if (← curScope).kind matches .module | .classBody then .unreachable
      else .block "ret" fun v => exitWalk false (some v) sr
    raise := if outer.args.isEmpty then .to outer.target
      else .block "reraise" fun e => build (PyBuild.jump { outer with args := outer.args.push e })
    «break» := ← loopArm true
    «continue» := ← loopArm false }

mutual

/-- Lower a statement list, skipping what follows a statement that ends every path. -/
partial def transStmts (ss : Array (stmt SourceRange)) : TransM Unit := do
  for s in ss do
    if !(← isOpen) then return
    transStmt s

/-- Lower a statement. -/
partial def transStmt (s : stmt SourceRange) : TransM Unit := withRange s.ann do
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
          discard <| build (emitActing (.str .base "store") Py.setItem #v[] #[d, key, t])
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
  | .FunctionDef sr ⟨_, n⟩ args body decs _ _ tps =>
    defStmt sr n args body.val decs.val (!tps.val.isEmpty) false
  | .Assert _ test ⟨_, msg⟩ => assertStmt test msg
  | .Raise _ ⟨_, some e⟩ ⟨_, cause⟩ => raiseStmt e cause
  | .Raise _ ⟨_, none⟩ _ =>
    let e ← match (← read).handled with
      | some exc => pure exc
      | none => build (emitFailing (.str .base "exc") Py.handledExc #v[] #[])
    build (PyBuild.jump (← build (raiseTo e)))
  | .With sr ⟨_, items⟩ ⟨_, body⟩ _ => withStmt sr items.toList body
  | .Try sr ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, final⟩ =>
    if final.isEmpty then tryStmt body handlers orelse
    else tryFinallyStmt sr body handlers orelse final
  | .Delete _ ⟨_, targets⟩ =>
    match targets.mapM deleter with
    | .error t => badTarget t
    | .ok dels => dels.forM id
  | .AsyncFunctionDef sr ⟨_, n⟩ args body decs _ _ tps =>
    defStmt sr n args body.val decs.val (!tps.val.isEmpty) true
  | .ClassDef sr ⟨_, n⟩ bases kws body decs tps =>
    classDef sr n bases.val kws.val body.val decs.val (!tps.val.isEmpty)
  | other => reject (stmtName other) other.ann

/-- `if test: body else: orelse` (§6.2).  `elif` is an `if` in `orelse`. -/
partial def ifStmt (test : expr SourceRange) (body orelse : Array (stmt SourceRange)) :
    TransM Unit := do
  let thenL ← build (freshLabel "then")
  let elseL ← build (freshLabel "else")
  let join ← build (freshLabel "join")
  transCond test thenL elseL
  build (startBlock thenL)
  transStmts body
  if ← isOpen then jump join
  build (startBlock elseL)
  transStmts orelse
  if ← isOpen then jump join
  if ← targeted join then build (startBlock join)

/-- `while test: body else: orelse` (§6.4). -/
partial def whileStmt (test : expr SourceRange) (body orelse : Array (stmt SourceRange)) :
    TransM Unit := do
  let head ← build (freshLabel "head")
  let bodyL ← build (freshLabel "body")
  let elseL? ← if orelse.isEmpty then pure none else some <$> build (freshLabel "else")
  let exit ← build (freshLabel "exit")
  jump head
  build (startBlock head)
  transCond test bodyL (elseL?.getD exit)
  build (startBlock bodyL)
  withExit (.loop exit head) (transStmts body)
  if ← isOpen then jump head
  if let some l := elseL? then
    build (startBlock l)
    transStmts orelse
    if ← isOpen then jump exit
  if ← targeted exit then build (startBlock exit)

/-- `assert test, msg` (§6.1): `test` as a condition.  Only the failing side evaluates
`msg`, then raises the `AssertionError` class called on it, or the class itself without a
`msg`, through `toException`, as CPython's `RAISE_VARARGS` does. -/
partial def assertStmt (test : expr SourceRange) (msg : Option (expr SourceRange)) :
    TransM Unit := do
  let ok ← build (freshLabel "ok")
  let fail ← build (freshLabel "fail")
  transCond test ok fail
  build (startBlock fail)
  let cls ← build (emitTotal (.str .base "AssertionError") Py.assertionError #v[] #[])
  let v ← match msg with
    | none => pure cls
    | some m => do
      let args ← build (emitTotal (.str .base "args") Py.mkTuple #v[] #[← transExpr m])
      let kwargs ← build (emitTotal (.str .base "kwargs") Py.mkKwargs #v[] #[])
      build (emitFailing (.str .base "call") Py.call #v[] #[cls, args, kwargs])
  let e ← build (emitFailing (.str .base "exc") Py.toException #v[] #[v])
  build (PyBuild.jump (← build (raiseTo e)))
  build (startBlock ok)

/-- `raise e from cause` (§7.1): evaluate `e`, then `cause`, make `e` an exception with
`toException`, set its cause, and jump to the enclosing handler. -/
partial def raiseStmt (e : expr SourceRange) (cause : Option (expr SourceRange)) :
    TransM Unit := do
  let v ← transExpr e
  let c ← cause.mapM transExpr
  let x ← build (emitFailing (.str .base "exc") Py.toException #v[] #[v])
  if let some c := c then
    discard <| build (emitActing (.str .base "cause") Py.setCause #v[] #[x, c])
  build (PyBuild.jump (← build (raiseTo x)))

/-- `try: body except …: … else: orelse` (§7.2).  A failure in `body` goes to `catch`, which
makes the exception the one being handled and tests the clauses in turn.  A failure in a
clause, and an exception that no clause matches, go to `unwind`.  It makes the previous
exception the one being handled again, then raises to the handler around the `try`.  `orelse`
runs after `body`, under that handler. -/
partial def tryStmt (body : Array (stmt SourceRange)) (handlers : Array (excepthandler SourceRange))
    (orelse : Array (stmt SourceRange)) : TransM Unit := do
  let outer ← build handler
  let catchL ← build (freshLabel "catch")
  let unwind ← build (freshLabel "unwind")
  let join ← build (freshLabel "join")
  withHandler catchL (transStmts body)
  if ← isOpen then
    transStmts orelse
    if ← isOpen then jump join
  let exc ← build (startBlockWith catchL (.str .base "exc"))
  let prev ← build (emitTotal (.str .base "prev") Py.pushExcInfo #v[] #[exc])
  withHandler unwind do
    for h in handlers do
      let .ExceptHandler hsr ⟨_, type⟩ ⟨_, name⟩ ⟨_, hbody⟩ := h
      let name := name.map (·.val, hsr)
      let some t := type
        | -- A bare `except:` is last; the scope pass reports one that is not.
          clause exc prev outer join unwind name hbody
          break
      let m ← build (excMatch exc (← transExpr t))
      let bodyL ← build (freshLabel "except")
      let next ← build (freshLabel "next")
      branch m bodyL next
      build (startBlock bodyL)
      clause exc prev outer join unwind name hbody
      build (startBlock next)
    if ← isOpen then jump unwind #[exc]
  let x ← build (startBlockWith unwind (.str .base "exc"))
  popExcept prev
  build (PyBuild.jump { outer with args := outer.args.push x })
  if ← targeted join then build (startBlock join)

/-- `try: … finally: final` at `sr` (§7.2), with the `except` clauses and `else` of `tryStmt`
if there are any.  Every way out of the protected part reaches the `finally` body as a
completion, through the `cleanup` exit for `return`, `break` and `continue`.  After the body,
the dispatch does from outside the `try` what the completion would have done.  Inside the
body, a `return`, `break` or `continue` first restores the exception handled before it. -/
partial def tryFinallyStmt (sr : SourceRange) (body : Array (stmt SourceRange))
    (handlers : Array (excepthandler SourceRange)) (orelse final : Array (stmt SourceRange)) :
    TransM Unit := do
  let outer ← build handler
  let join ← build (freshLabel "join")
  let finished ← tryFinally
    (fun fin => withExit (.cleanup fin) do
      if handlers.isEmpty then transStmts body else tryStmt body handlers orelse)
    (fun prev => withReader ({ · with handled := none })
      (withExit (.handler prev none outer) (transStmts final)))
    (exitArms join outer sr)
  if finished then build (startBlock join)

/-- `with item, …: body` at `sr` (§7.3), one item at a time, the first outermost. -/
partial def withStmt (sr : SourceRange) (items : List (withitem SourceRange))
    (body : Array (stmt SourceRange)) : TransM Unit :=
  match items with
  | [] => transStmts body
  | .mk_withitem _ ctx ⟨_, target⟩ :: rest => do
    let assign? ← match target.mapM (assigner sr) with
      | .error t => return ← badTarget t
      | .ok a => pure a
    let outer ← build handler
    let mgr ← transExpr ctx
    let enter ← build (emitFailing (.str .base "enter") Py.enterMethod #v[] #[mgr])
    let exit ← build (emitFailing (.str .base "exit") Py.exitMethod #v[] #[mgr])
    let noArgs ← build (emitTotal (.str .base "args") Py.mkTuple #v[] #[])
    let kw ← build (emitTotal (.str .base "kwargs") Py.mkKwargs #v[] #[])
    let v ← build (emitFailing (.str .base "entered") Py.call #v[] #[enter, noArgs, kw])
    let wexc ← build (freshLabel "wexc")
    let fin ← build (freshLabel "fin")
    let join ← build (freshLabel "join")
    -- The body, and the assignment to the target, which `__exit__` covers too.
    withExit (.cleanup fin) <| withHandler wexc do
      if let some assign := assign? then assign v
      withStmt sr rest body
    if ← isOpen then jump fin #[← build compNormal]
    -- An exception: `__exit__(type, exc, tb)` while it is the one being handled.
    let exc ← build (startBlockWith wexc (.str .base "exc"))
    let prev ← build (emitTotal (.str .base "prev") Py.pushExcInfo #v[] #[exc])
    let unwind ← build (freshLabel "unwind")
    let suppress ← build (freshLabel "suppress")
    withHandler unwind do
      let r ← build (emitFailing (.str .base "exited") Py.exitWithExc #v[] #[exit, exc])
      let b ← build (truthy r)
      branch b suppress unwind #[] #[exc]
    build (startBlock suppress)
    popExcept prev
    jump join
    let x ← build (startBlockWith unwind (.str .base "exc"))
    popExcept prev
    build (PyBuild.jump { outer with args := outer.args.push x })
    -- Every other way out, if there is one: `__exit__(None, None, None)`, then the dispatch.
    if ← targeted fin then
      let pending ← build (startBlockWith fin (.str .base "pending") Py.Completion.ty)
      let n ← build noneLit
      let t ← build (emitTotal (.str .base "args") Py.mkTuple #v[] #[n, n, n])
      let kw ← build (emitTotal (.str .base "kwargs") Py.mkKwargs #v[] #[])
      discard <| build (emitFailing (.str .base "exited") Py.call #v[] #[exit, t, kw])
      dispatchArms pending (← exitArms join outer sr)
    build (startBlock join)

/-- The body of an `except` clause handling `exc`, which binds it to `name` if there is one,
then leaves the handler (`leaveHandler`) and jumps to `join`.  `prev` is the exception handled
before, `outer` the handler around the `try`, and `unwind` the block that restores `prev` and
raises again.  With a `name`, a failure first unbinds it, in `clear`. -/
partial def clause (exc prev : ValId) (outer : BlockValue) (join unwind : Label)
    (name : Option (String × SourceRange)) (body : Array (stmt SourceRange)) : TransM Unit :=
  withReader ({ · with handled := some exc }) do
    let clear? ← name.mapM fun (n, r) => do
      writeName n exc r
      build (freshLabel "clear")
    withExit (.handler prev name outer) (withHandler (clear?.getD unwind) (transStmts body))
    if ← isOpen then
      leaveHandler prev name outer
      jump join
    if let (some clear, some (n, r)) := (clear?, name) then
      let x ← build (startBlockWith clear (.str .base "exc"))
      unbindName n r
      jump unwind #[x]

/-- `for target in iter: body else: orelse` at `sr` (§6.4).  Only `next` raises to `stop`,
which ends the loop on `StopIteration` and passes any other exception to the enclosing
handler. -/
partial def forStmt (sr : SourceRange) (target iter : expr SourceRange)
    (body orelse : Array (stmt SourceRange)) : TransM Unit := do
  match assigner sr target with
  | .error t => badTarget t
  | .ok assign =>
    let it ← build (emitFailing (.str .base "iter") Py.getIter #v[] #[← transExpr iter])
    let head ← build (freshLabel "head")
    let stop ← build (freshLabel "stop")
    let elseL? ← if orelse.isEmpty then pure none else some <$> build (freshLabel "else")
    let exit ← build (freshLabel "exit")
    jump head
    build (startBlock head)
    assign (← build (withHandler stop (emitFailing (.str .base "item") Py.next #v[] #[it])))
    withExit (.loop exit head) (transStmts body)
    if ← isOpen then jump head
    let e ← build (startBlockWith stop (.str .base "exc"))
    let done ← build (emitTest (.str .base "done") Py.isStopIteration #v[] #[e])
    let finished := elseL?.getD exit
    recordTarget finished
    build (PyBuild.branch done (Build.goto finished) (← build (raiseTo e)))
    if let some l := elseL? then
      build (startBlock l)
      transStmts orelse
      if ← isOpen then jump exit
    if ← targeted exit then build (startBlock exit)

end

/-! ## Modules -/

/-- The module's docstring: the value of a first statement that is a string constant. -/
def docstring? (stmts : Array (stmt SourceRange)) : Option String :=
  match stmts[0]? with
  | some (stmt.Expr _ (expr.Constant _ (constant.ConString _ ⟨_, s⟩) _)) => some s
  | _ => none

/-- Run `act` as the body of a function, then return `None` if it falls off the end. -/
def runBody (ctx : Ctx) (st : TState) (range : SourceRange) (act : TransM Unit) :
    PyM SourceRange TState := do
  let body : TransM Unit := withRange range do
    act
    if ← isOpen then build emitReturnNone
  let ((), st') ← (body.run ctx).run { st with exits := #[], targeted := {} }
  return st'

/-- `built`'s function and state, with an internal-error diagnostic at `range` for each
builder error. -/
def builtFunc (range : SourceRange) (built : Build.Built (Func Py.env SourceRange × TState)) :
    Func Py.env SourceRange × TState :=
  let (f, st) := built.value
  let ds := built.errors.map fun e =>
    ({ kind := .internal, message := s!"{nameText f.name}: {e}", range } : Diagnostic)
  (f, { st with diagnostics := st.diagnostics ++ ds })

/-- Emit the function `job` queues.  Its parameters are the cells it captures, in
`capturedVars` order, then its default cells, then `args` and `kwargs`.  A class body reads
its namespace from `args[0]`, stores `__module__`, `__qualname__` and its docstring, as
CPython 3.12 does, then runs. -/
def transFunc (ctx : Ctx) (st : TState) (job : FuncJob) : Func Py.env SourceRange × TState :=
  let ctx := { ctx with scope := job.scope, cur := job.cur }
  let free := capturedVars job.cur
  let defaults : Array String := match job.args with
    | some a => (defaultCellParams a).map (·.name)
    | none => #[]
  -- A class's own `__class__` cell is captured under `classCellKey`, named like any cell.
  let argTypes := free.map (fun x => (cellStem (if x == classCellKey then "__class__" else x),
      Py.cell.ty)) ++
    defaults.map (defaultStem ·, Py.cell.ty) ++
    #[(stem "args", Py.Value.ty), (stem "kwargs", Py.Value.ty)]
  builtFunc job.range <| buildFuncTypedWith job.name argTypes job.range fun ps =>
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
          let ns ← build (emitFailing (.str .base "ns") Py.getItem #v[] #[args, ← build (intLit 0)])
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

/-- The Mantle name of the Python module `m`: one segment per dotted component. -/
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
    | return { module := { name := mname, funcs := #[], info := range }
               diagnostics := #[{ kind := .internal, message := "no module scope", range }] }
  let ctx : Ctx :=
    { table, module := moduleName, moduleName := mname, scope := 0, cur,
      moduleAnnotations := findAnn stmts }
  let bodyName := mname.str "<module>"
  let st : TState := { funcNames := ({} : Std.HashSet Name).insert bodyName }
  let (body, st) := builtFunc range <| buildFuncTypedWith bodyName #[] range fun _ =>
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
  let mut funcs := #[body]
  let mut st := st
  let mut i := 0
  while h : i < st.pending.size do
    let (f, st') := transFunc ctx st st.pending[i]
    funcs := funcs.push f
    st := st'
    i := i + 1
  let diagnostics := (table.syntaxErrors ++ st.diagnostics).insertionSort
    fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  return { module := { name := mname, funcs, info := range }, diagnostics }

end -- public section

end StrataPython.Mantle.PyTranslate
