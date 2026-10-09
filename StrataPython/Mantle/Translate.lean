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

`translate` lowers a parsed Python module to a `Mantle.Module` over `Py.env`, as
`docs/PythonToMantle.md` specifies.  It returns the module and its diagnostics.  A result
with a diagnostic is a failure.

* The module body is the function `m.<module>`, with no parameters.  A module-level `def f`
  is the function `m.f`, with parameters `args` (a tuple) and `kwargs` (a dict).
* Names are classified by `PyScope.analyze`.  A function's locals are cells declared in its
  entry block.  A module global is the cell `py.globalCell m x`.  A global that is also a
  builtin falls back to `py.qualifiedRef "builtins" x` when its cell is undefined.
* Every instruction carries the source range of the Python node it lowers.
* A construct outside the supported subset is a diagnostic at its range.  A rejected
  expression is `py.unsupported`, a rejected statement emits nothing, and a rejected
  function (`async def`, a generator) is a stub that returns `py.unsupported`.
* An error the builder records is a bug in the translator: an `internal error` diagnostic at
  the range of the function it was emitting.

## Supported constructs

* `def` at module level: positional, positional-only, keyword-only, `*args` and `**kwargs`
  parameters, and constant defaults.  The argument-binding prologue is the spec's §5.4.
* Statements: expression statements, `pass`, assignment and annotated assignment to names,
  augmented assignment to a name,
  `if`/`elif`/`else`, `while`/`else`, `break`, `continue`, `return`, `global`,
  `import a.b [as c]` and `from a.b import x [as y]`.
* Expressions: `int`, `float`, `str`, `bytes`, `bool`, `None` and `...` literals, names,
  every binary and unary operator, comparisons (chained too), `and`, `or`,
  `x if c else y`, tuple, list, set and dict displays with `*x` and `**d`, calls with
  keyword, `*` and `**` arguments, attributes (mangled in a class), subscripts, slices,
  f-strings, and `x := e` outside a comprehension.
* Conditions: an `if` or `while` test, and the test of `x if c else y`, lower to branches by
  `transCond`, so each operand's truth is tested at most once.

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

`while c: B else: E` is `whileStmt`:

```
  let head ← build (freshLabel "head")       -- and `body`, `else`, `exit`
  jump head
  build (startBlock head)
  transCond c bodyL (elseL?.getD exit)
  build (startBlock bodyL)
  withExit (.loop exit head) (transStmts B)
  if ← isOpen then jump head
  …                                          -- `else` runs E, then jumps to `exit`
  if ← targeted exit then build (startBlock exit)
```

Its tests are `m_while.py` and `t04_while.py` in `mantle_tests/`.
-/

namespace StrataPython.Mantle.PyTranslate

open Strata.Mantle
open StrataPython.Mantle.PyBuild
open StrataPython.Mantle.PyScope (Table Scope ScopeId NameScope Diagnostic ParamKind mangle
  formatRange)
open StrataPython (stmt expr constant operator unaryop cmpop arguments arg keyword alias
  opt_expr excepthandler withitem match_case)
open StrataDDM (SourceRange)

public section

/-! ## Results -/

/-- A translated module and its diagnostics: the scope pass's syntax errors, then each
rejected construct, in source order. -/
structure Result where
  module : Module Py.env SourceRange
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

/-- The functions of `m` that are not well formed, by `Func.WF`. -/
def illFormed {α : Type} (m : Module Py.env α) : Array Name :=
  let names := m.funcs.map (·.name)
  (m.funcs.filter fun f => !decide (Func.WF names f)).map (·.name)

/-- A diagnostic as one comment line: `-- unsupported: lambda is not supported at 4:4-4:22`. -/
def formatDiagnostic (fileMap : Option Lean.FileMap) (d : Diagnostic) : String :=
  s!"-- {d.kind.text}: {d.message} at {formatRange fileMap d.range}"

end -- public section

/-! ## Builtins -/

/-- The names `builtins` defines in CPython 3.12, without the module's own dunders and the
keywords `True`, `False` and `None`. -/
def builtinNames : Std.HashSet String := .ofList [
  "ArithmeticError", "AssertionError", "AttributeError", "BaseException",
  "BaseExceptionGroup", "BlockingIOError", "BrokenPipeError", "BufferError", "BytesWarning",
  "ChildProcessError", "ConnectionAbortedError", "ConnectionError", "ConnectionRefusedError",
  "ConnectionResetError", "DeprecationWarning", "EOFError", "Ellipsis", "EncodingWarning",
  "EnvironmentError", "Exception", "ExceptionGroup", "FileExistsError", "FileNotFoundError",
  "FloatingPointError", "FutureWarning", "GeneratorExit", "IOError", "ImportError",
  "ImportWarning", "IndentationError", "IndexError", "InterruptedError", "IsADirectoryError",
  "KeyError", "KeyboardInterrupt", "LookupError", "MemoryError", "ModuleNotFoundError",
  "NameError", "NotADirectoryError", "NotImplemented", "NotImplementedError", "OSError",
  "OverflowError", "PendingDeprecationWarning", "PermissionError", "ProcessLookupError",
  "RecursionError", "ReferenceError", "ResourceWarning", "RuntimeError", "RuntimeWarning",
  "StopAsyncIteration", "StopIteration", "SyntaxError", "SyntaxWarning", "SystemError",
  "SystemExit", "TabError", "TimeoutError", "TypeError", "UnboundLocalError",
  "UnicodeDecodeError", "UnicodeEncodeError", "UnicodeError", "UnicodeTranslateError",
  "UnicodeWarning", "UserWarning", "ValueError", "Warning", "ZeroDivisionError",
  "__build_class__", "__debug__", "__import__", "abs", "aiter", "all", "anext", "any",
  "ascii", "bin", "bool", "breakpoint", "bytearray", "bytes", "callable", "chr",
  "classmethod", "compile", "complex", "copyright", "credits", "delattr", "dict", "dir",
  "divmod", "enumerate", "eval", "exec", "exit", "filter", "float", "format", "frozenset",
  "getattr", "globals", "hasattr", "hash", "help", "hex", "id", "input", "int", "isinstance",
  "issubclass", "iter", "len", "license", "list", "locals", "map", "max", "memoryview", "min",
  "next", "object", "oct", "open", "ord", "pow", "print", "property", "quit", "range", "repr",
  "reversed", "round", "set", "setattr", "slice", "sorted", "staticmethod", "str", "sum",
  "super", "tuple", "type", "vars", "zip"]

/-! ## Translator state -/

/-- A construct that `break`, `continue` and `return` leave through, innermost last. -/
inductive Exit where
  /-- A loop: `break` jumps to `brk`, `continue` to `cont`. -/
  | loop (brk cont : Label)

/-- A `def` whose function is emitted after the current one. -/
structure FuncJob where
  name : Name
  scope : ScopeId
  /-- `table.scopes[scope]`. -/
  cur : Scope
  qualname : String
  args : arguments SourceRange
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
  /-- The names some scope binds as module globals. -/
  globals : Std.HashSet String
  scope : ScopeId
  /-- `table.scopes[scope]`, the scope being translated. -/
  cur : Scope
  /-- The function's `__qualname__`, for the prologue's error messages. -/
  qualname : String

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

/-- Reject the expression `what` at `range`; its value is `py.unsupported "what"`. -/
def unsupportedValue (what : String) (range : SourceRange) : TransM ValId := do
  reject what range
  let n ← build (strLit what)
  build (emitTotal "unsupported" Py.unsupported #v[] #[n])

/-! ## Blocks -/

/-- Whether a block is open, so that instructions can be emitted. -/
def isOpen : TransM Bool := build PyBuild.isOpen

/-- Whether some transfer names `l`. -/
def targeted (l : Label) : TransM Bool := return (← get).targeted.contains l

private def recordTarget (l : Label) : TransM Unit :=
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
  /-- A variable of an enclosing function. -/
  | free
  /-- A local without a declared cell. -/
  | unresolved

/-- The current scope. -/
def curScope : TransM Scope := return (← read).cur

/-- `name`, mangled in the current scope. -/
def mangled (name : String) : TransM String := do
  return mangle (← curScope).privateName name

/-- Classify `name`, which must be mangled. -/
def place (name : String) : TransM Place := do
  let sc ← curScope
  if sc.kind == .module then return .global
  match ((sc.symbol? name).map (·.scope) : Option NameScope) with
  | some .«local» | some .cell =>
    match ← build (cellOf? name) with
    | some c => return .cell c
    | none => return .unresolved
  | some .free => return .free
  | some .globalExplicit | some .globalImplicit | none => return .global

/-- `py.requireDefined v excType msg`. -/
def requireDefined (v : ValId) (name excType msg : String) : TransM ValId := do
  let e ← build (emitConst "e" (.str excType))
  let m ← build (emitConst "msg" (.str msg))
  build (emitFailing name Py.requireDefined #v[] #[v, e, m])

/-- `py.qualifiedRef "builtins" name`. -/
def builtinRef (name : String) : TransM ValId := do
  let m ← build (emitConst "m" (.str "builtins"))
  let n ← build (emitConst "n" (.str name))
  build (emitFailing name Py.qualifiedRef #v[] #[m, n])

/-- Read the global `name`.  A name some scope binds as a global reads its cell; one that is
also a builtin falls back to the builtin when the cell is undefined.  A builtin no scope binds
is the builtin. -/
def readGlobalName (name : String) : TransM ValId := do
  let ctx ← read
  let bound := ctx.globals.contains name
  let builtin := builtinNames.contains name
  if bound && builtin then
    let v ← build (readCell (← build (globalCell ctx.module name)) name)
    let d ← build (emitTest "defined" Py.isDefined #v[] #[v])
    let fallback ← build (freshLabel "builtin")
    let join ← build (freshLabel "join")
    branch d join fallback #[v]
    build (startBlock fallback)
    jump join #[← builtinRef name]
    build (startBlockWith join name)
  else if builtin then builtinRef name
  else build (readGlobal ctx.module name)

/-- Read the name `name` at `range`. -/
def readName (name : String) (range : SourceRange) : TransM ValId := do
  let name ← mangled name
  match ← place name with
  | .cell c =>
    let v ← build (readCell c name)
    requireDefined v name "UnboundLocalError"
      s!"cannot access local variable '{name}' where it is not associated with a value"
  | .global => readGlobalName name
  | .free => unsupportedValue "closure variable" range
  | .unresolved => unsupportedValue "unresolved local" range

/-- Write `v` to the name `name` at `range`. -/
def writeName (name : String) (v : ValId) (range : SourceRange) : TransM Unit := do
  let name ← mangled name
  match ← place name with
  | .cell c => discard <| build (writeCell c v)
  | .global => discard <| build (writeGlobal (← read).module name v)
  | .free => reject "nonlocal assignment" range
  | .unresolved => reject "unresolved local" range

/-! ## Operators -/

/-- The raising operation `r` on `a` and `b`. -/
def binary {isig : InsnSig Py.env} (name : String) (r : InsnRef Py.env isig) (a b : ValId)
    (typeArgs : Vector (TypeExpr Py.env 0) isig.typeArgc := by exact #v[]) : TransM ValId :=
  build (emitFailing name r typeArgs #[a, b])

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
  | .Is _ => build (emitTotal "is" Py.is_ #v[] #[a, b])
  | .IsNot _ => build (emitTotal "isNot" Py.isNot #v[] #[a, b])
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
  | .ConEllipsis _ => builtinRef "Ellipsis"
  | .ConComplex .. => unsupportedValue "complex literal" range

/-! ## Rejected constructs -/

/-- The name of a statement `transStmt` rejects. -/
def stmtName : stmt SourceRange → String
  | .ClassDef .. => "class"
  | .Delete .. => "del"
  | .TypeAlias .. => "type alias"
  | .For .. => "for loop"
  | .AsyncFor .. => "async for"
  | .With .. => "with"
  | .AsyncWith .. => "async with"
  | .Match .. => "match"
  | .Raise .. => "raise"
  | .Try .. => "try"
  | .TryStar .. => "try/except*"
  | .Assert .. => "assert"
  | .Nonlocal .. => "nonlocal"
  | _ => "statement"

/-- The name of an assignment to a target other than a name. -/
def targetName : expr SourceRange → String
  | .Attribute .. => "attribute assignment"
  | .Subscript .. => "subscript assignment"
  | .Tuple .. | .List .. => "unpacking assignment"
  | .Starred .. => "starred assignment"
  | _ => "assignment target"

mutual

/-- The range of the first `yield` or `yield from` an expression evaluates in its own scope. -/
partial def exprYield? : expr SourceRange → Option SourceRange
  | .Yield sr _ | .YieldFrom sr _ => some sr
  | .Lambda .. | .ListComp .. | .SetComp .. | .DictComp .. | .GeneratorExp .. => none
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
  | .FunctionDef _ _ args _ decs _ _ _ | .AsyncFunctionDef _ _ args _ decs _ _ _ =>
    let .mk_arguments _ _ _ _ _ kwDefaults _ defaults := args
    (decs.val ++ defaults.val ++
      kwDefaults.val.filterMap (fun | .some_expr _ d => some d | _ => none)).findSome? exprYield?
  | .ClassDef _ _ bases kws _ decs _ =>
    (bases.val ++ kws.val.map (·.value) ++ decs.val).findSome? exprYield?
  | .Return _ v | .Raise _ v _ => v.val.bind exprYield?
  | .Delete _ ts => ts.val.findSome? exprYield?
  | .Assign _ ts v _ => (ts.val.push v).findSome? exprYield?
  | .AugAssign _ t _ v => #[t, v].findSome? exprYield?
  | .AnnAssign _ t _ v _ => (#[t] ++ v.val.toArray).findSome? exprYield?
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

/-! ## Expressions -/

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
    | .Not _ => build (emitFailing "not" Py.not_ #v[] #[v])
    | .USub _ => build (emitFailing "neg" Py.uSub #v[] #[v])
    | .UAdd _ => build (emitFailing "pos" Py.uAdd #v[] #[v])
    | .Invert _ => build (emitFailing "invert" Py.invert #v[] #[v])
  | .Compare _ l ops rs => compare l ops.val rs.val
  | .Call _ f args kws => call f args.val kws.val
  | .BoolOp _ op vs => boolOp (op matches .And _) vs.val
  | .NamedExpr _ (.Name nsr ⟨_, n⟩ _) v => do
    let x ← transExpr v
    writeName n x nsr
    return x
  | .NamedExpr sr .. => unsupportedValue "assignment expression" sr
  | .Lambda sr .. => unsupportedValue "lambda" sr
  | .IfExp _ c a b => ifExp c a b
  | .Dict _ ks vs => dictDisplay ks.val vs.val
  | .Set _ vs => setDisplay vs.val
  | .List _ vs _ => listDisplay vs.val
  | .Tuple _ vs _ => tupleDisplay vs.val
  | .ListComp sr .. => unsupportedValue "list comprehension" sr
  | .SetComp sr .. => unsupportedValue "set comprehension" sr
  | .DictComp sr .. => unsupportedValue "dict comprehension" sr
  | .GeneratorExp sr .. => unsupportedValue "generator expression" sr
  | .Await sr .. => unsupportedValue "await" sr
  | .Yield sr .. => unsupportedValue "yield" sr
  | .YieldFrom sr .. => unsupportedValue "yield from" sr
  | .JoinedStr _ vs => fString vs.val
  | .FormattedValue _ v conv spec => formatted v conv spec.val
  | .Interpolation sr .. | .TemplateStr sr .. => unsupportedValue "t-string" sr
  | .Attribute _ v ⟨_, a⟩ _ => do build (getAttr (← transExpr v) (← mangled a))
  | .Subscript _ v k _ => do
    let o ← transExpr v
    match k with
    | .Slice _ lo hi st =>
      let bs ← bounds #[lo.val, hi.val, st.val]
      build (emitFailing "slice" Py.getSlice #v[] (#[o] ++ bs))
    | k => build (emitFailing "item" Py.getItem #v[] #[o, ← transExpr k])
  | .Starred sr .. => unsupportedValue "starred expression" sr
  | .Slice _ lo hi st => do
    build (emitTotal "slice" Py.mkSlice #v[] (← bounds #[lo.val, hi.val, st.val]))

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
  build (startBlockWith join "cmp")

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
  else build (emitTotal "fstr" Py.strConcat #v[] (← vs.mapM transExpr))

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
      | 's' => build (emitFailing "str" Py.toStr #v[] #[x])
      | 'r' => build (emitFailing "repr" Py.repr #v[] #[x])
      | 'a' => build (emitFailing "ascii" Py.ascii #v[] #[x])
      | _ => unsupportedValue "f-string conversion" sr  -- the parser gives no other
  build (emitFailing "fmt" Py.fmtValue #v[] #[x, sp])

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
  build (startBlockWith join "bool")

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
  build (startBlockWith join "ifexp")

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
each `*x` and `LIST_APPEND` for each later element, as CPython does. -/
partial def listDisplay (vs : Array (expr SourceRange)) : TransM ValId := do
  let (first, rest) := splitStarred vs
  let l ← build (emitTotal "list" Py.mkList #v[] (← first.mapM transExpr))
  for v in rest do
    match v with
    | .Starred _ x _ =>
      discard <| build (emitActing "extend" Py.listExtend #v[] #[l, ← transExpr x])
    | v =>
      let x ← transExpr v
      discard <| build (emitEffect "append" Py.listAppend #v[] #[l, x])
  return l

/-- `(a, b)`: `BUILD_TUPLE`.  With a `*x`, a list display then `INTRINSIC_LIST_TO_TUPLE`, as
CPython does. -/
partial def tupleDisplay (vs : Array (expr SourceRange)) : TransM ValId := do
  if (splitStarred vs).2.isEmpty then
    build (emitTotal "tuple" Py.mkTuple #v[] (← vs.mapM transExpr))
  else
    build (emitTotal "tuple" Py.listToTuple #v[] #[← listDisplay vs])

/-- `{a, *x, b}`: as `listDisplay`, with `BUILD_SET`, `SET_UPDATE` and `SET_ADD`.  A set of
more than `stackUseGuideline` elements starts empty, as in CPython. -/
partial def setDisplay (vs : Array (expr SourceRange)) : TransM ValId := do
  let (first, rest) := if vs.size > stackUseGuideline then (#[], vs) else splitStarred vs
  let st ← build (emitFailing "set" Py.mkSet #v[] (← first.mapM transExpr))
  for v in rest do
    match v with
    | .Starred _ x _ =>
      discard <| build (emitActing "update" Py.setUpdate #v[] #[st, ← transExpr x])
    | v => discard <| build (emitActing "add" Py.setAdd #v[] #[st, ← transExpr v])
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
    (fun a d => build (emitFailing "update" Py.dictUpdate #v[] #[a, d]))
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
      let d ← build (emitFailing "dict" Py.mkDict #v[] #[])
      for (k, v) in kvs do
        let kv ← transExpr k
        let vv ← transExpr v
        discard <| build (emitActing "set" Py.dictSet #v[] #[d, kv, vv])
      return d
    let mut args := #[]
    for (k, v) in kvs do
      args := args.push (← transExpr k)
      args := args.push (← transExpr v)
    build (emitFailing "dict" Py.mkDict #v[] args)

/-- `f(a, *x, k=v, **m)`: `py.call f args kwargs`, evaluating the callee, the positional
arguments, then the keyword arguments, as CPython does.  `args` is a tuple display; a lone
`*x` is evaluated in place and made a tuple by `argsTuple` after the keyword arguments.
`kwargs` is runs of `k=v` pairs, each a total `mkKwargs`, and `DICT_MERGE` (`dictMerge`)
for each `**m`. -/
partial def call (f : expr SourceRange) (args : Array (expr SourceRange))
    (kws : Array (keyword SourceRange)) : TransM ValId := do
  let fv ← transExpr f
  let lone ← match args with
    | #[.Starred _ x _] => some <$> transExpr x
    | _ => pure none
  let t? ← if lone.isSome then pure none else some <$> tupleDisplay args
  let d ← dictFromEntries kws (fun kw => if kw.nameAndValue.1.isSome then none else some kw.value)
    (fun run => if run.isEmpty then #[] else #[run])
    (fun run => do
      let mut kvs := #[]
      for kw in run do
        kvs := kvs.push (← build (strLit (kw.nameAndValue.1.getD "")))
        kvs := kvs.push (← transExpr kw.value)
      build (emitTotal "kwargs" Py.mkKwargs #v[] kvs))
    (fun a m => build (emitFailing "merge" Py.dictMerge #v[] #[fv, a, m]))
  let t ← match t?, lone with
    | some t, _ => pure t
    | none, some x => build (emitFailing "args" Py.argsTuple #v[] #[fv, x])
    | none, none => build (emitTotal "args" Py.mkTuple #v[] #[])
  build (emitFailing "call" Py.call #v[] #[fv, t, d])

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

/-- Emit the argument-binding prologue (§5.4), writing each parameter's cell.  The checks
run in CPython's order: a duplicate value, an unexpected keyword, too many positional
arguments, a missing argument. -/
def prologue (ps : Array ParamWithDefault) (args kwargs : ValId) : TransM Unit := do
  let fn := (← read).qualname
  let pos := ps.filter fun p => p.kind == .posOnly || p.kind == .positional
  let varPos := ps.find? (·.kind == .varPositional)
  let kwOnly := ps.filter (·.kind == .kwOnly)
  let varKw := ps.find? (·.kind == .varKeyword)
  let fillSlot (p : ParamWithDefault) : TransM ValId := do
    match p.default with
    | some d => transExpr d
    | none => build (emitTotal p.name Py.undef #v[] #[← build (emitConst "n" (.str p.name))])
  let discardKey (key : ValId) : TransM Unit :=
    discard <| build (emitEffect "discard" Py.dictDiscard #v[] #[kwargs, key])
  let typeError (val : ValId) (limit : Option Int) (msg : String) : TransM Unit := do
    let lim ← limit.mapM fun l => build (emitConst "limit" (.int l))
    let e ← build (emitConst "e" (.str "TypeError"))
    let m ← build (emitConst "msg" (.str msg))
    match lim with
    | some l => discard <| build (emitActing "check" Py.requireAtMost #v[] #[val, l, e, m])
    | none => discard <| build (emitActing "check" Py.requireUndefined #v[] #[val, e, m])
  let nargs ← if !pos.isEmpty || varPos.isNone then
      some <$> build (emitTotal "nargs" Py.tupleLen #v[] #[args])
    else pure none
  let mut bound : Array (ParamWithDefault × ValId) := #[]
  let mut dups : Array (ParamWithDefault × ValId × ValId) := #[]
  if let some n := nargs then
    if !pos.isEmpty then
      let fill ← build (emitTotal "fill" Py.mkTuple #v[] (← pos.mapM fillSlot))
      let none₁ ← build noneLit
      let tail ← build (emitFailing "tail" Py.getSlice #v[] #[fill, n, none₁, none₁])
      let pad ← build (emitFailing "pad" Py.add #v[] #[args, tail])
      for h : i in [:pos.size] do
        let p := pos[i]
        let idx ← build (intLit i)
        let fromPos ← build (emitFailing "pos" Py.getItem #v[] #[pad, idx])
        if p.kind == .posOnly then
          bound := bound.push (p, fromPos)
        else
          let key ← build (strLit p.name)
          let got ← build (emitTotal p.name Py.dictGet #v[] #[kwargs, key, fromPos])
          let inKw ← build (emitFailing "inKw" Py.in_ #v[] #[key, kwargs])
          discardKey key
          bound := bound.push (p, got)
          dups := dups.push (p, idx, inKw)
  if let some p := varPos then
    let idx ← build (intLit pos.size)
    let none₁ ← build noneLit
    let rest ← build (emitFailing p.name Py.getSlice #v[] #[args, idx, none₁, none₁])
    writeName p.name rest .none
  for p in kwOnly do
    let key ← build (strLit p.name)
    let miss ← fillSlot p
    let got ← build (emitTotal p.name Py.dictGet #v[] #[kwargs, key, miss])
    discardKey key
    bound := bound.push (p, got)
  if let some n := nargs then
    for (p, idx, inKw) in dups do
      let filled ← build (emitFailing "filled" Py.lt #v[] #[idx, n])
      let both ← build (emitFailing "both" Py.mult #v[] #[inKw, filled])
      typeError both (some 0) s!"{fn}() got multiple values for argument '{p.name}'"
  if varKw.isNone then
    let kwName ← build (emitConst "n" (.str "kwargs"))
    let miss ← build (emitTotal "kw" Py.undef #v[] #[kwName])
    let left ← build (emitTotal "kw" Py.dictFirstKey #v[] #[kwargs, miss])
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

/-- A fresh function name: `m.f`, or `m.f.k` if that is taken. -/
def allocName (name : String) : TransM Name := do
  let first := (← read).moduleName.str name
  let taken := (← get).funcNames
  let mut n := first
  let mut k := 1
  while taken.contains n do
    n := .num first k
    k := k + 1
  modify fun s => { s with funcNames := s.funcNames.insert n }
  return n

/-- `def name(args): body` at `sr`: bind `name` to the function's closure, and queue the
function.  An `async def` or a generator is queued as a stub. -/
def defStmt (sr : SourceRange) (name : String) (args : arguments SourceRange)
    (body : Array (stmt SourceRange)) (decorators : Array (expr SourceRange))
    (hasTypeParams isAsync : Bool) : TransM Unit := do
  let ctx ← read
  if (← curScope).kind != .module then return ← reject "nested function" sr
  if let some d := decorators[0]? then return ← reject "decorator" d.ann
  if hasTypeParams then return ← reject "type parameters" sr
  if let some p := (params args).find? (·.default.any (!isConstantDefault ·)) then
    return ← reject "non-constant default" (p.default.map (·.ann) |>.getD sr)
  let some scope := ctx.table.childAt? ctx.scope sr
    | return ← reject "function without a scope" sr
  let some cur := ctx.table.scopes[scope]?
    | return ← internalError s!"scope {scope} is not in the table" sr
  let stub ← if isAsync then do reject "async def" sr; pure (some "async def")
    else match bodiesYield? #[body] with
      | some r => do reject "generator function" r; pure (some "generator function")
      | none => pure none
  let fname ← allocName name
  let job : FuncJob :=
    { name := fname, scope, cur, qualname := cur.qualname, args, body, range := sr, stub }
  modify fun s => { s with pending := s.pending.push job }
  writeName name (← build (funcValue fname)) sr

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

/-- Leave by `break` (`brk := true`), `continue`, or `return v` (`ret := some v`), walking the
exits stack from the innermost entry (§4). -/
def exitWalk (brk : Bool) (ret : Option ValId) (range : SourceRange) : TransM Unit := do
  for e in (← get).exits.reverse do
    match e, ret with
    | .loop b c, none => return ← jump (if brk then b else c)
    | .loop .., some _ => pure ()
  match ret with
  | some v => build (emitReturn v)
  | none => reject (if brk then "'break' outside loop" else "'continue' outside loop") range

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
  | .Pass _ | .Global .. => pure ()
  | .Assign sr ⟨_, targets⟩ v _ =>
    let names := targets.filterMap fun | .Name _ ⟨_, n⟩ _ => some n | _ => none
    if let some t := targets.find? (fun | .Name .. => false | _ => true) then
      return ← reject (targetName t) t.ann
    let x ← transExpr v
    for n in names do writeName n x sr
  | .AnnAssign sr target _ ⟨_, value⟩ _ =>
    match target, value with
    | .Name _ ⟨_, n⟩ _, some v => writeName n (← transExpr v) sr
    | .Name .., none => pure ()
    | t, _ => reject (targetName t) t.ann
  | .AugAssign sr target op v =>
    match target with
    | .Name nsr ⟨_, n⟩ _ =>
      let cur ← readName n nsr
      let rhs ← transExpr v
      writeName n (← inPlaceOp op cur rhs) sr
    | t => reject s!"augmented {targetName t}" t.ann
  | .If _ test body orelse => ifStmt test body.val orelse.val
  | .While _ test body orelse => whileStmt test body.val orelse.val
  | .Break sr => exitWalk true none sr
  | .Continue sr => exitWalk false none sr
  | .Return sr ⟨_, v⟩ =>
    if (← curScope).kind == .module then return ← reject "'return' outside function" sr
    let x ← match v with
      | some e => transExpr e
      | none => build noneLit
    exitWalk false (some x) sr
  | .Import _ ⟨_, aliases⟩ => aliases.forM importAlias
  | .ImportFrom sr ⟨_, m⟩ ⟨_, aliases⟩ ⟨_, level⟩ =>
    if m.isNone || (level.map (·.value)).getD 0 != 0 then reject "relative import" sr
    else if aliases.any (·.name == "*") then reject "import *" sr
    else aliases.forM importAlias
  | .FunctionDef sr ⟨_, n⟩ args body decs _ _ tps =>
    defStmt sr n args body.val decs.val (!tps.val.isEmpty) false
  | .AsyncFunctionDef sr ⟨_, n⟩ args body decs _ _ tps =>
    defStmt sr n args body.val decs.val (!tps.val.isEmpty) true
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

end

/-! ## Modules -/

/-- The names some scope binds as module globals: those the module binds, those a function
declares `global` and binds, and `__name__`. -/
def moduleGlobals (t : Table) : Std.HashSet String := Id.run do
  let mut out : Std.HashSet String := ({} : Std.HashSet String).insert "__name__"
  for sym in t.module.symbols do
    if sym.uses.bound then out := out.insert sym.name
  for sc in t.scopes do
    for sym in sc.symbols do
      if sym.scope == .globalExplicit && sym.uses.bound then out := out.insert sym.name
  return out

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

/-- Emit the function `job` queues. -/
def transFunc (ctx : Ctx) (st : TState) (job : FuncJob) : Func Py.env SourceRange × TState :=
  let ctx := { ctx with scope := job.scope, cur := job.cur, qualname := job.qualname }
  let argTypes := #[("args", Py.Value.ty), ("kwargs", Py.Value.ty)]
  builtFunc job.range <| buildFuncTypedWith job.name argTypes job.range fun ps =>
    runBody ctx st job.range do
      match job.stub with
      | some what =>
        let n ← build (strLit what)
        build (emitReturn (← build (emitTotal "unsupported" Py.unsupported #v[] #[n])))
      | none =>
        let sc ← curScope
        for sym in sc.symbols do
          if sym.scope == .«local» || sym.scope == .cell then
            discard <| build (declareLocal sym.name)
        let #[args, kwargs] := ps
          | internalError "a function without its args and kwargs parameters" job.range
        prologue (params job.args) args kwargs
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
    { table, module := moduleName, moduleName := mname, globals := moduleGlobals table
      scope := 0, cur, qualname := "<module>" }
  let bodyName := mname.str "<module>"
  let st : TState := { funcNames := ({} : Std.HashSet Name).insert bodyName }
  let (body, st) := builtFunc range <| buildFuncTypedWith bodyName #[] range fun _ =>
    runBody ctx st range do
      writeName "__name__" (← build (strLit moduleName)) .none
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
