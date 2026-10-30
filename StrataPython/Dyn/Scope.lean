/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.PythonDialect
public import StrataDDM.Util.SourceRange
public import Lean.Data.Position
import StrataPython.Dyn.Termination

set_option autoImplicit false

/-!
# Python name resolution

`analyze` classifies every name of a Python module the way CPython 3.12's symbol table
does, and resolves imports to fully qualified names.  Its result is a `Table`:

* one `Scope` per module, function, `lambda`, class body, generator expression and list,
  set or dict comprehension, in preorder, the module first;
* for each scope, its kind, name, `__qualname__`, parent, children and parameters, and for a
  function whether it is a generator;
* for each name a scope reads, binds or declares, a `Symbol`: its `NameScope` and its
  `Uses`;
* each import, with the module or member it binds;
* `Diagnostic`s: the errors CPython raises at compile time, and the constructs the
  translator rejects.

`Table.format` prints the table and `Table.symtableFormat` prints what CPython's `symtable`
module records, and which code objects are generators, for comparison with them.

The classification follows CPython 3.12's `Python/symtable.c`:

* `local`: bound in the scope (assignment and augmented-assignment targets, `for`, `with …
  as` and `except … as` targets, `import`, `def`, `class`, parameters, `del` targets, walrus
  targets and `match` captures), and not declared `global` or `nonlocal`.  A walrus inside a
  comprehension binds in the nearest enclosing function or module instead.
* `cell`: a function's local that a nested scope uses, or a name an inlined comprehension
  introduces as a cell.
* `free`: bound in an enclosing function, or declared `nonlocal`.  A function between the
  binding and the use gets the name as `free` too, to pass the cell on.
* `globalExplicit`: declared `global`.
* `globalImplicit`: neither bound here nor in an enclosing function: a module global or a
  builtin.

At module level a bound name is `local`: the module's locals are its globals.  A class
body's bindings are invisible to the scopes nested in it, which resolve as if the class
were not there.  Inside a class, private names (`__x`) are mangled (`_C__x`) as CPython
mangles them; `mangle` applies the rule.  An annotated assignment's annotation is a use, as
in 3.12's symbol table, except under `from __future__ import annotations`; so are a
function's parameter and return annotations, in the scope enclosing the function.

## Comprehensions

A generator expression is a `comprehension` scope: a function with one parameter, `.0`, the
outermost iterable, which the enclosing scope evaluates.

A list, set or dict comprehension is an `inlinedComprehension` scope (PEP 709): a region of
the enclosing scope, which also evaluates its outermost iterable.  Its symbols are
classified as a function's would be, and say how names resolve inside it:

* `local` or `cell`: an iteration variable, bound in the region apart from any binding of
  the same name outside it; `Scope.regionLocals` lists them.  A `cell` is fresh on each run
  of the comprehension.
* `free`: the name as the enclosing scope resolves it, skipping class bodies.
* `globalExplicit` or `globalImplicit`: a global.

The enclosing scope also lists each name the comprehension uses that it does not already
have, with the comprehension's flags and classification, as `symtable` does.  A name the
enclosing scope already has keeps its own flags and classification; if the enclosing scope
binds it, reading it in the comprehension does not make it a cell.  An iteration variable
that a scope nested in the comprehension captures is flagged `compCell` in the enclosing
scope, and `Uses.compCell` says how it is classified there.  The scopes nested in a
comprehension are named after the enclosing scope: a `lambda` in a list comprehension in
`f` is `f.<locals>.<lambda>`.

Relative imports, `import *`, `match`, `type` statements and type parameters are rejected
with an `unsupported` diagnostic.  The names they bind are still classified.
-/

namespace StrataPython.Dyn.PyScope

open StrataDDM (SourceRange Ann)
open StrataPython (stmt expr arguments arg alias excepthandler withitem comprehension
  pattern match_case keyword opt_expr expr_context)

public section

/-! ## The table -/

/-- What introduced a scope. -/
inductive ScopeKind where
  | module
  | function
  | lambda
  | classBody
  /-- A generator expression, which runs as a function of its own. -/
  | comprehension
  /-- A list, set or dict comprehension, which PEP 709 inlines into the enclosing scope: a
  region of it, with no frame of its own. -/
  | inlinedComprehension
  deriving DecidableEq, Repr, Inhabited

/-- Whether a scope of this kind is what CPython calls a function block: a function,
`lambda`, generator expression or comprehension.  A function block's local that a nested
scope uses is a cell. -/
def ScopeKind.isFunctionLike : ScopeKind → Bool
  | .function | .lambda | .comprehension | .inlinedComprehension => true
  | .module | .classBody => false

/-- Whether a scope of this kind is a comprehension or generator expression. -/
def ScopeKind.isComprehension : ScopeKind → Bool
  | .comprehension | .inlinedComprehension => true
  | .module | .function | .lambda | .classBody => false

/-- How a name resolves in a scope. -/
inductive NameScope where
  /-- Bound in this scope and used by no nested scope. -/
  | «local»
  /-- A function's local that a nested scope uses, or a name an inlined comprehension
  introduces as a cell (`Uses.compCell`). -/
  | cell
  /-- Bound in an enclosing function, or declared `nonlocal`. -/
  | free
  /-- Declared `global`. -/
  | globalExplicit
  /-- A module global or a builtin, without a `global` declaration. -/
  | globalImplicit
  deriving DecidableEq, Repr, Inhabited

/-- How a scope uses a name: the flags CPython's symbol table records. -/
structure Uses where
  /-- A parameter. -/
  param : Bool := false
  /-- Bound by an assignment, `for`, `with`, `except … as`, `def`, `class`, `del`, walrus
  or `match` capture. -/
  assigned : Bool := false
  /-- Bound by an import. -/
  imported : Bool := false
  /-- Read. -/
  referenced : Bool := false
  /-- Declared `global`, or a walrus target in a comprehension at module level. -/
  declaredGlobal : Bool := false
  /-- Declared `nonlocal`, or a walrus target in a comprehension. -/
  declaredNonlocal : Bool := false
  /-- The target of an annotated assignment `x: T`. -/
  annotated : Bool := false
  /-- A comprehension's iteration variable. -/
  compIter : Bool := false
  /-- Used in a class body, and free in a nested scope. -/
  freeClass : Bool := false
  /-- In the scope an inlined comprehension is merged into: the comprehension binds the name
  as a cell, because a scope nested in it captures the name, or because a comprehension
  inlined into it has this flag.  CPython's `DEF_COMP_CELL`.  The comprehension's binding is
  a fresh cell on each run, apart from the scope's own binding of the name, in a class body
  as elsewhere.

  The flag records the cell whatever the name's classification in the scope.  If the
  comprehension introduces the name, that is the comprehension's, `cell`.  A name the scope
  itself uses anywhere in its body, or that an earlier comprehension in it introduced, keeps
  its classification, except that a function's `local` becomes a `cell`.  So in a module or
  class body the name can stay `local` or `globalImplicit`, and in a function that only
  reads it, `globalImplicit`. -/
  compCell : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Both sets of flags. -/
def Uses.union (a b : Uses) : Uses where
  param := a.param || b.param
  assigned := a.assigned || b.assigned
  imported := a.imported || b.imported
  referenced := a.referenced || b.referenced
  declaredGlobal := a.declaredGlobal || b.declaredGlobal
  declaredNonlocal := a.declaredNonlocal || b.declaredNonlocal
  annotated := a.annotated || b.annotated
  compIter := a.compIter || b.compIter
  freeClass := a.freeClass || b.freeClass
  compCell := a.compCell || b.compCell

/-- Whether the scope binds the name: CPython's `DEF_BOUND`. -/
def Uses.bound (u : Uses) : Bool := u.param || u.assigned || u.imported

/-- A name of a scope and its classification. -/
structure Symbol where
  /-- The name, mangled if it is private. -/
  name : String
  scope : NameScope
  uses : Uses
  deriving Repr, Inhabited

/-- How a parameter is passed. -/
inductive ParamKind where
  | posOnly
  | positional
  | varPositional
  | kwOnly
  | varKeyword
  deriving DecidableEq, Repr, Inhabited

/-- A parameter, in signature order. -/
structure Param where
  /-- The name, mangled if it is private. -/
  name : String
  kind : ParamKind
  range : SourceRange
  deriving Repr, Inhabited

/-- The index of a scope in `Table.scopes`. -/
abbrev ScopeId := Nat

/-- A module, function, `lambda`, class body, generator expression or comprehension. -/
structure Scope where
  kind : ScopeKind
  /-- The `def` or `class` name; `<module>`, `<lambda>`, `<listcomp>`, `<setcomp>`,
  `<dictcomp>` or `<genexpr>` otherwise. -/
  name : String
  /-- CPython's `__qualname__`, such as `f.<locals>.g` or `C.m`; empty for the module.  An
  inlined comprehension has no code object; its name is `f.<locals>.<listcomp>`, as
  before PEP 709, and the scopes nested in it are named as if it were not there. -/
  qualname : String
  parent : Option ScopeId
  /-- The nested scopes, in the order their definitions are evaluated. -/
  children : Array ScopeId
  /-- The parameters.  A comprehension or generator expression has one, `.0`: the
  outermost iterator, which the enclosing scope evaluates. -/
  params : Array Param
  /-- Every name the scope uses, in order of first use, then the free names it only passes
  on to nested scopes.  The enclosing scope of an inlined comprehension also lists the
  names the comprehension uses that it did not already have. -/
  symbols : Array Symbol
  /-- The defining node's range: the `def`, `class`, `lambda` or comprehension. -/
  range : SourceRange
  /-- The name of the innermost class body containing the scope, or that is the scope:
  private names are mangled with it. -/
  privateName : Option String
  /-- For a class body: a nested function reads `__class__` or calls `super`, so the class
  needs an implicit `__class__` cell. -/
  needsClassCell : Bool
  /-- For a function or `lambda` that is a generator: its first `yield` or `yield from` in
  source order, as CPython 3.12 sets `CO_GENERATOR` from any `yield` the function evaluates. -/
  generator : Option SourceRange := none
  deriving Repr, Inhabited

/-- What an import binds a name to. -/
inductive ImportTarget where
  /-- The module with this dotted path. -/
  | module (path : String)
  /-- Attribute `name` of the module with dotted path `mod`. -/
  | member (mod name : String)
  deriving DecidableEq, Repr, Inhabited

/-- The fully qualified name an import binds: `a.b` or `a.b.x`. -/
def ImportTarget.qualified : ImportTarget → String
  | .module path => path
  | .member m name => s!"{m}.{name}"

/-- One name bound by an `import` or `from … import`.

* `import a.b.c` binds `a` to module `a`, loading `a.b.c`.
* `import a.b.c as d` binds `d` to module `a.b.c`.
* `from a.b import x as y` binds `y` to member `x` of `a.b`, loading `a.b`. -/
structure Import where
  /-- The scope the name is bound in. -/
  scope : ScopeId
  /-- The bound name, mangled if it is private. -/
  name : String
  target : ImportTarget
  /-- The module the statement imports. -/
  loads : String
  /-- The alias's range. -/
  range : SourceRange
  deriving Repr, Inhabited

/-- Why a program is not accepted. -/
inductive DiagnosticKind where
  /-- CPython raises a `SyntaxError` when compiling it. -/
  | syntaxError
  /-- Valid Python that the translator rejects. -/
  | unsupported
  /-- A bug in the translator, such as a misuse of the builder or a function that is not well
  formed. -/
  | internal
  deriving DecidableEq, Repr, Inhabited

/-- An error, with the range of the node it is about. -/
structure Diagnostic where
  kind : DiagnosticKind
  message : String
  range : SourceRange
  /-- A syntax error that CPython's compiler raises, which it reaches only once its symbol
  table has accepted the program. -/
  compiler : Bool := false
  deriving Repr, Inhabited

/-- How a diagnostic of this kind is labelled: `syntax error`, `unsupported` or
`internal error`. -/
def DiagnosticKind.text : DiagnosticKind → String
  | .syntaxError => "syntax error"
  | .unsupported => "unsupported"
  | .internal => "internal error"

/-- `sr` as `line:col-line:col` given `fileMap`, as byte offsets `start-stop` otherwise, and
as `?` if it is `SourceRange.none`. -/
def formatRange (fileMap : Option Lean.FileMap) (sr : SourceRange) : String :=
  if sr.isNone then "?"
  else match fileMap with
    | some fm =>
      let a := fm.toPosition sr.start
      let b := fm.toPosition sr.stop
      s!"{a.line}:{a.column}-{b.line}:{b.column}"
    | none => s!"{sr.start}-{sr.stop}"

/-- Each scope's parent comes before it in `xs`, and each of its children comes after it and is
in `xs`. -/
def Ordered {β : Type} (parent : β → Option ScopeId) (children : β → Array ScopeId)
    (xs : Array β) : Prop :=
  ∀ i (h : i < xs.size), (∀ q : Nat, parent xs[i] = some q → q < i) ∧
    ∀ c : Nat, c ∈ children xs[i] → i < c ∧ c < xs.size

/-- The scopes, imports and diagnostics of a module. -/
structure Table where
  /-- Every scope in preorder; `scopes[0]` is the module. -/
  scopes : Array Scope
  /-- Every import, in source order. -/
  imports : Array Import
  /-- Compile-time errors and rejected constructs, in the order CPython finds them. -/
  diagnostics : Array Diagnostic
  /-- The proof that a walk from any scope, up through parents or down through children, ends. -/
  ordered : Ordered Scope.parent Scope.children scopes
  /-- There is a scope 0, which `analyze` makes the module scope. -/
  scopes_ne : 0 < scopes.size
  deriving Repr

/-- A module scope with no names. -/
def Scope.emptyModule : Scope :=
  { kind := .module, name := "<module>", qualname := "", parent := none, children := #[]
    params := #[], symbols := #[], range := .none, privateName := none, needsClassCell := false }

instance : Inhabited Table :=
  ⟨{ scopes := #[Scope.emptyModule], imports := #[], diagnostics := #[]
     ordered := by
       intro i hi
       obtain rfl : i = 0 := by simpa using hi
       simp [Scope.emptyModule]
     scopes_ne := by decide }⟩

/-- A scope's parent comes before it in the table. -/
theorem Table.parent_lt (t : Table) {i : Nat} (h : i < t.scopes.size) {q : Nat}
    (hq : t.scopes[i].parent = some q) : q < i :=
  (t.ordered i h).1 q hq

/-- `name` mangled inside a class whose name is `privateName`: `__x` in class `_C` is
`_C__x`.  Names ending in `__`, dotted names, and names in classes named only with
underscores are not mangled. -/
def mangle (privateName : Option String) (name : String) : String :=
  match privateName with
  | none => name
  | some cls =>
    if !name.startsWith "__" || name.endsWith "__" || name.contains '.' then name
    else
      let stripped := (cls.dropWhile (· == '_')).toString
      if stripped.isEmpty then name else s!"_{stripped}{name}"

namespace Scope

/-- The symbol for `name`, which must be mangled already. -/
def symbol? (s : Scope) (name : String) : Option Symbol :=
  s.symbols.find? (·.name == name)

/-- The names classified `scope`, in order of first use. -/
def namesIn (s : Scope) (scope : NameScope) : Array String :=
  s.symbols.filterMap fun sym => if sym.scope == scope then some sym.name else none

/-- The locals that nested scopes capture. -/
def cellVars (s : Scope) : Array String := s.namesIn .cell

/-- The enclosing functions' cells this scope captures. -/
def freeVars (s : Scope) : Array String := s.namesIn .free

/-- For an inlined comprehension, the names it binds apart from the enclosing scope's
binding of the same name: its iteration variables, `local` or `cell`.  Empty otherwise. -/
def regionLocals (s : Scope) : Array String :=
  if s.kind != .inlinedComprehension then #[]
  else s.symbols.filterMap fun sym =>
    if (sym.scope == .local || sym.scope == .cell) && !sym.uses.param then some sym.name
    else none

end Scope

namespace Table

/-- The module scope. -/
def module (t : Table) : Scope := t.scopes[0]'t.scopes_ne

/-- The symbol for `name` in scope `s`; `name` must be mangled already. -/
def symbol? (t : Table) (s : ScopeId) (name : String) : Option Symbol :=
  t.scopes[s]? >>= (·.symbol? name)

/-- The scope that the `def`, `class`, `lambda`, generator expression or comprehension at
`range` opens, as a child of `parent`. -/
def childAt? (t : Table) (parent : ScopeId) (range : SourceRange) : Option ScopeId :=
  t.scopes[parent]? >>= fun p => p.children.find? fun c =>
    (t.scopes[c]?.map (·.range == range)).getD false

/-- The imports binding a name in scope `s`. -/
def importsIn (t : Table) (s : ScopeId) : Array Import :=
  t.imports.filter (·.scope == s)

/-- The compile-time errors, without the rejections: the symbol table's first, then the
compiler's, as CPython reports them, each in the order the scope pass visits the program.  So
the first is CPython's, except where two compiler errors meet in one statement that CPython
compiles in another order, such as `class C((yield 1)): return 1`. -/
def syntaxErrors (t : Table) : Array Diagnostic :=
  t.diagnostics.filter (·.kind == .syntaxError)

end Table

/-- The index of the starred element of a tuple or list target, or the error CPython's
compiler reports for more than one. -/
def starredIndex? (ts : Array (expr SourceRange)) : Except String (Option Nat) :=
  match ts.filter (· matches .Starred ..) with
  | #[] => .ok none
  | #[_] => .ok (ts.findIdx? (· matches .Starred ..))
  | _ => .error "multiple starred expressions in assignment"

end -- public section

/-! ## Collecting uses

The first phase mirrors `symtable_visit_*`: it walks the AST once, in CPython's order,
recording each scope's names and flags.  Visiting in CPython's order puts children and
compile-time errors in CPython's order. -/

/-- A scope under construction. -/
private structure Pending where
  kind : ScopeKind
  name : String
  parent : Option ScopeId
  range : SourceRange
  privateName : Option String
  params : Array Param := #[]
  children : Array ScopeId := #[]
  /-- The names in order of first use. -/
  names : Array String := #[]
  uses : Std.HashMap String Uses := {}
  /-- Where each name was first declared `global` or `nonlocal`, or first walrus-bound
  from a comprehension. -/
  directives : Std.HashMap String SourceRange := {}
  /-- Visiting a comprehension's iteration targets. -/
  inIterTarget : Bool := false
  /-- Visiting a comprehension's iterable, at this depth. -/
  inIterExpr : Nat := 0
  /-- The first `yield` in source order, if this is a function. -/
  generator : Option SourceRange := none
  deriving Inhabited

private structure CollectState where
  scopes : Array Pending
  cur : ScopeId := 0
  /-- The class name private names are mangled with. -/
  privateName : Option String := none
  imports : Array Import := #[]
  diagnostics : Array Diagnostic := #[]
  /-- The module has `from __future__ import annotations`: annotations are not analysed, as
  CPython 3.12's symbol table puts them in a block of their own. -/
  futureAnnotations : Bool := false
  /-- Visiting a loop body of the current function or class body: where `break` and
  `continue` may appear. -/
  inLoop : Bool := false
  hcur : cur < scopes.size
  hord : Ordered Pending.parent Pending.children scopes

private abbrev CollectM := StateM CollectState

private def curScope : CollectM Pending := do
  let st ← get
  return st.scopes[st.cur]'st.hcur

/-- The module scope. -/
private def moduleScope : CollectM Pending := do
  let st ← get
  return st.scopes[0]'(Nat.lt_of_le_of_lt (Nat.zero_le _) st.hcur)

/-- Scope `s`.  Every id the walk holds names a scope it opened, so a missing one is an
internal error, reported, with an empty module scope in its place. -/
private def scopeAt (s : ScopeId) : CollectM Pending := do
  match (← get).scopes[s]? with
  | some p => return p
  | none =>
    let d : Diagnostic :=
      { kind := .internal, message := s!"scope {s} is not in the table", range := .none }
    modify fun st => { st with diagnostics := st.diagnostics.push d }
    return { kind := .module, name := "", parent := none, range := .none, privateName := none }

/-- Changing scope `s` with a function `f` that keeps each scope's parent and children keeps
`Ordered`. -/
private theorem Ordered.modify_of_links {ps : Array Pending}
    (h : Ordered Pending.parent Pending.children ps) (s : ScopeId) (f : Pending → Pending)
    (hf : ∀ p, (f p).parent = p.parent ∧ (f p).children = p.children) :
    Ordered Pending.parent Pending.children (ps.modify s f) := by
  intro i hi
  have hi' : i < ps.size := by simpa using hi
  have hord := h i hi'
  simp only [Array.getElem_modify, Array.size_modify]
  split
  · rw [(hf _).1, (hf _).2]; exact hord
  · exact hord

/-- Change what scope `s` holds; `f` must keep its links. -/
private def modifyScope (s : ScopeId) (f : Pending → Pending)
    (hf : ∀ p, (f p).parent = p.parent ∧ (f p).children = p.children := by
      intro p; constructor <;> (try split) <;> rfl) : CollectM Unit :=
  modify fun st => { st with
    scopes := st.scopes.modify s f
    hcur := by simpa using st.hcur
    hord := st.hord.modify_of_links s f hf }

private def report (kind : DiagnosticKind) (message : String) (range : SourceRange) :
    CollectM Unit :=
  modify fun st => { st with diagnostics := st.diagnostics.push { kind, message, range } }

private def syntaxError (message : String) (range : SourceRange) : CollectM Unit :=
  report .syntaxError message range

/-- A syntax error that CPython's compiler, not its symbol table, raises. -/
private def compilerError (message : String) (range : SourceRange) : CollectM Unit :=
  let d : Diagnostic := { kind := .syntaxError, message, range, compiler := true }
  modify fun st => { st with diagnostics := st.diagnostics.push d }

private def unsupported (message : String) (range : SourceRange) : CollectM Unit :=
  report .unsupported message range

/-- Report a keyword argument named twice, as CPython's compiler does. -/
private def checkKeywords (kws : Array (keyword SourceRange)) : CollectM Unit := do
  let mut seen : Std.HashSet String := {}
  for k in kws do
    if let some n := k.nameAndValue.1 then
      if seen.contains n then return ← compilerError s!"keyword argument repeated: {n}" k.ann
      seen := seen.insert n

/-- Report a starred target outside a tuple or list, or two starred targets in one, as
CPython's compiler does. -/
private def checkTarget : expr SourceRange → CollectM Unit
  | .Starred sr _ _ => compilerError "starred assignment target must be in a list or tuple" sr
  | .Tuple sr ts _ | .List sr ts _ => do
    if let .error msg := starredIndex? ts.val then return ← compilerError msg sr
    for _ht : t in ts.val do
      match t, _ht with
      | .Starred _ v _, _ht => checkTarget v
      | t, _ht => checkTarget t
  | _ => pure ()
termination_by e => sizeOf e

private def mangled (name : String) : CollectM String := do
  return mangle (← get).privateName name

/-- The flags of an already-mangled name in scope `s`. -/
private def usesIn (s : ScopeId) (name : String) : CollectM Uses := do
  return ((← scopeAt s).uses[name]?).getD {}

/-- Add `flag` to an already-mangled name in scope `s`: `symtable_add_def_helper`. -/
private def addDefIn (s : ScopeId) (name : String) (flag : Uses) (range : SourceRange) :
    CollectM Unit := do
  let p ← scopeAt s
  let old := p.uses[name]?
  let mut val := (old.getD {}).union flag
  if flag.param && (old.map (·.param)).getD false then
    syntaxError s!"duplicate argument '{name}' in function definition" range
  if p.inIterTarget then
    if val.declaredGlobal || val.declaredNonlocal then
      syntaxError
        s!"comprehension inner loop cannot rebind assignment expression target '{name}'" range
    val := { val with compIter := true }
  modifyScope s fun p =>
    { p with uses := p.uses.insert name val
             names := if old.isSome then p.names else p.names.push name }
  -- A `global` declaration also lands in the module's table.
  if flag.declaredGlobal && s != 0 then
    let m ← moduleScope
    let mOld := m.uses[name]?
    modifyScope 0 fun m =>
      { m with uses := m.uses.insert name ((mOld.getD {}).union { declaredGlobal := true })
               names := if mOld.isSome then m.names else m.names.push name }

/-- Add `flag` to `name` in the current scope, mangling it: `symtable_add_def`. -/
private def addDef (name : String) (flag : Uses) (range : SourceRange) : CollectM Unit := do
  addDefIn (← get).cur (← mangled name) flag range

private def recordDirective (s : ScopeId) (name : String) (range : SourceRange) :
    CollectM Unit :=
  modifyScope s fun p =>
    if p.directives.contains name then p
    else { p with directives := p.directives.insert name range }

/-- Appending a scope `child`, whose parent is `cur` and which has no children, keeps `Ordered`
if `g` adds the new index to the children of `cur` and keeps the rest of the links. -/
private theorem Ordered.push_child {ps : Array Pending}
    (h : Ordered Pending.parent Pending.children ps) {cur : ScopeId} (hc : cur < ps.size)
    (g : Pending → Pending) (hgp : ∀ p, (g p).parent = p.parent)
    (hgc : ∀ p, (g p).children = p.children.push ps.size)
    (child : Pending) (hp : child.parent = some cur) (hch : child.children = #[]) :
    Ordered Pending.parent Pending.children ((ps.modify cur g).push child) := by
  intro i hi
  have hsize : ((ps.modify cur g).push child).size = ps.size + 1 := by simp
  rw [hsize] at hi ⊢
  by_cases hlt : i < ps.size
  · have ⟨h1, h2⟩ := h i hlt
    rw [Array.getElem_push_lt (by simpa using hlt), Array.getElem_modify]
    split
    · rename_i heq
      subst heq
      refine ⟨by rw [hgp]; exact h1, fun c hc' => ?_⟩
      rw [hgc, Array.mem_push] at hc'
      rcases hc' with hc' | rfl
      · have hlt' := h2 c hc'; omega
      · omega
    · exact ⟨h1, fun c hc' => by have hlt' := h2 c hc'; omega⟩
  · have hi' : i = ps.size := by omega
    subst hi'
    have hlast : ((ps.modify cur g).push child)[ps.size]'(by simp) = child := by
      simp [Array.getElem_push]
    rw [hlast]
    refine ⟨fun q hq => ?_, by simp [hch]⟩
    rw [hp] at hq
    cases hq
    exact hc

/-- Open a child scope of the current one and make it current.  A scope opened inside a
comprehension's iterable is inside it too: `symtable_enter_block`. -/
private def enter (kind : ScopeKind) (name : String) (range : SourceRange) : CollectM Unit := do
  let st ← get
  let id := st.scopes.size
  have hid : id = st.scopes.size := rfl
  let child : Pending :=
    { kind, name, parent := some st.cur, range, privateName := st.privateName
      inIterExpr := (st.scopes[st.cur]'st.hcur).inIterExpr }
  set ({ st with
    scopes := (st.scopes.modify st.cur fun p =>
      { p with children := p.children.push id }).push child
    cur := id
    hcur := by simp [hid]
    hord := st.hord.push_child st.hcur (fun p => { p with children := p.children.push id })
      (fun _ => rfl) (fun _ => rfl) child rfl rfl } : CollectState)

/-- Make the parent of the current scope current.  After `enter`, this is the scope that was
current before it.  The module has no parent: leaving it is an internal error. -/
private def leave : CollectM Unit :=
  modify fun st =>
    match hp : (st.scopes[st.cur]'st.hcur).parent with
    | some q =>
      have hq := (st.hord st.cur st.hcur).1 q hp
      have hc := st.hcur
      { st with cur := q, hcur := Nat.lt_trans hq hc }
    | none =>
      let d : Diagnostic :=
        { kind := .internal, message := "the module scope was left", range := .none }
      { st with diagnostics := st.diagnostics.push d }

/-- Bind each parameter of `args`, recording the signature: `symtable_visit_arguments`.
CPython adds positional-only, positional and keyword-only parameters, then `*args`, then
`**kwargs`. -/
private def visitParams (args : arguments SourceRange) : CollectM Unit := do
  let .mk_arguments _ posonly pos vararg kwonly _ kwarg _ := args
  let one (kind : ParamKind) (a : arg SourceRange) : CollectM Param := do
    let .mk_arg sr ⟨_, name⟩ _ _ := a
    let name ← mangled name
    addDef name { param := true } sr
    return { name, kind, range := sr }
  let posonly ← posonly.val.mapM (one .posOnly)
  let pos ← pos.val.mapM (one .positional)
  let kwonly ← kwonly.val.mapM (one .kwOnly)
  let vararg ← vararg.val.mapM (one .varPositional)
  let kwarg ← kwarg.val.mapM (one .varKeyword)
  let params := posonly ++ pos ++ vararg.toArray ++ kwonly ++ kwarg.toArray
  modifyScope (← get).cur fun p => { p with params }

/-- Bind one alias of an `import` or `from … import`.  `fromModule` is the module of an
absolute `from` import; `none` for `import`. -/
private def visitAlias (a : alias SourceRange) (fromModule : Option String)
    (relative : Bool) (stmtRange : SourceRange) : CollectM Unit := do
  let .mk_alias sr ⟨_, name⟩ ⟨_, asname⟩ := a
  let asname := asname.map (·.val)
  if name == "*" then
    if (← curScope).kind != .module then
      syntaxError "import * only allowed at module level" stmtRange
    unsupported "'import *' is not supported" sr
    return
  let bound := asname.getD (name.takeWhile (· != '.')).toString
  addDef bound { imported := true } sr
  if relative then return
  let target : ImportTarget := match fromModule, asname with
    | some m, _ => .member m name
    | none, some _ => .module name
    | none, none => .module bound
  let loads := fromModule.getD name
  let st ← get
  let i : Import :=
    { scope := st.cur, name := mangle st.privateName bound, target, loads, range := sr }
  set { st with imports := st.imports.push i }

/-- Where the walk up from scope `s` for the walrus target `name` stops, as
`symtable_extend_namedexpr_scope` walks: past comprehensions, to the first other scope. -/
private inductive WalrusStop where
  /-- A comprehension iterates over `name`. -/
  | rebindsIteration
  /-- The function or lambda `s`. -/
  | function (s : ScopeId)
  | module
  | classBody
  /-- No enclosing scope was found.  This does not happen: every comprehension has a
  parent. -/
  | none

/-- The walk up from scope `s` for the walrus target `name`, by recursion on the scope id:
each parent comes before its scope. -/
private def walrusStop (ps : Array Pending) (h : Ordered Pending.parent Pending.children ps)
    (name : String) (s : ScopeId) : WalrusStop :=
  if hs : s < ps.size then
    let p := ps[s]
    match p.kind with
    | .comprehension | .inlinedComprehension =>
      if (p.uses[name]?.map fun u => u.compIter && u.assigned).getD false then .rebindsIteration
      else
        match hq : p.parent with
        | some q => walrusStop ps h name q
        | none => .none
    | .function | .lambda => .function s
    | .module => .module
    | .classBody => .classBody
  else .none
termination_by s
decreasing_by exact (h s hs).1 q hq

/-- Find the scope a walrus inside a comprehension binds in, and bind it there:
`symtable_extend_namedexpr_scope`. -/
private def extendNamedExprScope (name : String) (range : SourceRange) : CollectM Unit := do
  let name ← mangled name
  let st ← get
  let cur := st.cur
  match walrusStop st.scopes st.hord name cur with
  | .rebindsIteration =>
    syntaxError s!"assignment expression cannot rebind comprehension iteration variable '{name}'"
      range
  | .function s =>
    if (← usesIn s name).declaredGlobal then
      addDefIn cur name { declaredGlobal := true } range
    else
      addDefIn cur name { declaredNonlocal := true } range
    recordDirective cur name range
    addDefIn s name { assigned := true } range
  | .module =>
    addDefIn cur name { declaredGlobal := true } range
    recordDirective cur name range
    addDefIn 0 name { declaredGlobal := true } range
  | .classBody =>
    syntaxError "assignment expression within a comprehension cannot be used in a class body"
      range
  | .none => report .internal s!"no scope encloses the comprehension that binds '{name}'" range

/-- The names a `match` pattern captures, with their ranges. -/
private def patternCaptures : pattern SourceRange → Array (String × SourceRange)
  | .MatchValue .. | .MatchSingleton .. => #[]
  | .MatchSequence _ ps => ps.val.flatMap patternCaptures
  | .MatchMapping sr _ ps rest =>
    ps.val.flatMap patternCaptures ++ (rest.val.map fun n => (n.val, sr)).toArray
  | .MatchClass _ _ ps _ kps =>
    ps.val.flatMap patternCaptures ++ kps.val.flatMap patternCaptures
  | .MatchStar sr n => (n.val.map fun n => (n.val, sr)).toArray
  | .MatchAs sr ⟨_, p⟩ n =>
    (match p with | some p => patternCaptures p | none => #[]) ++
      (n.val.map fun n => (n.val, sr)).toArray
  | .MatchOr _ ps => ps.val.flatMap patternCaptures
termination_by p => sizeOf p

/-- The `yield` error inside a comprehension or generator expression named `name`. -/
private def yieldInComprehension (name : String) : String :=
  match name with
  | "<listcomp>" => "'yield' inside list comprehension"
  | "<setcomp>" => "'yield' inside set comprehension"
  | "<dictcomp>" => "'yield' inside dict comprehension"
  | _ => "'yield' inside generator expression"

/-- Run `act` with `inLoop` set to `b`, restoring it afterwards. -/
private def withInLoop (b : Bool) (act : CollectM Unit) : CollectM Unit := do
  let saved := (← get).inLoop
  modify fun st => { st with inLoop := b }
  act
  modify fun st => { st with inLoop := saved }

/-- A loop body. -/
private def inLoopBody : CollectM Unit → CollectM Unit := withInLoop true

/-- A function or class body, where an enclosing loop does not count. -/
private def outsideLoop : CollectM Unit → CollectM Unit := withInLoop false

/-- Run `act` on the iteration target of the comprehension `cur`: `symtable`'s
`ste_comp_iter_target`. -/
private def withIterTarget (cur : ScopeId) (act : CollectM Unit) : CollectM Unit := do
  modifyScope cur fun p => { p with inIterTarget := true }
  act
  modifyScope cur fun p => { p with inIterTarget := false }

mutual

private def visitExpr (e : expr SourceRange) : CollectM Unit := do
  match e with
  | .BoolOp _ _ vs => for v in vs.val do visitExpr v
  | .NamedExpr sr target value =>
    if (← curScope).inIterExpr > 0 then
      syntaxError "assignment expression cannot be used in a comprehension iterable expression"
        sr
    if (← curScope).kind.isComprehension then
      if let .Name _ ⟨_, name⟩ _ := target then
        extendNamedExprScope name sr
    visitExpr value
    visitExpr target
  | .BinOp _ l _ r => visitExpr l; visitExpr r
  | .UnaryOp _ _ x => visitExpr x
  | .Lambda sr args body =>
    visitDefaults args
    enter .lambda "<lambda>" sr
    visitParams args
    visitExpr body
    leave
  | .IfExp _ c t f => visitExpr c; visitExpr t; visitExpr f
  | .Dict _ keys values =>
    for _hk : k in keys.val do
      match k, _hk with
      | .some_expr _ k, _hk => visitExpr k
      | .missing_expr _, _ => pure ()
    for v in values.val do visitExpr v
  | .Set _ elts => for x in elts.val do visitExpr x
  | .ListComp sr elt gens =>
    visitComprehension sr .inlinedComprehension "<listcomp>" gens.val elt none
  | .SetComp sr elt gens =>
    visitComprehension sr .inlinedComprehension "<setcomp>" gens.val elt none
  | .DictComp sr k v gens =>
    visitComprehension sr .inlinedComprehension "<dictcomp>" gens.val k (some v)
  | .GeneratorExp sr elt gens =>
    visitComprehension sr .comprehension "<genexpr>" gens.val elt none
  | .Await _ x => visitExpr x
  | .YieldFrom sr x => visitExpr x; checkYield "'yield from'" sr
  | .Yield sr ⟨_, x⟩ =>
    if let some x := x then visitExpr x
    checkYield "'yield'" sr
  | .Compare _ l _ rs => visitExpr l; for r in rs.val do visitExpr r
  | .Call _ f args kws =>
    visitExpr f
    for a in args.val do visitExpr a
    for _hk : k in kws.val do
      match k, _hk with
      | .mk_keyword _ _ v, _hk =>
        visitExpr v
    checkKeywords kws.val
  | .FormattedValue _ v _ ⟨_, spec⟩ =>
    visitExpr v
    if let some s := spec then visitExpr s
  | .Interpolation _ v _ _ ⟨_, spec⟩ =>
    visitExpr v
    if let some s := spec then visitExpr s
  | .JoinedStr _ vs | .TemplateStr _ vs => for v in vs.val do visitExpr v
  | .Constant .. => pure ()
  | .Attribute _ v _ _ => visitExpr v
  | .Subscript _ v i _ => visitExpr v; visitExpr i
  | .Starred _ v _ => visitExpr v
  | .Name sr ⟨_, name⟩ ctx =>
    match ctx with
    | .Load _ =>
      addDef name { referenced := true } sr
      -- `super()` reads the implicit `__class__` cell.
      if (← curScope).kind.isFunctionLike && name == "super" then
        addDef "__class__" { referenced := true } sr
    | _ => addDef name { assigned := true } sr
  | .List _ elts _ | .Tuple _ elts _ => for x in elts.val do visitExpr x
  | .Slice _ ⟨_, lo⟩ ⟨_, hi⟩ ⟨_, step⟩ =>
    if let some x := lo then visitExpr x
    if let some x := hi then visitExpr x
    if let some x := step then visitExpr x
termination_by sizeOf e

/-- `yield` (`what`) is allowed only in a function, and not in a comprehension or generator
expression.  CPython's compiler reports the first, its symbol table the second. -/
private def checkYield (what : String) (sr : SourceRange) : CollectM Unit := do
  let p ← curScope
  if p.kind.isComprehension then syntaxError (yieldInComprehension p.name) sr
  else if p.kind matches .module | .classBody then compilerError s!"{what} outside function" sr
  else
    let earlier := match p.generator with
      | some r => decide (sr.start < r.start)
      | none => true
    if earlier then modifyScope (← get).cur fun p => { p with generator := some sr }

/-- The defaults of `args`, which the enclosing scope evaluates. -/
private def visitDefaults (args : arguments SourceRange) : CollectM Unit := do
  let .mk_arguments _ _ _ _ _ kwDefaults _ defaults := args
  for d in defaults.val do visitExpr d
  for _hd : d in kwDefaults.val do
    match d, _hd with
    | .some_expr _ d, _hd => visitExpr d
    | .missing_expr _, _ => pure ()
termination_by sizeOf args

/-- The annotation of the parameter `a`, if it has one. -/
private def visitArgAnnotation (a : arg SourceRange) : CollectM Unit := do
  let .mk_arg _ _ ⟨_, ann⟩ _ := a
  if let some t := ann then visitExpr t

/-- `symtable_handle_comprehension`: the enclosing scope evaluates the outermost iterable;
everything else is in the comprehension's scope, of kind `kind`. -/
private def visitComprehension (sr : SourceRange) (kind : ScopeKind) (name : String)
    (gens : Array (comprehension SourceRange)) (elt : expr SourceRange)
    (value : Option (expr SourceRange)) : CollectM Unit := do
  match hg : (gens[0]? : Option (comprehension SourceRange)) with
  | none => return
  | some (comprehension.mk_comprehension _ target iter ifs _) =>
    have hsize : sizeOf target + sizeOf iter + sizeOf ifs < sizeOf gens := by
      have hmem := Array.sizeOf_lt_of_mem (Array.mem_of_getElem? hg); simp at hmem; omega
    let outer := (← get).cur
    modifyScope outer fun p => { p with inIterExpr := p.inIterExpr + 1 }
    visitExpr iter
    modifyScope outer fun p => { p with inIterExpr := p.inIterExpr - 1 }
    enter kind name sr
    let cur := (← get).cur
    addDefIn cur ".0" { param := true } sr
    let dotZero : Param := { name := ".0", kind := .positional, range := sr }
    modifyScope cur fun p => { p with params := #[dotZero] }
    withIterTarget cur (visitExpr target)
    checkTarget target
    for c in ifs.val do visitExpr c
    for h : i in [1:gens.size] do
      have hlt := Array.sizeOf_getElem gens i (by get_elem_tactic)
      match hg : gens[i] with
      | .mk_comprehension _ target iter ifs _ =>
        have hsize : sizeOf target + sizeOf iter + sizeOf ifs < sizeOf gens := by
          rw [hg] at hlt; simp at hlt; omega
        withIterTarget cur (visitExpr target)
        modifyScope cur fun p => { p with inIterExpr := p.inIterExpr + 1 }
        visitExpr iter
        modifyScope cur fun p => { p with inIterExpr := p.inIterExpr - 1 }
        checkTarget target
        for c in ifs.val do visitExpr c
    if let some v := value then visitExpr v
    visitExpr elt
    leave
termination_by sizeOf gens + sizeOf elt + sizeOf value

/-- Visit the expressions a `match` pattern evaluates: values, mapping keys and classes. -/
private def visitPatternExprs (p : pattern SourceRange) : CollectM Unit := do
  match p with
  | .MatchValue _ e => visitExpr e
  | .MatchSingleton .. | .MatchStar .. => pure ()
  | .MatchSequence _ ps | .MatchOr _ ps => for q in ps.val do visitPatternExprs q
  | .MatchMapping _ keys ps _ =>
    for k in keys.val do visitExpr k
    for q in ps.val do visitPatternExprs q
  | .MatchClass _ cls ps _ kps =>
    visitExpr cls
    for q in ps.val do visitPatternExprs q
    for q in kps.val do visitPatternExprs q
  | .MatchAs _ ⟨_, q⟩ _ => if let some q := q then visitPatternExprs q
termination_by sizeOf p

private def visitStmts (ss : Array (stmt SourceRange)) : CollectM Unit := do
  for s in ss do visitStmt s
termination_by sizeOf ss

private def visitStmt (s : stmt SourceRange) : CollectM Unit := do
  match s with
  | .FunctionDef sr ⟨_, name⟩ args body decorators returns _ typeParams
  | .AsyncFunctionDef sr ⟨_, name⟩ args body decorators returns _ typeParams =>
    if !typeParams.val.isEmpty then unsupported "type parameters are not supported" sr
    addDef name { assigned := true } sr
    -- In the order of 3.12's symbol table, which records the child scopes in that order.
    visitDefaults args
    for d in decorators.val do visitExpr d
    unless (← get).futureAnnotations do
      let .mk_arguments _ ⟨_, posOnly⟩ ⟨_, pos⟩ ⟨_, varPos⟩ ⟨_, kwOnly⟩ _ ⟨_, varKw⟩ _ := args
      for a in posOnly do visitArgAnnotation a
      for a in pos do visitArgAnnotation a
      if let some a := varPos then visitArgAnnotation a
      if let some a := varKw then visitArgAnnotation a
      for a in kwOnly do visitArgAnnotation a
      if let ⟨_, some r⟩ := returns then visitExpr r
    enter .function name sr
    visitParams args
    outsideLoop (visitStmts body.val)
    leave
  | .ClassDef sr ⟨_, name⟩ bases kws body decorators typeParams =>
    if !typeParams.val.isEmpty then unsupported "type parameters are not supported" sr
    addDef name { assigned := true } sr
    for b in bases.val do visitExpr b
    for _hk : k in kws.val do
      match k, _hk with
      | .mk_keyword _ _ v, _hk =>
        visitExpr v
    checkKeywords kws.val
    for d in decorators.val do visitExpr d
    let outerPrivate := (← get).privateName
    modify fun st => { st with privateName := some name }
    enter .classBody name sr
    outsideLoop (visitStmts body.val)
    leave
    modify fun st => { st with privateName := outerPrivate }
  | .Return sr ⟨_, v⟩ =>
    if (← curScope).kind matches .module | .classBody then
      compilerError "'return' outside function" sr
    if let some v := v then visitExpr v
  | .Delete _ ts => for t in ts.val do visitExpr t
  | .Assign _ ts v _ =>
    for t in ts.val do visitExpr t
    visitExpr v
    ts.val.forM checkTarget
  | .TypeAlias sr n _ _ =>
    unsupported "'type' statements are not supported" sr
    visitExpr n
  | .AugAssign _ t _ v => visitExpr t; visitExpr v
  | .AnnAssign sr target ann ⟨_, value⟩ simple =>
    match target with
    | .Name nsr ⟨_, name⟩ _ =>
      let m ← mangled name
      let cur ← usesIn (← get).cur m
      let simple := simple.value != 0
      if simple && (← get).cur != 0 && (cur.declaredGlobal || cur.declaredNonlocal) then
        let what := if cur.declaredGlobal then "global" else "nonlocal"
        syntaxError s!"annotated name '{name}' can't be {what}" sr
      if simple then addDef name { annotated := true, assigned := true } nsr
      else if value.isSome then addDef name { assigned := true } nsr
    | _ => visitExpr target
    -- `symtable` visits the annotation, then the value; CPython 3.12 evaluates it in a module
    -- or class body.
    unless (← get).futureAnnotations do visitExpr ann
    if let some v := value then visitExpr v
  | .For _ t it body orelse _ | .AsyncFor _ t it body orelse _ =>
    visitExpr t
    visitExpr it
    checkTarget t
    inLoopBody (visitStmts body.val)
    visitStmts orelse.val
  | .While _ c body orelse =>
    visitExpr c
    inLoopBody (visitStmts body.val)
    visitStmts orelse.val
  | .If _ c body orelse =>
    visitExpr c
    visitStmts body.val
    visitStmts orelse.val
  | .With _ items body _ | .AsyncWith _ items body _ =>
    for _hi : i in items.val do
      match i, _hi with
      | .mk_withitem _ ctx ⟨_, vars⟩, _hi =>
        visitExpr ctx
        if let some t := vars then visitExpr t; checkTarget t
    visitStmts body.val
  | .Match sr subject cases =>
    unsupported "'match' is not supported" sr
    visitExpr subject
    for _hc : c in cases.val do
      match c, _hc with
      | .mk_match_case _ p ⟨_, guard⟩ body, _hc =>
        visitPatternExprs p
        for (n, nsr) in patternCaptures p do
          addDef n { assigned := true } nsr
        if let some g := guard then visitExpr g
        visitStmts body.val
  | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
    if let some e := exc then visitExpr e
    if let some c := cause then visitExpr c
  | .Try _ body handlers orelse finalbody | .TryStar _ body handlers orelse finalbody =>
    visitStmts body.val
    visitStmts orelse.val
    let hs := handlers.val
    for h : i in [:hs.size] do
      let .ExceptHandler hsr ty _ _ := hs[i]
      if ty.val.isNone && i + 1 < hs.size then
        -- CPython reports only the first.
        compilerError "default 'except:' must be last" hsr
        break
    for _hh : h in handlers.val do
      match h, _hh with
      | .ExceptHandler hsr ⟨_, ty⟩ name hbody, _hh =>
        if let some t := ty then visitExpr t
        if let some n := name.val then addDef n.val { assigned := true } hsr
        visitStmts hbody.val
    visitStmts finalbody.val
  | .Assert _ t ⟨_, m⟩ =>
    visitExpr t
    if let some m := m then visitExpr m
  | .Import sr aliases => aliases.val.forM (visitAlias · none false sr)
  | .ImportFrom sr modName aliases level =>
    let level := (level.val.map (·.value)).getD 0
    let relative := level != 0 || modName.val.isNone
    if relative then unsupported "relative imports are not supported" sr
    let m := modName.val.map (·.val)
    aliases.val.forM (visitAlias · (if relative then none else m) relative sr)
  | .Global sr names => names.val.forM fun n => declare true n.val sr
  | .Nonlocal sr names => names.val.forM fun n => declare false n.val sr
  | .Expr _ v => visitExpr v
  -- CPython's compiler reports these; its symbol table does not.
  | .Break sr => unless (← get).inLoop do compilerError "'break' outside loop" sr
  | .Continue sr => unless (← get).inLoop do compilerError "'continue' not properly in loop" sr
  | .Pass _ => pure ()
termination_by sizeOf s

/-- `global name` (`isGlobal`) or `nonlocal name` at `sr`. -/
private def declare (isGlobal : Bool) (name : String) (sr : SourceRange) :
    CollectM Unit := do
  let kw := if isGlobal then "global" else "nonlocal"
  let m ← mangled name
  let cur := (← get).cur
  let u ← usesIn cur m
  if u.param then syntaxError s!"name '{name}' is parameter and {kw}" sr
  else if u.referenced then syntaxError s!"name '{name}' is used prior to {kw} declaration" sr
  else if u.annotated then syntaxError s!"annotated name '{name}' can't be {kw}" sr
  else if u.assigned then
    syntaxError s!"name '{name}' is assigned to before {kw} declaration" sr
  addDefIn cur m (if isGlobal then { declaredGlobal := true } else { declaredNonlocal := true })
    sr
  recordDirective cur m sr

end

/-! ## Classifying names

The second phase mirrors `analyze_block`: a preorder walk passing down the names enclosing
functions bind, and passing up the free names nested scopes use.  After classifying an
inlined comprehension, it merges the comprehension's names into the enclosing scope:
`inline_comprehension`. -/

/-- The state of the analysis of `n` scopes, each indexed by scope. -/
private structure Analysis (n : Nat) where
  /-- The scopes' names and flags, extended with those of inlined comprehensions. -/
  pending : Vector Pending n
  scopes : Vector (Std.HashMap String NameScope) n
  /-- Free names a scope gets only to pass a cell on to a nested scope. -/
  passThrough : Vector (Array String) n
  freeClass : Vector (Std.HashSet String) n
  needsClassCell : Vector Bool n
  diagnostics : Array Diagnostic := #[]

private abbrev AnalyzeM (n : Nat) := StateM (Analysis n)

/-- `v` with its `i`th element replaced by `f` of it.  `f` gets the element unshared when `v`
is unshared. -/
private def modifyAt {α : Type} {n : Nat} (v : Vector α n) (i : Fin n) (f : α → α) :
    Vector α n :=
  ⟨v.toArray.modify i f, by simp⟩

/-- The children of `s`, with each inlined comprehension replaced by its own children,
recursively: CPython's `ste_children` after splicing. -/
private def splicedChildren (tree : Array Pending)
    (h : Ordered Pending.parent Pending.children tree) (s : ScopeId) : Array (Fin tree.size) :=
  if hs : s < tree.size then
    tree[s].children.attach.flatMap fun ⟨c, hc⟩ =>
      have hlt := (h s hs).2 c hc
      if tree[c].kind == ScopeKind.inlinedComprehension then splicedChildren tree h c
      else #[⟨c, hlt.2⟩]
  else #[]
termination_by tree.size - s

/-- Merge the names of the inlined comprehension `c`, just classified, into its parent `s`.
`scopes` is the classification of `s` so far and `compFree` the free names of `c`; return
both updated, with the names `c` makes cells added to `cells`.

A name new to `s` is added with the comprehension's flags and classification.  A free
name that `s` binds is no longer free, unless a scope nested in `c` uses it or `s` is a
class body. -/
private def inlineComprehension (tree : Array Pending)
    (htree : Ordered Pending.parent Pending.children tree) (s c : Fin tree.size)
    (scopes : Std.HashMap String NameScope)
    (compFree cells : Std.HashSet String) :
    AnalyzeM tree.size
      (Std.HashMap String NameScope × Std.HashSet String × Std.HashSet String) := do
  let a ← get
  let comp := a.pending[c]
  let compScopes := a.scopes[c]
  let parentKind := a.pending[s].kind
  let nested := splicedChildren tree htree c
  let mut scopes := scopes
  let mut compFree := compFree
  let mut cells := cells
  let mut dropClass := false
  for k in comp.names ++ a.passThrough[c] do
    let flags := (comp.uses[k]?).getD {}
    if flags.param then continue
    let mut scope := (compScopes[k]?).getD .globalImplicit
    if scope == .cell || flags.compCell then cells := cells.insert k
    -- `__class__` is never free in a class body.
    if scope == .free && parentKind == .classBody && k == "__class__" then
      scope := .globalImplicit
      compFree := compFree.erase k
      dropClass := true
    match (← get).pending[s].uses[k]? with
    | none =>
      modify fun a => { a with pending := modifyAt a.pending s fun p =>
        { p with uses := p.uses.insert k flags, names := p.names.push k } }
      scopes := scopes.insert k scope
    | some existing =>
      let freeInNested := nested.any fun m => a.scopes[m][k]? == some .free
      if existing.bound && !freeInNested && parentKind != .classBody then
        compFree := compFree.erase k
  if dropClass then
    modify fun a => { a with
      pending := modifyAt a.pending c fun p =>
        { p with names := p.names.erase "__class__", uses := p.uses.erase "__class__" }
      scopes := modifyAt a.scopes c (·.erase "__class__")
      passThrough := modifyAt a.passThrough c (·.erase "__class__") }
  return (scopes, compFree, cells)

/-- Classify the names of scope `s` and its descendants.  `bound` is the set of names the
enclosing functions bind, `none` for the module.  Return the free names of `s` and its
descendants that `s` does not bind. -/
private def analyzeBlock (tree : Array Pending)
    (htree : Ordered Pending.parent Pending.children tree) (s : ScopeId)
    (bound : Option (Std.HashSet String)) : AnalyzeM tree.size (Std.HashSet String) := do
  if hs : s < tree.size then
    let p := (← get).pending[s]
    let err (msg : String) (name : String) : AnalyzeM tree.size Unit :=
      let range := (p.directives[name]?).getD p.range
      let d : Diagnostic := { kind := .syntaxError, message := msg, range }
      modify fun a => { a with diagnostics := a.diagnostics.push d }
    let mut result : Std.HashMap String NameScope := {}
    let mut locals : Std.HashSet String := {}
    let mut free : Std.HashSet String := {}
    let mut boundHere := bound
    for name in p.names do
      let u := (p.uses[name]?).getD {}
      if u.declaredGlobal then
        if u.declaredNonlocal then err s!"name '{name}' is nonlocal and global" name
        result := result.insert name .globalExplicit
        boundHere := boundHere.map (·.erase name)
      else if u.declaredNonlocal then
        match bound with
        | none => err "nonlocal declaration not allowed at module level" name
        | some b =>
          if !b.contains name then err s!"no binding for nonlocal '{name}' found" name
        result := result.insert name .free
        -- An unbound `nonlocal` is an error; do not pass it on.
        if (bound.map (·.contains name)).getD false then free := free.insert name
      else if u.bound then
        result := result.insert name .local
        locals := locals.insert name
      else if (bound.map (·.contains name)).getD false then
        result := result.insert name .free
        free := free.insert name
      else
        result := result.insert name .globalImplicit
    -- A class body's bindings are invisible to nested scopes.
    let newBound : Std.HashSet String :=
      if p.kind == .classBody then (bound.getD {}).insert "__class__"
      else
        let outer := boundHere.getD {}
        if p.kind.isFunctionLike then locals.fold (·.insert ·) outer else outer
    let mut childFree : Std.HashSet String := {}
    let mut cells : Std.HashSet String := {}
    -- Phase 2 never changes the links, so the children are those of phase 1's tree.
    for hc : c in tree[s].children do
      have hlt := (htree s hs).2 c hc
      let mut f ← analyzeBlock tree htree c (some newBound)
      if tree[c].kind == ScopeKind.inlinedComprehension then
        let r ← inlineComprehension tree htree ⟨s, hs⟩ ⟨c, hlt.2⟩ result f cells
        result := r.1
        f := r.2.1
        cells := r.2.2
      childFree := f.fold (·.insert ·) childFree
    -- The names of inlined comprehensions are now names of `s`.
    let p := (← get).pending[s]
    if p.kind.isFunctionLike then
      for name in p.names do
        if result[name]? == some .local && (childFree.contains name || cells.contains name)
        then
          result := result.insert name .cell
          childFree := childFree.erase name
    else if p.kind == .classBody && childFree.contains "__class__" then
      childFree := childFree.erase "__class__"
      modify fun a => { a with needsClassCell := a.needsClassCell.set s true }
    let markCell (us : Std.HashMap String Uses) (n : String) :=
      us.modify n fun u => { u with compCell := true }
    let p := { p with uses := cells.fold markCell p.uses }
    modify fun a => { a with pending := a.pending.set s p }
    -- Free names of nested scopes: a class using the name marks it; a scope between the
    -- binding and the use passes the cell on.
    let mut extra : Array String := #[]
    let mut freeClass : Std.HashSet String := {}
    for name in childFree.toArray.qsort (· < ·) do
      if p.uses.contains name then
        if p.kind == .classBody then freeClass := freeClass.insert name
        continue
      -- Only a name an enclosing function binds is passed on; the module binds none.
      if !(boundHere.map (·.contains name)).getD false then continue
      extra := extra.push name
      result := result.insert name .free
    let resultFinal := result
    modify fun a => { a with scopes := a.scopes.set s resultFinal
                             passThrough := a.passThrough.set s extra
                             freeClass := a.freeClass.set s freeClass }
    return childFree.fold (·.insert ·) free
  else return {}
termination_by tree.size - s

/-- CPython's `__qualname__` for each scope of `tree`, given the scopes' classifications.  A
scope in an inlined comprehension is named after the scope the comprehension is inlined into. -/
private def qualnames (tree : Array Pending) (htree : Ordered Pending.parent Pending.children tree)
    (classes : Vector (Std.HashMap String NameScope) tree.size) : Vector String tree.size :=
    Id.run do
  let mut out : Vector String tree.size := Vector.replicate tree.size ""
  -- For each scope, the nearest scope that is not an inlined comprehension.
  let mut frame : Vector (Fin tree.size) tree.size := Vector.ofFn id
  for h : i in [0:tree.size] do
    have hi : i < tree.size := h.upper
    let p := tree[i]
    match hq : p.parent with
    | none => pure ()
    | some q =>
      have hqi : q < tree.size := Nat.lt_trans ((htree i hi).1 q hq) hi
      let q : Fin tree.size := if p.kind == .inlinedComprehension then ⟨q, hqi⟩ else frame[q]
      if p.kind == .inlinedComprehension then frame := frame.set i frame[q]
      let parent := tree[q]
      -- A `def` or `class` whose name the parent declares `global` is top level.
      let forceGlobal := (p.kind == .function || p.kind == .classBody) &&
        classes[q].get? (mangle parent.privateName p.name) == some .globalExplicit
      if parent.kind == .module || forceGlobal then out := out.set i p.name
      else
        let base := out[q]
        let base := if parent.kind == .function || parent.kind == .lambda then
          s!"{base}.<locals>" else base
        out := out.set i s!"{base}.{p.name}"
  return out

public section

/-- Whether the module has `from __future__ import annotations`. -/
def hasFutureAnnotations (stmts : Array (stmt SourceRange)) : Bool :=
  stmts.any fun
    | .ImportFrom _ m aliases _ =>
      (m.val.map (·.val)) == some "__future__" && aliases.val.any (·.name == "annotations")
    | _ => false

/-- Classify every name of the module `stmts` and resolve its imports. -/
def analyze (stmts : Array (stmt SourceRange)) : Table := Id.run do
  let root : Pending :=
    { kind := .module, name := "<module>", parent := none, range := .none, privateName := none }
  let ((), st) := (visitStmts stmts).run
    { scopes := #[root], futureAnnotations := hasFutureAnnotations stmts, hcur := by simp
      hord := by intro i hi; simp at hi; subst hi; simp [root] }
  let n := st.scopes.size
  let init : Analysis n :=
    { pending := ⟨st.scopes, rfl⟩, scopes := Vector.replicate n {}
      passThrough := Vector.replicate n #[], freeClass := Vector.replicate n {}
      needsClassCell := Vector.replicate n false }
  let (_, a) := (analyzeBlock st.scopes st.hord 0 none).run init
  -- Phase 2 does not change the `kind`, `name`, `privateName` or `parent` that `qualnames` reads.
  let quals := qualnames st.scopes st.hord a.scopes
  -- The links come from phase 1's tree, which phase 2 does not change; the rest from phase 2.
  let scopes := st.scopes.mapFinIdx fun i t hi =>
    let p := a.pending[i]
    let names := p.names ++ a.passThrough[i]
    let symbols := names.map fun name =>
      let uses := (p.uses[name]?).getD {}
      { name
        scope := (a.scopes[i][name]?).getD .globalImplicit
        uses := { uses with freeClass := a.freeClass[i].contains name } : Symbol }
    { kind := p.kind, name := p.name, qualname := quals[i], parent := t.parent
      children := t.children, params := p.params, symbols, range := p.range
      privateName := p.privateName, needsClassCell := a.needsClassCell[i]
      generator := p.generator : Scope }
  -- As in CPython, the symbol table's errors, from the walk and then the analysis, come before
  -- the compiler's.
  let (compiler, walk) := st.diagnostics.partition (·.compiler)
  have ordered : Ordered Scope.parent Scope.children scopes := by
    intro i hi
    have hi' : i < st.scopes.size := by simpa [scopes] using hi
    simpa [scopes] using st.hord i hi'
  have scopes_ne : 0 < scopes.size := by
    simpa [scopes] using Nat.lt_of_le_of_lt (Nat.zero_le _) st.hcur
  return { scopes, imports := st.imports, diagnostics := walk ++ a.diagnostics ++ compiler,
           ordered, scopes_ne }

end -- public section

/-! ## Printing -/

private def NameScope.text : NameScope → String
  | .local => "local"
  | .cell => "cell"
  | .free => "free"
  | .globalExplicit => "global explicit"
  | .globalImplicit => "global implicit"

private def Uses.words (u : Uses) : Array String :=
  #[(u.param, "parameter"), (u.assigned, "assigned"), (u.imported, "imported"),
    (u.referenced, "referenced"), (u.declaredGlobal, "declared_global"),
    (u.declaredNonlocal, "nonlocal"), (u.annotated, "annotated"), (u.compIter, "comp_iter"),
    (u.freeClass, "free_class"), (u.compCell, "comp_cell")].filterMap fun (b, w) =>
    if b then some w else none

private def Symbol.line (s : Symbol) : String :=
  let ws := s.uses.words
  let suffix := if ws.isEmpty then "" else s!" ({", ".intercalate ws.toList})"
  s!"{s.name}: {s.scope.text}{suffix}"

private def ScopeKind.text : ScopeKind → String
  | .module => "module"
  | .function => "function"
  | .lambda => "lambda"
  | .classBody => "class"
  | .comprehension => "generator expression"
  | .inlinedComprehension => "inlined comprehension"

/-- A signature in Python's notation: `a, /, b, *args, c, **kw`. -/
private def signature (ps : Array Param) : String := Id.run do
  let mut out : Array String := #[]
  let mut starred := false
  for h : i in [0:ps.size] do
    let p := ps[i]
    match p.kind with
    | .posOnly =>
      out := out.push p.name
      if ps[i+1]?.all (·.kind != .posOnly) then out := out.push "/"
    | .positional => out := out.push p.name
    | .varPositional => out := out.push s!"*{p.name}"; starred := true
    | .kwOnly =>
      if !starred then out := out.push "*"; starred := true
      out := out.push p.name
    | .varKeyword => out := out.push s!"**{p.name}"
  return ", ".intercalate out.toList

private def Import.line (i : Import) : String :=
  let target := match i.target with
    | .module path => s!"module {path}"
    | .member m n => s!"member {n} of {m}"
  let loads := if i.loads == i.target.qualified || i.target matches .member .. then ""
    else s!" (loads {i.loads})"
  s!"import {i.name}: {target}{loads}"

namespace Table

/-- The lines for scope `s` and its descendants, by recursion on the scope id: each child
comes after its scope. -/
private def scopeLines (t : Table) (s : ScopeId) (hs : s < t.scopes.size) (indent : String) :
    Array String := Id.run do
  let sc := t.scopes[s]
  let title := if sc.kind == .module then "module" else s!"{sc.kind.text} {sc.qualname}"
  let cell := if sc.needsClassCell then " (needs __class__ cell)" else ""
  let mut out := #[indent ++ title ++ cell]
  let inner := indent ++ "  "
  if !sc.params.isEmpty then
    out := out.push s!"{inner}params: {signature sc.params}"
  for i in t.importsIn s do out := out.push (inner ++ i.line)
  for sym in sc.symbols do out := out.push (inner ++ sym.line)
  for hc : c in t.scopes[s].children do
    have hlt := (t.ordered s hs).2 c hc
    out := out ++ scopeLines t c hlt.2 inner
  return out
termination_by t.scopes.size - s

/-- The table as text, for golden tests: each scope with its parameters, imports and
symbols in order of first use, nested scopes indented, then the diagnostics.  Positions
are `line:column` given `fileMap`, byte offsets otherwise. -/
public def format (t : Table) (fileMap : Option Lean.FileMap := none) : String :=
  let lines := scopeLines t 0 t.scopes_ne ""
  let diags := t.diagnostics.map fun d =>
    s!"{d.kind.text} at {formatRange fileMap d.range}: {d.message}"
  let all := if diags.isEmpty then lines else lines.push "diagnostics:" ++ diags.map ("  " ++ ·)
  "\n".intercalate all.toList ++ "\n"

/-- `name` without surrounding angle brackets: the `symtable` module calls `<lambda>`
`lambda`. -/
private def symtableName (name : String) : String :=
  if name.startsWith "<" && name.endsWith ">" then
    ((name.drop 1).dropEnd 1).toString
  else name

/-- The `symtable` lines for scope `s` and its descendants, by recursion on the scope id: each
child comes after its scope.  An inlined comprehension has no lines; its children are listed in
its place. -/
private def symtableLines (t : Table) (s : ScopeId) (hs : s < t.scopes.size) (depth : Nat) :
    Array String := Id.run do
  let sc := t.scopes[s]
  if sc.kind == .inlinedComprehension then
    return t.scopes[s].children.attach.flatMap fun ⟨c, hc⟩ =>
      have hlt := (t.ordered s hs).2 c hc
      symtableLines t c hlt.2 depth
  let pad (d : Nat) := "".pushn ' ' (2 * d)
  let header := match sc.kind with
    | .module => "module top"
    | .classBody => s!"class {sc.name}"
    | _ => s!"function {symtableName sc.name}"
  let mut out := #[pad depth ++ header]
  for sym in sc.symbols.qsort (·.name < ·.name) do
    out := out.push (pad (depth + 1) ++ sym.line)
  for hc : c in t.scopes[s].children do
    have hlt := (t.ordered s hs).2 c hc
    out := out ++ symtableLines t c hlt.2 (depth + 1)
  return out
termination_by t.scopes.size - s

/-- What CPython 3.12's `symtable` module records, in the format of
`StrataPythonTest/Dyn/scope_symtable.py`: each scope with its symbols sorted by name, then
the sorted `__qualname__`s of the code objects, then of the generators if there are any.
Inlined comprehensions are not scopes there.  If CPython rejects the program, only its first
error, with the line `fileMap` gives. -/
public def symtableFormat (t : Table) (fileMap : Option Lean.FileMap := none) : String :=
  match t.syntaxErrors[0]? with
  | some d =>
    let line := match fileMap with
      | some fm => s!" (line {(fm.toPosition d.range.start).line})"
      | none => ""
    s!"error: {d.message}{line}\n"
  | none =>
    let quals := (t.scopes.toList.drop 1).filter (·.kind != .inlinedComprehension)
      |>.map (·.qualname) |>.toArray.qsort (· < ·)
    let gens := (t.scopes.filter (·.generator.isSome)).map (·.qualname) |>.qsort (· < ·)
    let lines := symtableLines t 0 t.scopes_ne 0
      |>.push s!"qualnames: {", ".intercalate quals.toList}"
    let lines := if gens.isEmpty then lines
      else lines.push s!"generators: {", ".intercalate gens.toList}"
    "\n".intercalate lines.toList ++ "\n"

end Table

end StrataPython.Dyn.PyScope
