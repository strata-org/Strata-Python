/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.Dyn.Scope
import StrataPython.Dyn.Termination

set_option autoImplicit false

/-!
# Loop-invariant markers

A module states loop invariants with `loop_invariant(lambda: P)` and `OLD(e)`, imported with
`from pyhard import loop_invariant, OLD` (`docs/PythonToDyn.md` §6.11). The translator drops the
marker calls, which is faithful only if the marker names surely are `pyhard`'s markers wherever
the module calls them. `analyze` checks the module-wide half of that:

* the import is one `from pyhard import …` of marker names only, with no `as`, at the module's
  top level, after nothing but a docstring and `from __future__` imports, so that the names are
  bound before any marker call can run;
* no other import loads `pyhard`;
* no scope of the module binds a marker name, by any binding form that the scope pass knows,
  and no scope declares one `global` or `nonlocal`.

The translator checks where each marker call stands and its shape, and the guard that it puts
before the loop checks at run time that `loop_invariant` is still the marker, since other code,
such as another module, can rebind it where no scope pass sees it.
-/

namespace StrataPython.Dyn.PyMarkers

open StrataDDM (SourceRange)
open StrataPython (stmt expr alias keyword comprehension)
open StrataPython.Dyn.PyScope

public section

/-- The module that defines the markers. -/
def markerModule : String := "pyhard"

/-- The names that `markerModule` defines as markers. -/
def allMarkers : Array String := #["loop_invariant", "OLD"]

/-- The markers that a module imports. -/
structure Markers where
  /-- The marker names that the module's import binds, in the import's order. -/
  names : Array String
  /-- The names of `invariantBuiltins` that some scope of the module binds, or declares
  `global` or `nonlocal`: an invariant can't use them as the builtins. -/
  reboundBuiltins : Array String := #[]
  deriving Repr, Inhabited

/-- Whether `name` is one of the module's markers. -/
def Markers.has (m : Markers) (name : String) : Bool := m.names.contains name

/-- Whether an import of `m` loads the marker module or one of its submodules. -/
def loadsMarkerModule (m : String) : Bool :=
  m == markerModule || m.startsWith (markerModule ++ ".")

/-- A rejection of a misuse of the markers, worded as the translator's other rejections. -/
def unsupported (what : String) (range : SourceRange) : Diagnostic :=
  { kind := .unsupported, message := s!"{what} is not supported", range }

/-- Whether a program module named `m` is named like the marker module: some component of its
dotted name is `pyhard` (`pyhard`, `pyhard.x`, `pkg.pyhard`). The translator rejects such a module,
whatever it contains, as a defensive check: if PyHard's module weren't loaded first (§12.9), CPython
could import such a module in its place (§6.11). -/
def namedLikeMarkerModule (m : String) : Bool :=
  (m.splitOn ".").contains markerModule

/-- The rejection of a main script whose file is named like the marker module, `pyhard.py`: it is
translated as `__main__`, so `translate` can't see its name. A defensive check: if PyHard's module
weren't loaded first (§12.9), CPython would import the script as `pyhard` when it imports the
markers. -/
def mainFileProblem? (path : System.FilePath) : Option String :=
  -- A Python Ion file of `pyhard.py` is `pyhard.py.ion`, `pyhard.python.st.ion` or `pyhard.st.ion`.
  let name := path.fileName.getD ""
  let name := match [".python.st.ion", ".py.ion", ".st.ion", ".ion", ".py"].find? (name.endsWith ·) with
    | some sfx => (name.dropEnd sfx.length).toString
    | none => name
  if name == markerModule then
    some "a main script named pyhard.py is not supported: without PyHard's pyhard loaded first, CPython would import the script in its place"
  else none

/-- Whether `s` may come before the marker import: a docstring or a `from __future__`
import. -/
def mayPrecede (first : Bool) : stmt SourceRange → Bool
  | .Expr _ (.Constant _ (.ConString ..) _) => first
  | .ImportFrom _ m _ _ => (m.val.map (·.val)) == some "__future__"
  | _ => false

/-- The index of the first statement that `mayPrecede` doesn't allow. -/
def firstOther (stmts : Array (stmt SourceRange)) : Nat :=
  (List.range stmts.size).find? (fun i => !(stmts[i]?.map (mayPrecede (i == 0))).getD false)
    |>.getD stmts.size

/-- The marker import at `s`, if `s` is `from pyhard import …`: its aliases. -/
def markerImport? : stmt SourceRange → Option (SourceRange × Array (alias SourceRange))
  | .ImportFrom sr m aliases level =>
    if (m.val.map (·.val)) == some markerModule && (level.val.map (·.value)).getD 0 == 0 then
      some (sr, aliases.val)
    else none
  | _ => none

/-- The rebindings of the marker `name` in `t`: a range for each scope that binds it, other than
the module scope's import, or that declares it `global` or `nonlocal`.  The module scope's is
`moduleRange`. -/
def rebindings (t : Table) (name : String) (moduleRange : SourceRange) : Array SourceRange :=
  t.scopes.filterMap fun s =>
    match s.symbol? name with
    | none => none
    | some sym =>
      let u := sym.uses
      let atModule := s.kind == .module
      let bad := u.param || u.assigned || u.declaredGlobal || u.declaredNonlocal ||
        u.annotated || u.compIter || (u.imported && !atModule)
      if bad then some (if atModule then moduleRange else s.range) else none

/-- The builtins that an invariant may call, each lowered to its operation. -/
def invariantBuiltins : Array String := #["len", "isinstance", "all", "any"]

/-- Whether some scope of `t` binds `name`, or declares it `global` or `nonlocal`. -/
def boundAnywhere (t : Table) (name : String) : Bool :=
  t.scopes.any fun s => match s.symbol? name with
    | some sym => sym.uses.bound || sym.uses.declaredGlobal || sym.uses.declaredNonlocal
    | none => false

/-- Check the module-wide rules of the markers. With no `from pyhard import …` at the top, the
module has no markers, and `loop_invariant` is an ordinary name; any other import of `pyhard`
is still rejected, so that a module can't get the markers in a way the translator doesn't
recognize. -/
def analyze (stmts : Array (stmt SourceRange)) (t : Table) : Option Markers × Array Diagnostic :=
  Id.run do
  let mut ds : Array Diagnostic := #[]
  let i := firstOther stmts
  let head := stmts[i]? >>= markerImport?
  -- Every import of the marker module other than the one at the top is rejected.
  let headRanges := (head.map fun (_, as) => as.map (·.ann)).getD #[]
  for imp in t.imports do
    if loadsMarkerModule imp.loads && !headRanges.contains imp.range then
      ds := ds.push (unsupported "importing pyhard other than at the top of the module" imp.range)
  let some (importRange, aliases) := head | return (none, ds)
  let mut names : Array String := #[]
  for a in aliases do
    let .mk_alias asr ⟨_, n⟩ ⟨_, asname⟩ := a
    if !allMarkers.contains n then
      ds := ds.push (unsupported "importing names from pyhard other than loop_invariant and OLD"
        asr)
    else if asname.isSome then
      ds := ds.push (unsupported "renaming a pyhard marker" asr)
    else if names.contains n then
      ds := ds.push (unsupported "importing a pyhard marker twice" asr)
    else names := names.push n
  for n in names do
    -- The scope table keeps no position for a module-level binding, so that one is reported at
    -- the marker import; another scope's at its `def`, `class`, `lambda` or comprehension.
    for r in rebindings t n importRange do
      ds := ds.push (unsupported s!"rebinding the marker {n}" r)
    -- The module scope binds the name only by the marker import.
    if ((t.importsIn 0).filter (·.name == n)).size != 1 then
      ds := ds.push (unsupported s!"rebinding the marker {n}" importRange)
  return (some { names, reboundBuiltins := invariantBuiltins.filter (boundAnywhere t) }, ds)

/-! ## What an invariant may contain

An invariant `P` is lowered with the translator's own expression lowering into a contract region
(§6.11), which may apply no operation that writes.  `checkInvariant` admits only the constructs
whose lowering applies none: names, literals, operators, comparisons, `and`, `or`, `not`,
conditional expressions, attributes, subscripts and slices, and calls of `len`, `isinstance`,
`all` and `any`, the last two on a generator expression with one `for` clause. -/

/-- A rejection of `what` in an invariant, at `range`. -/
abbrev InvCheck := Except (String × SourceRange) Unit

/-- Reject `what` at `range`. -/
def bad (what : String) (range : SourceRange) : InvCheck := .error (what, range)

/-- The method of `e` if it is `d.items()`, `d.keys()` or `d.values()`: the method's name and `d`. -/
def dictView? : expr SourceRange → Option (String × expr SourceRange)
  | .Call _ (.Attribute _ d ⟨_, m⟩ _) args kws =>
    if args.val.isEmpty && kws.val.isEmpty && (m == "items" || m == "keys" || m == "values") then
      some (m, d)
    else none
  | _ => none

/-- What is wrong with `target`, the target of a quantifier over `iter`, where `view` is the dict
view that `iter` calls, if it calls one: a pair of names over `items()`, a name otherwise.
`mangle` gives a name as CPython stores it, private names mangled. -/
def targetProblem (mangle : String → String) (view : Option String) (target : expr SourceRange) :
    Option String :=
  -- Two names, which must differ as CPython stores them: in `for k, k in d.items()`, and in a
  -- method of `C` in `for __k, _C__k in d.items()`, CPython binds one name, to the value.
  let pair := match target with
    | .Tuple _ ⟨_, #[.Name _ ⟨_, k⟩ _, .Name _ ⟨_, v⟩ _]⟩ _ => mangle k != mangle v
    | _ => false
  let name := target matches .Name ..
  if view == some "items" then
    if pair then none else some "a quantifier over items() whose target is not two different names"
  else if name then none
  else some "a quantifier whose target is not a name in a loop invariant"

mutual

/-- Check the invariant expression `e` of a module with the markers `m`.  `nameProblem` says why
the lowering of a name would reject it, if it would, such as a marker name. -/
def checkInvariant (m : Markers) (nameProblem : String → Option String) (mangle : String → String)
    (e : expr SourceRange) :
    InvCheck := do
  match e with
  | .Name sr ⟨_, n⟩ _ => if let some what := nameProblem n then bad what sr
  | .Constant .. => pure ()
  | .BinOp _ l _ r => checkInvariant m nameProblem mangle l; checkInvariant m nameProblem mangle r
  | .UnaryOp _ _ x => checkInvariant m nameProblem mangle x
  | .BoolOp _ _ vs => for v in vs.val do checkInvariant m nameProblem mangle v
  | .Compare _ l _ rs => checkInvariant m nameProblem mangle l; for r in rs.val do checkInvariant m nameProblem mangle r
  | .IfExp _ c a b => checkInvariant m nameProblem mangle c; checkInvariant m nameProblem mangle a; checkInvariant m nameProblem mangle b
  | .Attribute _ v _ _ => checkInvariant m nameProblem mangle v
  | .Subscript _ v i _ => checkInvariant m nameProblem mangle v; checkInvariant m nameProblem mangle i
  | .Slice _ ⟨_, lo⟩ ⟨_, hi⟩ ⟨_, st⟩ =>
    if let some x := lo then checkInvariant m nameProblem mangle x
    if let some x := hi then checkInvariant m nameProblem mangle x
    if let some x := st then checkInvariant m nameProblem mangle x
  | .Call sr f args kws =>
    unless kws.val.isEmpty do return ← bad "a keyword argument in a loop invariant" sr
    if args.val.any (· matches .Starred ..) then
      return ← bad "a starred expression in a loop invariant" sr
    match f with
    | .Name fsr ⟨_, n⟩ _ =>
      if n == "OLD" then
        if !m.has "OLD" then return ← bad "OLD without importing it from pyhard" fsr
        return ← bad "OLD in a loop invariant" sr
      if !invariantBuiltins.contains n then return ← bad "a call in a loop invariant" sr
      if m.reboundBuiltins.contains n then
        return ← bad s!"{n} in a loop invariant of a module that binds {n}" fsr
      let quantifier := n == "all" || n == "any"
      unless args.val.size == (if n == "isinstance" then 2 else 1) do
        return ← bad "a call in a loop invariant" sr
      for a in args.val do
        if quantifier then checkQuantifier m nameProblem mangle sr a else checkInvariant m nameProblem mangle a
    | _ => bad "a call in a loop invariant" sr
  | .Lambda sr .. => bad "a lambda in a loop invariant" sr
  | .NamedExpr sr .. => bad "an assignment expression in a loop invariant" sr
  | .Yield sr .. | .YieldFrom sr .. => bad "yield in a loop invariant" sr
  | .Await sr .. => bad "await in a loop invariant" sr
  | .Starred sr .. => bad "a starred expression in a loop invariant" sr
  | .List sr .. | .Tuple sr .. | .Set sr .. | .Dict sr .. => bad "a display in a loop invariant" sr
  | .ListComp sr .. | .SetComp sr .. | .DictComp sr .. | .GeneratorExp sr .. =>
    bad "a comprehension in a loop invariant" sr
  | .JoinedStr sr .. | .FormattedValue sr .. | .TemplateStr sr .. | .Interpolation sr .. =>
    bad "an f-string in a loop invariant" sr
termination_by sizeOf e

/-- Check `g`, the argument of `all` or `any` at `sr`: a generator expression with one `for`
clause, not `async`, whose target is a name, or a pair of names over `d.items()`. -/
def checkQuantifier (m : Markers) (nameProblem : String → Option String) (mangle : String → String)
    (sr : SourceRange)
    (g : expr SourceRange) : InvCheck := do
  let .GeneratorExp _ elt gens := g | bad "a call in a loop invariant" sr
  unless gens.val.size == 1 do
    return ← bad "a quantifier with several for clauses in a loop invariant" sr
  for _hc : c in gens.val do
    match c, _hc with
    | .mk_comprehension _ target iter ifs isAsync, _hc =>
    if isAsync.value != 0 then return ← bad "an async quantifier in a loop invariant" sr
    if let some what := targetProblem mangle ((dictView? iter).map (·.1)) target then
      return ← bad what sr
    have := Array.sizeOf_lt_of_mem _hc
    -- The view's dict, or the iterable.
    match _hi : iter with
    | .Call _ (.Attribute _ d _ _) _ _ =>
      if (dictView? iter).isSome then checkInvariant m nameProblem mangle d
      else return ← bad "a call in a loop invariant" sr
    | other => checkInvariant m nameProblem mangle other
    for x in ifs.val do checkInvariant m nameProblem mangle x
  checkInvariant m nameProblem mangle elt
termination_by sizeOf g

end

end -- public section

end StrataPython.Dyn.PyMarkers
