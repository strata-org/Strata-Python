/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython.Dyn.Env
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF
meta import StrataDyn.RefToReg
meta import StrataPythonTest.Util.Python
meta import StrataPythonTest.Dyn.TestUtil

/-! # Hand-written models of PySpec fixtures

Each file of `StrataPythonTest/Dyn/contract_models/` is a Dyn module written by hand by the
rules of `docs/PythonToDyn.md` §12, which say how a PySpec model is represented.  Seven files
represent one PySpec fixture each, named in the file's first comment; four are written for this
test.  For each file:

* the file reads in `Py.env`, which checks it, and the module prints back as the file without
  its comment lines;
* one change to the file is rejected by the reader or the checker, with its rule's message.

Three more checks follow:

* every predicate entry of `py.invariants` names a function that takes one `py.Value` for the
  invariant's parameter and one for each ghost that the entry lists, and returns a `base.Bool`
  (§12.6);
* with CPython 3.12, a class that defines the names that a model class body stores, the
  synthesized `__getattr__` among them, gives an unknown value for `C().extra` but raises
  `AttributeError` for `C.extra` and `super().extra` (§12.1).  It raises `TypeError` for
  `len(C())` and `iter(C())`, and `bool(C())` is `True`, since CPython looks special methods up
  on the type (§12.11);
* ref-to-reg (`refToReg`) accepts every model and changes none: it changes only bodies, and no
  model's body makes a cell, so every contract and every extern function prints the same.

The test runs from the package root.  The CPython check needs Python, as `withPython` finds it;
`SKIP_PYTHON_TESTS=1` skips it.
-/

namespace StrataPython.ContractModelTest

open Strata.Dyn
open StrataPython.Dyn
open StrataPython (withPython)
open StrataPython.Dyn.TestUtil (firstDiff)

/-- The directory of the models. -/
private meta def modelDir : System.FilePath := "StrataPythonTest" / "Dyn" / "contract_models"

/-- `text` without its comment lines, those that start with `--` after their indentation. -/
private meta def uncommented (text : String) : String :=
  "\n".intercalate <| (text.splitOn "\n").filter fun l => !l.trimAsciiStart.startsWith "--"

#guard uncommented "-- a model\nmodule m {\n  -- a note\n  ghost @|m.<ghost>.g| : py.Value\n}\n" ==
  "module m {\n  ghost @|m.<ghost>.g| : py.Value\n}\n"

/-- The model `file` as read in `Py.env`, or its diagnostics as an error. -/
private meta def readModel (file text : String) : IO (Module Py.env Info) := do
  match ← Module.read Py.env text file with
  | .ok m => return m
  | .error e => throw <| IO.userError (toString e)

/-- Read the model `file` in `Py.env`.  Print its diagnostics, or the first line where the module
prints differently from the file without its comment lines. -/
private meta def check (file : String) : IO Unit := do
  let text ← IO.FS.readFile (modelDir / file)
  match ← Module.read Py.env text file with
  | .error e => IO.println e
  | .ok m =>
    let expected := uncommented text
    unless toString m == expected do
      IO.println s!"{file} prints differently, at {(firstDiff (toString m) expected).getD "its end"}"

/-- `text` with one change: the first `old` after `anchor`, which occurs once, becomes `new`.
Throws if `anchor` does not occur exactly once or no `old` follows it, so that a change is never
lost. -/
private meta def change (text anchor old new : String) : IO String := do
  let [before, after] := text.splitOn anchor
    | throw <| IO.userError s!"the text does not hold `{anchor}` exactly once"
  let head :: tail@(_ :: _) := after.splitOn old
    | throw <| IO.userError s!"the text holds no `{old}` after `{anchor}`"
  return before ++ anchor ++ head ++ new ++ old.intercalate tail

/-- `diag` without the `file:line:column: ` that starts it. -/
private meta def messageText (file diag : String) : String :=
  if diag.startsWith s!"{file}:" then
    match ((diag.drop (file.length + 1)).toString).splitOn ": " with
    | _ :: msg@(_ :: _) => ": ".intercalate msg
    | _ => diag
  else diag

#guard messageText "m.dyn" "m.dyn:3:4: no ghost @m.h: here" == "no ghost @m.h: here"

/-- Read the model `file` with one change (`change`), and print each diagnostic's message,
without its position. -/
private meta def mutate (file anchor old new : String) : IO Unit := do
  let text ← change (← IO.FS.readFile (modelDir / file)) anchor old new
  match ← Module.read Py.env text file with
  | .error e => for d in e.toArray do IO.println (messageText file d)
  | .ok _ => IO.println s!"{file} still reads after the change"

/-! ## `ghost_old.dyn`: `servicelib/GhostOld.py`

Ghosts with an initializer and an invariant, `old` over a ghost, and frames that name ghosts and
`py.instanceState`. -/

#guard_msgs in
#eval check "ghost_old.dyn"

-- The old region reads the ghost after the call, not before it (O2).
/-- info: the old region in @servicelib.GhostOld.acquire uses %allocated.0, which the clause defines outside the old region -/
#guard_msgs in
#eval mutate "ghost_old.dyn" "free ensures \"admitted postcondition of 'acquire'\" {\n      post.1("
  "py.add(%allocated.1, %int.0)" "py.add(%allocated.0, %int.0)"

/-! ## `storage.dyn`: `servicelib/Storage.py`

An `@exhaustive` class with eighteen methods: `**kwargs` with a TypedDict, declared types and
their schemas, `py.len`, `py.reSearch`, the four quantifiers, `py.fields`, and the synthesized
`__init__` and `__getattr__`. -/

#guard_msgs in
#eval check "storage.dyn"

-- The body of a quantifier turns a failure into `true` (C3).
/-- info: in a region nested in a contract of @servicelib.Storage.Storage.require_some_match, the failure successor of %eq.0 goes to propagate.1, which does not pass the failure on with base.error -/
#guard_msgs in
#eval mutate "storage.dyn" "requires \"at least one key must match the needle\""
  "base.error[py.Value, base.Bool](%exc.1)" "base.ok[py.Value, base.Bool](true)"

/-! ## `dispatch.dyn`: `servicelib/__init__.py`

The extern that stands for the overloads of `connect`. -/

#guard_msgs in
#eval check "dispatch.dyn"

-- A failure in a `free ensures` clause gives `false` (C1).
/-- info: in a free ensures clause of @servicelib.connect, the failure successor of %service_name.2 goes to fail.0, which returns false; a failure must give true or be unreachable -/
#guard_msgs in
#eval mutate "dispatch.dyn" "free ensures \"overload of 'connect' for 'storage'\""
  "ret(true)\n    }" "ret(false)\n    }"

/-! ## `admitted.dyn`: `servicelib/Admitted.py`

A `free ensures` clause that holds when the function raises, and the return type's test. -/

#guard_msgs in
#eval check "admitted.dyn"

-- An extern's `ensures` clause is not `free` (X4).
/-- info: @servicelib.Admitted.admitted_value is extern, so its ensures clauses must be free -/
#guard_msgs in
#eval mutate "admitted.dyn" "requires \"arguments bind to 'admitted_value'\""
  "free ensures" "ensures"

/-! ## `modifies_self.dyn`: `native_cases/modifies_self.py`

The receiver's type test, and frames that name what the receiver reaches and an attribute of the
receiver. -/

#guard_msgs in
#eval check "modifies_self.dyn"

-- A frame region changes state (E1).
/-- info: a contract region of @modifies_self.C.m may not change state, but py.unsupported is declared writes -/
#guard_msgs in
#eval mutate "modifies_self.dyn" "extern func @modifies_self.C.m("
  "py.argOf(%args.0, %kwargs.0, 0, \"self\", %undef.2)" "py.unsupported(%undef.2)"

/-! ## `init_contract.dyn`: `native_cases/init_contract.py`

A stub's `__init__` with a contract, a field that the `__init__` declares, and a nested class
whose synthesized `__init__` reads it through the outer class. -/

#guard_msgs in
#eval check "init_contract.dyn"

-- The field's `in` names a function that the module lacks.
/-- info: no function @init_contract.C.__init9__ in this module -/
#guard_msgs in
#eval mutate "init_contract.dyn" "{name = \"helper\""
  "in = @init_contract.C.__init__}" "in = @init_contract.C.__init9__}"

/-! ## `invariant.dyn`: `native_cases/class_invariant_with_method_contract.py`

A class invariant as a predicate function, named by `py.invariants`. -/

#guard_msgs in
#eval check "invariant.dyn"

-- A failure in a `requires` clause gives `true` (C1).
/-- info: in a requires clause of @class_invariant_with_method_contract.C.m, the failure successor of %ge.0 goes to fail.2, which returns true; a failure must give false or be unreachable -/
#guard_msgs in
#eval mutate "invariant.dyn" "requires \"precondition 0\""
  "ret(false)" "ret(true)"

/-! ## `invariant_untranslated.dyn`: written for this test

A class with a base, a field whose type is a TypedDict (`{expr = "TypedDict"}`), and a predicate
entry and an untranslated entry in `py.invariants`.  The untranslated entry's source text has a
string literal and a line break, and reads back unchanged. -/

#guard_msgs in
#eval check "invariant_untranslated.dyn"

-- The predicate entry names a function that the module lacks.
/-- info: no function @m.C.<invariant>.9 in this module -/
#guard_msgs in
#eval mutate "invariant_untranslated.dyn" "#[py.invariants = ["
  "<invariant>.0|" "<invariant>.9|"

/-! ## `invariant_ghost.dyn`: written for this test

A class invariant that names a ghost: its predicate takes the ghost's contents as a second
parameter, and its entry lists the ghost. -/

#guard_msgs in
#eval check "invariant_ghost.dyn"

-- The predicate entry names a ghost that the module lacks (G7).
/-- info: no ghost @m.<ghost>.limits -/
#guard_msgs in
#eval mutate "invariant_ghost.dyn" "ghosts = ["
  "<ghost>.limit|" "<ghost>.limits|"

/-! ## `ghost_untestable.dyn`: written for this test

Ghosts whose declared types have no runtime test, `BinaryIO` and `Union[int, BinaryIO]`, so
neither has an invariant. -/

#guard_msgs in
#eval check "ghost_untestable.dyn"

-- Two ghosts have one name (G1).
/-- info: ghost @m.<ghost>.stream is declared twice -/
#guard_msgs in
#eval mutate "ghost_untestable.dyn" "ghost @|m.<ghost>.stream| : py.Value\n"
  "<ghost>.either|" "<ghost>.stream|"

/-! ## `dispatch_params.dyn`: written for this test

Overloads whose stubs have different parameters: each stub's own clauses apply only when the
dispatch argument is its literal. -/

#guard_msgs in
#eval check "dispatch_params.dyn"

-- A contract region has a cycle (C4).
/-- info: a contract region of @m.connect has a cycle through other.1 -/
#guard_msgs in
#eval mutate "dispatch_params.dyn" "requires \"'region' is required for 'storage'\""
  "ret(true)" "jump ^other.1()"

/-! ## Predicate entries of `py.invariants`

An entry `{fn = @f, ghosts = [g₁, …, gₙ]}` is a predicate only when `@f` takes `1 + n`
parameters of type `py.Value` and returns a `base.Bool`.  Any other entry states nothing. -/

/-- A record's field `k`, if it has one. -/
private meta def field? (fs : Array (Name × AttrValue)) (k : String) : Option AttrValue :=
  (fs.find? (·.1 == Name.base.str k)).map (·.2)

/-- What the entry `e` of `py.invariants` in `m` is: the function it names, and whether that
function has a predicate's parameters for the entry's ghosts. -/
private meta def describeEntry (m : Module Py.env Info) (e : AttrValue) : String :=
  match e with
  | .record fs =>
    match field? fs "fn", field? fs "ghosts" with
    | some (.const (.func f)), ghosts =>
      let n := match ghosts with
        | some (.list gs) => gs.size
        | _ => 0
      let verdict := match m.raw.funcs.find? (·.name == f) with
        | some g =>
          if g.params.size == 1 + n && g.params.all (·.type == Py.Value) &&
              g.retType == Base.Bool then "a predicate"
          else s!"states nothing, since it takes {g.params.size} parameters"
        | none => "states nothing, since the module has no such function"
      s!"@{ToDDM.nameText f} with {n} ghosts: {verdict}"
    | _, _ => "an entry without `fn`: states nothing"
  | _ => "an entry that is not a record: states nothing"

/-- Print what each entry of `py.invariants` in the model `file`, whose text is `text`, is. -/
private meta def printEntries (file text : String) : IO Unit := do
  let m ← readModel file text
  for fn in m.raw.funcs do
    for (k, v) in fn.info.attrs do
      if k == Py.pn "invariants" then
        if let .list entries := v then
          for e in entries do IO.println s!"{file}: {describeEntry m e}"

-- Every model's entries.
/--
info: invariant.dyn: @class_invariant_with_method_contract.C.<invariant>.0 with 0 ghosts: a predicate
invariant_ghost.dyn: @m.Counter.<invariant>.0 with 1 ghosts: a predicate
invariant_untranslated.dyn: @m.C.<invariant>.0 with 0 ghosts: a predicate
invariant_untranslated.dyn: an entry without `fn`: states nothing
-/
#guard_msgs in
#eval do
  let files := (← modelDir.readDir).map (·.fileName) |>.qsort (· < ·)
  for file in files do
    printEntries file (← IO.FS.readFile (modelDir / file))

-- An entry that lists no ghost, for a function that takes the contents of one.
/-- info: invariant_ghost.dyn: @m.Counter.<invariant>.0 with 0 ghosts: states nothing, since it takes 2 parameters -/
#guard_msgs in
#eval do
  let text ← IO.FS.readFile (modelDir / "invariant_ghost.dyn")
  printEntries "invariant_ghost.dyn"
    (← change text "#[py.invariants = [" ", ghosts = [ghost @|m.<ghost>.limit|]" "")

/-! ## Names and operations that the synthesized `__getattr__` does not cover

The class body of `C` in `modifies_self.dyn` stores `__module__` and `__qualname__`, its
method, the synthesized `__init__` and the synthesized `__getattr__`.  CPython 3.12 runs a class
with exactly these names, with a `__getattr__` that returns an unknown value, as the synthesized
one may.  An instance's missing
name and a module's missing name give that value, but a missing class attribute and a missing
name read through `super()` raise `AttributeError` (§12.1).  An operation that CPython performs
through a special method of the instance's type does not call `__getattr__`: `len(C())` and
`iter(C())` raise `TypeError`, and `bool(C())` is `True` (§12.11). -/

/-- The names that the class body `fn` stores in its namespace, in order: the keys of the
`py.setItem`s of its blocks whose key is a `py.strLit` of a constant. -/
private meta def classStores (fn : Func Py.env Info) : Array String := Id.run do
  let mut consts : Std.HashMap Nat String := {}
  let mut lits : Std.HashMap Nat String := {}
  let mut keys := #[]
  for b in fn.blocks do
    for i in b.instrs do
      match i with
      | .const _ d (.str s) => consts := consts.insert d.id.id s
      | .apply _ d r _ args _ _ =>
        if r.name == Py.pn "strLit" then
          if let some s := args[0]?.bind (consts[·.id]?) then lits := lits.insert d.id.id s
        else if r.name == Py.pn "setItem" then
          if let some s := args[1]?.bind (lits[·.id]?) then keys := keys.push s
      | _ => pure ()
  return keys

/-- The names that the class body of `C` in `modifies_self.dyn` stores. -/
private meta def modelStores : IO (Array String) := do
  let file := "modifies_self.dyn"
  let m ← readModel file (← IO.FS.readFile (modelDir / file))
  let some body := m.raw.funcs.find? (ToDDM.nameText ·.name == "modifies_self.C.<body>")
    | throw <| IO.userError s!"{file} has no class body of C"
  return classStores body

/-- info: __module__, __qualname__, m, __init__, __getattr__ -/
#guard_msgs in
#eval do IO.println (", ".intercalate (← modelStores).toList)

/-- A Python program that builds a class `C` with the names it receives, reads `extra` through an
instance, the class, `super()` and a module with a `__getattr__`, and applies `len`, `iter` and
`bool` to an instance. -/
private meta def lookupProgram : String := "import sys, types
UNKNOWN = object()
def method(*args, **kwargs):
    return None
def synthesized_getattr(self, name):
    return UNKNOWN
ns = {name: method for name in sys.argv[1:]}
if '__getattr__' in ns:
    ns['__getattr__'] = synthesized_getattr
if '__module__' in ns:
    ns['__module__'] = 'm'
if '__qualname__' in ns:
    ns['__qualname__'] = 'C'
C = type('C', (), ns)
class D(C):
    def read(self):
        return super().extra
module = types.ModuleType('m')
module.__getattr__ = lambda name: UNKNOWN
def outcome(read):
    try:
        return 'an unknown value' if read() is UNKNOWN else 'another value'
    except AttributeError:
        return 'AttributeError'
print('C().extra:', outcome(lambda: C().extra))
print('C.extra:', outcome(lambda: C.extra))
print('super().extra:', outcome(lambda: D().read()))
print('m.extra:', outcome(lambda: module.extra))
def result(op):
    try:
        return repr(op())
    except TypeError:
        return 'TypeError'
print('len(C()):', result(lambda: len(C())))
print('iter(C()):', result(lambda: iter(C())))
print('bool(C()):', result(lambda: bool(C())))
"

#eval withPython fun python => do
  let out ← IO.Process.output
    { cmd := python.toString, args := #["-c", lookupProgram] ++ (← modelStores) }
  let expected := "C().extra: an unknown value\nC.extra: AttributeError\n\
    super().extra: AttributeError\nm.extra: an unknown value\n\
    len(C()): TypeError\niter(C()): TypeError\nbool(C()): True\n"
  unless out.exitCode == 0 && out.stdout == expected do
    throw <| IO.userError s!"CPython gives, with exit code {out.exitCode}:\n{out.stdout}{out.stderr}"

/-! ## Ref-to-reg keeps every model -/

/-- Promote the cells of every model with `refToReg`, print each model that it rejects or
changes, and then the number of models. -/
private meta def promoteModels : IO Unit := do
  let files := ((← modelDir.readDir).filter (·.fileName.endsWith ".dyn")).qsort
    (·.fileName < ·.fileName)
  for f in files do
    let m ← readModel f.fileName (← IO.FS.readFile f.path)
    match refToReg m with
    | .error es =>
      IO.println s!"{f.fileName}: {es.toList.map fun (n, e) => s!"{ToDDM.nameText n}: {e}"}"
    | .ok m₁ =>
      if let some d := firstDiff (toString m₁) (toString m) then
        IO.println s!"{f.fileName}: ref-to-reg changes it at {d}"
  IO.println s!"{files.size} models"

/-- info: 11 models -/
#guard_msgs in
#eval promoteModels

end StrataPython.ContractModelTest
