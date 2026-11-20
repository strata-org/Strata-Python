/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataPython.Dyn.Env
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.Canonicalize
meta import StrataPython.Dyn.Canonical
meta import StrataDynTest.Unforward
meta import StrataDyn.Env.WF
meta import StrataPythonTest.Dyn.TestUtil

/-! # Reading the translator goldens back

Reads every `NAME.expected.dyn`, and every ref-to-reg golden `NAME.expected.ssa.dyn`, in
`StrataPythonTest/Dyn/dyn_tests/` against `Py.env`,
the diagnostic lines before its module read as comments, and checks both printed forms:

* folded, as the goldens are, reprinting the module gives the golden's module text, byte for
  byte;
* in full, printing, reading and printing again gives the same text;
* no name read has a `.` inside a segment;
* `PyCanonical.runModule` puts every function in Python's canonical form, and undoing the forwarding
  blocks it added gives back the module read (`Unforward.moduleUndoesTo`);
* in every translator golden but four, every function's entry block only binds the arguments
  (`docs/PythonToDyn.md` §5.4): each `base.refSet` writes a cell that a `base.refNew` of the same
  block made, each `py.uSub` negates a literal of the same block, and its other operations are
  the binding's.  `py.bindArgs` takes the block's last two parameters and one default per name,
  and has the names, counts and flags of the function's signature in the program's scope golden,
  `NAME.expected.scope`.  Each write gives a parameter's new cell the slot of the `py.bindArgs`
  result that binds that parameter, once, and the block makes one new cell per name.  Which default
  each parameter gets is not checked.  One gap is pinned (`misbindGap`): when the translator
  replaces a function by a stub without a binding, such as a generator lambda, another function
  with the same qualified name may be checked against the stub's signature.  The four are programs
  that the translator rejects because a parameter is declared global or nonlocal, or is named
  twice: their entry blocks write the global cell, or the enclosing function's cell, of that
  name, or one cell twice.

Nothing is excluded from the read-back checks: the goldens' floats print as the shortest
decimals that read back exactly.  No Python is needed. -/

namespace StrataPython.DynReadTest

open Strata.Dyn
open StrataPython.Dyn
open StrataPython.Dyn.TestUtil (firstDiff dottedNames)

/-- The directory holding the goldens. -/
private meta def testDir : System.FilePath := "StrataPythonTest" / "Dyn" / "dyn_tests"

/-- The suffixes of a translator golden and of a ref-to-reg golden. -/
private meta def goldenSuffixes : List String := [".expected.dyn", ".expected.ssa.dyn"]

/-- The module part of a golden: from its `module` line on. -/
private meta def moduleText (golden : String) : String :=
  "\n".intercalate ((golden.splitOn "\n").dropWhile (!·.startsWith "module ")) |>.trimAsciiEnd
    |>.toString |>.push '\n'

/-- The literals that an argument binding may build, as constant defaults. -/
private meta def literalOps : List String :=
  ["py.intLit", "py.strLit", "py.floatLit", "py.boolLit", "py.noneLit"]

/-- The other operations of an argument binding, besides `base.refNew`, `base.refSet` and
`py.uSub`. -/
private meta def bindingOps : List String :=
  ["py.undef", "py.bindArgs", "py.tupleGet", "py.mkTuple", "base.refGet"] ++ literalOps

/-- The translator goldens whose entry blocks do more than bind the arguments, with what the
checks say about each of their functions: programs that the translator rejects, because a parameter
is declared global or nonlocal, or is named twice. -/
private meta def notBinding : List (String × List String) :=
  [("e02_global_param.expected.dyn", ["e02_global_param.f runs py.globalCell"]),
   ("e09_duplicate_argument.expected.dyn",
    ["e09_duplicate_argument.f: the cell of a is written twice"]),
   ("e11_nonlocal_param.expected.dyn", ["e11_nonlocal_param.f.g runs base.refSet"]),
   ("e28_symtable_error_first.expected.dyn",
    ["e28_symtable_error_first.f: the cell of a is written twice"])]

/-- The first instruction of the function's entry block that does more than bind the arguments:
a `base.refSet` of a cell that no `base.refNew` of the block made, a `py.uSub` of a value that is
not a literal of the block, or another operation than the binding's. -/
private meta def entryNotBinding? {α : Type} (fn : Func Py.env α) : Option String :=
  fn.blocks[0]?.bind fun e =>
    let opName (i : Instruction Py.env α) : Option String :=
      match i with
      | .apply _ _ r .. => some (ToDDM.nameText r.name)
      | .const .. => none
    let madeBy (ops : List String) := e.instrs.toList.filterMap fun i =>
      if (opName i).any ops.contains then some i.result.id else none
    let cells := madeBy ["base.refNew"]
    let literals := madeBy literalOps
    (e.instrs.toList.find? fun i => match opName i with
      | some "base.refNew" => false
      | some "base.refSet" => !(i.args[0]?).any cells.contains
      | some "py.uSub" => !(i.args[0]?).any literals.contains
      | some n => !bindingOps.contains n
      | none => false).bind opName

/-- A function's parameters, as its scope golden gives them: the named parameters in order, how
many of them are positional-only and how many positional, and the names of `*args` and `**kw`. -/
private structure Sig where
  names : List String := []
  nPosOnly : Nat := 0
  nPos : Nat := 0
  varPos : Option String := none
  varKw : Option String := none

/-- The parameters that the items of a line such as `params: a, /, b, *rest, c, **kw` give. -/
private meta def sigOf (items : List String) : Sig :=
  (items.foldl (init := (({} : Sig), false)) fun (s, kwOnly) item =>
    let rest (n : Nat) := String.ofList (item.toList.drop n)
    if item == "/" then ({ s with nPosOnly := s.names.length }, kwOnly)
    else if item == "*" then (s, true)
    else if item.startsWith "**" then ({ s with varKw := some (rest 2) }, kwOnly)
    else if item.startsWith "*" then ({ s with varPos := some (rest 1) }, true)
    else ({ s with names := s.names ++ [item],
                   nPos := if kwOnly then s.nPos else s.names.length + 1 }, kwOnly)).1

/-- The parameters of each function and lambda of a scope golden, with its qualified name.  A
function without parameters has no `params:` line. -/
private meta def sigsOf (scope : String) : List (String × Sig) :=
  let lines := (scope.splitOn "\n").map fun l => String.ofList (l.toList.dropWhile (· == ' '))
  (lines.zip (lines.drop 1 ++ [""])).filterMap fun (l, next) =>
    (["function ", "lambda "].find? fun k => l.startsWith k).map fun k =>
      (String.ofList (l.toList.drop k.length),
        if next.startsWith "params: " then sigOf ((String.ofList (next.toList.drop 8)).splitOn ", ")
        else {})

/-- What is wrong with the binding of the function's entry block, given the signatures `sigs` of
the scope golden: `py.bindArgs` must take the block's last two parameters, the positional and
keyword arguments, which follow the cells that a closure captures, and a tuple of one default per
name, and its names, counts and flags must be those of the function's signature.  Each write must
give a parameter's new cell the slot of the result that binds that parameter: slot `k` binds the
`k`-th name, then `*args`, then `**kw`.  A parameter's cell is a `base.refNew` of `py.undef` of
its name, made once.  Each slot must be written once.  A block that writes no cell needs no
`py.bindArgs`.  Gives the index in `sigs` of the signature that the binding has, if it binds the
arguments. -/
private meta def entryMisbinds? {α : Type} (sigs : List (String × Sig)) (fn : Func Py.env α) :
    Except String (Option Nat) :=
  match fn.blocks[0]? with
  | none => .ok none
  | some e =>
    let instrs := e.instrs.toList
    let opName (i : Instruction Py.env α) : Option String :=
      match i with
      | .apply _ _ r .. => some (ToDDM.nameText r.name)
      | .const .. => none
    let defOf (v : ValId) := instrs.find? (·.result.id == v)
    let applies (op : String) (v : ValId) := (defOf v).any (opName · == some op)
    let argOf (v : ValId) (k : Nat) : Option ValId := (defOf v).bind (·.args[k]?)
    let constOf (v : ValId) : Option Const := (defOf v).bind fun
      | .const _ _ c => some c
      | .apply .. => none
    let strOf (v : ValId) : Option String := match constOf v with
      | some (.str s) => some s
      | _ => none
    let intOf (v : ValId) : Option Int := match constOf v with
      | some (.int n) => some n
      | _ => none
    let boolOf (v : ValId) : Option Bool := match constOf v with
      | some (.bool b) => some b
      | _ => none
    let cellOf (c : ValId) : Option String :=
      if applies "base.refNew" c then (argOf c 0).bind fun u =>
        if applies "py.undef" u then (argOf u 0).bind strOf else none
      else none
    let cells := instrs.filterMap fun i =>
      if opName i == some "base.refNew" then cellOf i.result.id else none
    let sets := instrs.filter (opName · == some "base.refSet")
    if let some c := cells.find? (cells.count · > 1) then .error s!"it makes two new cells of {c}"
    else match instrs.filter (opName · == some "py.bindArgs") with
    | [] => if sets.isEmpty then .ok none else .error "it writes a cell, but binds no arguments"
    | [b] =>
      let names := (b.args.toList.drop 8).map strOf
      let q := ((b.args[3]?).bind strOf).getD ""
      let shape := (names, (b.args[4]?).bind intOf, (b.args[5]?).bind intOf,
        (b.args[6]?).bind boolOf, (b.args[7]?).bind boolOf)
      let n := e.params.size
      if n < 2 || b.args[0]? != (e.params[n - 2]?).map (·.id) ||
          b.args[1]? != (e.params[n - 1]?).map (·.id) then
        .error "py.bindArgs does not take the block's last two parameters, the arguments, in order"
      else if !(b.args[2]?).any fun d =>
          applies "py.mkTuple" d && (defOf d).any (·.args.size == names.length) then
        .error "the defaults are not a tuple with one entry per name"
      else
      -- What is wrong with the writes, if the function has the signature `sig`.
      let wrongWrites (sig : Sig) : Option String :=
        let slots := sig.names ++ sig.varPos.toList ++ sig.varKw.toList
        -- Each write, as the slot it takes, or what is wrong with it.
        let writes : List (Except String (String × Nat)) := sets.map fun i =>
          match (i.args[0]?).bind cellOf with
          | none => .error "it writes a cell that is not a new cell of a parameter"
          | some cell =>
            let slot? := (i.args[1]?).bind fun v =>
              if applies "py.tupleGet" v && argOf v 0 == some b.result.id then
                match (argOf v 1).bind intOf with
                | some k => if k ≥ 0 then some k.toNat else none
                | none => none
              else none
            match slot? with
            | none => .error s!"the cell of {cell} gets a value that is not a slot of the binding"
            | some k => match slots[k]? with
              | none => .error s!"the cell of {cell} gets slot {k}, past the {slots.length} slots"
              | some n =>
                if n == cell then .ok (cell, k)
                else .error s!"the cell of {cell} gets slot {k}, which binds {n}"
        match writes.findSome? fun | .error m => some m | .ok _ => none with
        | some m => some m
        | none =>
          let ok := writes.filterMap fun | .ok w => some w | .error _ => none
          let written := ok.map (·.1)
          let taken := ok.map (·.2)
          -- A slot goes to the one cell of its name, so a slot taken twice writes a cell twice.
          if let some c := written.find? (written.count · > 1) then
            some s!"the cell of {c} is written twice"
          else (List.range slots.length).find? (!taken.contains ·) |>.map fun k =>
            s!"slot {k} of the binding is not written"
      -- The signatures of the scope golden that the binding may have: those of its qualified
      -- name, with its names, counts and flags.  Their writes may still differ, by the names of
      -- `*args` and `**kw`.
      let fits := (List.range sigs.length).filterMap fun i => sigs[i]?.bind fun (q', s) =>
        if q' == q && shape == (s.names.map some, some (s.nPosOnly : Int), some (s.nPos : Int),
            some s.varPos.isSome, some s.varKw.isSome) then some (i, s) else none
      match fits.find? (wrongWrites ·.2 |>.isNone), fits.head? with
      | some (i, _), _ => .ok (some i)
      | none, some (_, sig) => .error ((wrongWrites sig).getD "")
      | none, none => .error s!"its binding does not match the signature of {q} in the scope golden"
    | _ => .error "it binds the arguments twice"

/-- The signatures of the scope golden of the translator golden at `path`. -/
private meta def sigsAt (path : System.FilePath) : IO (List (String × Sig)) :=
  return sigsOf (← IO.FS.readFile (path.toString.replace ".expected.dyn" ".expected.scope"))

/-- What the checks of the entry blocks say about each function of `m` whose entry block does
more than bind its arguments, given the signatures `sigs` of its scope golden.  Each signature
serves one function: two functions with one qualified name, such as a property's getter and
setter, have two signatures.  A function that the translator replaces by a stub without a binding
uses no signature, so another function with its qualified name may take its signature
(`misbindGap`). -/
private meta def entryChecks {α : Type} (sigs : List (String × Sig)) (m : Module Py.env α) :
    List String :=
  (m.raw.funcs.toList.foldl (init := (sigs, ([] : List String))) fun (left, bad) f =>
    let name := ToDDM.nameText f.name
    match entryNotBinding? f with
    | some op => (left, bad ++ [s!"{name} runs {op}"])
    | none => match entryMisbinds? left f with
      | .error why => (left, bad ++ [s!"{name}: {why}"])
      | .ok none => (left, bad)
      | .ok (some i) => (left.eraseIdx i, bad)).2

/-- Check one golden, or say what is wrong with it. -/
private meta def check (path : System.FilePath) : IO (Option String) := do
  let golden ← IO.FS.readFile path
  let text := moduleText golden
  match ← Module.read Py.env golden path.toString with
  | .error e => return some s!"{path}: does not read back:\n{e}"
  | .ok m =>
    unless (dottedNames m.raw).isEmpty do
      return some s!"{path}: a name has a `.` inside a segment: {(dottedNames m.raw).map ToDDM.nameText}"
    if let some d := firstDiff (toString m) text then
      return some s!"{path}: reprints differently at {d}"
    if path.toString.endsWith ".expected.dyn" then
      let bad := entryChecks (← sigsAt path) m
      if let some (_, want) := notBinding.find? (·.1 == path.fileName.getD "") then
        unless bad == want do
          return some s!"{path}: the checks of its entry blocks say {bad}, not {want}"
      else if let some why := bad.head? then
        return some s!"{path}: an entry block does more than bind its arguments: {why}"
    let full := m.format .full
    match ← Module.read Py.env full s!"{path} (full)" with
    | .error e => return some s!"{path}: the full form does not read back:\n{e}"
    | .ok m' =>
      if let some d := firstDiff (m'.format .full) full then
        return some s!"{path}: the full form reprints differently at {d}"
      match StrataPython.Dyn.PyCanonical.runModule m with
      | .error fs => return some s!"{path}: not put in canonical form: {fs.map toString}"
      | .ok cm =>
        unless Unforward.moduleUndoesTo m.raw cm.canonical.module.raw full do
          return some s!"{path}: in canonical form, does not undo to the module read"
        return none

/-- The write of `n`'s cell in the entry block of `total`, in `g06_function_contract`. -/
private meta def nWrite : String := "%set.0 : base.Unit = base.refSet[py.Value](%n.cell.0, %n.6)"

/-- The binding of `total`, in `g06_function_contract`. -/
private meta def nBind : String :=
  "%bound.0 : py.Value = py.bindArgs(%args.0, %kwargs.0, %defaults.0, \"total\", 0, 1, false, \
    false, \"n\") ^propagate.0()"

/-- Wrong entry blocks for the checks of the binding: each case names a translator golden,
replaces a text that it holds once, and gives what the checks must say about its functions. -/
private meta def misbindCases : List (String × String × String × String) :=
  let g06 := "g06_function_contract"
  let i02 := "i02_param_kinds"
  [(g06, nWrite, "%set.0 : base.Unit = base.refSet[py.Value](%i.cell.0, %n.6)",
      "g06_function_contract.total: the cell of i gets slot 0, which binds n"),
   (g06, nWrite, "%set.0 : base.Unit = base.refSet[py.Value](%n.cell.0, %n.1)",
      "g06_function_contract.total: the cell of n gets a value that is not a slot of the binding"),
   (g06, "base.refNew[py.Value](%n.1)", "base.refNew[py.Value](%args.0)",
      "g06_function_contract.total: it writes a cell that is not a new cell of a parameter"),
   (g06, nWrite, s!"{nWrite}\n      %set.9 : base.Unit = base.refSet[py.Value](%n.cell.0, %n.6)",
      "g06_function_contract.total: the cell of n is written twice"),
   (g06, s!"{nWrite}\n      ", "",
      "g06_function_contract.total: slot 0 of the binding is not written"),
   (g06, "%n.6 : py.Value = py.tupleGet(%bound.0, 0)", "%n.6 : py.Value = py.tupleGet(%bound.0, 5)",
      "g06_function_contract.total: the cell of n gets slot 5, past the 1 slots"),
   (g06, nWrite, "%n.9 : py.Value = py.undef(\"n\")\n      \
      %n.cell.9 : base.Ref(py.Value) = base.refNew[py.Value](%n.9)\n      \
      %set.0 : base.Unit = base.refSet[py.Value](%n.cell.9, %n.6)",
      "g06_function_contract.total: it makes two new cells of n"),
   (g06, "py.bindArgs(%args.0, %kwargs.0,", "py.bindArgs(%kwargs.0, %args.0,",
      "g06_function_contract.total: py.bindArgs does not take the block's last two parameters, \
        the arguments, in order"),
   (g06, "py.mkTuple(%n.5)", "py.mkTuple()",
      "g06_function_contract.total: the defaults are not a tuple with one entry per name"),
   (g06, "\"total\", 0, 1, false", "\"total\", 0, 9, false",
      "g06_function_contract.total: its binding does not match the signature of total in the \
        scope golden"),
   (g06, nBind, s!"{nBind}\n      \
      %bound.9 : py.Value = py.bindArgs(%args.0, %kwargs.0, %defaults.0, \
      \"total\", 0, 1, false, false, \"n\") ^propagate.0()",
      "g06_function_contract.total: it binds the arguments twice"),
   (g06, "    entry.0():\n      jump ^start.0()",
    "    entry.0():\n      %z.0 : py.Value = py.undef(\"z\")\n      \
      %z.cell.0 : base.Ref(py.Value) = base.refNew[py.Value](%z.0)\n      \
      %set.9 : base.Unit = base.refSet[py.Value](%z.cell.0, %z.0)\n      jump ^start.0()",
      "g06_function_contract.<module>: it writes a cell, but binds no arguments"),
   (g06, "%n.5 : py.Value = py.undef(\"n\")", "%n.5 : py.Value = py.uSub(%args.0) ^propagate.0()",
      "g06_function_contract.total runs py.uSub"),
   (i02, "%set.1 : base.Unit = base.refSet[py.Value](%more.cell.0, %more.1)\n      \
      %opts.1 : py.Value = py.tupleGet(%bound.0, 2)\n      \
      %set.2 : base.Unit = base.refSet[py.Value](%opts.cell.0, %opts.1)",
    "%set.1 : base.Unit = base.refSet[py.Value](%opts.cell.0, %more.1)\n      \
      %opts.1 : py.Value = py.tupleGet(%bound.0, 2)\n      \
      %set.2 : base.Unit = base.refSet[py.Value](%more.cell.0, %opts.1)",
      "i02_param_kinds.both: the cell of opts gets slot 1, which binds more"),
   ("s67_property_setter", "%defaults.0 : py.Value = py.mkTuple(%self.1, %v.1)\n      \
      %bound.0 : py.Value = py.bindArgs(%args.0, %kwargs.0, %defaults.0, \"C.x\", 0, 2, false, \
        false, \"self\", \"v\") ^propagate.0()\n      \
      %self.2 : py.Value = py.tupleGet(%bound.0, 0)\n      \
      %set.0 : base.Unit = base.refSet[py.Value](%self.cell.0, %self.2)\n      \
      %v.2 : py.Value = py.tupleGet(%bound.0, 1)\n      \
      %set.1 : base.Unit = base.refSet[py.Value](%v.cell.0, %v.2)",
    "%defaults.0 : py.Value = py.mkTuple(%self.1)\n      \
      %bound.0 : py.Value = py.bindArgs(%args.0, %kwargs.0, %defaults.0, \"C.x\", 0, 1, false, \
        false, \"self\") ^propagate.0()\n      \
      %self.2 : py.Value = py.tupleGet(%bound.0, 0)\n      \
      %set.0 : base.Unit = base.refSet[py.Value](%self.cell.0, %self.2)",
      "s67_property_setter.C.x.1: its binding does not match the signature of C.x in the scope \
        golden")]

/-- A wrong binding that the checks accept, pinned until they reject it: in `m_lambda`,
`bad = lambda d=[]: d` bound as if it had no parameters, with no write of `d`'s cell.  The
translator replaces `gen = lambda: (yield)` by a stub without a binding, so `gen`'s signature, a
`<lambda>` without parameters, is left unused, and `bad` takes it. -/
private meta def misbindGap : String × String × String × List String :=
  ("m_lambda", "%defaults.0 : py.Value = py.mkTuple(%d.default.1)\n      \
      %bound.0 : py.Value = py.bindArgs(%args.0, %kwargs.0, %defaults.0, \"<lambda>\", 0, 1, false, \
        false, \"d\") ^propagate.0()\n      \
      %d.1 : py.Value = py.tupleGet(%bound.0, 0)\n      \
      %set.0 : base.Unit = base.refSet[py.Value](%d.cell.0, %d.1)\n",
    "%defaults.0 : py.Value = py.mkTuple\n      \
      %bound.0 : py.Value = py.bindArgs(%args.0, %kwargs.0, %defaults.0, \"<lambda>\", 0, 0, false, \
        false) ^propagate.0()\n",
    [])

#eval show IO Unit from do
  for (name, old, new, why) in misbindCases.map (fun (n, o, w, y) => (n, o, w, [y])) ++
      [misbindGap] do
    let path := testDir / s!"{name}.expected.dyn"
    let golden ← IO.FS.readFile path
    unless (golden.splitOn old).length == 2 do
      throw <| IO.userError s!"DynReadTest: {path} does not hold {old} once"
    match ← Module.read Py.env (golden.replace old new) path.toString with
    | .error e => throw <| IO.userError s!"DynReadTest: {path}, changed, does not read:\n{e}"
    | .ok m =>
      let got := entryChecks (← sigsAt path) m
      unless got == why do
        throw <| IO.userError s!"DynReadTest: with {new}, the checks say {got}, not {why}"

#eval show IO Unit from do
  let goldens := (← testDir.readDir).filter fun f => goldenSuffixes.any (f.fileName.endsWith ·)
  let goldens := goldens.qsort (·.fileName < ·.fileName)
  let mut failures := #[]
  for g in goldens do
    if let some msg ← check g.path then failures := failures.push msg
  IO.println s!"DynReadTest: {goldens.size - failures.size}/{goldens.size} read back and \
    put in canonical form"
  if !failures.isEmpty then
    for f in failures do IO.println f
    throw <| IO.userError s!"DynReadTest: {failures.size} failure(s)"

end StrataPython.DynReadTest
