/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Table
public import StrataDyn.Exec.Run
public import StrataPython.Dyn.Sem.Exceptions

set_option autoImplicit false

/-!
# Running a translated program, and its trace

`runModuleThen` runs the body of a translated module with `PySem`, then each named function of
the same module, each from where the previous run ended (`runPreparedFrom`), and prints what
the runs did, in the text that CPython's side (`StrataPythonTest/Dyn/trace.py`) prints too:

```
--- stdout <n>
<the n characters that the program printed, then one newline>
--- outcome
ok                       (or: raised <ExcType>: <str(exc)>, and a line "  context <ExcType>"
                          or "  cause <ExcType>" per link of the exception's chain)
--- globals
<name> = <render>        (sorted by name: every global but the dunder names, and __name__,
                          __doc__ and __annotations__ if set)
```

A gap prints `--- gap <message>` in place of the outcome (after a line `raised <ExcType>` when the
run raised an exception whose type is known), or in place of the first global that can't be
rendered, which ends the trace; a run out of fuel prints `--- out of fuel`, and any other
fault `--- fault <fault>`.
`render` gives `None`, `bool`, `int`, `float` (its `repr`), `str` and `bytes` (their `repr`),
lists, tuples, dicts, sets and frozensets in full (a set's members sorted by their render, so that
an order that depends on the hash seed shows no difference), `range` and `slice` as their `repr`,
`Ellipsis` and `NotImplemented`, `<class 'Q'>` for a class, `<T object>` for any other object of
type `T` (a function object, a built-in function), and `...` for an object inside itself. A value
that holds a symbolic hash renders as a gap, since its number differs between runs.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn Strata.Dyn.Exec

@[expose] public section

/-- How to run a program. -/
structure RunOptions where
  /-- The steps a run may take. -/
  fuel : Nat := 1000000000

/-- A render that may stop with a gap's message. -/
abbrev RenderM := Except String

/-- The `repr` of an `int`, or a gap for one too long to print. -/
def intText (i : Int) : RenderM String :=
  match Format.intRepr i with
  | .ok s => pure s
  | .error _ => throw "the repr of an int with too many digits"

/-- The `repr` of a `bytes`. -/
def bytesText (b : Array UInt8) : String :=
  let quote := if b.contains 39 && !b.contains 34 then '"' else '\''
  let body := b.toList.foldl (fun acc x =>
    let c := Char.ofNat x.toNat
    acc ++ (if x == 92 then "\\\\"
      else if c == quote then s!"\\{c}"
      else if x == 9 then "\\t" else if x == 10 then "\\n" else if x == 13 then "\\r"
      else if x < 32 || x ≥ 127 then
        let h := Nat.toDigits 16 x.toNat
        "\\x" ++ String.ofList (if h.length < 2 then '0' :: h else h)
      else String.singleton c)) ""
  s!"b{quote}{body}{quote}"

/-- The name of the class `cls` of an object, for `<T object>` and an exception's type. -/
def className (st : ObjStore Run) (cls : Value) : String :=
  match cls with
  | .builtin b => b.info.name
  | .obj id => match st.get? id with
    | some { payload := .cls c, .. } => c.qualname
    | _ => "?"
  | _ => "?"

/-- `render v`, with `fuel` the depth of nesting left and `seen` the objects being rendered. -/
def renderN (st : ObjStore Run) : Nat → List ObjId → Value → RenderM String
  | 0, _, _ => throw "a value nested deeper than the trace prints"
  | fuel + 1, seen, v =>
    let r := renderN st fuel seen
    match v with
    | .none => pure "None"
    | .bool b => pure (if b then "True" else "False")
    | .int i => intText i
    | .float bits => pure (Format.floatRepr bits)
    | .str s => pure (Format.strRepr s.s)
    | .bytes b => pure (bytesText b)
    | .tuple xs => do
      let parts ← xs.toList.mapM r
      pure (if parts.length == 1 then s!"({parts.head!},)" else s!"({", ".intercalate parts})")
    | .symHash _ => throw "the number of a symbolic hash"
    | .builtin b =>
      if b.info.kind == .type then pure s!"<class '{b.info.name}'>"
      else match v.classOfImm with
        | some (.builtin c) => pure s!"<{c.info.name} object>"
        | _ => throw s!"the trace does not render the built-in {b.info.name}"
    | .descr _ _ k => pure s!"<{k.descrType.info.name} object>"
    | .bound _ _ _ .tpNew => throw "a type's tp_new outside a class call"
    | .bound _ _ _ k => pure s!"<{k.boundType.info.name} object>"
    | .method .. => pure "<method object>"
    | .ellipsis => pure "Ellipsis"
    | .notImplemented => pure "NotImplemented"
    | .range a b c => do
      if c == 1 then pure s!"range({← intText a}, {← intText b})"
      else pure s!"range({← intText a}, {← intText b}, {← intText c})"
    | .slice a b c => do pure s!"slice({← r a}, {← r b}, {← r c})"
    | .obj id =>
      if seen.contains id then pure "..." else
      let r' := renderN st fuel (id :: seen)
      match st.get? id with
      | some { cls := .builtin .list, payload := .list xs _, .. } => do
        pure s!"[{", ".intercalate (← xs.toList.mapM r')}]"
      | some { cls := .builtin .dict, payload := .dict t, .. } => do
        let parts ← t.live.toList.mapM fun (e, x) => do pure s!"{← r' e.key}: {← r' x}"
        pure s!"\{{", ".intercalate parts}}"
      | some { cls := .builtin .«set», payload := .set t, .. } => do
        let parts := ((← t.active.mapM fun (_, _, k) => r' k).toArray.qsort (· < ·)).toList
        pure (if parts.isEmpty then "set()" else s!"\{{", ".intercalate parts}}")
      | some { cls := .builtin .«frozenset», payload := .frozenset t _, .. } => do
        let parts := ((← t.active.mapM fun (_, _, k) => r' k).toArray.qsort (· < ·)).toList
        pure (if parts.isEmpty then "frozenset()" else s!"frozenset(\{{", ".intercalate parts}})")
      | some { payload := .cls c, .. } => pure s!"<class '{c.qualname}'>"
      | some o => pure s!"<{className st o.cls} object>"
      | none => throw s!"object {id} does not exist"
    | v => throw s!"the trace does not render {reprStr v}"

/-- `render v`. -/
def render (st : ObjStore Run) (v : Value) : RenderM String := renderN st 100 [] v

/-- `str(e)` for an exception `e` of the class `cls`: for a user class, that of the first built-in
class of its MRO, when no user class before it defines `__str__`; `none` otherwise, since a user
`__str__` runs code that the trace can't run. An `ImportError` whose `msg` is a `str` gives it, as
`ImportError.__str__` does. -/
def excStrOf (st : ObjStore Run) (cls : Value) (e : ExcState) : Option String :=
  let builtinStr (b : Value) : Option String := match b with
    | .builtin bt =>
      if bt.info.mro.contains .ImportError then
        match ((e.fields.find? (·.1 == "msg")).map (·.2) : Option Value) with
        | some (.str s) => some s.s
        | _ => excStr b e.args
      else excStr b e.args
    | _ => none
  match cls with
  | .obj id => match st.get? id with
    | some { payload := .cls c, .. } =>
      let defines (v : Value) : Bool := match v with
        | .obj cid => match st.get? cid with
          | some { payload := .cls c', .. } => match st.get? c'.ns with
            | some { payload := .dict t, .. } =>
              t.live.any fun (e, _) => e.key == .str (.ofString "__str__")
            | _ => true
          | _ => true
        | _ => false
      match c.mro.toList.find? (· matches .builtin _) with
      | some b => if c.mro.toList.takeWhile (!· matches .builtin _) |>.any defines then none
        else builtinStr b
      | none => none
    | _ => none
  | _ => builtinStr cls

/-- `raised <ExcType>` for the exception `v`, the start of its outcome line, if its type's name
holds no line break. -/
def excTypeLine (st : ObjStore Run) (v : Value) : Option String :=
  match v with
  | .obj id => match st.get? id with
    | some { cls, payload := .exc _, .. } =>
      let name := className st cls
      if name.contains '\n' then none else some s!"raised {name}"
    | _ => none
  | _ => none

/-- The outcome section of an exception: its type and `str`, then the types along its chain,
a `cause` before a `context` as CPython prints them, `fuel` the links left. -/
def excLines (st : ObjStore Run) : Nat → Value → RenderM (List String)
  | 0, _ => pure []
  | fuel + 1, .obj id =>
    match st.get? id with
    | some { cls, payload := .exc e, .. } => do
      let name := className st cls
      let some str := excStrOf st cls e | throw s!"the str() of an uncaught {name}"
      let lines := s!"raised {name}: {str}" :: excChain st fuel [id] e
      -- A line break would let the text forge a section's header, such as a gap's.
      if lines.any (·.contains '\n') then throw "an exception whose text has a line break"
      pure lines
    | _ => throw "an exception that is not an exception object"
  | _, v => throw s!"an exception that is not an object: {reprStr v}"
where
  /-- The types along the chain of `e`, up to an exception of `seen`, as CPython's traceback
  printer stops at one. -/
  excChain (st : ObjStore Run) : Nat → List ObjId → ExcState → List String
    | 0, _, _ => []
    | fuel + 1, seen, e =>
      let link : Option (String × Value) :=
        match e.cause with
        | .none => if e.suppressContext then none else match e.context with
          | .none => none
          | c => some ("context", c)
        | c => some ("cause", c)
      match link with
      | none => []
      | some (kind, .obj id) => if seen.contains id then [] else match st.get? id with
        | some { cls, payload := .exc e', .. } =>
          s!"  {kind} {className st cls}" :: excChain st fuel (id :: seen) e'
        | _ => []
      | some _ => []

/-- The `Value` at location `l` of `heap`, if it holds one. -/
def readValue (heap : Heap PySem.model.at) (l : Nat) : Option Value :=
  heap.cell l PySem.T.py.Value (fun hl ht => some (heap.valueAt hl ht : Value)) (fun _ => none)

/-- The lines of the globals section: every global of `module` but the dunder names, and
`__name__`, `__doc__` and `__annotations__` if set, sorted by name.  A global that can't be
rendered ends the section with its gap's line, after the globals before it. -/
def globalLines (w : World Run) (heap : Heap PySem.model.at) (module : String) : List String :=
  match w.modules.map[module]? with
  | none => []
  | some e => go (e.cells.toList.filter fun (n, _) =>
    !(n.startsWith "__" && n.endsWith "__") || n == "__name__" || n == "__doc__" ||
      n == "__annotations__")
where
  go : List (String × Ref Run Value) → List String
    | [] => []
    | (n, r) :: rest => match readValue heap r.loc with
      | some (.undef _) | none => go rest
      | some v => match render w.store v with
        | .ok s =>
          -- A line break would let the text forge a section's header, such as a gap's.
          if s.contains '\n' then ["--- gap a render with a line break"]
          else s!"{n} = {s}" :: go rest
        | .error msg => [s!"--- gap {msg}"]

/-- A render's text, or the gap's line, also for a text with a line break, which could forge a
section's header. -/
def renderOr (r : RenderM String) : String :=
  match r with
  | .ok s => if s.contains '\n' then "--- gap a render with a line break" else s
  | .error msg => s!"--- gap {msg}"

/-- The line of a fault. -/
def faultLine (f : Fault) : String :=
  match f with
  | .gap msg => s!"--- gap {msg}"
  | .outOfFuel => "--- out of fuel"
  | f => s!"--- fault {repr f}"

/-- The sections of a run of a module's body: its stdout, its outcome and the globals of
`module`; and whether the trace ends there, at a gap of the outcome or of the globals. -/
def bodySections (module : String) (o : Outcome PySem.model) : List String × Bool :=
  -- The program's output exactly as it printed it, so that an output that differs only in its
  -- final newline differs in the trace too.  The header gives its length in characters, so that a
  -- reader of the trace never takes a line of the output for a section's header.
  let out := String.join o.snapshot.world.out.pieces.toList
  let stdout := [s!"--- stdout {out.length}\n{out}"]
  match o.result with
  | .fault f => (stdout ++ [faultLine f], false)
  | .ok _ =>
    let globals := "--- globals" :: globalLines o.snapshot.world o.snapshot.heap module
    let gapped := globals.getLast?.any (·.startsWith "--- gap ")
    match o.read? (Except Value Value) with
    | some (.ok _) => (stdout ++ ["--- outcome", "ok"] ++ globals, gapped)
    | some (.error e) => match excLines o.snapshot.world.store 100 e with
      | .ok ls => (stdout ++ "--- outcome" :: ls ++ globals, gapped)
      -- The section's header comes first: the run has ended, so its output is complete.  The
      -- exception's type comes before the gap, so that the gap can't hide a wrong outcome.
      | .error msg => (stdout ++ "--- outcome" :: (excTypeLine o.snapshot.world.store e).toList ++
          [s!"--- gap {msg}"], true)
    | none => (stdout ++ ["--- fault a result that is not an Except"], false)

/-- The section of a named function's run: its rendered return value, the exception it
raised, or its fault. -/
def resultSection (name : Name) (o : Outcome PySem.model) : List String :=
  let head := s!"--- result {nameStr name}"
  match o.result with
  | .fault f => [head, faultLine f]
  | .ok _ => match o.read? (Except Value Value) with
    | some (.ok v) => [head, renderOr (render o.snapshot.world.store v)]
    | some (.error e) => match excLines o.snapshot.world.store 100 e with
      | .ok ls => head :: ls
      | .error msg => [head, s!"--- gap {msg}"]
    | none => [head, "--- fault a result that is not an Except"]

/-- **Run the body `body` of the translated module `prog`, whose module is `module`, then each
function of `fns`**, each from where the previous run ended (`runPreparedFrom`), and print the
trace.  Each function of `fns` takes no parameters.  After a run that faulted, the remaining
functions run nothing, and their sections show that fault.  A gap in the body's outcome or
globals ends the trace. -/
def runModuleThen {α : Type} (prog : Module Py.env α) (body : Name) (module : String)
    (fns : List Name) (opts : RunOptions := {}) : String :=
  match prepare PySem.model prog body with
  | .error f => faultLine f
  | .ok ⟨lm, hw, i⟩ =>
    let o := runPrepared hw i #[] opts.fuel (fun _ => 0)
    let (body, ended) := bodySections module o
    if ended then "\n".intercalate body ++ "\n" else
    let (_, rest) := fns.foldl (init := (o, ([] : List String))) fun (prev, acc) f =>
      match lm.funcIndex f with
      | none => (prev, acc ++ [s!"--- result {nameStr f}", s!"--- fault no function {nameStr f}"])
      | some j => match runPreparedFrom hw j prev #[] opts.fuel with
        | .ok o' => (o', acc ++ resultSection f o')
        | .error p => (p, acc ++ resultSection f p)
    "\n".intercalate (body ++ rest) ++ "\n"

end

end StrataPython.Dyn.Sem
