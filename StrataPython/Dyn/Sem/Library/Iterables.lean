/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Bind
public import StrataPython.Dyn.Sem.Proto.Containers
public import StrataPython.Dyn.Sem.Proto.Calls
public import StrataPython.Dyn.Sem.Proto.Iter
public import StrataPython.Dyn.Sem.Library.Sum

set_option autoImplicit false

/-!
# The functions over iterables

Generic over the record, CPython 3.12's `any`, `all`, `sum`, `max` and `min` (`builtin_any`,
`builtin_all`, `builtin_sum_impl` and `min_max` in `Python/bltinmodule.c`) as step machines.
Each activation walks the iterator with `Proto.forEachItem`; a walk that doesn't end gives the
machine's frame, a `LoopState`, which `py.call` saves for the next activation. Called inside another
operation's step, where no frame can be saved, the same walk runs once, and a walk that needs
another activation stops with a gap.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The binding of the method `name` of the built-in type `t` with no arguments (`METH_NOARGS`),
called on `self`. A wrong call's message names the method by `t` for an immediate call
`x.m(…)` or a call through the descriptor ("int.__trunc__() takes no arguments (1 given)"), but
by the class of `self` for a bound method object called later (`f = I(1).__trunc__; f(1)` gives
"I.__trunc__() …"). A body can't see the call form, so a wrong call on a value whose class is not
exactly `t` stops with a gap; a slot wrapper's own style is `noArg`'s. -/
def noArgsMethod [PyReads m V] (t : Builtin) (name : String) (self args kwargs : V) : m Unit := do
  if (← tupleItems args).isEmpty && (← PyReads.dictLen kwargs) == 0 then return
  let exact ← match ← PyPure.immView (← PyReads.classOf self) with
    | some (.builtin b) => pure (b == t)
    | _ => pure false
  unless exact do
    PyPure.gap s!"the message of a wrong call of {t.info.name}.{name} depends on how it is called"
  discard <| bindBuiltinArgs { name, qualname := s!"{t.info.name}.{name}", style := .noArgs }
    args kwargs

/-- The gap of a looping built-in reached inside another operation's step, whose walk needs
another activation. -/
def midStepGap [PyPure m V] {α : Type} : m α :=
  PyPure.gap "a looping built-in was reached inside an operation"

/-- One activation of `any` or `all` over the iterator `it`: the result once an item decides
it or the iterator ends; otherwise `it`, to go on from. -/
def anyAllStep [PyWrites m V] (stopAt : Bool) (it : V) : m (LoopStep V Bool) := do
  match ← forEachItem iterNext it false fun x _ => do
      if (← truthy x) == stopAt then pure (.stop true) else pure (.next false) with
  | .done found => return .done (if found then stopAt else !stopAt)
  | .more _ => return .more it

/-- **An inexact set whose walk can't change a result**: for `v` an exact `set` or `frozenset`
whose order the model doesn't know (`SetView.inOrder?` gives none) and whose members all have one
exact type, `int` or `str`, or that is empty, a tuple of its members in no promised order; else
`v`. Members of these
types run no user code, compare totally, and are never equal to each other, so `any`, `all`,
`max` and `min` without a key, and `sum` without a start or with an exact `int` start, give the
same result over that tuple as over the set in CPython's order. Floats are left out: a NaN and
rounding make the result depend on the order. -/
def orderFree [PyReads m V] (v : V) : m V := do
  unless (← classIs v .set) || (← classIs v .frozenset) do return v
  let some vw ← PyReads.setView v | return v
  if vw.inOrder?.isSome then return v
  let xs := vw.unordered.map (·.1)
  let kinds ← xs.mapM fun x => do
    match ← PyPure.immView x with
    | some (.int _) => pure (some true)
    | some (.str _) => pure (some false)
    | _ => pure none
  match kinds[0]? with
  | none => return PyPure.imm (m := m) (.tuple #[])
  | some (some k) =>
    if kinds.all (· == some k) then return PyPure.imm (m := m) (.tuple xs) else return v
  | some none => return v

/-- The iterator of the argument of `any` or `all` (`METH_O`). -/
def anyAllIter [PyWrites m V] (name : String) (args kwargs : V) : m V := do
  let b ← bindBuiltinArgs { name, qualname := name, style := .methO } args kwargs
  let #[some x] := b.params |
    PyPure.modelInvariant s!"{name}: the binder gave a parameter array of another shape"
  getIter (← orderFree x)

/-- An item of `sum`, as its phases tell items apart: an exact `int` or `bool`, an exact `float`,
an instance of a subclass of `int`, or anything else. -/
def sumItem [PyReads m V] (x : V) : m Sum.Item := do
  match ← PyPure.immView x with
  | some (.int i) => pure (.int i true)
  | some (.bool b) => pure (.int (if b then 1 else 0) true)
  | some (.float bits) => pure (.float bits)
  | some _ => pure .other
  | none =>
    match ← PyReads.numView x with
    | some (.int i) => pure (.int i false)
    | _ => pure .other

/-- Whether the class of `v` is the built-in type `b` or a subclass of it. -/
def isInstanceOfBuiltin [PyReads m V] (v : V) (b : Builtin) : m Bool := do
  let some mro ← mroOf (← PyReads.classOf v) | return false
  mro.anyM fun c => do
    match ← PyPure.immView c with
    | some (.builtin b') => pure (b' == b)
    | _ => pure false

/-- The start of `sum`, as its phases tell starts apart: not given, an exact `int` or `float`,
an instance of `str`, `bytes` or `bytearray` (a subclass included), or anything else. -/
def sumStart [PyReads m V] : Option V → m (Sum.Start V)
  | none => pure .none
  | some v => do
    match ← PyPure.immView v with
    | some (.int i) => pure (.int i v)
    | some (.float bits) => pure (.float bits)
    | some (.str _) => pure (.rejected .str)
    | some (.bytes _) => pure (.rejected .bytes)
    | some _ => pure (.other v)
    | none =>
      if (← PyReads.strView v).isSome then return .rejected .str
      if (← PyReads.bytesView v).isSome then return .rejected .bytes
      if ← isInstanceOfBuiltin v .bytearray then return .rejected .bytearray
      pure (.other v)

/-- The iterator and the first phase of a call of `sum`: CPython makes the iterator before it
checks the start. -/
def sumInit [PyWrites m V] (args kwargs : V) : m (V × Sum.State V) := do
  let sig : BuiltinSig :=
    { name := "sum", qualname := "sum", style := .keywords, posonly := 1, minpos := 1,
      maxpos := 2, kwnames := #["start"] }
  let b ← bindBuiltinArgs sig args kwargs
  let #[some iterable, start] := b.params |
    PyPure.modelInvariant "sum: the binder gave a parameter array of another shape"
  let st ← sumStart start
  -- Over an inexact set, the walk's order changes no result only from an exact int start.
  let it ← getIter (← if st matches .none | .int .. then orderFree iterable else pure iterable)
  match Sum.init st with
  | .ok s => return (it, s)
  | .error f => ofFailure f

/-- A total of `sum` as an object. -/
def totalValue [PyPure m V] : Sum.Total V → V
  | .int i => PyPure.imm (m := m) (.int i)
  | .float bits => PyPure.imm (m := m) (.float bits)
  | .obj v => v

/-- One activation of `sum` over the iterator `it`, from the phase `s`: the sum once the iterator
ends; otherwise the phase to go on from. An item that the phase doesn't take is added with `+`,
as `PyNumber_Add`. -/
def sumStep [PyWrites m V] (it : V) (s : Sum.State V) : m (LoopStep (Sum.State V) V) := do
  let walk ← forEachItem iterNext it s fun x s => do
    match Sum.step s (← sumItem x) with
    | .next s' => pure (.next s')
    | .add t =>
      let r ← binaryOp .add (totalValue (m := m) t) x
      let bits := match ← PyPure.immView r with
        | some (.float b) => some b
        | _ => none
      pure (.next (Sum.afterAdd s r bits))
  match walk with
  | .more s => return .more s
  | .done s => return .done (totalValue (m := m) (Sum.finish s))

/-- **`any(it)` and `all(it)` inside another operation's step**: one walk, which must end. -/
def anyAllBody [PyWrites m V] (stopAt : Bool) (_self args kwargs : V) : m V := do
  let name := if stopAt then "any" else "all"
  match ← anyAllStep stopAt (← anyAllIter name args kwargs) with
  | .done r => pure (PyPure.imm (m := m) (.bool r))
  | .more _ => midStepGap

/-- **`sum(it, start)` inside another operation's step**: one walk, which must end. -/
def sumBody [PyWrites m V] (_self args kwargs : V) : m V := do
  let (it, s) ← sumInit args kwargs
  match ← sumStep it s with
  | .done r => pure r
  | .more _ => midStepGap

/-- The iterator, the key function (none for `None`) and the default of a call of `max` or
`min`: the iterator of its one positional argument, or of the tuple of its positional arguments
when there are several. -/
def minMaxInit [PyWrites m V] (isMax : Bool) (args kwargs : V) : m (V × Option V × Option V) := do
  let name := if isMax then "max" else "min"
  let xs ← tupleItems args
  let v ← match xs with
    | #[] => raiseBuiltin "TypeError" s!"{name} expected at least 1 argument, got 0"
    | #[x] => pure x
    | _ => pure args
  let sig : BuiltinSig :=
    { name, qualname := name, style := .keywords, kwnames := #["key", "default"] }
  let b ← bindBuiltinArgs sig (PyPure.imm (m := m) (.tuple #[])) kwargs
  let #[key, dflt] := b.params |
    PyPure.modelInvariant s!"{name}: the binder gave a parameter array of another shape"
  if xs.size > 1 && dflt.isSome then
    raiseBuiltin "TypeError"
      s!"Cannot specify a default for {name}() with multiple positional arguments"
  let key ← match key with
    | some k => pure (if (← PyPure.immView k) matches some .none then none else some k)
    | none => pure none
  let it ← getIter (← if key.isNone then orderFree v else pure v)
  return (it, key, dflt)

/-- The best of `best` and the item `item` with the key `val`: the later item replaces the best
one only if its key is greater (`max`) or less (`min`), so the first of equal items wins. -/
def minMaxOffer [PyCalls m V] (isMax : Bool) (best : Option (V × V)) (item val : V) :
    m (Option (V × V)) := do
  match best with
  | none => pure (some (item, val))
  | some (bi, bv) =>
    if ← richCompare (if isMax then .gt else .lt) val bv then pure (some (item, val))
    else pure (some (bi, bv))

/-- What an activation of `max` or `min` ends with. -/
inductive MinMaxStep (S V : Type) where
  /-- The iterator ended, with the best item and its key. -/
  | done (best : Option (V × V))
  /-- The walk needs another activation. -/
  | more (best : Option (V × V))
  /-- The key call of `item` suspended, with its frames. -/
  | suspended (best : Option (V × V)) (item : V) (frames : List S)

/-- One activation of `max` or `min` over the iterator `it`, where `callKey k x` calls the key
function `k` on the item `x`. -/
def minMaxStep [PyWrites m V] {S : Type} (callKey : V → V → m (CallStep S V)) (isMax : Bool)
    (it : V) (key : Option V) (best : Option (V × V)) : m (MinMaxStep S V) := do
  let walk ← forEachItem iterNext it (best, (none : Option (V × List S))) fun x (best, _) => do
    match key with
    | none => pure (.next (← minMaxOffer isMax best x x, none))
    | some k =>
      match ← callKey k x with
      | .done val => pure (.next (← minMaxOffer isMax best x val, none))
      | .suspend fs => pure (.stop (best, some (x, fs)))
  match walk with
  | .done (best, some (x, fs)) => return .suspended best x fs
  | .done (best, none) => return .done best
  | .more (best, _) => return .more best

/-- The result of `max` or `min` once the iterator ended: the best item, else the default, else
CPython's `ValueError`. -/
def minMaxResult [PyCalls m V] (isMax : Bool) (dflt : Option V) : Option (V × V) → m V
  | some (bi, _) => pure bi
  | none => match dflt with
    | some d => pure d
    | none =>
      raiseBuiltin "ValueError" s!"{if isMax then "max" else "min"}() iterable argument is empty"

/-- **`max(…)` and `min(…)` inside another operation's step**: one walk, which must end; the key
calls are plain calls. -/
def minMaxBody [PyWrites m V] (isMax : Bool) (_self args kwargs : V) : m V := do
  let (it, key, dflt) ← minMaxInit isMax args kwargs
  let callKey (k x : V) : m (CallStep Unit V) := do
    return .done (← callN dispatchDepth k (PyPure.imm (m := m) (.tuple #[x])) (← PyPure.allocDict))
  match ← minMaxStep callKey isMax it key none with
  | .done best => minMaxResult isMax dflt best
  | .more _ => midStepGap
  | .suspended .. => PyPure.modelInvariant "a plain key call suspended"

/-- The bodies of the built-in functions over iterables. -/
def iterablesFunction : Builtin → Option BuiltinImpl
  | .any => some fun {_} {_} [_] [_] => anyAllBody true
  | .all => some fun {_} {_} [_] [_] => anyAllBody false
  | .sum => some fun {_} {_} [_] [_] => sumBody
  | .max => some fun {_} {_} [_] [_] => minMaxBody true
  | .min => some fun {_} {_} [_] [_] => minMaxBody false
  | _ => none

end

end

end StrataPython.Dyn.Sem.Library
