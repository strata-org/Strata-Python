/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Classes
public import StrataPython.Dyn.Sem.Proto.Iter
public import StrataPython.Dyn.Sem.Proto.Values

set_option autoImplicit false

/-!
# The contract operations, over the record of primitives

Generic over the record of primitives, as the other combinators of `Sem/Proto/` are.  Each follows
its operation's docstring in `StrataPython/Dyn/Env.lean`:

* the arguments of a call: `argOf`, `extraKwargs`, `bindsTo`;
* the tests: `stdClass`, `typeIsSubclass`, `strIsOneOf`, `intIsOneOf`, `isImmutableScalar`,
  `dictKeysWithin`; `isInstance` and `len` are the combinators of `isinstance` and `len`.

A key or a value counts as a `str` here only if it is exactly a `str`, which the model keeps as an
immediate; an instance of a subclass of `str` is an object, and never counts.  So only
`isInstance` and `len` run user code, as `isinstance` and `len` do.  An operand that is unassigned (`undef`) is no `str`, `int`, tuple or dict, so the
operations whose docstrings are total in their operand's kind treat it as one of the other kinds,
and the operations that would raise stop with a gap on it, since CPython has no unassigned
values.
-/

namespace StrataPython.Dyn.Sem.Contracts

open StrataPython.Dyn.Sem

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The characters of `v` if it is exactly a `str`. -/
def exactStr? [PyPure m V] (v : V) : m (Option String) := do
  match ← PyPure.immViewAll v with
  | some (.str s) => pure (some s.s)
  | _ => pure none

/-- The elements of `v` if it is exactly a tuple. -/
def exactTuple? [PyPure m V] (v : V) : m (Option (Array V)) := do
  match ← PyPure.immViewAll v with
  | some (.tuple xs) => pure (some xs)
  | _ => pure none

/-- Whether `v` is exactly a dict: an object whose class is `dict`. -/
def isExactDict [PyReads m V] (v : V) : m Bool := do
  if (← PyPure.immViewAll v).isSome || (← PyPure.isUndef v) then return false
  return (← Proto.builtinClass? v) matches some .dict

/-- The keys of the dict `d` that are exactly `str`s, with each entry's position and value, and
whether every key is exactly a `str`; `none` if `d` is not exactly a dict. -/
def strEntries? [PyReads m V] (d : V) : m (Option (Array (Option String × V))) := do
  unless ← isExactDict d do return none
  let es ← PyReads.dictEntries d
  return some (← es.mapM fun (k, v, _) => return (← exactStr? k, v))

/-- `py.argOf args kwargs pos name default`: `args[pos]` if `args` is exactly a tuple and `pos` is
in range, else the value of the key of `kwargs` that is exactly the `str` `name`, if `kwargs` is
exactly a dict, else `default`.  A dict holds at most one key equal to `name`. -/
def argOf [PyReads m V] (args kwargs : V) (pos : Int) (name : String) (default : V) : m V := do
  if let some xs ← exactTuple? args then
    if 0 ≤ pos then
      if h : pos.toNat < xs.size then return xs[pos.toNat]
  if let some es ← strEntries? kwargs then
    for (k, v) in es do
      if k == some name then return v
  return default

/-- `py.extraKwargs kwargs names`: a new dict of the entries of `kwargs`, in order, but those whose
key is exactly a `str` among `names`; an empty dict if `kwargs` is not exactly a dict.  The new
dict keeps each entry's stored hash, so no hash or comparison runs. -/
def extraKwargs [PyReads m V] (kwargs : V) (names : Array String) : m V := do
  let some es ← strEntries? kwargs | PyPure.allocDict
  let drop := es.map fun (k, _) => match k with
    | some s => names.contains s
    | none => false
  PyReads.allocDictFrom kwargs fun i => !(drop[i]?.getD false)

/-- `py.bindsTo args kwargs nPos varKw names`: whether binding `args` and `kwargs` to the
parameters `names` raises none of the `TypeError`s that the docstring lists. -/
def bindsTo [PyReads m V] (args kwargs : V) (nPos : Int) (varKw : Bool) (names : Array String) :
    m Bool := do
  let some xs ← exactTuple? args | return false
  let some es ← strEntries? kwargs | return false
  let some keys := es.mapM (·.1) | return false
  if nPos < 0 || nPos.toNat > names.size || xs.size > nPos.toNat then return false
  let positional := names.extract 0 xs.size
  if keys.any positional.contains then return false
  if !varKw && !keys.all names.contains then return false
  return true

/-- `py.stdClass module name`: the class that the module `module` of CPython 3.12's standard
library defines as `name`.  Only `builtins` is modelled; a name of `builtins` that isn't a type is
not well defined.  Either stops with a gap. -/
def stdClass [PyPure m V] (module name : String) : m V := do
  unless module == "builtins" do
    PyPure.gap s!"py.stdClass: the module {module} is not modelled"
  match Builtin.ofName? name with
  | some b =>
    if Builtin.dictNames.contains name && b.info.kind == .type then
      return PyPure.imm (m := m) (.builtin b)
    PyPure.gap s!"py.stdClass: builtins.{name} is not a class"
  | none => PyPure.gap s!"py.stdClass: builtins.{name} is not a class"

/-- Whether the class `c`'s metaclass is `abc.ABCMeta` or a subclass of it: then a registration or
a `__subclasshook__` of the standard library could count. -/
def hasABCMeta [PyReads m V] (c : V) : m Bool := do
  let some mro ← Proto.mroOf (← PyReads.classOf c) | return false
  for t in mro do
    if let some cd ← Proto.classData? t then
      if cd.module == "abc" && cd.qualname == "ABCMeta" then return true
  return false

/-- `py.typeIsSubclass v cls`: whether `type(v)`, by its stored MRO, is `cls` or a subclass of it,
or of one class of the tuple `cls`.  `cls` must be a class or a flat tuple of classes, else
`TypeError`; every element is checked first.  An instance of a subclass of `tuple` stops with a
gap, and so does an undefined operand or element. -/
def typeIsSubclass [PyReads m V] (v cls : V) : m Bool := do
  if (← PyPure.isUndef v) || (← PyPure.isUndef cls) then
    PyPure.gap "py.typeIsSubclass: an operand is undefined"
  let cs ← match ← PyPure.immViewAll cls with
    | some (.tuple cs) => pure cs
    | _ =>
      if (← Proto.builtinBase? cls) matches some .tuple then
        PyPure.gap "py.typeIsSubclass: an instance of a subclass of tuple is not modelled"
      pure #[cls]
  for c in cs do
    if ← PyPure.isUndef c then PyPure.gap "py.typeIsSubclass: an operand is undefined"
  for c in cs do
    unless ← Proto.isType c do
      Proto.raiseBuiltin "TypeError" "typeIsSubclass() arg 2 must be a class or a tuple of classes"
  for c in cs do
    if ← hasABCMeta c then
      PyPure.gap "py.typeIsSubclass: a class whose metaclass is abc.ABCMeta is not modelled"
  let some mro ← Proto.mroOf (← PyReads.classOf v) |
    PyPure.modelInvariant "py.typeIsSubclass: the type of a value has no MRO"
  for c in cs do
    for t in mro do
      match ← PyPure.identical t c with
      | .yes => return true
      | .no => pure ()
      | .unknown => PyPure.gap "py.typeIsSubclass: the identity of two classes is unknown"
  return false

/-- `py.isInstance v cls`: `isinstance(v, cls)`. -/
def isInstance [PyCalls m V] (v cls : V) : m Bool := do
  if (← PyPure.isUndef v) || (← PyPure.isUndef cls) then
    PyPure.gap "py.isInstance: an operand is undefined"
  Builtins.isinstanceN Proto.dispatchDepth v cls

/-- `py.len v`: `len(v)`, as a Python `int`. -/
def len [PyCalls m V] (v : V) : m V := do
  if ← PyPure.isUndef v then PyPure.gap "py.len: an operand is undefined"
  return PyPure.imm (m := m) (.int (← Proto.pyLen v))

/-- `py.strIsOneOf v lits`: whether `v` is exactly a `str` with the characters of one of `lits`. -/
def strIsOneOf [PyPure m V] (v : V) (lits : Array String) : m Bool := do
  match ← exactStr? v with
  | some s => return lits.contains s
  | none => return false

/-- `py.intIsOneOf v lits`: whether `v` is exactly an `int`, not a `bool`, whose value is one of
`lits`.  An `int` whose value depends on the hash seed stops with a gap. -/
def intIsOneOf [PyPure m V] (v : V) (lits : Array Int) : m Bool := do
  match ← PyPure.immViewAll v with
  | some (.int i) => return lits.contains i
  | some (.symHash _) => PyPure.gap "py.intIsOneOf: an int whose value depends on the hash seed"
  | _ => return false

/-- `py.isImmutableScalar v`: whether the type of `v` is exactly `int`, `float`, `complex`, `bool`,
`str`, `bytes` or `NoneType`.  The model has no `complex` value. -/
def isImmutableScalar [PyPure m V] (v : V) : m Bool := do
  match ← PyPure.immViewAll v with
  | some (.int _) | some (.symHash _) | some (.float _) | some (.bool _) | some (.str _)
  | some (.bytes _) | some .none => return true
  | _ => return false

/-- `py.dictKeysWithin d keys`: whether `d` is exactly a dict whose keys are all exactly `str`s
among `keys`. -/
def dictKeysWithin [PyReads m V] (d : V) (keys : Array String) : m Bool := do
  let some es ← strEntries? d | return false
  return es.all fun (k, _) => match k with
    | some s => keys.contains s
    | none => false

end

end

end StrataPython.Dyn.Sem.Contracts
