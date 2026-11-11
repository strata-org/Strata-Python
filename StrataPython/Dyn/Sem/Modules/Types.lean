/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Common
public import StrataPython.Dyn.Sem.Proto.Repr

set_option autoImplicit false

/-!
# `types.GenericAlias` and `types.UnionType`

`list[int]` is a `types.GenericAlias` and `int | None` a `types.UnionType`. Both are C types of
CPython 3.12 (`Objects/genericaliasobject.c` and `Objects/unionobject.c`), ported here as store
classes whose methods are native functions. A `GenericAlias` keeps its origin and its arguments
tuple as opaque state, and a `UnionType` its arguments tuple.

CPython counts C levels on the nested paths (`PyObject_Repr`, `PyObject_RichCompare`): measured on
3.12.15, `GenericAlias`'s `==` raises `RecursionError` at depth 5,000 and `UnionType`'s at 2,500
(a level being `list[x] | None`). So each body counts, with `withDepth`, at least CPython's levels,
and the model stops with a gap past its own limit before CPython raises.
-/

namespace StrataPython.Dyn.Sem.Modules

open Proto Builtins

@[expose] public section

/-- The tag of a `GenericAlias`'s opaque state: the origin and the arguments tuple. -/
def gaTag : String := "types.GenericAlias"

/-- The tag of a `UnionType`'s opaque state: the arguments tuple. -/
def unionTag : String := "types.UnionType"

/-- The native key of the method `name` of the class `cls`. -/
def methodKey (cls name : String) : String := s!"{cls}.{name}"

/-- `types.GenericAlias`: `vars()` of CPython 3.12's class, the members and getsets, `__new__`,
`__iter__`, `__reduce__` and `__dir__` unmodelled. Subclassing it is unmodelled too. -/
def gaSpec : ClassSpec where
  name := "GenericAlias"
  qualname := "GenericAlias"
  «module» := "types"
  tpName := some "types.GenericAlias"
  immutable := true
  instanceWritesGap := true
  cType := true
  asBase := .gap
  entries :=
    (#["__repr__", "__hash__", "__call__", "__getattribute__", "__lt__", "__le__", "__eq__",
        "__ne__", "__gt__", "__ge__", "__or__", "__ror__", "__getitem__"].map fun n =>
      Entry.native n (methodKey gaTag n) .wrapperDescriptor) ++
    (#["__mro_entries__", "__instancecheck__", "__subclasscheck__"].map fun n =>
      Entry.native n (methodKey gaTag n) .methodDescriptor) ++
    #[.str "__doc__" ("Represent a PEP 585 generic type\n\nE.g. for t = list[int], t.__origin__ is " ++
      "list and t.__args__ is (int,).")]
  gapped := #["__new__", "__iter__", "__reduce__", "__dir__", "__origin__", "__args__",
    "__unpacked__", "__parameters__", "__typing_unpacked_tuple_args__"]

/-- `types.UnionType`: `vars()` of CPython 3.12's class, its member and getset unmodelled; it has
no `__new__` (calling the class is unmodelled). -/
def unionSpec : ClassSpec where
  name := "UnionType"
  qualname := "UnionType"
  «module» := "types"
  tpName := some "types.UnionType"
  immutable := true
  instanceWritesGap := true
  cType := true
  asBase := .notAcceptable
  entries :=
    (#["__repr__", "__hash__", "__getattribute__", "__lt__", "__le__", "__eq__", "__ne__", "__gt__",
        "__ge__", "__or__", "__ror__", "__getitem__"].map fun n =>
      Entry.native n (methodKey unionTag n) .wrapperDescriptor) ++
    #[.str "__doc__" "Represent a PEP 604 union type\n\nE.g. for int | str"]
  gapped := #["__new__", "__args__", "__parameters__"]

section
variable {m : Type → Type 1} {V : Type}

/-- The origin and the arguments of a `GenericAlias`, or `none` for any other value. -/
def gaParts? [PyReads m V] (v : V) : m (Option (V × V)) := do
  match ← PyReads.objView v with
  | some (.opaque t st) =>
    if t == gaTag then
      if h : st.size = 2 then return some (st[0], st[1])
      PyPure.modelInvariant "a GenericAlias's state is its origin and its arguments"
    return none
  | _ => return none

/-- The arguments tuple of a `UnionType`, or `none` for any other value. -/
def unionArgs? [PyReads m V] (v : V) : m (Option V) := do
  match ← PyReads.objView v with
  | some (.opaque t st) =>
    if t == unionTag then
      if h : st.size = 1 then return some st[0]
      PyPure.modelInvariant "a UnionType's state is its arguments tuple"
    return none
  | _ => return none

/-- Whether `v` is `NoneType`. -/
def isNoneType [PyPure m V] (v : V) : m Bool := do
  return (← PyPure.identical v (PyPure.imm (m := m) (.builtin .NoneType))) == .yes

/-- `x == y` as `PyObject_RichCompareBool` gives it, one C level deeper. -/
def eqBool [PyCalls m V] (x y : V) : m Bool :=
  PyReads.withDepth 1 (sameOrEq (richCompare .eq) x y)

/-- `repr(x)`'s text, one C level deeper, as `PyObject_Repr` counts it. -/
def reprText1 [PyCalls m V] (x : V) : m String := PyReads.withDepth 1 (reprTextOf x)

/-- **`ga_repr_item` and `union_repr_item`**: `...` for `Ellipsis` (in a `GenericAlias`), `None` for
`NoneType` (in a union), the `repr` of a value that has `__origin__` and `__args__`, `qualname` or
`module.qualname` for a value with both (without `builtins.`), and the `repr` otherwise. -/
def reprItem [PyCalls m V] (union : Bool) (p : V) : m String := do
  if !union && (← PyPure.immView p) matches some .ellipsis then return "..."
  if union && (← isNoneType p) then return "None"
  if (← lookupAttr? p "__origin__").isSome then
    if (← lookupAttr? p "__args__").isSome then return ← reprText1 p
  let some q ← lookupAttr? p "__qualname__" | reprText1 p
  let some md ← lookupAttr? p "__module__" | reprText1 p
  if (← PyPure.immView md) matches some .none then return ← reprText1 p
  -- `PyUnicode_Check(module)`: a `str` or a `str` subclass instance, compared by its text.
  let text ← match ← str? md with
    | some t => pure (some t)
    | none => pure ((← PyReads.strView md).map (·.s))
  if text == some "builtins" then return ← strTextOf q
  -- `PyUnicode_FromFormat("%S.%S", module, qualname)`, `module`'s `str` first.
  let ms ← strTextOf md
  let qs ← strTextOf q
  return s!"{ms}.{qs}"

/-- `ga_repr`'s text for the origin `o` and the arguments `a`: `o[a, ...]`, `tuple[()]` for no
arguments, and a list argument written as `[x, y]` (a `ParamSpec`'s arguments). -/
def gaReprText [PyCalls m V] (o a : V) : m String := do
  let head ← reprItem false o
  let xs ← tupleItems a
  let mut parts : Array String := #[]
  for x in xs do
    let isList ← match ← PyReads.listView x with
      | some _ => pure ((← PyPure.identical (← PyReads.classOf x)
          (PyPure.imm (m := m) (.builtin .list))) == .yes)
      | none => pure false
    if isList then
      let some (ys, _) ← PyReads.listView x | PyPure.modelInvariant "a list without its items"
      -- `ga_repr_items_list` takes the length once and reads each item when it writes it, so a
      -- `repr` that changes the list is seen; one that shrinks it makes CPython read past its end.
      let mut ps : Array String := #[]
      for i in [0:ys.size] do
        let some (zs, _) ← PyReads.listView x | PyPure.modelInvariant "a list without its items"
        let some y := zs[i]? | PyPure.gap "a list argument that shrinks while its repr is written"
        ps := ps.push (← reprItem false y)
      parts := parts.push ("[" ++ ", ".intercalate ps.toList ++ "]")
    else parts := parts.push (← reprItem false x)
  let body := if xs.isEmpty then "()" else ", ".intercalate parts.toList
  return s!"{head}[{body}]"

/-- `union_repr`'s text: the items joined by ` | `. -/
def unionReprText [PyCalls m V] (a : V) : m String := do
  let xs ← tupleItems a
  let ps ← xs.mapM (reprItem true)
  return " | ".intercalate ps.toList

/-- Whether `x` is one of the values that `_Py_union_type_or` takes: `None`, a class, a
`GenericAlias` or a `UnionType`. -/
def unionable [PyReads m V] (x : V) : m Bool := do
  if (← PyPure.immView x) matches some .none then return true
  if ← isType x then return true
  if (← gaParts? x).isSome then return true
  return (← unionArgs? x).isSome

/-- `get_types`: `None` as `NoneType`, a union as its arguments, any other value alone. -/
def unionItems [PyReads m V] (x : V) : m (V × Array V) := do
  let x := if (← PyPure.immView x) matches some .none then
    PyPure.imm (m := m) (.builtin .NoneType) else x
  match ← unionArgs? x with
  | some a => return (x, ← tupleItems a)
  | none => return (x, #[x])

/-- `is_same`: `==` for two `GenericAlias`es, identity otherwise. -/
def unionSame [PyCalls m V] (x y : V) : m Bool := do
  if (← gaParts? x).isSome && (← gaParts? y).isSome then return ← eqBool x y
  return (← PyPure.identical x y) == .yes

/-- `merge`: the items of `ys` that `xs` doesn't hold (by `is_same`) added after `xs`, or `none`
when none is new. -/
def unionMerge [PyCalls m V] (xs ys : Array V) : m (Option (Array V)) := do
  let mut out := xs
  let mut added := false
  for y in ys do
    let mut dup := false
    for x in xs do
      if ← unionSame x y then
        dup := true
        break
    if !dup then
      out := out.push y
      added := true
  return if added then some out else none


/-- A slot wrapper's call with exactly one argument after `self`. -/
def slotArg [PyReads m V] (name : String) (args kwargs : V) : m V := oneArg name args kwargs

/-- A `METH_O` method's argument: CPython's message names it by `qualname`. -/
def methArg [PyReads m V] (qualname : String) (args kwargs : V) : m V := do
  let b ← bindBuiltinArgs { name := qualname, qualname, style := .methO } args kwargs
  let #[some o] := b.params | PyPure.modelInvariant "a METH_O method: the binder's assumption failed"
  pure o

/-- CPython's descriptor `TypeError` for the method `name` of the class `tpName` called on `self` of
another class: a slot wrapper's message, or (`method`) a method descriptor's. -/
def wrongSelf [PyReads m V] {α : Type} (method : Bool) (tpName name : String) (self : V) : m α := do
  let other ← typeName self
  raiseBuiltin "TypeError" <| if method then
    s!"descriptor '{name}' for '{tpName}' objects doesn't apply to a '{other}' object"
  else s!"descriptor '{name}' requires a '{tpName}' object but received a '{other}'"

/-- The names of `GenericAlias`'s methods that are method descriptors; the others are slot
wrappers. -/
def gaMethods : List String := gaSpec.entries.toList.filterMap fun
  | .native n _ .methodDescriptor => some n
  | _ => none

/-- The origin and arguments of `self`, a `GenericAlias`, for its method `name`; another `self`
raises CPython's descriptor `TypeError`. -/
def gaSelf [PyReads m V] (name : String) (self : V) : m (V × V) := do
  match ← gaParts? self with
  | some p => pure p
  | none => wrongSelf (gaMethods.contains name) "types.GenericAlias" name self

/-- The arguments tuple of `self`, a `UnionType`, for its slot wrapper `name`; another `self`
raises CPython's descriptor `TypeError`. -/
def unionSelf [PyReads m V] (name : String) (self : V) : m V := do
  match ← unionArgs? self with
  | some a => pure a
  | none => wrongSelf false "types.UnionType" name self

/-- **`Py_GenericAlias(origin, item)`**: a new `GenericAlias`; an `item` that is not a tuple
becomes a one-tuple. -/
def newGenericAlias [PyWrites m V] [PyNew m V] (origin item : V) : m V := do
  -- CPython keeps an instance of a subclass of `tuple` as the arguments tuple itself.
  if (← PyPure.immView item).isNone && (← builtinBase? item) == some .tuple then
    PyPure.gap "a GenericAlias whose arguments are an instance of a subclass of tuple"
  let args := if (← PyPure.immView item) matches some (.tuple _) then item
    else PyPure.imm (m := m) (.tuple #[item])
  PyPure.allocObj (← modelClass gaSpec) (.opaque gaTag #[origin, args])

/-- `make_union(args)`: a new `UnionType` of the arguments `xs`. -/
def newUnion [PyWrites m V] [PyNew m V] (xs : Array V) : m V := do
  PyPure.allocObj (← modelClass unionSpec) (.opaque unionTag #[PyPure.imm (m := m) (.tuple xs)])

/-- **`_Py_union_type_or(a, b)`**, `a | b` for `None`, classes, `GenericAlias`es and `UnionType`s:
`NotImplemented` for any other operand; else the union of their items, or `a` (`None` as
`NoneType`) when `b` adds none. -/
def unionOr [PyWrites m V] [PyNew m V] (a b : V) : m V := do
  if !(← unionable a) || !(← unionable b) then return notImpl (m := m)
  let (a', xs) ← unionItems a
  let (_, ys) ← unionItems b
  match ← unionMerge xs ys with
  | some zs => newUnion zs
  | none => pure a'

/-- The arguments tuple of `self`, a `GenericAlias` or a `UnionType`. -/
def aliasArgs [PyReads m V] (self : V) : m V := do
  if let some (_, a) ← gaParts? self then return a
  if let some a ← unionArgs? self then return a
  PyPure.modelInvariant "a GenericAlias or UnionType method on another value"

/-- The built-in classes whose `__class_getitem__` (or, for `type`, subscription) makes a
`GenericAlias`; none of them has a `__typing_subst__`. -/
def aliasOrigins : List Builtin := [.list, .dict, .tuple, .set, .frozenset, .type]

/-- Whether `x` is a class whose metaclass is exactly `type`, so that its `==` and `hash` are
`type`'s, by identity. -/
def plainClass [PyReads m V] (x : V) : m Bool := do
  if !(← isType x) then return false
  return (← PyPure.identical (← PyReads.classOf x) (PyPure.imm (m := m) (.builtin .type))) == .yes

/-- Whether every item of `xs` is a known value of this file's kind: `None`, `Ellipsis`, a `bool`,
`int` or `str`, a tuple of known values, a class whose metaclass is exactly `type`, a
`GenericAlias` whose origin is one of `aliasOrigins` and whose arguments are known, or a
`UnionType` whose arguments are known; `fuel` bounds the nesting. A known value's `==` and `hash`
run no user code, and reading its `__typing_subst__` and `__parameters__` runs none either, and
finds no type parameter. -/
def knownArgs [PyReads m V] : Nat → Array V → m Bool
  | 0, _ => PyPure.gap "arguments nested deeper than the model of types.GenericAlias follows"
  | n + 1, xs => xs.allM fun x => do
    match ← PyPure.immView x with
    | some .none | some .ellipsis | some (.bool _) | some (.int _) | some (.str _) => pure true
    | some (.tuple ys) => knownArgs n ys
    | some _ => plainClass x
    | none =>
      if ← isType x then return ← plainClass x
      if let some (o, a) ← gaParts? x then
        let builtinOrigin := match ← PyPure.immView o with
          | some (.builtin b) => aliasOrigins.contains b
          | _ => false
        return builtinOrigin && (← knownArgs n (← tupleItems a))
      if let some a ← unionArgs? x then return ← knownArgs n (← tupleItems a)
      return false

/-- **`__parameters__`** of a `GenericAlias` or a `UnionType`: `()` when its arguments are known
(no known value holds a type variable); otherwise a gap, since CPython's `_Py_make_parameters`
would read attributes of the arguments and keep the result. -/
def aliasParameters [PyReads m V] (self : V) : m V := do
  if ← knownArgs compareDepth (← tupleItems (← aliasArgs self)) then
    return PyPure.imm (m := m) (.tuple #[])
  PyPure.gap "__parameters__ of a type alias with arguments that the model doesn't know"

/-- `ga_repr` and `union_repr`. -/
def gaReprBody [PyWrites m V] (self args kwargs : V) : m V := do
  let (o, a) ← gaSelf "__repr__" self
  noArg "__repr__" args kwargs
  return strValue (m := m) (← gaReprText o a)

/-- `union_repr`. -/
def unionReprBody [PyWrites m V] (self args kwargs : V) : m V := do
  let a ← unionSelf "__repr__" self
  noArg "__repr__" args kwargs
  return strValue (m := m) (← unionReprText a)

/-- `ga_hash`'s combination of the hashes of the origin and of the arguments: their `^`. -/
def gaHash (h0 h1 : Hash) : Hash :=
  combineHash "GenericAlias.__hash__" [h0, h1] fun
    | [x, y] => ofUHash (toUHash x ^^^ toUHash y)
    | _ => 0

/-- `ga_hash`: `hash(origin) ^ hash(args)`. CPython's hash recursion has no limit; the model
counts one C level per nested hash and stops with a gap past its own. -/
def gaHashBody [PyWrites m V] (self args kwargs : V) : m V := do
  let (o, a) ← gaSelf "__hash__" self
  noArg "__hash__" args kwargs
  let h0 ← PyReads.withDepth 1 (Proto.hash o)
  let h1 ← PyReads.withDepth 1 (Proto.hash a)
  let h := gaHash h0 h1
  -- `ga_hash` returning -1 makes `hash()` raise `SystemError` in CPython.
  if h matches .exact (-1) then PyPure.gap "a GenericAlias whose hash is -1"
  PyPure.hashValue h

/-- The arguments of a union without their `==`-duplicates, for a union whose arguments are
known, in which `==` is identity except between `GenericAlias`es. -/
def distinctArgs [PyCalls m V] (xs : Array V) : m (Array V) := do
  let mut out : Array V := #[]
  for x in xs do
    if !(← out.anyM fun y => unionSame y x) then out := out.push x
  return out

/-- `union_hash`: `hash(frozenset(args))`, computed from the hashes of the distinct arguments as
a frozenset's hash is; arguments that the model doesn't know stop with a gap. -/
def unionHashBody [PyWrites m V] (self args kwargs : V) : m V := do
  let a ← unionSelf "__hash__" self
  noArg "__hash__" args kwargs
  let xs ← tupleItems a
  if !(← knownArgs compareDepth xs) then
    PyPure.gap "the hash of a union with arguments that the model doesn't know"
  let hs ← (← distinctArgs xs).toList.mapM fun x => PyReads.withDepth 1 (Proto.hash x)
  PyPure.hashValue (frozensetHash hs)

/-- `ga_richcompare`: for `==` and `!=` against another `GenericAlias`, the origins with `==`, then
the arguments tuples; `NotImplemented` otherwise. -/
def gaCmpBody [PyWrites m V] (name : String) (op : Arith.CmpOp) (self args kwargs : V) : m V := do
  let (oa, aa) ← gaSelf name self
  let o ← slotArg name args kwargs
  let boolV (r : Bool) : V := PyPure.imm (m := m) (.bool r)
  let some (ob, ab) ← gaParts? o | return notImpl (m := m)
  if op != .eq && op != .ne then return notImpl (m := m)
  -- `PyObject_RichCompareBool` of the origins, then `PyObject_RichCompare` of the arguments
  -- tuples, which compares their items one C level further down.
  let eq ← do
    if !(← eqBool oa ob) then pure (boolV false)
    else PyReads.withDepth 2 (richCompareV .eq aa ab)
  if op == .eq then return eq
  return boolV !((← PyPure.immView eq) matches some (.bool true))

/-- `union_richcompare`: for `==` and `!=` against another `UnionType`, the sets of their
arguments; `NotImplemented` otherwise. Arguments that the model doesn't know stop with a gap. -/
def unionCmpBody [PyWrites m V] (name : String) (op : Arith.CmpOp) (self args kwargs : V) : m V := do
  let a ← unionSelf name self
  let o ← slotArg name args kwargs
  let boolV (r : Bool) : V := PyPure.imm (m := m) (.bool r)
  let some b ← unionArgs? o | return notImpl (m := m)
  if op != .eq && op != .ne then return notImpl (m := m)
  let xs ← tupleItems a
  let ys ← tupleItems b
  if !(← knownArgs compareDepth xs) || !(← knownArgs compareDepth ys) then
    PyPure.gap "comparing unions with arguments that the model doesn't know"
  -- Two sets of known values are equal when each holds the other's members; a member's
  -- comparison is a set's, two C levels down (the set, then the member).
  let xs ← distinctArgs xs
  let ys ← distinctArgs ys
  let inOther (zs : Array V) (x : V) : m Bool := zs.anyM fun z => PyReads.withDepth 2 (unionSame z x)
  let eq ← if xs.size != ys.size then pure false else xs.allM (inOther ys)
  return boolV (if op == .eq then eq else !eq)

/-- The `str` name of a `__getattribute__` call: CPython's `TypeError` for a value that is not a
`str`; an instance of a `str` subclass stops with a gap, since CPython's type lookup hashes it with
its own `__hash__`. -/
def attrNameOf [PyReads m V] (nv : V) : m String := do
  if let some name ← str? nv then return name
  if (← builtinBase? nv) == some .str then
    PyPure.gap "an attribute name that is an instance of a subclass of str is not modelled yet"
  raiseBuiltin "TypeError" s!"attribute name must be string, not '{← typeName nv}'"

/-- `ga_getattro`: CPython's list of names gets the generic lookup, which the model gives for
each of them; any other name is read from the origin. -/
def gaGetattrBody [PyWrites m V] (self args kwargs : V) : m V := do
  let (o, a) ← gaSelf "__getattribute__" self
  let nv ← slotArg "__getattribute__" args kwargs
  let name ← attrNameOf nv
  match name with
  | "__origin__" => pure o
  | "__args__" => pure a
  | "__unpacked__" => pure (PyPure.imm (m := m) (.bool false))
  | "__parameters__" => aliasParameters self
  | "__typing_unpacked_tuple_args__" => pure (PyPure.imm (m := m) .none)
  | "__class__" => PyReads.classOf self
  | "__mro_entries__" | "__reduce_ex__" | "__reduce__" | "__copy__" | "__deepcopy__" =>
    genericGetAttr self (← PyReads.classOf self) name
  | _ => getAttr o name

/-- `union_getattro`: `__module__` from the class; the members and getsets; else the generic
lookup. -/
def unionGetattrBody [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| unionSelf "__getattribute__" self
  let nv ← slotArg "__getattribute__" args kwargs
  let name ← attrNameOf nv
  match name with
  | "__module__" => getAttr (← PyReads.classOf self) "__module__"
  | "__args__" => aliasArgs self
  | "__parameters__" => aliasParameters self
  | _ => genericGetAttr self (← PyReads.classOf self) name

/-- `ga_call`: the origin's call, then `__orig_class__` set on the result, ignoring
`AttributeError` and `TypeError`. -/
def gaCallBody [PyWrites m V] (self args kwargs : V) : m V := do
  let (o, _) ← gaSelf "__call__" self
  let r ← callN dispatchDepth o args kwargs
  tryCatch (setAttr r "__orig_class__" (some self)) fun x => do
    if (← isAttributeError x) || (← isTypeErrorExc x) then pure () else throw x
  pure r

/-- `ga_getitem` (`union` false) and `union_getitem`: with no type parameters, CPython's
`TypeError`. -/
def aliasGetItemBody [PyWrites m V] (union : Bool) (self args kwargs : V) : m V := do
  if union then discard <| unionSelf "__getitem__" self
  else discard <| gaSelf "__getitem__" self
  discard <| slotArg "__getitem__" args kwargs
  let ps ← tupleItems (← aliasParameters self)
  if ps.isEmpty then
    raiseBuiltin "TypeError" s!"{← reprTextOf self} is not a generic class"
  PyPure.gap "substituting type parameters is not modelled yet"

/-- `nb_or` of `type`, `GenericAlias` and `UnionType` (`__or__`), and its reflected form; `owner` is
the class whose slot this is, `none` for `type`'s, whose receiver the call of the slot wrapper
checks. -/
def unionOrBody [PyWrites m V] [PyNew m V] (owner : Option String) (reflected : Bool)
    (self args kwargs : V) : m V := do
  let name := if reflected then "__ror__" else "__or__"
  if owner == some gaTag then discard <| gaSelf name self
  if owner == some unionTag then discard <| unionSelf name self
  let o ← slotArg name args kwargs
  if reflected then unionOr o self else unionOr self o

/-- `ga_mro_entries(self, bases)`: `(origin,)`. -/
def gaMroEntriesBody [PyWrites m V] (self args kwargs : V) : m V := do
  let (o, _) ← gaSelf "__mro_entries__" self
  discard <| methArg "GenericAlias.__mro_entries__" args kwargs
  pure (PyPure.imm (m := m) (.tuple #[o]))

/-- `ga_instancecheck` and `ga_subclasscheck`: CPython's `TypeError`. -/
def gaCheckBody [PyWrites m V] (which : String) (self args kwargs : V) : m V := do
  discard <| gaSelf s!"__{which}check__" self
  discard <| methArg s!"GenericAlias.__{which}check__" args kwargs
  let fn := if which == "instance" then "isinstance" else "issubclass"
  raiseBuiltin "TypeError" s!"{fn}() argument 2 cannot be a parameterized generic"

/-- `t.__class_getitem__(item)` of `list`, `dict`, `tuple`, `set` and `frozenset`: a
`GenericAlias` of the class. -/
def classGetItemBody [PyWrites m V] [PyNew m V] (t : Builtin) (self args kwargs : V) : m V := do
  let item ← methArg s!"{t.info.name}.__class_getitem__" args kwargs
  newGenericAlias self item

/-- `type[item]`: `PyObject_GetItem`'s case for exactly the object `type`, a `GenericAlias`. -/
def typeGetItemBody [PyWrites m V] [PyNew m V] (self args kwargs : V) : m V := do
  let item ← slotArg "__getitem__" args kwargs
  newGenericAlias self item

/-- The arguments tuple of `self` when it is a `UnionType`, else `None`: `isinstance` and
`issubclass` try them in order. -/
def unionArgsHookBody [PyWrites m V] (self _args _kwargs : V) : m V := do
  match ← unionArgs? self with
  | some a => pure a
  | none => pure (PyPure.imm (m := m) .none)

end

/-- A method body run as a native: its receiver and arguments from `nativeRecv`. -/
def asMethod (body : BuiltinImpl) : BuiltinImpl := fun {_} {_} [_] [_] fn args kwargs => do
  let (recv, rest) ← nativeRecv fn args
  body recv rest kwargs

/-- The bodies of `types.GenericAlias`'s and `types.UnionType`'s methods, over their receiver. -/
def typesMethod (key : String) : Option BuiltinImpl :=
  let ga (n : String) := methodKey gaTag n
  let un (n : String) := methodKey unionTag n
  let cmps : List (String × Arith.CmpOp) :=
    [("__eq__", .eq), ("__ne__", .ne), ("__lt__", .lt), ("__le__", .le), ("__gt__", .gt),
      ("__ge__", .ge)]
  if let some (n, op) := cmps.find? (fun (n, _) => key == ga n) then
    some fun {_} {_} [_] [_] => gaCmpBody n op
  else if let some (n, op) := cmps.find? (fun (n, _) => key == un n) then
    some fun {_} {_} [_] [_] => unionCmpBody n op
  else if key == ga "__repr__" then some fun {_} {_} [_] [_] => gaReprBody
  else if key == un "__repr__" then some fun {_} {_} [_] [_] => unionReprBody
  else if key == ga "__hash__" then some fun {_} {_} [_] [_] => gaHashBody
  else if key == un "__hash__" then some fun {_} {_} [_] [_] => unionHashBody
  else if key == ga "__getattribute__" then some fun {_} {_} [_] [_] => gaGetattrBody
  else if key == un "__getattribute__" then some fun {_} {_} [_] [_] => unionGetattrBody
  else if key == ga "__call__" then some fun {_} {_} [_] [_] => gaCallBody
  else if key == ga "__getitem__" then some fun {_} {_} [_] [_] => aliasGetItemBody false
  else if key == un "__getitem__" then some fun {_} {_} [_] [_] => aliasGetItemBody true
  else if key == ga "__or__" then some fun {_} {_} [_] [_] => unionOrBody (some gaTag) false
  else if key == un "__or__" then some fun {_} {_} [_] [_] => unionOrBody (some unionTag) false
  else if key == ga "__ror__" then some fun {_} {_} [_] [_] => unionOrBody (some gaTag) true
  else if key == un "__ror__" then some fun {_} {_} [_] [_] => unionOrBody (some unionTag) true
  else if key == ga "__mro_entries__" then some fun {_} {_} [_] [_] => gaMroEntriesBody
  else if key == ga "__instancecheck__" then some fun {_} {_} [_] [_] => gaCheckBody "instance"
  else if key == ga "__subclasscheck__" then some fun {_} {_} [_] [_] => gaCheckBody "subclass"
  else none

/-- The native bodies of `types.GenericAlias`'s and `types.UnionType`'s methods. -/
def typesNative (key : String) : Option BuiltinImpl := (typesMethod key).map asMethod

/-- **The rules of `types.GenericAlias` and `types.UnionType`**: the native bodies of the two classes; `__class_getitem__` of
`list`, `dict`, `tuple`, `set` and `frozenset`; `type`'s `__or__`, `__ror__` and subscription;
and the union-arguments hook of `isinstance` and `issubclass`. -/
def typesImpls : Impls where
  method
    | .type, "__or__" => some fun {_} {_} [_] [_] => unionOrBody none false
    | .type, "__ror__" => some fun {_} {_} [_] [_] => unionOrBody none true
    | .type, n => if n == typeGetItemHook then some fun {_} {_} [_] [_] => typeGetItemBody else none
    | .object, n => if n == unionArgsHook then some fun {_} {_} [_] [_] => unionArgsHookBody else none
    | t, "__class_getitem__" =>
      if [Builtin.list, .dict, .tuple, .«set», .«frozenset»].contains t then
        some fun {_} {_} [_] [_] => classGetItemBody t
      else none
    | _, _ => none
  native := typesNative

end

end StrataPython.Dyn.Sem.Modules
