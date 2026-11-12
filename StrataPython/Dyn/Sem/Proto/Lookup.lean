/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Values
public import StrataPython.Dyn.Sem.Generated.Names

set_option autoImplicit false

/-!
# Lookups on types, calls and descriptors

Generic over the record of primitives, the parts of CPython 3.12's object protocol that every
operator needs:

* `lookupType t name`, CPython's `_PyType_Lookup`: the first class of `t`'s MRO whose namespace
  has `name`, a user class's namespace dict or a built-in type's table (`Builtin.ownNames`);
* `callN f args kwargs`, CPython's `PyObject_Call`, and `typeCallN`, `type.__call__`;
* `descrGetN d obj type`, the `__get__` of each kind of descriptor: functions bind as methods,
  built-in methods bind to their object, `classmethod`, `staticmethod`, `property`, slots'
  `member` descriptors, the getsets of built-in types that this piece models, and a user class's
  `__get__`.

An entry of a built-in type's table that no piece models yet stops with a gap.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The gap of a value whose type is a user class, where the model doesn't follow its dunders. -/
def userGap : String := "the dunder protocol of a user class is not modelled yet"

/-- The gap of an `__index__` that returns a `bool` or an instance of a subclass of `int`: CPython
accepts it with a `DeprecationWarning`, which records the warning in the module's
`__warningregistry__`. -/
def indexWarnGap : String :=
  "an __index__ that returns a strict subclass of int, which warns, is not modelled yet"

/-- The class `v`, as generic code sees it, if it is a class object. -/
def classData? [PyReads m V] (v : V) : m (Option (ClassData V)) := do
  match ← PyReads.objView v with
  | some (.cls c) => pure (some c)
  | _ => pure none

/-- Whether `v` is a class: a built-in type or a class object. -/
def isType [PyReads m V] (v : V) : m Bool := do
  match ← PyPure.immView v with
  | some (.builtin b) => pure (b.info.kind == .type)
  | some _ => pure false
  | none => return (← classData? v).isSome

/-- The MRO of the class `t`, the class first; `none` if `t` is not a class. -/
def mroOf [PyReads m V] (t : V) : m (Option (Array V)) := do
  match ← PyPure.immView t with
  | some (.builtin b) =>
    if b.info.kind == .type then
      pure (some (b.info.mro.map fun c => PyPure.imm (m := m) (.builtin c)))
    else pure none
  | some _ => pure none
  | none => return (← classData? t).map fun c => #[t] ++ c.mroTail

/-- The `__name__` of the class `t`. -/
def classNameRaw [PyReads m V] (t : V) : m String := do
  match ← PyPure.immView t with
  | some (.builtin b) => pure b.info.name
  | _ => match ← classData? t with
    | some c => pure c.name
    | none => PyPure.gap "the name of a class that is not a class"

/-- The `__name__` of the class `t`, for a message.  CPython cuts a name in a message at 50, 100 or
200 bytes of its UTF-8 text, by the message; a name longer than 50 bytes stops with a gap. -/
def classNameOf [PyReads m V] (t : V) : m String := do
  let n ← classNameRaw t
  if n.utf8ByteSize > 50 then PyPure.gap "a message with a class name longer than 50 bytes is not modelled yet"
  pure n

/-- The `__qualname__` of the class `t`, for a message, as `classNameOf`. -/
def classQualnameOf [PyReads m V] (t : V) : m String := do
  let n ← match ← PyPure.immView t with
    | some (.builtin b) => pure b.info.qualname
    | _ => match ← classData? t with
      | some c => pure c.qualname
      | none => PyPure.gap "the name of a class that is not a class"
  if n.utf8ByteSize > 50 then PyPure.gap "a message with a class name longer than 50 bytes is not modelled yet"
  pure n

/-- The `tp_name` of the class `c`: a built-in type's name, or a user class's. -/
def tpNameOf [PyReads m V] (c : V) : m String := do
  match ← PyPure.immView c with
  | some (.builtin b) => pure b.info.tpName
  | _ => match ← classData? c with
    | some cd => pure (cd.tpName.getD cd.name)
    | none => PyPure.gap "the tp_name of a value that is not a class"

/-- The `__name__` of the type of `v`, as CPython's messages give it (a built-in type's `tp_name`). -/
def typeName [PyReads m V] (v : V) : m String := do
  let t ← PyReads.classOf v
  match ← PyPure.immView t with
  | some (.builtin b) => pure (if b.info.tpName.isEmpty then b.info.name else b.info.tpName)
  | _ => classNameOf t

/-- The name of `v`'s type as Argument Clinic's `_PyArg_BadArgument` gives it: `None` for `None`. -/
def argTypeName [PyReads m V] (v : V) : m String := do
  if (← PyPure.immView v) matches some .none then pure "None" else typeName v

/-- `v` as a Lean `str`, if it is one. -/
def str? [PyPure m V] (v : V) : m (Option String) := do
  match ← PyPure.immView v with
  | some (.str s) => pure (some s.s)
  | _ => pure none

/-- `v` as a Lean `str` if it is a `str`, and `none` if it is neither a `str` nor an instance of a
subclass of `str`.  An instance of a subclass of `str`, which CPython accepts where it asks for a
`str`, stops with a gap that names `what`: the class's MRO holds `str`, or `v` holds a built-in
`str` part. -/
def strArg? [PyReads m V] (what : String) (v : V) : m (Option String) := do
  if let some s ← str? v then return some s
  let mro := (← mroOf (← PyReads.classOf v)).getD #[]
  if (← PyReads.strView v).isSome ||
      (← mro.anyM fun c => return (← PyPure.immView c) matches some (.builtin .str)) then
    PyPure.gap s!"{what} that is an instance of a subclass of str is not modelled yet"
  return none

/-- `TypeError` if a key of the kwargs dict `kwargs` is not a `str`, as CPython's
`_PyStack_UnpackDict` raises it; a key that is an instance of a subclass of `str`, which CPython
accepts, stops with a gap. -/
def checkKwargs [PyReads m V] (kwargs : V) : m Unit := do
  for (k, _, _) in ← PyReads.dictEntries kwargs do
    match ← PyPure.immView k with
    | some (.str _) => pure ()
    | some _ => raiseBuiltin "TypeError" "keywords must be strings"
    | none => do
      discard <| strArg? "a keyword" k
      raiseBuiltin "TypeError" "keywords must be strings"

/-- A gap when the kwargs dict `kwargs` has a key that isn't a `str` and the callee `f` is neither
a Python function nor a bound method: CPython checks the keys where the callee's own call path
unpacks them, so which error a built-in raises first depends on the built-in. -/
def kwargsKeysGap [PyReads m V] (f kwargs : V) : m Unit := do
  if (← PyReads.dictLen kwargs) == 0 then return
  let mut allStr := true
  for (k, _, _) in ← PyReads.dictEntries kwargs do
    if !((← PyPure.immView k) matches some (.str _)) then allStr := false
  if allStr then return
  match ← PyPure.immView f with
  | some (.method ..) => pure ()
  | some _ => PyPure.gap "a call of a built-in with a keyword that is not a str is not modelled yet"
  | none => match ← PyReads.objView f with
    | some (.func ..) => pure ()
    | _ => PyPure.gap "a call of a built-in with a keyword that is not a str is not modelled yet"

/-- The descriptor kind of an entry of a built-in type's table, if the entry is a descriptor. -/
def _root_.StrataPython.Dyn.Sem.AttrKind.descr? : AttrKind → Option DescrKind
  | .slotWrapper => some .slotWrapper
  | .method => some .method
  | .classMethodDescr => some .classMethod
  | .getset => some .getset
  | .member => some .member
  | _ => none

/-- The entry `name` of the built-in type `t`'s own table: a descriptor, `None`, or a gap for a
value the model doesn't hold; `none` if the table has no such name. -/
def builtinEntry [PyPure m V] (t : Builtin) (name : String) : m (Option V) := do
  match t.ownNames.find? (·.1 == name) with
  | none => pure none
  | some (_, k) => match k.descr? with
    | some d => pure (some (PyPure.imm (m := m) (.descr t name d)))
    | none => match k with
      | .builtinMethod =>
        pure (some (PyPure.imm (m := m) (.bound (PyPure.imm (m := m) (.builtin t)) t name .method)))
      | .noneValue => pure (some (PyPure.imm (m := m) .none))
      | _ => PyPure.gap s!"the attribute {t.info.name}.{name} is not modelled yet"

/-- The value of the `str` key `name` in the dict `d`; a dict whose keys may run user code is not
read. -/
def dictFindStr [PyReads m V] (d : V) (name : String) : m (Option V) := do
  let k := PyPure.imm (m := m) (.str (.ofString name))
  PyReads.dictFind d k none fun _ =>
    PyPure.gap "a namespace whose keys run user code is not modelled yet"

/-- The entry `name` of the namespace of the class `c` (a class object or a built-in type), if it
has one; a gap for a name that the class gaps.  `k` is `name` as a `str` key, built once for a walk
of several classes. -/
def lookupOwnK [PyReads m V] (c : V) (name : String) (k : V) : m (Option V) := do
  match ← PyPure.immView c with
  | some (.builtin b) => builtinEntry b name
  | _ => match ← classData? c with
    | some cd =>
      if cd.gapped.contains name then
        PyPure.gap s!"the attribute {cd.name}.{name} is not modelled yet"
      PyReads.dictFind cd.ns k none fun _ =>
        PyPure.gap "a namespace whose keys run user code is not modelled yet"
    | none => pure none

/-- The first entry `name` along the classes `mro`, with `k` as in `lookupOwnK`. -/
def lookupMroK [PyReads m V] (mro : List V) (name : String) (k : V) : m (Option V) :=
  match mro with
  | [] => pure none
  | c :: rest => do
    if let some v ← lookupOwnK c name k then return some v
    lookupMroK rest name k

/-- The first entry `name` along the classes `mro`. -/
def lookupMro [PyReads m V] (mro : List V) (name : String) : m (Option V) :=
  lookupMroK mro name (PyPure.imm (m := m) (.str (.ofString name)))

/-- **`_PyType_Lookup(t, name)`**: the first entry `name` along the MRO of the class `t`. -/
def lookupType [PyReads m V] (t : V) (name : String) : m (Option V) := do
  let some mro ← mroOf t | PyPure.gap "a lookup on a type that is not a class"
  lookupMro mro.toList name

/-- The built-in type whose `__getattribute__` the class `t` inherits as its default lookup: the
first built-in type along `t`'s MRO whose table has `__getattribute__`.  A `__getattribute__`
descriptor of another built-in type, found earlier on the MRO, is not `t`'s default lookup. -/
def defaultGetattrOwner [PyReads m V] (t : V) : m (Option Builtin) := do
  let some mro ← mroOf t | return none
  for c in mro do
    if let some (.builtin b) ← PyPure.immView c then
      if b.ownNames.any (·.1 == "__getattribute__") then return some b
  return none

/-- `(lookupType t n₁, lookupType t n₂)`, in one walk of the MRO of the class `t`. -/
def lookupType2 [PyReads m V] (t : V) (n₁ n₂ : String) : m (Option V × Option V) := do
  let some mro ← mroOf t | PyPure.gap "a lookup on a type that is not a class"
  let k₁ := PyPure.imm (m := m) (.str (.ofString n₁))
  let k₂ := PyPure.imm (m := m) (.str (.ofString n₂))
  let mut r₁ : Option V := none
  let mut r₂ : Option V := none
  for c in mro do
    if r₁.isNone then r₁ ← lookupOwnK c n₁ k₁
    if r₂.isNone then r₂ ← lookupOwnK c n₂ k₂
    if r₁.isSome && r₂.isSome then break
  return (r₁, r₂)

/-- What `lookupTypeEntry` finds: nothing; a plain value (a `str`, an `int` or `None`) in the
table of the built-in type `b`; or an entry. -/
inductive TypeEntry (V : Type) where
  | none
  | plain (b : Builtin)
  | entry (v : V)

/-- `lookupType t name` in one walk of the MRO, with a plain value of a built-in type's table told
apart.  No descriptor protocol applies to such a value, so an attribute write goes to the
instance, and the model may not hold the value itself. -/
def lookupTypeEntry [PyReads m V] (t : V) (name : String) : m (TypeEntry V) := do
  let some mro ← mroOf t | PyPure.gap "a lookup on a type that is not a class"
  let k := PyPure.imm (m := m) (.str (.ofString name))
  for c in mro do
    match ← PyPure.immView c with
    | some (.builtin b) =>
      if let some (_, kind) := b.ownNames.find? (·.1 == name) then
        if kind == .strValue || kind == .intValue || kind == .noneValue then return .plain b
        if let some v ← builtinEntry b name then return .entry v
    | _ => if let some v ← lookupOwnK c name k then return .entry v
  return .none

/-- Whether the class of `v` is exactly the built-in type `b`. -/
def classIs [PyReads m V] (v : V) (b : Builtin) : m Bool := do
  match ← PyPure.immView (← PyReads.classOf v) with
  | some (.builtin b') => pure (b' == b)
  | _ => pure false

/-- The value of the getset or member `name` of the built-in type `t` on `obj`, for the ones that
this piece models; a gap for the others. -/
def builtinGetsetGet [PyReads m V] (t : Builtin) (name : String) (obj : V) : m V := do
  let gapIt : m V := PyPure.gap s!"the attribute {t.info.name}.{name} is not modelled yet"
  match t, name with
  | .object, "__class__" => PyReads.classOf obj
  | .type, "__name__" => return PyPure.imm (m := m) (.str (.ofString (← classNameRaw obj)))
  | .type, "__qualname__" => match ← PyPure.immView obj with
    | some (.builtin b) => return PyPure.imm (m := m) (.str (.ofString b.info.qualname))
    | _ => match ← classData? obj with
      | some cd => return PyPure.imm (m := m) (.str (.ofString cd.qualname))
      | none => gapIt
  | .type, "__module__" => match ← PyPure.immView obj with
    | some (.builtin b) => return PyPure.imm (m := m) (.str (.ofString b.info.module))
    | _ => match ← classData? obj with
      | some cd => match ← dictFindStr cd.ns "__module__" with
        | some x => pure x
        | none =>
          let nameV := PyPure.imm (m := m) (.str (.ofString "__module__"))
          raiseBuiltin "AttributeError" "__module__" #[("name", nameV), ("obj", obj)]
      | none => gapIt
  | .type, "__mro__" => match ← mroOf obj with
    | some mro => return PyPure.imm (m := m) (.tuple mro)
    | none => gapIt
  | .type, "__bases__" => match ← PyPure.immView obj with
    | some (.builtin b) =>
      return PyPure.imm (m := m) (.tuple (b.info.bases.map fun c => PyPure.imm (m := m) (.builtin c)))
    | _ => match ← classData? obj with
      | some cd => return PyPure.imm (m := m) (.tuple cd.bases)
      | none => gapIt
  | .type, "__dict__" => match ← classData? obj with
    | some cd => PyPure.allocObj (PyPure.imm (m := m) (.builtin .mappingproxy)) (.mappingProxy cd.ns)
    | none => gapIt
  | .type, "__doc__" => match ← classData? obj with
    | some cd => return (← dictFindStr cd.ns "__doc__").getD (PyPure.imm (m := m) .none)
    | none => gapIt
  | .function, "__name__" => match ← PyReads.objView obj with
    | some (.func n _ _ _) => return PyPure.imm (m := m) (.str (.ofString n))
    | _ => gapIt
  | .function, "__module__" => match ← PyReads.objView obj with
    | some (.func _ mo _ _) => pure mo
    | _ => gapIt
  | .function, "__annotations__" => match ← PyReads.objView obj with
    | some (.func _ _ (some a) _) => pure a
    | _ => PyPure.gap "the __annotations__ of a function that has none set is not modelled yet"
  | .function, "__dict__" => match ← PyReads.objDict obj with
    | some d => pure d
    | none => PyPure.gap "the __dict__ of a function that has none yet is not modelled yet"
  | t, name =>
    -- An exception's state, and the member fields of its class (`None` until set).
    if !t.info.mro.contains .BaseException then gapIt else
    let some (.exc d) ← PyReads.objView obj | gapIt
    match name, (t.ownNames.find? (·.1 == name)).map (·.2) with
    | "args", _ => pure d.args
    | "__context__", _ => pure d.context
    | "__cause__", _ => pure d.cause
    | "__traceback__", _ => pure d.traceback
    | "__suppress_context__", _ => pure (PyPure.imm (m := m) (.bool d.suppressContext))
    | "__dict__", _ => match ← PyReads.objDict obj with
      | some dict => pure dict
      | none => PyPure.gap "the __dict__ of an exception that has none yet is not modelled yet"
    | n, some AttrKind.member =>
      -- The unicode errors' and the `SyntaxError` family's members are not all objects.
      if t.info.mro.any ([Builtin.UnicodeError, .SyntaxError].contains ·) then gapIt else
      pure ((d.fields.find? (·.1 == n)).map (·.2) |>.getD (PyPure.imm (m := m) .none))
    | _, _ => gapIt

/-- The args tuple `args` with `x` in front. -/
def prepend [PyPure m V] (x args : V) : m V := do
  let some (.tuple xs) ← PyPure.immView args | PyPure.gap "an args value that is not a tuple"
  pure (PyPure.imm (m := m) (.tuple (#[x] ++ xs)))

/-- `AttributeError` for the name `name` of `obj`, with CPython's message `msg` and its fields. -/
def raiseAttr [PyReads m V] {α : Type} (obj : V) (name msg : String) : m α :=
  raiseBuiltin "AttributeError" msg
    #[("name", PyPure.imm (m := m) (.str (.ofString name))), ("obj", obj)]

/-- How deep a dispatch of one call or one attribute access may nest inside one step before the
model gaps: a `property` whose getter is a bound method of a class with `__call__`, and so on. -/
def dispatchDepth : Nat := 100

/-- Whether the class `c` is in the MRO `mro`, by identity. -/
def inMro [PyPure m V] (c : V) (mro : Array V) : m Bool := do
  for x in mro do
    if (← PyPure.identical x c) == .yes then return true
  return false

/-- Whether the exception `x` is an `AttributeError`, of the built-in class or a subclass. -/
def isAttributeError [PyReads m V] (x : V) : m Bool := do
  let some mro ← mroOf (← PyReads.classOf x) | return false
  inMro (PyPure.imm (m := m) (.builtin .AttributeError)) mro

/-- The elements of the tuple `v`, or a gap. -/
def tupleItems [PyPure m V] (v : V) : m (Array V) := do
  let some (.tuple xs) ← PyPure.immView v | PyPure.gap "a value that is not a tuple"
  pure xs

/-- The `self` of a call of the method `name` of the built-in type `t` through its descriptor
(`list.append(l, x)`) or its slot wrapper (`int.__add__(a, b)`, when `wrapper`): the first
argument, which must be an instance of `t`, and the other arguments; CPython's `TypeError`
otherwise. -/
def descrSelf [PyReads m V] (t : Builtin) (name : String) (wrapper : Bool) (args : V) :
    m (V × V) := do
  let xs ← tupleItems args
  let some self := xs[0]? |
    if wrapper then
      raiseBuiltin "TypeError" s!"descriptor '{name}' of '{t.info.name}' object needs an argument"
    else raiseBuiltin "TypeError" s!"unbound method {t.info.name}.{name}() needs an argument"
  let some mro ← mroOf (← PyReads.classOf self) | PyPure.gap "a class without an MRO"
  if !(← inMro (PyPure.imm (m := m) (.builtin t)) mro) then
    if wrapper then
      raiseBuiltin "TypeError"
        s!"descriptor '{name}' requires a '{t.info.name}' object but received a '{← typeName self}'"
    else
      raiseBuiltin "TypeError"
        s!"descriptor '{name}' for '{t.info.name}' objects doesn't apply to a '{← typeName self}' object"
  return (self, PyPure.imm (m := m) (.tuple (xs.extract 1 xs.size)))

/-- The `tp_name` of the class `c`, as CPython's messages give it. -/
def classTpName [PyReads m V] (c : V) : m String := do
  match ← PyPure.immView c with
  | some (.builtin b) => pure (if b.info.tpName.isEmpty then b.info.name else b.info.tpName)
  | _ => classNameOf c

/-- CPython's `classmethod_get` check of the class `cls` that the class method `name` of the
built-in type `t` binds to: `TypeError` unless `cls` is a class that is `t` or a subclass of it. -/
def classDescrCheck [PyReads m V] (t : Builtin) (name : String) (cls : V) : m Unit := do
  let tName ← classTpName (PyPure.imm (m := m) (.builtin t))
  if !(← isType cls) then
    raiseBuiltin "TypeError"
      s!"descriptor '{name}' for type '{tName}' needs a type, not a '{← typeName cls}' as arg 2"
  let some mro ← mroOf cls | PyPure.gap "a class without an MRO"
  if !(← inMro (PyPure.imm (m := m) (.builtin t)) mro) then
    raiseBuiltin "TypeError"
      s!"descriptor '{name}' requires a subtype of '{tName}' but received '{← classTpName cls}'"

/-- The class of a call of the class method `name` of the built-in type `t` through its
descriptor (`dict.__dict__["fromkeys"](D, xs)`), as CPython's `classmethoddescr_call`: the first
argument, checked by `classDescrCheck`, and the other arguments. -/
def classDescrSelf [PyReads m V] (t : Builtin) (name : String) (args : V) : m (V × V) := do
  let xs ← tupleItems args
  let some cls := xs[0]? |
    raiseBuiltin "TypeError"
      s!"descriptor '{name}' of '{← classTpName (PyPure.imm (m := m) (.builtin t))}' object needs an argument"
  classDescrCheck t name cls
  return (cls, PyPure.imm (m := m) (.tuple (xs.extract 1 xs.size)))

/-- A gap where whether `d` is a descriptor depends on more than its built-in part: an instance of a
user subclass of `property`, `classmethod`, `staticmethod` or `super`, whose `__get__` or `__set__`
may be the subclass's own, an exception of a user class that defines `__get__`, `__set__` or
`__delete__`, and a class whose metaclass defines one of them. -/
def descrKindCheck [PyReads m V] (d : V) : m Unit := do
  match ← PyReads.objView d with
  | some (.property ..) | some (.classmethod _) | some (.staticmethod _) | some (.member ..)
  | some (.super ..) =>
    if !((← PyPure.immView (← PyReads.classOf d)) matches some (.builtin _)) then
      PyPure.gap "a descriptor of a subclass of a built-in descriptor type is not modelled yet"
  | some (.cls _) =>
    let mt ← PyReads.classOf d
    if !((← PyPure.immView mt) matches some (.builtin _)) then
      for n in ["__get__", "__set__", "__delete__"] do
        if (← lookupType mt n).isSome then
          PyPure.gap "a class whose metaclass defines a descriptor method is not modelled yet"
  | some (.exc _) =>
    let t ← PyReads.classOf d
    if !((← PyPure.immView t) matches some (.builtin _)) then
      for n in ["__get__", "__set__", "__delete__"] do
        if (← lookupType t n).isSome then
          PyPure.gap "an exception whose class defines a descriptor method is not modelled yet"
  | _ => pure ()

/-- Whether the descriptor `d` is a data descriptor: its type has `__set__` or `__delete__`. -/
def isDataDescr [PyReads m V] (d : V) : m Bool := do
  descrKindCheck d
  match ← PyPure.immView d with
  | some (.descr _ _ k) => pure (k == .getset || k == .member)
  | some _ => pure false
  | none => match ← PyReads.objView d with
    | some (.property ..) | some (.member ..) => pure true
    | some .inst =>
      let t ← PyReads.classOf d
      return (← lookupType t "__set__").isSome || (← lookupType t "__delete__").isSome
    | _ => pure false

/-- Whether `d` has a `__get__`. -/
def hasGet [PyReads m V] (d : V) : m Bool := do
  descrKindCheck d
  match ← PyPure.immView d with
  | some (.descr ..) => pure true
  | some _ => pure false
  | none => match ← PyReads.objView d with
    | some (.func ..) | some (.classmethod _) | some (.staticmethod _) | some (.property ..)
    | some (.member ..) => pure true
    | some .inst => return (← lookupType (← PyReads.classOf d) "__get__").isSome
    | _ => pure false

/-- CPython's `descr_check`: `TypeError` unless `obj` is an instance of the class `owner` of the
descriptor `name`. -/
def descrCheck [PyReads m V] (owner : V) (name : String) (obj : V) : m Unit := do
  let some mro ← mroOf (← PyReads.classOf obj) | PyPure.gap "a class without an MRO"
  if !(← inMro owner mro) then
    raiseBuiltin "TypeError"
      s!"descriptor '{name}' for '{← classNameOf owner}' objects doesn't apply to a '{← typeName obj}' object"

/-- Whether the class `a` is a subclass of the class `b`: `b` is in `a`'s MRO. -/
def isSubclass [PyReads m V] (a b : V) : m Bool := do
  let some mro ← mroOf a | return false
  inMro b mro

/-- The solid base of the class `c`: a built-in type's own, or a class object's stored one. -/
def solidBaseOf [PyReads m V] (c : V) : m V := do
  match ← PyPure.immView c with
  | some (.builtin b) => pure (PyPure.imm (m := m) (.builtin b.info.solidBase))
  | _ => match ← classData? c with
    -- A class with slots of its own is its own solid base, which `None` records.
    | some cd => if (← PyPure.immView cd.solidBase) matches some .none then pure c else pure cd.solidBase
    | none => PyPure.gap "the solid base of a value that is not a class"

/-- CPython's `best_base`: the base whose solid base is the most derived, with CPython's
`TypeError` when the solid bases are not on one chain. -/
def bestBase [PyReads m V] (bases : Array V) : m V := do
  let mut winner : Option (V × V) := none
  for b in bases do
    let sb ← solidBaseOf b
    match winner with
    | none => winner := some (b, sb)
    | some (_, wsb) =>
      if ← isSubclass wsb sb then pure ()
      else if ← isSubclass sb wsb then winner := some (b, sb)
      else raiseBuiltin "TypeError" "multiple bases have instance lay-out conflict"
  match winner with
  | some (b, _) => pure b
  | none => PyPure.gap "a class without bases"

/-- The class whose C function is the `tp_new` of the built-in exception class `u`, as
`exceptions.c` defines them: `OSError_new` for `FileNotFoundError`, `BaseException_new` for
`ValueError`. -/
def excNewClass (u : Builtin) : Builtin :=
  if u.info.mro.contains .OSError then .OSError
  else if u.info.mro.contains .BaseExceptionGroup then .BaseExceptionGroup
  else if u.info.mro.contains .MemoryError then .MemoryError
  else .BaseException

/-- The C function of the `tp_new` of the built-in type `b`, named by the type that defines it,
where the model knows it: the exception classes, `object` and `type`. -/
def _root_.StrataPython.Dyn.Sem.Builtin.newId (b : Builtin) : Option Builtin :=
  if b.info.mro.contains .BaseException then some (excNewClass b)
  else if b == .object || b == .type then some b
  else none

/-- What a class's `tp_new` is: CPython's `slot_tp_new`, which calls the `__new__` that the MRO
gives, decided at the class `decidedAt` of the class's chain of `tp_base`s (every class of the chain
before `decidedAt` has the same `tp_new`); or the `tp_new` of the built-in type `b`. -/
inductive TpNew (V : Type) where
  | slot (decidedAt : V)
  | builtin (b : Builtin)

/-- How many classes the walks of `tpNewOf` and `staticBaseOf` follow. -/
def tpNewFuel : Nat := 1000

/-- **The `tp_new` of the class `c`**, as `type_new` and `update_one_slot` set it: `slot_tp_new`
when the `__new__` that the MRO gives first is not a built-in type's own; else the `tp_new` that
`c` inherits from its `tp_base`. -/
def tpNewOf [PyReads m V] : Nat → V → m (TpNew V)
  | 0, _ => PyPure.gap "a chain of bases longer than the model follows"
  | n + 1, c => do
    if let some (.builtin b) ← PyPure.immView c then return .builtin b
    let some cd ← classData? c | PyPure.gap "a base that is not a class"
    -- A class with one base and no `__new__` of its own has its base's MRO after itself and
    -- its base as `tp_base`, so it has its base's `tp_new`.
    if let #[b] := cd.bases then
      if (← dictFindStr cd.ns "__new__").isNone then return ← tpNewOf n b
    if let some f ← lookupType c "__new__" then
      if !((← PyPure.immView f) matches some (.bound _ _ "__new__" _)) then return .slot c
    tpNewOf n (← bestBase cd.bases)

/-- `tp_new_wrapper`'s `staticbase` of the class `c`: the first class of its chain of `tp_base`s
whose `tp_new` is not `slot_tp_new`, with the built-in type whose `tp_new` that class has; it
goes on from the base of the class where `tpNewOf` decided `slot_tp_new`. -/
def staticBaseOf [PyReads m V] : Nat → V → m (V × Builtin)
  | 0, _ => PyPure.gap "a chain of bases longer than the model follows"
  | n + 1, c => do
    match ← tpNewOf tpNewFuel c with
    | .builtin b => pure (c, b)
    | .slot d =>
      let some cd ← classData? d | PyPure.gap "a base that is not a class"
      staticBaseOf n (← bestBase cd.bases)

/-- A metaclass's own `__call__` for a call of the class `cls`, other than `type`'s: `type_call`
runs only when there is none. -/
def metaCall? [PyReads m V] (cls : V) : m (Option V) := do
  if ← classIs cls .type then return none
  let some mc ← lookupType (← PyReads.classOf cls) "__call__" | return none
  if (← PyPure.immView mc) matches some (.descr .type "__call__" _) then return none
  return some mc

/-- A gap where `slot_tp_new` reads `cls.__new__` through a metaclass's `__getattribute__` other
than `type`'s, which may give another `__new__` than the class's own. -/
def metaGetattributeCheck [PyReads m V] (cls : V) : m Unit := do
  if let some ga ← lookupType (← PyReads.classOf cls) "__getattribute__" then
    if !((← PyPure.immView ga) matches some (.descr .type "__getattribute__" _)) then
      PyPure.gap "a class call whose metaclass defines __getattribute__ is not modelled yet"

/-- What a class call runs for `__new__`, as `type_call` does. -/
inductive ClassNew (V : Type) where
  /-- The `tp_new` of the built-in type `t`, bound to `self`, called directly (`callTpNew`). -/
  | builtin (self : V) (t : Builtin)
  /-- The `__new__` that the class's MRO gives, called as `slot_tp_new` calls it. -/
  | slot

/-- What a call of the class `cls`, whose MRO gives `new` as its `__new__`, runs for it: when `new`
is a built-in type's `__new__` and that type's C function is `cls`'s `tp_new` (`tpNewOf`), that
`tp_new` itself, without `tp_new_wrapper`'s check; when `cls`'s `tp_new` is `slot_tp_new`, or `new`
is not built in, `new` itself; and `none` when `new` is a built-in type's `__new__` other than
`cls`'s `tp_new`. -/
def tpNewFor [PyReads m V] (cls new : V) : m (Option (ClassNew V)) := do
  match ← PyPure.immView new with
  | some (.bound s u "__new__" _) =>
    match ← tpNewOf tpNewFuel cls with
    | .builtin b =>
      if b == u || (b.newId.isSome && b.newId == u.newId) then return some (.builtin s u)
      else return none
    | .slot _ => return some .slot
  | _ => return some .slot

/-- **The `tp_new` of the built-in type `t`, bound to `self`, called as `type_call` calls it**:
its body, without `tp_new_wrapper`'s check.  The `.tpNew` value that names it is made here and
handed to `callBuiltin` at once, which doesn't keep it: this call is the value's whole life. -/
def callTpNew [PyCalls m V] (self : V) (t : Builtin) (args kwargs : V) : m V :=
  PyCalls.callBuiltin (PyPure.imm (m := m) (.bound self t "__new__" .tpNew)) args kwargs

/-- The special methods that each have a slot of their own in CPython: a class whose method is a
built-in type's slot wrapper runs that type's C slot. A slot that several methods share (`__eq__`
and `__ne__`, `__setattr__` and `__delattr__`, `__add__` and `__radd__`) holds the C function only
when all of them are a built-in type's, so it isn't listed. -/
def loneSlots : List String :=
  ["__repr__", "__str__", "__init__", "__hash__", "__iter__", "__next__", "__call__", "__len__",
    "__contains__", "__int__", "__float__", "__index__", "__bool__", "__get__", "__iadd__",
    "__isub__", "__imul__", "__imatmul__", "__itruediv__", "__ifloordiv__", "__imod__", "__ipow__",
    "__ilshift__", "__irshift__", "__iand__", "__ixor__", "__ior__"]

/-- Whether the attribute `f`, found as the special method `name` on the type `t`, is what CPython
installs as `t`'s C slot: a built-in type's slot wrapper descriptor for `name`, of a type that `t`
subclasses, where `name` has a slot of its own (`loneSlots`). A method-wrapper such as
`x.__repr__` is not one, and neither is a wrapper of a method with a shared slot. -/
def isOwnSlot [PyReads m V] (name : String) (f t : V) : m Bool := do
  if !loneSlots.contains name then return false
  match ← PyPure.immView f with
  | some (.descr b fname .slotWrapper) =>
    if fname != name then return false
    let some mro ← mroOf t | return false
    inMro (PyPure.imm (m := m) (.builtin b)) mro
  | _ => return false

mutual
/-- **`f(*args, **kwargs)`**, CPython's `PyObject_Call`, at the dispatch depth `n`: a function
object runs its closure; a built-in callable or a native function its body (`callBuiltin`); a bound
method its function with its object in front; a class `type.__call__`; an instance its type's
`__call__`. -/
def callN [PyCalls m V] : Nat → V → V → V → m V
  | 0, _, _, _ => PyPure.gap "a call dispatch nested deeper than the model follows"
  | n + 1, f, args, kwargs => do
    kwargsKeysGap f kwargs
    match ← PyPure.immView f with
    -- A call of a built-in callable counts one C level: CPython counts one for every built-in
    -- but the FASTCALL ones (`setattr`, `iter`, `dict.get`), which the model overcounts by one.
    -- A class-method descriptor, which CPython calls through `_PyObject_MakeTpCall`, counts two.
    | some (.builtin b) =>
      if b.info.kind == .type then typeCallN n true f args kwargs
      else PyReads.withDepth 1 (PyCalls.callBuiltin f args kwargs)
    | some (.descr t name kind) =>
      if kind == .method || kind == .slotWrapper then
        PyReads.withDepth 1 do
          let (self, rest) ← descrSelf t name (kind == .slotWrapper) args
          PyCalls.callBuiltin (PyPure.imm (m := m) (.bound self t name kind)) rest kwargs
      else if kind == .classMethod then
        PyReads.withDepth 2 do
          let (cls, rest) ← classDescrSelf t name args
          PyCalls.callBuiltin (PyPure.imm (m := m) (.bound cls t name kind)) rest kwargs
      else PyReads.withDepth 1 (PyCalls.callBuiltin f args kwargs)
    | some (.bound _ _ _ k) =>
      if k == .tpNew then PyPure.modelInvariant "a type's tp_new outside a class call"
      else PyReads.withDepth 1 (PyCalls.callBuiltin f args kwargs)
    | some (.method func self) => callN n func (← prepend self args) kwargs
    | some _ => raiseBuiltin "TypeError" s!"'{← typeName f}' object is not callable"
    | none => match ← PyReads.objView f with
      | some (.func ..) =>
        checkKwargs kwargs
        -- A call into Python costs CPython about 2 C levels.
        PyReads.withDepth 2 (PyCalls.callFunc f args kwargs)
      | some (.native _) => PyReads.withDepth 1 (PyCalls.callBuiltin f args kwargs)
      | some (.cls _) => typeCallN n true f args kwargs
      | some .inst =>
        let t ← PyReads.classOf f
        match ← lookupType t "__call__" with
        | some c =>
          -- `slot_tp_call` through `_PyObject_MakeTpCall`, which counts a C level.
          PyReads.withDepth 1 do
            let g ← descrGetN n c (some f) t
            callN n g args kwargs
        | none => raiseBuiltin "TypeError" s!"'{← classNameOf t}' object is not callable"
      | _ => PyPure.gap "a call of this built-in object is not modelled yet"

/-- **A call of the class `cls`**: with `viaMeta`, a metaclass's own `__call__` if it has one; then,
as `type.__call__` (`type_call`), `type(x)`'s one-argument form, else `__new__`, then `__init__`
if the result is an instance of `cls`. -/
def typeCallN [PyCalls m V] : Nat → Bool → V → V → V → m V
  | 0, _, _, _, _ => PyPure.gap "a call dispatch nested deeper than the model follows"
  | n + 1, viaMeta, cls, args, kwargs =>
    -- A call of a class goes through `_PyObject_MakeTpCall`, which counts a C level.
    PyReads.withDepth 1 do
      let mt ← PyReads.classOf cls
      if viaMeta then
        if let some mc ← metaCall? cls then
          let g ← descrGetN n mc (some cls) mt
          return ← callN n g args kwargs
      let some (.tuple xs) ← PyPure.immView args | PyPure.gap "an args value that is not a tuple"
      if (← PyPure.immView cls) matches some (.builtin .type) then
        -- `type_vectorcall`: one argument and keywords is its own error.
        if let #[x] := xs then
          if (← PyReads.dictLen kwargs) == 0 then return ← PyReads.classOf x
          raiseBuiltin "TypeError" "type() takes no keyword arguments"
        if xs.size != 3 then raiseBuiltin "TypeError" "type() takes 1 or 3 arguments"
      let some new ← lookupType cls "__new__" |
        PyPure.gap s!"a class without __new__"
      metaGetattributeCheck cls
      -- `type_call` runs the class's `tp_new`, not the `__new__` that the MRO gives: where that
      -- is a built-in type's, the two must be the same C function.
      let some tpNew ← tpNewFor cls new |
        PyPure.gap "a class whose __new__ comes from another built-in base than its tp_new is not modelled yet"
      let obj ← match tpNew with
        -- `type_call` calls the type's `tp_new` directly, without `tp_new_wrapper`'s check.
        | .builtin s u => callTpNew s u (← prepend cls args) kwargs
        | .slot => callN n (← descrGetN n new none cls) (← prepend cls args) kwargs
      -- `__init__` runs only on an instance of `cls`.
      let some objMro ← mroOf (← PyReads.classOf obj) | return obj
      let mut isInst := false
      for c in objMro do
        if (← PyPure.identical c cls) == .yes then isInst := true
      if !isInst then return obj
      let some init ← lookupType (← PyReads.classOf obj) "__init__" | return obj
      let initF ← descrGetN n init (some obj) (← PyReads.classOf obj)
      -- `type_call` runs a built-in type's own `tp_init` as the C slot, with no C level of its own.
      let r ← if ← isOwnSlot "__init__" init (← PyReads.classOf obj) then
          PyCalls.callBuiltin initF args kwargs
        else callN n initF args kwargs
      if !((← PyPure.immView r) matches some .none) then
        raiseBuiltin "TypeError" s!"__init__() should return None, not '{← typeName r}'"
      return obj

/-- **`d.__get__(obj, type)`**, for the descriptor `d` found on the class `type`; `obj` is `none`
for a lookup on the class itself (CPython's `NULL`), which differs from the object `None`. -/
def descrGetN [PyCalls m V] : Nat → V → Option V → V → m V
  | 0, _, _, _ => PyPure.gap "a call dispatch nested deeper than the model follows"
  | n + 1, d, obj?, type => do
    let noObj := obj?.isNone
    -- What a `__get__` written in Python receives for `NULL`.
    let obj := obj?.getD (PyPure.imm (m := m) .none)
    match ← PyPure.immView d with
    | some (.descr t name k) => match k with
      | .method | .slotWrapper =>
        if noObj then pure d else do
          -- CPython's message for a slot wrapper of another type depends on whether the
          -- attribute is called as a method, which the IR doesn't show.
          if k == .slotWrapper then
            let some mro ← mroOf (← PyReads.classOf obj) | PyPure.gap "a class without an MRO"
            if !(← inMro (PyPure.imm (m := m) (.builtin t)) mro) then
              PyPure.gap "a slot wrapper bound to an object of another type is not modelled yet"
          descrCheck (PyPure.imm (m := m) (.builtin t)) name obj
          pure (PyPure.imm (m := m) (.bound obj t name k))
      | .classMethod => do
        -- `classmethod_get`: the class is `obj`'s when `type` is `None`.
        let cls ← if (← PyPure.immView type) matches some .none then PyReads.classOf obj else pure type
        classDescrCheck t name cls
        pure (PyPure.imm (m := m) (.bound cls t name k))
      | .staticMethod => pure d
      | .tpNew => PyPure.modelInvariant "a type's tp_new outside a class call"
      | .getset | .member => if noObj then pure d else do
          descrCheck (PyPure.imm (m := m) (.builtin t)) name obj
          -- `type_get_doc`: a class's own `__doc__`, bound by its `__get__` when it has one.
          if t == .type && name == "__doc__" then
            if let some cd ← classData? obj then
              let some doc ← dictFindStr cd.ns "__doc__" | return PyPure.imm (m := m) .none
              if ← hasGet doc then return ← descrGetN n doc none obj
              return doc
          builtinGetsetGet t name obj
    | some _ => pure d
    | none => do
      descrKindCheck d
      match ← PyReads.objView d with
      | some (.func ..) => if noObj then pure d else pure (PyPure.imm (m := m) (.method d obj))
      | some (.classmethod none) =>
        -- `classmethod.__new__` leaves the callable `NULL`.
        PyPure.gap "an unset classmethod is not modelled yet"
      | some (.classmethod (some f)) =>
        if (← PyPure.immView f) matches some .none then
          PyPure.gap "a classmethod whose callable is None is not modelled yet"
        -- CPython 3.12's `classmethod` binds through its callable's `__get__`, when it has one.
        if ← hasGet f then descrGetN n f (some type) type else pure (PyPure.imm (m := m) (.method f type))
      -- CPython raises `RuntimeError: uninitialized staticmethod object`.
      | some (.staticmethod none) => PyPure.gap "an unset staticmethod is not modelled yet"
      | some (.staticmethod (some f)) => pure f
      | some (.property fget _ _ _) =>
        if noObj then pure d
        else if (← PyPure.immView fget) matches some .none then
          PyPure.gap "a property without a getter is not modelled yet"
        else callN n fget (PyPure.imm (m := m) (.tuple #[obj])) (← PyPure.allocDict)
      | some (.member owner name i) =>
        if noObj then pure d
        else do
        descrCheck owner name obj
        match ← PyReads.slotGet obj i with
          | some v => pure v
          | none => do
            let tn ← classNameOf (← PyReads.classOf obj)
            raiseAttr obj name s!"'{tn}' object has no attribute '{name}'"
      | some .inst =>
        match ← lookupType (← PyReads.classOf d) "__get__" with
        -- `slot_tp_descr_get` calls `__get__` as it is, with the descriptor first.
        | some g => callN n g (PyPure.imm (m := m) (.tuple #[d, obj, type])) (← PyPure.allocDict)
        | none => pure d
      | _ => pure d
end

/-- **A call of `g`, the special method `name` that CPython's slot dispatch reaches**, bound from
`f`, the attribute found on the type `t`: where `f` is `t`'s own C slot (`isOwnSlot`), it runs as
CPython runs the C slot, with no C level of its own; anything else is called as `callN` calls it. -/
def callSlotN [PyCalls m V] (n : Nat) (name : String) (f t g args kwargs : V) : m V := do
  if ← isOwnSlot name f t then PyCalls.callBuiltin g args kwargs
  else callN n g args kwargs

/-- Whether `f`, an attribute found on a type, is one that CPython's `lookup_maybe_method` calls
unbound, since its type has `Py_TPFLAGS_METHOD_DESCRIPTOR`: a Python function, a method
descriptor or a slot wrapper, built in or native. -/
def isMethodDescriptor [PyReads m V] (f : V) : m Bool := do
  match ← PyPure.immView f with
  | some (.descr _ _ .method) | some (.descr _ _ .slotWrapper) => pure true
  | some _ => pure false
  | none => match ← PyReads.objView f with
    | some (.func ..) => pure true
    | some (.native nf) => pure (nf.kind matches .function | .methodDescriptor | .wrapperDescriptor)
    | _ => pure false

/-- The special method `f`, found on the type `t` of `self`, bound as `lookup_maybe_method` binds
it: a method descriptor (`isMethodDescriptor`) as `descrGetN` binds it, whose errors CPython
raises when it calls it; anything else by its `__get__`, where an exception gives `none`, the
`NULL` that each caller handles as CPython does. -/
def bindMaybe [PyCalls m V] (f self t : V) : m (Option V) := do
  if ← isMethodDescriptor f then return some (← descrGetN dispatchDepth f (some self) t)
  tryCatch (some <$> descrGetN dispatchDepth f (some self) t) fun _ => pure none

/-- The dunder `name`, `f`, found on the type `t` of `self`, called with `args`: bound by its
`__get__` first (a function binds `self`, as CPython's `lookup_maybe_method` and
`vectorcall_unbound` do; a value without `__get__` is called as it is), then called as the slot
dispatch calls it (`callSlotN`). -/
def callFound [PyCalls m V] (name : String) (f self t : V) (args : Array V) (kwargs : V) : m V := do
  let g ← descrGetN dispatchDepth f (some self) t
  callSlotN dispatchDepth name f t g (PyPure.imm (m := m) (.tuple args)) kwargs


/-- The `str` key `name`. -/
def strKey [PyPure m V] (name : String) : V := PyPure.imm (m := m) (.str (.ofString name))

end

end

end StrataPython.Dyn.Sem.Proto
