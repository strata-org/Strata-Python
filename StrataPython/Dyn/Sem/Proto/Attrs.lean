/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Calls

set_option autoImplicit false

/-!
# Attributes

Generic over the record of primitives, CPython 3.12's attribute protocol, over the lookups of
`Lookup.lean` (`lookupType`, `descrGetN`):

* `getAttr v name`, `PyObject_GetAttr`: a user `__getattribute__`, or the generic lookup of
  `_PyObject_GenericGetAttrWithDict` (data descriptors with a `__get__` on the type, the instance
  dict, other descriptors and class attributes), `type_getattro` on a class, `super_getattro` on
  a `super` object, a module's globals; then `__getattr__` when the lookup raises
  `AttributeError`;
* `setAttr v name val`, `PyObject_SetAttr` and `PyObject_DelAttr`: a user `__setattr__` or
  `__delattr__`, else data descriptors, then the instance dict; `type.__setattr__` on a class.

An entry of a built-in type's table that no piece models yet stops with a gap.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The value of the attribute `name` of the module object `v`, named `mod`: an entry of the
`builtins` dict for the `builtins` module (`isBuiltins`), a global of the module otherwise. -/
def moduleAttr [PyReads m V] (v : V) (mod : String) (gapped : Array String) (isBuiltins : Bool)
    (name : String) : m V := do
  if gapped.contains name then PyPure.gap s!"the attribute {mod}.{name} is not modelled yet"
  let r ← if isBuiltins then PyReads.builtinGet name else PyReads.globalGet mod name
  match r with
  | some x => pure x
  | none => raiseAttr v name s!"module '{mod}' has no attribute '{name}'"

/-- A gap where `v`'s instance dict decides an attribute, if `v` is a built-in constant whose type
gives its instances a `__dict__` (`exit`, `help`, `builtins.__spec__`): the model holds no dict for
it. -/
def builtinDictGap [PyPure m V] (v : V) (name : String) : m Unit := do
  if let some (.builtin b) ← PyPure.immView v then
    if b.typeOf.info.instanceDict then
      PyPure.gap s!"the attribute {name} of the built-in {b.info.name} is not modelled yet"

/-- `_PyObject_GenericGetAttrWithDict(v, name)`: a data descriptor with a `__get__` on `v`'s
type, then `v`'s `__dict__`, then any other descriptor or class attribute. -/
def genericGetAttr [PyCalls m V] (v t : V) (name : String) : m V := do
  -- A plain value of a built-in type's table is no data descriptor, so the instance dict comes
  -- first; the model may not hold the value itself.
  let descr ← match ← lookupTypeEntry t name with
    | .plain b =>
      if let some dict ← PyReads.objDict v then
        if let some x ← dictFindStr dict name then return x
      builtinEntry b name
    | .entry d => pure (some d)
    | .none => pure none
  if let some d := descr then
    if (← isDataDescr d) && (← hasGet d) then return ← descrGetN dispatchDepth d (some v) t
  -- The dict of a built-in constant such as exit holds no name that its type has (`gen_types.py`
  -- checks this), so it decides only the names that the type lacks.
  if descr.isNone then builtinDictGap v name
  if let some dict ← PyReads.objDict v then
    -- A user class's `__dict__` descriptor, which `type.__new__` puts in its namespace.
    if name == "__dict__" && descr.isNone then return dict
    -- Its `__weakref__` descriptor is a data descriptor too, so an entry of the dict can't shadow it.
    if name == "__weakref__" && descr.isNone then implicitDescrGap name ((← mroOf t).getD #[])
    if let some x ← dictFindStr dict name then return x
  match descr with
  | some d => if ← hasGet d then descrGetN dispatchDepth d (some v) t else pure d
  | none =>
    implicitDescrGap name ((← mroOf t).getD #[])
    raiseAttr v name s!"'{← classTpName t}' object has no attribute '{name}'"

/-- `type_getattro(cls, name)`: a data descriptor with a `__get__` on the metaclass, then the
class's own MRO, then the metaclass's other attributes. -/
def typeGetAttr [PyCalls m V] (cls : V) (name : String) : m V := do
  if name == "__new__" then cTypeNewGap cls
  -- A name that the class gaps gaps before the metaclass's data descriptors (`__module__`,
  -- `__doc__`, …) read the class.
  if let some cd ← classData? cls then
    if cd.gapped.contains name then
      PyPure.gap s!"the attribute {cd.name}.{name} is not modelled yet"
  let mt ← PyReads.classOf cls
  let metaAttr ← lookupType mt name
  if let some d := metaAttr then
    if (← isDataDescr d) && (← hasGet d) then return ← descrGetN dispatchDepth d (some cls) mt
  if let some a ← lookupType cls name then
    return ← if ← hasGet a then descrGetN dispatchDepth a none cls else pure a
  match metaAttr with
  | some d => if ← hasGet d then descrGetN dispatchDepth d (some cls) mt else pure d
  | none =>
    implicitDescrGap name ((← mroOf cls).getD #[])
    raiseAttr cls name s!"type object '{← classTpName cls}' has no attribute '{name}'"

/-- `super_getattro`: the attribute `name` from the classes after `thisType` in the MRO of the
start type (`obj`'s type, or `obj` itself when it is a subclass of `thisType`). -/
def superGetAttr [PyCalls m V] (sup thisType obj : V) (name : String) : m V := do
  -- `super_getattro` doesn't look `__class__` up in the MRO: it is the `super` object's own.
  if name == "__class__" then return ← genericGetAttr sup (← PyReads.classOf sup) name
  let objIsType ← isType obj
  let start ← if objIsType then
      match ← mroOf obj with
      | some mro => if ← inMro thisType mro then pure obj else PyReads.classOf obj
      | none => PyReads.classOf obj
    else PyReads.classOf obj
  let some mro ← mroOf start | PyPure.gap "super() of a start type that is not a class"
  let mut after := false
  let mut rest : Array V := #[]
  for c in mro do
    if after then rest := rest.push c
    else if (← PyPure.identical c thisType) == .yes then after := true
  match ← lookupMro rest.toList name with
  | some a =>
    -- `super_getattro` passes `NULL` for the object when it is the start type itself.
    let bindTo : Option V := if (← PyPure.identical obj start) == .yes then none else some obj
    if ← hasGet a then descrGetN dispatchDepth a bindTo start else pure a
  | none =>
    implicitDescrGap name rest
    genericGetAttr sup (← PyReads.classOf sup) name

/-- A gap when `v` is a native function and `name` is one of the attributes that it gaps. -/
def nativeAttrGap [PyReads m V] (v : V) (name : String) : m Unit := do
  if let some (.native f) ← PyReads.objView v then
    if f.gapped.contains name then
      PyPure.gap s!"the attribute {name} of the built-in {f.qualname} is not modelled yet"

/-- The lookup of `getAttr` without a user `__getattr__`: by the kind of `v`. -/
def getAttrCore [PyCalls m V] (v : V) (name : String) : m V := do
  if ← isType v then return ← typeGetAttr v name
  if let some (.method f _) ← PyPure.immView v then
    -- `method_getattro`: the method type's attributes, then the function's.
    if (← lookupType (← PyReads.classOf v) name).isSome then
      return ← genericGetAttr v (← PyReads.classOf v) name
    if (← builtinClass? f) matches some .function then
      nativeAttrGap f name
      return ← genericGetAttr f (← PyReads.classOf f) name
    PyPure.gap
      s!"the attribute {name} of a method whose function isn't a function object is not modelled yet"
  match ← PyReads.objView v with
  | some (.classmethod none) | some (.staticmethod none) =>
    PyPure.gap s!"the attribute {name} of an unset classmethod or staticmethod is not modelled yet"
  | some (.classmethod (some f)) | some (.staticmethod (some f)) =>
    -- What `functools_wraps` copies from a function, a built-in or an object of a built-in type
    -- that the model doesn't hold.
    if ["__module__", "__name__", "__qualname__", "__doc__", "__annotations__", "__dict__"].contains name then
      let held ← match ← PyReads.objDict v with
        | some d => pure (name != "__dict__" && (← dictFindStr d name).isSome)
        | none => pure false
      let plain := (← PyPure.immView f).isSome ||
        (← PyPure.immView (← PyReads.classOf f)) matches some (.builtin _)
      if plain && !held then
        PyPure.gap s!"the {name} of a classmethod or staticmethod of a function is not modelled yet"
    genericGetAttr v (← PyReads.classOf v) name
  | some (.super thisType obj) => superGetAttr v thisType obj name
  | some (.module mod gapped _ kind) =>
    -- `module_getattro` is the generic lookup first, which finds the module type's attributes.
    if (← lookupType (← PyReads.classOf v) name).isSome then
      PyPure.gap s!"the attribute {name} of a module, which its type gives, is not modelled yet"
    if gapped.contains name then PyPure.gap s!"the attribute {mod}.{name} is not modelled yet"
    let .made attrs := kind | moduleAttr v mod gapped (kind matches .builtins) name
    let own := attrs.find? (·.1 == name)
    -- CPython's import sets each imported submodule on its package, over any attribute that the
    -- package's body gave the same name; a package's attribute that is the submodule itself is
    -- the same either way.
    if let some sub ← PyReads.moduleGet s!"{mod}.{name}" then
      if let some (_, x) := own then
        if (← PyPure.identical x sub) matches .yes then return x
      PyPure.gap s!"the attribute {mod}.{name} is not modelled yet"
    if let some (_, x) := own then return x
    -- A module that a piece's body made has only the attributes that the body gave it. CPython's
    -- import also sets dunders such as `__name__` and `__spec__`, and CPython calls a module's
    -- `__getattr__` for a missing name, which the model doesn't.
    if (name.startsWith "__" && name.endsWith "__") || attrs.any (·.1 == "__getattr__") ||
        gapped.contains "__getattr__" then
      PyPure.gap s!"the attribute {mod}.{name} is not modelled yet"
    raiseAttr v name s!"module '{mod}' has no attribute '{name}'"
  | some (.native f) =>
    if f.gapped.contains name then
      PyPure.gap s!"the attribute {name} of the built-in {f.qualname} is not modelled yet"
    genericGetAttr v (← PyReads.classOf v) name
  | _ => genericGetAttr v (← PyReads.classOf v) name

/-- **`getattr(v, name)`**, CPython's `PyObject_GetAttr`: a user `__getattribute__` if `v`'s type
has one, else the lookup by kind; then `__getattr__` of the type, when there is one and the lookup
raised `AttributeError`; without `set_attribute_error_context`. -/
def getAttrRaw [PyCalls m V] (v : V) (name : String) : m V := do
  let t ← PyReads.classOf v
  let nameV := PyPure.imm (m := m) (.str (.ofString name))
  let (ga?, hook?) ← lookupType2 t "__getattribute__" "__getattr__"
  let attempt : m V := do
    match ga? with
    | some ga =>
      match ← PyPure.immView ga with
      | some (.descr b "__getattribute__" _) =>
        if (← defaultGetattrOwner t) == some b then
          -- With a `__getattr__` too, CPython's `slot_tp_getattr_hook` runs a built-in
          -- `__getattribute__` other than the generic one (`type`'s, a module's) through its
          -- wrapper, which counts a C level.
          if hook?.isSome && b != .object && b != .BaseException then
            PyReads.withDepth 1 (getAttrCore v name)
          else getAttrCore v name
        else PyPure.gap s!"the __getattribute__ of the built-in {b.info.name} on another type is not \
          modelled yet"
      | _ => callFound "__getattribute__" ga v t #[nameV] (← PyPure.allocDict)
    | none => getAttrCore v name
  match hook? with
  | none => attempt
  | some hook => tryCatch attempt fun x => do
    if ← isAttributeError x then
      callFound "__getattr__" hook v t #[nameV] (← PyPure.allocDict)
    else throw x

/-- **`getattr(v, name)`**, CPython's `PyObject_GetAttr`: `getAttrRaw`, and an `AttributeError`
that it raises without `name` and `obj` stops with a gap. -/
def getAttr [PyCalls m V] (v : V) (name : String) : m V :=
  tryCatch (getAttrRaw v name) fun x => do
    -- `set_attribute_error_context` writes `name` and `obj` of an `AttributeError` that has
    -- neither, which a rule at `calls` may not do to an exception that it didn't make.
    if ← isAttributeError x then
      if let some (.exc d) ← PyReads.objView x then
        if !(d.fields.any (·.1 == "name")) && !(d.fields.any (·.1 == "obj")) then
          PyPure.gap "an AttributeError without name and obj from an attribute read is not modelled yet"
    throw x

/-- `AttributeError` with the message `msg` and no fields, as CPython's attribute writes raise it. -/
def raiseAttrPlain [PyReads m V] {α : Type} (msg : String) : m α := raiseBuiltin "AttributeError" msg

/-- A write (`val = some x`) or deletion (`none`) of the attribute `n` of the exception `v`, a
getset or member descriptor of the exception class `t` (`k`), with CPython's checks. -/
def excSetAttr [PyWrites m V] (v : V) (t : Builtin) (n : String) (k : DescrKind)
    (val : Option V) : m Unit := do
  let some (.exc _) ← PyReads.objView v |
    PyPure.gap s!"a write to the attribute {t.info.name}.{n} of a value that is not an exception"
  let some x := val | match n with
    | "args" | "__context__" | "__cause__" | "__traceback__" =>
      raiseBuiltin "TypeError" s!"{n} may not be deleted"
    | _ => PyPure.gap s!"deleting the attribute {t.info.name}.{n} is not modelled yet"
  let isNone := (← PyPure.immView x) matches some .none
  let excOrNone (what : String) : m Unit := do
    if !isNone then
      let some mro ← mroOf (← PyReads.classOf x) |
        raiseBuiltin "TypeError" s!"exception {what} must be None or derive from BaseException"
      if !(← inMro (PyPure.imm (m := m) (.builtin .BaseException)) mro) then
        raiseBuiltin "TypeError" s!"exception {what} must be None or derive from BaseException"
  if t == .BaseExceptionGroup && (n == "message" || n == "exceptions") then
    raiseBuiltin "AttributeError" "readonly attribute"
  -- The unicode errors' and the `SyntaxError` family's members are not all objects: `start` and
  -- `end` are C integers, so a write checks its value.
  if t.info.mro.any ([Builtin.UnicodeError, .SyntaxError].contains ·) then
    PyPure.gap s!"a write to the attribute {t.info.name}.{n} is not modelled yet"
  match n with
  | "args" =>
    let items ← (← iterSeq x fun tn => s!"'{tn}' object is not iterable").items
    PyWrites.excSet v (.args (PyPure.imm (m := m) (.tuple items)))
  | "__context__" => excOrNone "context"; PyWrites.excSet v (.context x)
  | "__cause__" => excOrNone "cause"; PyWrites.excSet v (.cause x)
  | "__traceback__" =>
    if !isNone && !((← PyPure.immView x) matches some .traceback) then
      raiseBuiltin "TypeError" "__traceback__ must be a traceback or None"
    PyWrites.excSet v (.traceback x)
  | "__suppress_context__" =>
    let some (.bool b) ← PyPure.immView x | raiseBuiltin "TypeError" "attribute value type must be bool"
    PyWrites.excSet v (.suppressContext b)
  | _ =>
    if k != .member then PyPure.gap s!"a write to the attribute {t.info.name}.{n} is not modelled yet"
    PyWrites.excSet v (.field n (some x))

/-- An attribute write (`val = some x`) or deletion (`none`) on the instance `v`, as
`PyObject_GenericSetAttr` does it: a data descriptor on the type, else `v`'s `__dict__`. -/
def genericSetAttr [PyWrites m V] (v t : V) (name : String) (val : Option V) : m Unit := do
  -- A native function that a piece makes (`NativeKind.function`) is a Python function in CPython,
  -- whose writes go to its getsets and its `__dict__`, which the native doesn't follow.
  if let some (.native { kind := .function, qualname, .. }) ← PyReads.objView v then
    PyPure.gap s!"an attribute write to the function {qualname} is not modelled yet"
  if let some cd ← classData? t then
    if cd.instanceWritesGap then
      PyPure.gap s!"an attribute write to an instance of {cd.name} is not modelled yet"
  -- Its message is built only when it is raised.
  let noAttr : m Unit := do raiseAttrPlain s!"'{← classTpName t}' object has no attribute '{name}'"
  let (plain, descr) ← match ← lookupTypeEntry t name with
    | .plain .. => pure (true, none)
    | .entry d => pure (false, some d)
    | .none => pure (false, none)
  -- With no `__dict__`, a name that the type has is read-only.
  let noDict : m Unit := do
    builtinDictGap v name
    if plain || descr.isSome then
      raiseAttrPlain s!"'{← classNameOf t}' object attribute '{name}' is read-only"
    else noAttr
  if let some d := descr then
    if ← isDataDescr d then
      match ← PyPure.immView d with
      | some (.descr .function "__name__" _) =>
        let some x := val | return ← raiseBuiltin "TypeError" "__name__ must be set to a string object"
        let some (.str sv) ← PyPure.immView x |
          return ← raiseBuiltin "TypeError" "__name__ must be set to a string object"
        return ← PyWrites.funcSetName v sv.s
      | some (.descr .function "__annotations__" _) =>
        -- `func_set_annotations`: `None` and a deletion clear it, and a read then makes a new
        -- empty dict.
        let x ← match val with
          | none => PyPure.allocDict
          | some x => if (← PyPure.immView x) matches some .none then PyPure.allocDict else pure x
        if !(← isDict x) then
          return ← raiseBuiltin "TypeError" "__annotations__ must be set to a dict object"
        return ← PyWrites.funcSetAnnotations v x
      | some (.descr t' n k) =>
        if t'.info.mro.contains .BaseException then return ← excSetAttr v t' n k val
        return ← PyPure.gap s!"a write to the attribute {t'.info.name}.{n} is not modelled yet"
      | _ => match ← PyReads.objView d with
        | some (.property _ fset fdel _) =>
          let f := if val.isSome then fset else fdel
          if (← PyPure.immView f) matches some .none then
            return ← PyPure.gap "a write to a property without a setter or deleter is not modelled yet"
          let args := match val with
            | some x => PyPure.imm (m := m) (.tuple #[v, x])
            | none => PyPure.imm (m := m) (.tuple #[v])
          discard <| callN dispatchDepth f args (← PyPure.allocDict)
          return
        | some (.member owner n i) =>
          descrCheck owner n v
          match val with
          | some x => return ← PyWrites.slotSet v i x
          | none =>
            if (← PyReads.slotGet v i).isNone then return ← raiseAttrPlain n
            return ← PyWrites.slotDel v i
        | some .inst =>
          let dt ← PyReads.classOf d
          let (hook, args) := match val with
            | some x => ("__set__", #[v, x])
            | none => ("__delete__", #[v])
          match ← lookupType dt hook with
          | some f =>
            discard <| callFound hook f d dt args (← PyPure.allocDict)
            return
          | none => return ← raiseAttrPlain s!"__{if val.isSome then "set" else "delete"}__"
        | _ => pure ()
  -- The `__weakref__` and `__dict__` descriptors that `type.__new__` puts in a user class's
  -- namespace take a write or a deletion before the instance dict does.
  if descr.isNone && (name == "__weakref__" || (name == "__dict__" && (← PyReads.objDict v).isNone)) then
    implicitDescrGap name ((← mroOf t).getD #[])
  if name == "__dict__" && (← PyReads.objDict v).isSome then
    PyPure.gap "assigning or deleting an instance's __dict__ is not modelled yet"
  -- A function or an exception makes its `__dict__` on its first attribute write.
  let dict? ← match ← PyReads.objDict v with
    | some d => pure (some d)
    | none => match ← PyReads.objView v with
      | some (.func ..) | some (.exc _) =>
        if val.isSome then some <$> PyWrites.objEnsureDict v else pure none
      | _ => pure none
  let some dict := dict? | noDict
  let k := strKey (m := m) name
  match val with
  | some x => PyWrites.dictSet dict k x none fun _ =>
      PyPure.gap "an instance dict whose keys run user code is not modelled yet"
  | none =>
    let r ← PyWrites.dictDelete dict k none fun _ =>
      PyPure.gap "an instance dict whose keys run user code is not modelled yet"
    if r.isNone then noAttr

/-- An attribute write or deletion on the class `cls`, as `type.__setattr__` does it: an immutable
type refuses, and a built-in type that isn't immutable gaps; a name that the model doesn't follow
there gaps; else the namespace. -/
def typeSetAttr [PyWrites m V] (cls : V) (name : String) (val : Option V) : m Unit := do
  match ← PyPure.immView cls with
  | some (.builtin b) =>
    if !b.info.immutable then
      PyPure.gap s!"an attribute write to the mutable built-in type {b.info.name} is not modelled yet"
    raiseBuiltin "TypeError" s!"cannot set '{name}' attribute of immutable type '{b.info.tpName}'"
  | _ => pure ()
  let some cd ← classData? cls | PyPure.gap "an attribute write to a class that is not a class"
  if cd.immutable then
    raiseBuiltin "TypeError" s!"cannot set '{name}' attribute of immutable type '{← classTpName cls}'"
  if cd.writesGap then PyPure.gap s!"an attribute write to the class {cd.name} is not modelled yet"
  if name == "__del__" then PyPure.gap "a class with a finalizer is not modelled yet"
  -- `type.__setattr__` is the generic write on the class: a data descriptor of the metaclass first.
  if let some d ← lookupType (← PyReads.classOf cls) name then
    -- `type`'s own `__annotations__` writes the class's namespace, as the code below does.
    if (← isDataDescr d) && !((← PyPure.immView d) matches some (.descr .type "__annotations__" _)) then
      PyPure.gap "a class attribute write through the metaclass's data descriptor is not modelled yet"
  -- A write of `__new__` changes the class's `tp_new` by `update_one_slot`'s rules, which depend
  -- on the `tp_new` the class had before, so the class's namespace no longer tells it.
  if (name.startsWith "__" && name.endsWith "__") &&
      ["__class__", "__bases__", "__name__", "__qualname__", "__module__", "__mro__", "__dict__",
        "__doc__", "__new__"].contains name then
    PyPure.gap s!"a write to the attribute {name} of a class is not modelled yet"
  let k := strKey (m := m) name
  match val with
  | some x => PyWrites.dictSet cd.ns k x none fun _ => PyPure.gap "a namespace key that runs user code"
  | none =>
    let r ← PyWrites.dictDelete cd.ns k none fun _ => PyPure.gap "a namespace key that runs user code"
    if r.isNone then
      -- `type_set_annotations` names only the attribute.
      if name == "__annotations__" then raiseAttrPlain name
      raiseAttrPlain s!"type object '{← classTpName cls}' has no attribute '{name}'"

/-- **`setattr(v, name, x)`** (`val = some x`) or **`delattr(v, name)`** (`none`), CPython's
`PyObject_SetAttr`: a user `__setattr__` or `__delattr__`, else by the kind of `v`. -/
def setAttr [PyWrites m V] (v : V) (name : String) (val : Option V) : m Unit := do
  let t ← PyReads.classOf v
  let hookName := if val.isSome then "__setattr__" else "__delattr__"
  -- `object`'s and `type`'s own hooks are the generic writes below.
  let builtinHook (n : String) : m Bool := do
    let some hook ← lookupType t n | return true
    return match ← PyPure.immView hook with
      | some (.descr b n' _) => (b == .object || b == .type) && n' == n
      | _ => false
  if let some hook ← lookupType t hookName then
    if !(← builtinHook hookName) then
      let nameV := strKey (m := m) name
      let args := match val with
        | some x => #[nameV, x]
        | none => #[nameV]
      discard <| callFound hookName hook v t args (← PyPure.allocDict)
      return
  let write : m Unit := do
    if ← isType v then return ← typeSetAttr v name val
    match ← PyReads.objView v with
    | some (.module mod _ writesGap _) =>
      if writesGap then PyPure.gap s!"an attribute write to the module {mod} is not modelled yet"
      PyPure.gap "an attribute write to a module is not modelled yet"
    | _ => genericSetAttr v t name val
  -- `__setattr__` and `__delattr__` share one slot: when the other one is the class's own, CPython
  -- runs the built-in hook through its wrapper, which counts a C level.
  if ← builtinHook (if val.isSome then "__delattr__" else "__setattr__") then write
  else PyReads.withDepth 1 write


/-- The import of the one module `module`, without the packages above it: the module from the module
table, or, at its first import, the module that a piece's body makes (`importHook`), which adds it
to the table; a module that no piece makes stops with a gap. So does the translated program's own
module, whose attributes are its global cells: CPython's module also has the attributes that the
import system sets (`__spec__`, …) and a module `__getattr__`, which the model doesn't follow. So
does a body that raises after it added its module to the table: CPython removes the failed module
from `sys.modules`, and a rule can't remove a table entry. A body that gives a program a
module object (a modelled `__import__` or `sys.modules`, for example) goes through `importModule`,
or tests the module's kind (`ModuleKind`). -/
def importOne [PyCalls m V] (module : String) : m V := do
  if let some v ← PyReads.moduleGet module then
    if let some (.module _ _ _ .translated) ← PyReads.objView v then
      PyPure.gap s!"import of the translated module {module} is not modelled yet"
    return v
  let hook := PyPure.imm (m := m) (.bound (PyPure.imm (m := m) .none) .module (importHook module) .method)
  let args := PyPure.imm (m := m) (.tuple #[])
  let v ← tryCatch (PyCalls.callBuiltin hook args (← PyPure.allocDict)) fun x => do
    -- The body raised after it added its module to the table.
    if (← PyReads.moduleGet module).isSome then
      PyPure.gap s!"the failed import of {module} is not modelled yet"
    throw x
  -- CPython's import gives the module that the table holds after the body, which may be another
  -- one than the body returns; the next import finds the module in the table.
  if let some w ← PyReads.moduleGet module then return w
  PyReads.moduleAdd module v
  return v

/-- **`import module`**: each package above the module first, outermost first (`a`, then `a.b`, for
`a.b.c`), as CPython's import does, then the module itself, each by `importOne`. -/
def importModule [PyCalls m V] (module : String) : m V := do
  importCheck
  let parts := module.splitOn "."
  for i in List.range (parts.length - 1) do
    discard <| importOne (".".intercalate (parts.take (i + 1)))
  importOne module

/-- `from module import name`: an entry of the `builtins` module, or CPython's `ImportError`;
any other module stops with a gap. -/
def importFrom [PyCalls m V] (module name : String) : m V := do
  importCheck
  if module != "builtins" then
    -- `IMPORT_FROM` reads the attribute of the imported module; a missing one, whose
    -- `ImportError` names the module's file, stops with a gap.
    let mod ← importModule module
    return ← tryCatch (getAttrRaw mod name) fun x => do
      if ← isAttributeError x then
        PyPure.gap s!"from {module} import {name} of a name that the module lacks is not modelled yet"
      throw x
  match ← PyReads.builtinGet name with
  | some v => pure v
  | none =>
    -- `IMPORT_FROM` reads an attribute of the module object, and the module type's own
    -- attributes, such as `__dict__`, are all dunder names.
    if name.startsWith "__" && name.endsWith "__" then
      PyPure.gap s!"from builtins import {name} is not modelled yet"
    let msg := s!"cannot import name '{name}' from 'builtins' (unknown location)"
    raiseBuiltin "ImportError" msg
      #[("msg", PyPure.imm (m := m) (.str (.ofString msg))),
        ("name", PyPure.imm (m := m) (.str (.ofString "builtins"))),
        ("path", PyPure.imm (m := m) .none),
        ("name_from", PyPure.imm (m := m) (.str (.ofString name)))]

end

end

end StrataPython.Dyn.Sem.Proto
