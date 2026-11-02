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

/-- The value of the attribute `name` of the module object `v`, named `mod`: a global of the module,
or an entry of the `builtins` dict. -/
def moduleAttr [PyReads m V] (v : V) (mod : String) (gapped : Array String) (name : String) :
    m V := do
  if gapped.contains name then PyPure.gap s!"the attribute {mod}.{name} is not modelled yet"
  let r ← if mod == "builtins" then PyReads.builtinGet name else PyReads.globalGet mod name
  match r with
  | some x => pure x
  | none => raiseAttr v name s!"module '{mod}' has no attribute '{name}'"

/-- A gap for `__dict__` and `__weakref__` when a user class is among the classes `mro`:
`type.__new__` puts a descriptor for each in a user class's namespace, which the model doesn't
hold, so a lookup that finds nothing else may still find them in CPython. -/
def implicitDescrGap [PyReads m V] (name : String) (mro : Array V) : m Unit := do
  if name == "__dict__" || name == "__weakref__" then
    if ← mro.anyM fun c => return (← PyPure.immView c).isNone then
      PyPure.gap s!"the {name} that a user class's namespace holds is not modelled yet"

/-- `_PyObject_GenericGetAttrWithDict(v, name)`: a data descriptor with a `__get__` on `v`'s
type, then `v`'s `__dict__`, then any other descriptor or class attribute. -/
def genericGetAttr [PyCalls m V] (v t : V) (name : String) : m V := do
  -- A plain value of a built-in type's table is no data descriptor, so the instance dict comes
  -- first; the model may not hold the value itself.
  if ← lookupIsPlainValue t name then
    if let some dict ← PyReads.objDict v then
      if let some x ← dictFindStr dict name then return x
  let descr ← lookupType t name
  if let some d := descr then
    if (← isDataDescr d) && (← hasGet d) then return ← descrGetN dispatchDepth d (some v) t
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
    raiseAttr v name s!"'{← classNameOf t}' object has no attribute '{name}'"

/-- `type_getattro(cls, name)`: a data descriptor with a `__get__` on the metaclass, then the
class's own MRO, then the metaclass's other attributes. -/
def typeGetAttr [PyCalls m V] (cls : V) (name : String) : m V := do
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
    raiseAttr cls name s!"type object '{← classNameOf cls}' has no attribute '{name}'"

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
  | some (.module mod gapped _) =>
    -- `module_getattro` is the generic lookup first, which finds the module type's attributes.
    if (← lookupType (← PyReads.classOf v) name).isSome then
      PyPure.gap s!"the attribute {name} of a module, which its type gives, is not modelled yet"
    moduleAttr v mod gapped name
  | some (.native f) =>
    if f.gapped.contains name then
      PyPure.gap s!"the attribute {name} of the built-in {f.qualname} is not modelled yet"
    genericGetAttr v (← PyReads.classOf v) name
  | _ => genericGetAttr v (← PyReads.classOf v) name

/-- **`getattr(v, name)`**, CPython's `PyObject_GetAttr`: a user `__getattribute__` if `v`'s type
has one, else the lookup by kind; then `__getattr__` of the type, when there is one and the lookup
raised `AttributeError`. -/
def getAttr [PyCalls m V] (v : V) (name : String) : m V := do
  let t ← PyReads.classOf v
  let nameV := PyPure.imm (m := m) (.str (.ofString name))
  let attempt : m V := do
    match ← lookupType t "__getattribute__" with
    | some ga =>
      match ← PyPure.immView ga with
      | some (.descr b "__getattribute__" _) =>
        if (← defaultGetattrOwner t) == some b then getAttrCore v name
        else PyPure.gap s!"the __getattribute__ of the built-in {b.info.name} on another type is not \
          modelled yet"
      | _ => callFound ga v t #[nameV] (← PyPure.allocDict)
    | none => getAttrCore v name
  match ← lookupType t "__getattr__" with
  | none => attempt
  | some hook => tryCatch attempt fun x => do
    if ← isAttributeError x then
      callFound hook v t #[nameV] (← PyPure.allocDict)
    else throw x

/-- `AttributeError` with the message `msg` and no fields, as CPython's attribute writes raise it. -/
def raiseAttrPlain [PyReads m V] {α : Type} (msg : String) : m α := raiseBuiltin "AttributeError" msg

/-- An attribute write (`val = some x`) or deletion (`none`) on the instance `v`, as
`PyObject_GenericSetAttr` does it: a data descriptor on the type, else `v`'s `__dict__`. -/
def genericSetAttr [PyWrites m V] (v t : V) (name : String) (val : Option V) : m Unit := do
  if let some cd ← classData? t then
    if cd.instanceWritesGap then
      PyPure.gap s!"an attribute write to an instance of {cd.name} is not modelled yet"
  let noAttr : m Unit := raiseAttrPlain s!"'{← classNameOf t}' object has no attribute '{name}'"
  let plain ← lookupIsPlainValue t name
  let descr ← if plain then pure none else lookupType t name
  -- With no `__dict__`, a name that the type has is read-only.
  let noDict : m Unit := do
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
      | some (.descr t' n _) =>
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
            discard <| callFound f d dt args (← PyPure.allocDict)
            return
          | none => return ← raiseAttrPlain s!"__{if val.isSome then "set" else "delete"}__"
        | _ => pure ()
  -- The `__weakref__` and `__dict__` descriptors that `type.__new__` puts in a user class's
  -- namespace take a write or a deletion before the instance dict does.
  if descr.isNone && (name == "__weakref__" || (name == "__dict__" && (← PyReads.objDict v).isNone)) then
    implicitDescrGap name ((← mroOf t).getD #[])
  if name == "__dict__" && (← PyReads.objDict v).isSome then
    PyPure.gap "assigning or deleting an instance's __dict__ is not modelled yet"
  -- A function makes its `__dict__` on its first attribute write.
  let dict? ← match ← PyReads.objDict v with
    | some d => pure (some d)
    | none => match ← PyReads.objView v with
      | some (.func ..) => if val.isSome then some <$> PyWrites.objEnsureDict v else pure none
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

/-- An attribute write or deletion on the class `cls`, as `type.__setattr__` does it: a built-in
or immutable type refuses; a name that the model doesn't follow there gaps; else the namespace. -/
def typeSetAttr [PyWrites m V] (cls : V) (name : String) (val : Option V) : m Unit := do
  match ← PyPure.immView cls with
  | some (.builtin b) =>
    raiseBuiltin "TypeError" s!"cannot set '{name}' attribute of immutable type '{b.info.name}'"
  | _ => pure ()
  let some cd ← classData? cls | PyPure.gap "an attribute write to a class that is not a class"
  if cd.immutable then
    raiseBuiltin "TypeError" s!"cannot set '{name}' attribute of immutable type '{← classNameOf cls}'"
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
      raiseAttrPlain s!"type object '{← classNameOf cls}' has no attribute '{name}'"

/-- **`setattr(v, name, x)`** (`val = some x`) or **`delattr(v, name)`** (`none`), CPython's
`PyObject_SetAttr`: a user `__setattr__` or `__delattr__`, else by the kind of `v`. -/
def setAttr [PyWrites m V] (v : V) (name : String) (val : Option V) : m Unit := do
  let t ← PyReads.classOf v
  let hookName := if val.isSome then "__setattr__" else "__delattr__"
  if let some hook ← lookupType t hookName then
    -- `object`'s and `type`'s own hooks are the generic writes below.
    let builtinHook := match ← PyPure.immView hook with
      | some (.descr b n _) => (b == .object || b == .type) && n == hookName
      | _ => false
    if !builtinHook then
      let nameV := strKey (m := m) name
      let args := match val with
        | some x => #[nameV, x]
        | none => #[nameV]
      discard <| callFound hook v t args (← PyPure.allocDict)
      return
  if ← isType v then return ← typeSetAttr v name val
  match ← PyReads.objView v with
  | some (.module mod _ writesGap) =>
    if writesGap then PyPure.gap s!"an attribute write to the module {mod} is not modelled yet"
    PyPure.gap "an attribute write to a module is not modelled yet"
  | _ => genericSetAttr v t name val

end

end

end StrataPython.Dyn.Sem.Proto
