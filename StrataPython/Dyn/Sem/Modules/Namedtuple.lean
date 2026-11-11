/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.TypingSpecs
public import StrataPython.Dyn.Sem.Proto.Printf

set_option autoImplicit false

/-!
# The model of `collections.namedtuple`

A port of CPython 3.12's `collections.namedtuple` (`Lib/collections/__init__.py`), which
`typing.NamedTuple` calls, and of the C type `collections._tuplegetter`
(`Modules/_collectionsmodule.c`), the field accessors. A named tuple class is a plain class of
`type` with the base `tuple`; its methods are Python functions of the model, which keep the
class's field names in their captured values.
-/

namespace StrataPython.Dyn.Sem.Modules

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- `collections._tuplegetter`. -/
def tupleGetterCls [PyWrites m V] [PyNew m V] : m V := modelClass tupleGetterSpec

/-- `_tuplegetter(index, doc)`: its slots `__doc__` and `index`. -/
def newTupleGetter [PyWrites m V] [PyNew m V] (index : Nat) (doc : String) : m V := do
  PyReads.allocInstance (← tupleGetterCls) .plain #[]
    #[some (strValue (m := m) doc), some (PyPure.imm (m := m) (.int index))]

/-- The index of the `_tuplegetter` `self`; another value raises CPython's descriptor
`TypeError`. -/
def tupleGetterIndex [PyReads m V] (name : String) (self : V) : m Nat := do
  let some c ← modelClass? tupleGetterSpec | PyPure.modelInvariant "a _tuplegetter before its class"
  if !(← isSubclass (← PyReads.classOf self) c) then
    raiseBuiltin "TypeError"
      s!"descriptor '{name}' requires a 'collections._tuplegetter' object but received a '{← typeName self}'"
  let some iv ← PyReads.slotGet self 1 | PyPure.modelInvariant "a _tuplegetter without its index"
  let some (.int i) ← PyPure.immView iv | PyPure.modelInvariant "a _tuplegetter index that is no int"
  pure i.toNat

/-- The items of a tuple, or of the built-in part of an instance of a subclass of `tuple`. -/
def tupleOrPart? [PyReads m V] (v : V) : m (Option (Array V)) := do
  if let some (.tuple xs) ← PyPure.immView v then return some xs
  PyReads.tupleView v

/-- **`tuplegetter_descr_get(self, obj, type)`**: `self` without an object (or for `None`); else
the item `index` of the tuple `obj`, with CPython's `TypeError` for another object and
`IndexError` past its end. -/
def tupleGetterGet [PyReads m V] (self obj : V) : m V := do
  let i ← tupleGetterIndex "__get__" self
  if (← PyPure.immView obj) matches some .none then return self
  let some xs ← tupleOrPart? obj |
    raiseBuiltin "TypeError"
      s!"descriptor for index '{i}' for tuple subclasses doesn't apply to '{← typeName obj}' object"
  let some x := xs[i]? | raiseBuiltin "IndexError" "tuple index out of range"
  pure x

/-- The bodies of `_tuplegetter`'s slot wrappers, over the receiver. -/
def tupleGetterBody [PyWrites m V] (name : String) (self args kwargs : V) : m V := do
  discard <| tupleGetterIndex name self
  let xs ← tupleItems args
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" s!"wrapper {name}() takes no keyword arguments"
  match name with
  | "__get__" =>
    -- `wrap_descr_get`: one or two arguments, `None` meaning none.
    let (obj, type) ← match xs with
      | #[o] => pure (o, PyPure.imm (m := m) .none)
      | #[o, t] => pure (o, t)
      | _ =>
        if xs.isEmpty then raiseBuiltin "TypeError" " expected at least 1 argument, got 0"
        raiseBuiltin "TypeError" s!" expected at most 2 arguments, got {xs.size}"
    if (← PyPure.immView obj) matches some .none then
      if (← PyPure.immView type) matches some .none then
        raiseBuiltin "TypeError" "__get__(None, None) is invalid"
    tupleGetterGet self obj
  | "__set__" =>
    if xs.size != 2 then raiseBuiltin "TypeError" s!" expected 2 arguments, got {xs.size}"
    raiseBuiltin "AttributeError" "can't set attribute"
  | "__delete__" =>
    if xs.size != 1 then raiseBuiltin "TypeError" s!"expected 1 argument, got {xs.size}"
    raiseBuiltin "AttributeError" "can't delete attribute"
  | _ =>
    if !xs.isEmpty then raiseBuiltin "TypeError" s!"expected 0 arguments, got {xs.size}"
    let i ← tupleGetterIndex name self
    let some doc ← PyReads.slotGet self 0 | PyPure.modelInvariant "a _tuplegetter without its doc"
    return strValue (m := m) s!"_tuplegetter({i}, {← reprTextOf doc})"

/-- **`tuple.__new__(cls, items)`** for a `tuple` `items`: the tuple itself for `tuple`, a new
instance of `cls` for a subclass of `tuple`, with CPython's `TypeError` otherwise. -/
def tupleNewOf [PyWrites m V] [PyNew m V] (cls : V) (items : Array V) : m V := do
  if !(← isType cls) then
    raiseBuiltin "TypeError" s!"tuple.__new__(X): X is not a type object ({← typeName cls})"
  let tupleV := PyPure.imm (m := m) (.builtin .tuple)
  if (← PyPure.identical cls tupleV) == .yes then return PyPure.imm (m := m) (.tuple items)
  if !(← isSubclass cls tupleV) then
    let n ← classTpName cls
    raiseBuiltin "TypeError" s!"tuple.__new__({n}): {n} is not a subtype of tuple"
  cTypeNewGap cls
  let some mro ← mroOf cls | PyPure.modelInvariant "a class without its MRO"
  PyReads.allocInstance cls (.tuple items) #[] (Array.replicate (← slotCountOf mro.toList) none)

/-- The items of `self`, a tuple, as iterating it gives them: a class that overrides `__iter__`
stops with a gap. -/
def tupleItemsOf [PyReads m V] (self : V) : m (Array V) := do
  match ← lookupType (← PyReads.classOf self) "__iter__" with
  | some f =>
    if !((← PyPure.immView f) matches some (.descr .tuple "__iter__" _)) then
      PyPure.gap "iterating a named tuple whose class defines __iter__ is not modelled yet"
  | none => PyPure.gap "iterating a named tuple whose class has no __iter__ is not modelled yet"
  let some xs ← tupleOrPart? self |
    PyPure.gap "iterating a value that is not a tuple in a named tuple's method is not modelled yet"
  pure xs

/-- The items of the iterable `it` of `_make` inside another built-in's step: a tuple's or a list's;
any other iterable stops with a gap, since its walk could run Python code. -/
def makeItems [PyReads m V] (it : V) : m (Array V) := do
  if let some (.tuple xs) ← PyPure.immView it then return xs
  if (← builtinClass? it) == some .list then
    let some (xs, _) ← PyReads.listView it | PyPure.modelInvariant "a list without its items"
    return xs
  PyPure.gap "_make of an iterable other than a tuple or a list inside another built-in's step is not modelled yet"

/-- **`setattr(cls, name, v)`** on a class `cls` of `type` that a port made, for the names whose
setter is one of `type`'s getsets: `__module__` and `__doc__` write the class's namespace, and
`__qualname__` sets the class's qualified name, as `type_set_module`, `type_set_doc` and
`type_set_qualname` do; any other name is the generic write. -/
def setOnClass [PyWrites m V] (cls : V) (name : String) (v : V) : m Unit := do
  let some cd ← classData? cls | PyPure.modelInvariant "a port's class that is no class"
  match name with
  | "__module__" | "__doc__" =>
    PyWrites.dictSet cd.ns (strValue (m := m) name) v none fun _ => pure false
  | "__qualname__" =>
    let some q ← str? v |
      raiseBuiltin "TypeError" s!"can only assign string to {cd.name}.__qualname__, not '{← typeName v}'"
    PyWrites.classSetName cls cd.name q
  | _ => setAttr cls name (some v)

/-- What the methods of a named tuple class keep: its field names, its name, and the format of its
`repr`. -/
structure NamedtupleInfo (V : Type) where
  fields : Array V
  typename : String
  reprFmt : String

/-- The info that the native `fn` captured: the field names tuple, the type name and the `repr`
format. -/
def namedtupleInfo [PyReads m V] (fn : V) : m (NamedtupleInfo V) := do
  let some (.native nf) ← PyReads.objView fn | PyPure.modelInvariant "a namedtuple method without its native"
  let #[fs, tn, rf] := nf.captured | PyPure.modelInvariant "a namedtuple method without its info"
  let some (.tuple fields) ← PyPure.immView fs | PyPure.modelInvariant "namedtuple fields that are no tuple"
  let some typename ← str? tn | PyPure.modelInvariant "a namedtuple name that is no str"
  let some reprFmt ← str? rf | PyPure.modelInvariant "a namedtuple repr format that is no str"
  pure { fields, typename, reprFmt }

/-- `_make`'s check of the result of `tuple.__new__`: CPython's `TypeError` unless its `len` is the
number of fields; the message's `len` is the global one. -/
def makeCheck [PyCalls m V] (fields : Nat) (result : V) : m V := do
  if (← pyLen result) != fields then
    useBuiltin "len"
    raiseBuiltin "TypeError" s!"Expected {fields} arguments, got {← pyLen result}"
  pure result

/-- **`_make(cls, iterable)`** inside another built-in's step, where it can't suspend:
`tuple.__new__(cls, iterable)` for a tuple or a list, then `makeCheck`. -/
def namedtupleMake [PyWrites m V] [PyNew m V] (info : NamedtupleInfo V) (cls items : V) : m V := do
  makeCheck info.fields.size (← tupleNewOf cls (← makeItems items))

/-- The bodies of the methods of a named tuple class, by native key. -/
def namedtupleBody [PyWrites m V] [PyNew m V] (key : String) (fn args kwargs : V) : m V := do
  let bad {α : Type} : m α := PyPure.modelInvariant "a bound call"
  let info ← namedtupleInfo fn
  let q (name : String) := s!"{info.typename}.{name}"
  -- The arguments bound to the parameters of the method that `key` names.
  let bound (params : Array String) : m (Array V) :=
    bindPy (q (key.drop "collections.namedtuple.".length).toString) params args kwargs
  match key with
  | "collections.namedtuple.__new__" =>
    let some (.native nf) ← PyReads.objView fn | PyPure.modelInvariant "a native"
    let defaults ← match nf.defaults with
      | some d => tupleItems d
      | none => pure #[]
    let names := #[strValue (m := m) "_cls"] ++ info.fields
    let xs ← bindPyDefaults (q "__new__") names defaults args kwargs
    let some cls := xs[0]? | bad
    tupleNewOf cls (xs.extract 1 xs.size)
  | "collections.namedtuple._make" =>
    let #[cls, it] ← bound #["cls", "iterable"] | bad
    namedtupleMake info cls it
  | "collections.namedtuple._replace" =>
    keywordsCheck kwargs
    let xs ← bindArgs (q "_replace") args kwargs (PyPure.imm (m := m) (.tuple #[])) 1 1 false true #["self"]
    let #[self, kwds] ← tupleItems xs | bad
    -- `self._make`: the class's own `_make`, bound to the class; another one stops with a gap.
    let mk ← getAttr self "_make"
    let some (.method f cls) ← PyPure.immView mk |
      PyPure.gap "_replace with a _make that is not the named tuple's is not modelled yet"
    let some (.native nf) ← PyReads.objView f |
      PyPure.gap "_replace with a _make that is not the named tuple's is not modelled yet"
    if nf.key != "collections.namedtuple._make" then
      PyPure.gap "_replace with a _make that is not the named tuple's is not modelled yet"
    let made ← namedtupleInfo f
    -- `map(kwds.pop, field_names, self)`, which `tuple.__new__` consumes.
    let items ← tupleItemsOf self
    let mut vals : Array V := #[]
    for (name, item) in info.fields.zip items do
      let v ← PyWrites.dictDelete kwds name none fun _ => pure false
      vals := vals.push (v.getD item)
    let result ← pyFrame (namedtupleMake made cls (PyPure.imm (m := m) (.tuple vals)))
    if (← PyReads.dictLen kwds) > 0 then
      useBuiltin "list"
      let ks := (← PyReads.dictEntries kwds).map (·.1)
      raiseBuiltin "ValueError" s!"Got unexpected field names: {← reprTextOf (← PyPure.allocList ks)}"
    pure result
  | "collections.namedtuple.__repr__" =>
    let #[self] ← bound #["self"] | bad
    let name ← getAttr (← getAttr self "__class__") "__name__"
    let some nameText ← str? name |
      PyPure.gap "the repr of a named tuple whose class name is not a str is not modelled yet"
    let body ← printfStr info.reprFmt self
    let some bodyText ← str? body | PyPure.modelInvariant "a printf result that is no str"
    return strValue (m := m) (nameText ++ bodyText)
  | "collections.namedtuple._asdict" =>
    let #[self] ← bound #["self"] | bad
    let fs ← getAttr self "_fields"
    let names ← match ← PyPure.immView fs with
      | some (.tuple ns) => pure ns
      | _ => PyPure.gap "_asdict with _fields that are not a tuple is not modelled yet"
    let items ← tupleItemsOf self
    let d ← PyPure.allocDict
    for (n, v) in names.zip items do
      if !((← PyPure.immView n) matches some (.str _)) then
        PyPure.gap "_asdict with a field name that is not a str is not modelled yet"
      PyNew.dictSetNew d n v none fun _ => pure false
    pure d
  | "collections.namedtuple.__getnewargs__" =>
    let #[self] ← bound #["self"] | bad
    return PyPure.imm (m := m) (.tuple (← tupleItemsOf self))
  | _ => PyPure.modelInvariant s!"a namedtuple native without a body: {key}"

/-- Whether `x` is an ASCII identifier that is not a keyword (`str.isidentifier` and
`keyword.iskeyword`): `some false` for a string that isn't one, `none` for a non-ASCII string, whose
check the model doesn't have. -/
def identifierKind (x : String) : Option (Bool × Bool) :=
  if !x.toList.all (·.toNat < 128) then none else
  let keywords := ["False", "None", "True", "and", "as", "assert", "async", "await", "break",
    "class", "continue", "def", "del", "elif", "else", "except", "finally", "for", "from", "global",
    "if", "import", "in", "is", "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try",
    "while", "with", "yield"]
  let ident := match x.toList with
    | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_')
    | [] => false
  some (ident, keywords.contains x)

/-- A method of a named tuple class: a Python function of the model with the class's info. -/
def namedtupleFunction [PyPure m V] (info : NamedtupleInfo V) (name «module» : String)
    (defaults : Option V := none) : m V :=
  let captured : Array V := #[PyPure.imm (m := m) (.tuple info.fields),
    strValue (m := m) info.typename, strValue (m := m) info.reprFmt]
  let nd : NativeData V :=
    { key := s!"collections.namedtuple.{name}", kind := .function, captured := captured,
      name := name, qualname := s!"{info.typename}.{name}", «module» := «module»,
      defaults := defaults }
  allocNative nd

/-- **`collections.namedtuple(typename, field_names, defaults=defaults, module=module)`** for a
list of field names: the checks of the names and their messages, then the class
`type(typename, (tuple,), namespace)` with its methods and field accessors, and `__module__`. -/
def namedtuple [PyWrites m V] [PyNew m V] (typename : String) (fieldNames : Array V)
    (defaults : Array V) (module : V) : m V := pyFrame do
  for b in ["isinstance", "list", "map", "str", "type", "set", "len", "tuple", "dict", "reversed",
      "zip", "enumerate", "eval", "classmethod", "repr"] do
    useBuiltin b
  -- `field_names = list(map(str, field_names))`: the model takes exact `str`s.
  let mut fields : Array String := #[]
  for f in fieldNames do
    let some (.str s) ← PyPure.immView f |
      PyPure.gap "a namedtuple field name that is not a str is not modelled yet"
    fields := fields.push s.s
  for name in #[typename] ++ fields do
    match identifierKind name with
    | none => PyPure.gap "a namedtuple name that is not ASCII is not modelled yet"
    | some (false, _) =>
      raiseBuiltin "ValueError"
        s!"Type names and field names must be valid identifiers: {← reprTextOf (strValue (m := m) name)}"
    | some (true, true) =>
      raiseBuiltin "ValueError"
        s!"Type names and field names cannot be a keyword: {← reprTextOf (strValue (m := m) name)}"
    | some (true, false) => pure ()
  let mut seen : Array String := #[]
  for name in fields do
    if name.startsWith "_" then
      raiseBuiltin "ValueError"
        s!"Field names cannot start with an underscore: {← reprTextOf (strValue (m := m) name)}"
    if seen.contains name then
      raiseBuiltin "ValueError"
        s!"Encountered duplicate field name: {← reprTextOf (strValue (m := m) name)}"
    seen := seen.push name
  if defaults.size > fields.size then
    raiseBuiltin "TypeError" "Got more default values than field names"
  let fieldVs := fields.map (strValue (m := m) ·)
  let argList := ", ".intercalate fields.toList ++ (if fields.size == 1 then "," else "")
  let reprFmt := "(" ++ ", ".intercalate (fields.map (· ++ "=%r")).toList ++ ")"
  let info : NamedtupleInfo V := { fields := fieldVs, typename, reprFmt }
  let defaultsV := PyPure.imm (m := m) (.tuple defaults)
  let new ← namedtupleFunction info "__new__" s!"namedtuple_{typename}" (some defaultsV)
  let make ← namedtupleFunction info "_make" "collections"
  let fieldDefaults ← PyPure.allocDict
  for (f, d) in (fieldVs.extract (fields.size - defaults.size) fields.size).zip defaults do
    PyNew.dictSetNew fieldDefaults f d none fun _ => pure false
  let ns ← PyPure.allocDict
  let put (k : String) (v : V) : m Unit :=
    PyNew.dictSetNew ns (strValue (m := m) k) v none fun _ => pure false
  put "__doc__" (strValue (m := m) s!"{typename}({argList})")
  put "__slots__" (PyPure.imm (m := m) (.tuple #[]))
  put "_fields" (PyPure.imm (m := m) (.tuple fieldVs))
  put "_field_defaults" fieldDefaults
  put "__new__" (← PyPure.allocObj (PyPure.imm (m := m) (.builtin .staticmethod)) (.staticmethod (some new)))
  put "_make" (← PyPure.allocObj (PyPure.imm (m := m) (.builtin .classmethod)) (.classmethod (some make)))
  for name in ["_replace", "__repr__", "_asdict", "__getnewargs__"] do
    put name (← namedtupleFunction info name "collections")
  put "__match_args__" (PyPure.imm (m := m) (.tuple fieldVs))
  for (f, i) in fields.zipIdx do
    put f (← newTupleGetter i s!"Alias for field number {i}")
  -- `type()` takes `__module__` from the caller's globals, `collections`.
  put "__module__" (strValue (m := m) "collections")
  let tupleV := PyPure.imm (m := m) (.builtin .tuple)
  let result ← typeNew (PyPure.imm (m := m) (.builtin .type))
    (PyPure.imm (m := m) (.tuple #[PyPure.imm (m := m) (.builtin .type), strValue (m := m) typename,
      PyPure.imm (m := m) (.tuple #[tupleV]), ns])) (← PyPure.allocDict)
  setOnClass result "__module__" module
  pure result

/-! ## The step machine of `_make` -/

/-- The frames of this file's step machine: `_make` while its call of `tuple.__new__(cls,
iterable)` is suspended, with the number of fields that its result must have; the frames of that
call follow this frame. -/
inductive LoopState (V : Type) where
  | make (fields : Nat)

section
variable {S : Type} [HasLoopPart S (LoopState V)] [HasLoopPart S (Proto.OpsLoopState V)]
variable [PyWrites m V] [PyNew m V] [PyMachines m V S]

/-- `_make`'s step from the step of its `tuple.__new__` call. -/
def makeAfter (fields : Nat) : CallStep S V → m (CallStep S V)
  | .done r => .done <$> makeCheck fields r
  | .suspend fs => pure (.suspend (HasLoopPart.inj (LoopState.make (V := V) fields) :: fs))

/-- A call of `_make`, a Python function: one Python frame, and CPython's C levels of a call from
C (`pyFunctionCall`). -/
def makeFrame {α : Type} (body : m α) : m α := pyFrame (pyFunctionCall body)

/-- **The first step of `_make(cls, iterable)`**, the native `f` called with `args` and `kwargs`:
`tuple.__new__(cls, iterable)` through `callResumable`, so that an iterable whose `__next__` is
Python code suspends it; `none` when `f` is not `_make`. -/
def machineStart (f args kwargs : V) : m (Option (CallStep S V)) := do
  let some (.native nf) ← PyReads.objView f | return none
  if nf.key != "collections.namedtuple._make" then return none
  some <$> makeFrame do
    let info ← namedtupleInfo f
    let #[cls, it] ← bindPy s!"{info.typename}._make" #["cls", "iterable"] args kwargs |
      PyPure.modelInvariant "a bound call"
    let tupleNew ← getAttr (PyPure.imm (m := m) (.builtin .tuple)) "__new__"
    makeAfter info.fields.size
      (← callResumable dispatchDepth tupleNew (PyPure.imm (m := m) (.tuple #[cls, it]))
        (← PyPure.allocDict) [])

/-- **The resume entry of this file's frames**: `_make` resumes its `tuple.__new__` call from the
frames after its own, then checks the result. -/
def machineResume (fr : LoopState V) (rest : List S) : m (CallStep S V) := do
  match fr, rest with
  | .make fields, s :: rest' => makeFrame do makeAfter fields (← PyMachines.resume s rest')
  | .make _, [] => PyPure.modelInvariant "a frame of _make without its call's frames"

end

end

/-- The native bodies of the model of `collections.namedtuple`. -/
def namedtupleNative (key : String) : Option BuiltinImpl :=
  if key.startsWith "collections.namedtuple." then
    some fun {_} {_} [_] [_] fn args kwargs => pyFunctionCall (namedtupleBody key fn args kwargs)
  else if key.startsWith "collections._tuplegetter." then
    let name := (key.drop "collections._tuplegetter.".length).toString
    some fun {_} {_} [_] [_] fn args kwargs => do
      let (recv, rest) ← nativeRecv fn args
      tupleGetterBody name recv rest kwargs
  else none

end

end StrataPython.Dyn.Sem.Modules
