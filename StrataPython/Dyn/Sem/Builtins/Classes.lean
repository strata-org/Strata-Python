/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Attrs
public import StrataPython.Dyn.Sem.Builtins.Bind
public import StrataPython.Dyn.Sem.Mro

set_option autoImplicit false

/-!
# Classes: `__build_class__`, `type`, `object` and `super`

Generic over the record, the bodies of CPython 3.12's class machinery:

* `buildClass`, `builtin___build_class__`: `__mro_entries__` of the bases, the metaclass (the
  `metaclass` keyword, else the most derived metaclass of the bases), `__prepare__`, the class
  body called with its namespace, `__orig_bases__`, then the metaclass called;
* `typeNew`, `type.__new__`: the bases (`(object,)` for none), the best base and its layout,
  `__slots__`, the MRO by C3, the class object, `__set_name__`, and the parent's
  `__init_subclass__`;
* `object.__new__`, `object.__init__` with CPython's excess-argument errors,
  `object.__init_subclass__`, `object.__setattr__`, `object.__delattr__`,
  `object.__getattribute__`, `object.__eq__`, `object.__ne__` and `object.__hash__`;
* `super(T, obj)`, and `isinstance`.

A class body with `__del__`, a `__prepare__` that returns something other than a dict,
`type.__new__` called with a metaclass that the bases make more derived (CPython's winner), and a
class whose methods use `__class__` or `super()` made by a metaclass other than `type`, stop with
gaps.
-/

namespace StrataPython.Dyn.Sem.Builtins

open Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The entries of the kwargs dict `kw`, by name; a key that is not a `str` gaps. -/
def kwEntries [PyReads m V] (kw : V) : m (Array (String × V)) := do
  (← PyReads.dictEntries kw).mapM fun (k, v, _) => do
    let some s ← str? k | PyPure.gap "a keyword that is not a str"
    pure (s, v)

/-- A new dict of the `str`-keyed entries `kvs`. -/
def dictOfEntries [PyReads m V] [PyNew m V] (kvs : Array (String × V)) : m V := do
  let d ← PyPure.allocDict
  for (k, v) in kvs do
    PyNew.dictSetNew d (strKey (m := m) k) v none fun _ => pure false
  pure d

/-- The position of `x` in `xs`, by identity. -/
def indexOf [PyPure m V] (x : V) (xs : Array V) : m (Option Nat) := do
  for (y, i) in xs.zipIdx do
    if (← PyPure.identical x y) == .yes then return some i
  return none

/-- The MRO after the new class of a class with the bases `bases`, by C3 (`C3.mro`), with
CPython's `TypeError` when there is none.  The classes are numbered by identity for C3. -/
def c3Tail [PyReads m V] (bases : Array V) : m (Array V) := do
  let mut classes : Array V := #[]
  let mut baseMros : Array (List Nat) := #[]
  for b in bases do
    let some mro ← mroOf b | PyPure.gap "a base that is not a class"
    let mut ids := #[]
    for c in mro do
      match ← indexOf c classes with
      | some i => ids := ids.push i
      | none =>
        ids := ids.push classes.size
        classes := classes.push c
    baseMros := baseMros.push ids.toList
  let mut baseIds := #[]
  for b in bases do
    let some i ← indexOf b classes | PyPure.gap "a base outside its own MRO"
    baseIds := baseIds.push i
  -- The new class is the number after every other class.
  let self := classes.size
  let mroOfId (i : Nat) : List Nat := (baseIds.zip baseMros).findSome? (fun (b, ms) =>
    if b == i then some ms else none) |>.getD [i]
  match C3.mro self baseIds.toList mroOfId with
  | .ok ids => pure ((ids.drop 1).filterMap (classes[·]?)).toArray
  | .error err =>
    let mut names := #[]
    for c in classes do names := names.push (← classNameOf c)
    match err.message (fun i => names[i]?) with
    | some msg => raiseBuiltin "TypeError" msg
    | none => PyPure.gap "an MRO error whose message cuts a character"

/-- The name and `__itemsize__` of the first built-in type of the MRO of the class `c`. -/
def itemsizeOf [PyReads m V] (c : V) : m (String × Nat) := do
  let some mro ← mroOf c | PyPure.gap "the layout of a value that is not a class"
  for t in mro do
    if let some (.builtin b) ← PyPure.immView t then return (b.info.name, b.info.itemsize)
  pure ("object", 0)

/-- Whether `s` is an ASCII identifier; `none` when it has a non-ASCII character. -/
def asciiIdentifier? (s : String) : Option Bool :=
  if s.toList.any (fun (c : Char) => c.toNat ≥ 128) then none
  else some (match s.toList with
    | c :: rest => (c.isAlpha || c == '_') && rest.all fun (d : Char) => d.isAlphanum || d == '_'
    | [] => false)

/-- The `tp_name` of the class `c`: a built-in type's name, or a user class's. -/
def tpNameOf [PyReads m V] (c : V) : m String := do
  match ← PyPure.immView c with
  | some (.builtin b) => pure b.info.tpName
  | _ => match ← classData? c with
    | some cd => pure (cd.tpName.getD cd.name)
    | none => PyPure.gap "the tp_name of a value that is not a class"

/-- **CPython's `tp_new_wrapper`** for `t.__new__(subtype, ...)`, with the arguments `args`
(`subtype` first): `TypeError` unless `subtype` is a class that is `t` or a subclass of it, and
unless `subtype`'s `staticbase` has `t`'s `tp_new`; a `staticbase` other than `t` stops with a gap. -/
def tpNewCheck [PyReads m V] (t : Builtin) (args : V) : m Unit := do
  let tName := t.info.tpName
  let some sub := (← tupleItems args)[0]? |
    raiseBuiltin "TypeError" s!"{tName}.__new__(): not enough arguments"
  if !(← isType sub) then
    raiseBuiltin "TypeError" s!"{tName}.__new__(X): X is not a type object ({← tpNameOf (← PyReads.classOf sub)})"
  let (_, b) ← staticBaseOf tpNewFuel sub
  -- `sub`'s static base has `t`'s `tp_new`, so `sub` is `t` or a subclass of it: the check of a
  -- class call, which always passes, walks the bases once.
  if b == t then return
  let tV := PyPure.imm (m := m) (.builtin t)
  if !(← isSubclass sub tV) then
    let sn ← tpNameOf sub
    raiseBuiltin "TypeError" s!"{tName}.__new__({sn}): {sn} is not a subtype of {tName}"
  -- Whether the static base's `tp_new` is `t`'s C function, as `tp_new_wrapper` checks, is not
  -- modelled yet.
  PyPure.gap s!"{tName}.__new__ of a class whose static base is {b.info.name} is not modelled yet"

/-- CPython's `_PyType_CalculateMetaclass`: the most derived of `mcls` and the bases' metaclasses,
or its `TypeError`. -/
def calculateMeta [PyReads m V] (mcls : V) (bases : Array V) : m V := do
  let mut winner := mcls
  for b in bases do
    let t ← PyReads.classOf b
    if ← isSubclass winner t then continue
    if ← isSubclass t winner then winner := t; continue
    raiseBuiltin "TypeError" "metaclass conflict: the metaclass of a derived class must be a \
      (non-strict) subclass of the metaclasses of all its bases"
  pure winner

/-- The items of a class body's `__slots__`: a `str` as one item, or a tuple's or a list's items,
as `type_new_get_slots` takes them. -/
def slotItems [PyReads m V] (v : V) : m (Array V) := do
  if (← str? v).isSome then return #[v]
  match ← PyPure.immView v with
  | some (.tuple xs) => pure xs
  | _ => match ← listOf? v with
    | some xs => pure xs
    | none => PyPure.gap "__slots__ that is not a str, a tuple or a list"

/-- A slot name as CPython stores it: mangled with the class name for a private name. -/
def mangle (cls name : String) : String :=
  if name.startsWith "__" && !name.endsWith "__" then
    let stripped := (cls.dropWhile (· == '_')).toString
    if stripped.isEmpty then name else s!"_{stripped}{name}"
  else name

/-- The number of slots of the classes `cs` together, as an instance's layout holds them. -/
def slotCountOf [PyReads m V] : List V → m Nat
  | [] => pure 0
  | c :: rest => do
    let own := match ← classData? c with
      | some cd => cd.slots.size
      | none => 0
    return own + (← slotCountOf rest)

/-- Append `note` to the exception `exc`'s `__notes__`, read with the attribute protocol and made
a new list if there is none, as `BaseException.add_note` does.  An exception has no `__dict__`
yet, so a note on one stops with a gap. -/
def addNoteTo [PyWrites m V] [PyNew m V] (exc note : V) : m Unit := do
  if (← PyReads.objView exc) matches some .exc then
    PyPure.gap "a note on an exception is not modelled yet"
  let notes ← tryCatch (some <$> getAttr exc "__notes__") fun x => do
    if ← isAttributeError x then pure none else throw x
  let notes ← match notes with
    | some l => pure l
    | none =>
      let l ← PyPure.allocList #[]
      setAttr exc "__notes__" (some l)
      pure l
  if (← listOf? notes).isNone then raiseBuiltin "TypeError" "Cannot add note: __notes__ is not a list"
  PyWrites.listAppend notes note

/-- Whether the instances of the class `c` have a `__dict__`: a user class's own flag, and for a
built-in type CPython's `tp_dictoffset != 0`. -/
def instanceDictOf [PyReads m V] (c : V) : m Bool := do
  match ← classData? c with
  | some cd => pure cd.instanceDict
  | none => match ← PyPure.immView c with
    | some (.builtin b) => pure b.info.instanceDict
    | _ => pure false

/-- **`type.__new__(mcls, name, bases, ns, **kwds)`**: a new class. -/
def typeNew [PyWrites m V] [PyNew m V] (_self args kwargs : V) : m V := do
  let xs ← tupleItems args
  let #[mcls, nameV, basesV, ns0] := xs |
    if xs.size == 2 then PyPure.gap "type.__new__ with one argument is not modelled yet"
    else raiseBuiltin "TypeError" s!"type.__new__() takes exactly 3 arguments ({xs.size - 1} given)"
  let some name ← str? nameV |
    raiseBuiltin "TypeError" s!"type.__new__() argument 1 must be str, not {← argTypeName nameV}"
  let some (.tuple bases0) ← PyPure.immView basesV |
    raiseBuiltin "TypeError" s!"type.__new__() argument 2 must be tuple, not {← argTypeName basesV}"
  if !(← isDictLike ns0) then
    raiseBuiltin "TypeError" s!"type.__new__() argument 3 must be dict, not {← argTypeName ns0}"
  -- `type_new_get_bases`: a base that is not a type but has `__mro_entries__` is an error here.
  for b in bases0 do
    if !(← isType b) then
      let me? ← tryCatch (some <$> getAttr b "__mro_entries__") fun x => do
        if ← isAttributeError x then pure none else throw x
      if me?.isSome then
        raiseBuiltin "TypeError" "type() doesn't support MRO entry resolution; use types.new_class()"
  -- `type_new_get_bases`: the metaclass first, then `best_base`, one base at a time.
  let bases := if bases0.isEmpty then #[PyPure.imm (m := m) (.builtin .object)] else bases0
  let winner ← calculateMeta mcls bases
  if (← PyPure.identical winner mcls) != .yes then
    PyPure.gap "a class whose metaclass is derived from its bases' is not modelled yet"
  for h : i in [:bases.size] do
    let b := bases[i]
    if !(← isType b) then raiseBuiltin "TypeError" "bases must be types"
    if let some (.builtin bt) ← PyPure.immView b then
      if !bt.info.basetype then
        raiseBuiltin "TypeError" s!"type '{bt.info.name}' is not an acceptable base type"
    -- A layout conflict with an earlier base comes before the next base's checks.
    discard <| bestBase (bases.extract 0 (i + 1))
  let best ← bestBase bases
  -- A `__classcell__` that the class body didn't set (it sets none) must be a cell.
  if (← dictFindStr ns0 "__classcell__").isSome then
    PyPure.gap "a __classcell__ in a class's namespace is not modelled yet"
  -- The namespace is a copy of the dict given, as `type_new` makes it.
  let ns ← PyReads.dictCopy ns0
  if (← dictFindStr ns "__module__").isNone then
    PyPure.gap "a class made without __module__ in its namespace is not modelled yet"
  -- A metaclass's own `mro()` decides the MRO.
  if let some mro ← lookupType mcls "mro" then
    if !((← PyPure.immView mro) matches some (.descr .type "mro" _)) then
      PyPure.gap "a metaclass with its own mro() is not modelled yet"
  for b in bases do
    if let some cd ← classData? b then
      if cd.hasDel then PyPure.gap "a class with a finalizer is not modelled yet"
  if (← dictFindStr ns "__del__").isSome then
    PyPure.gap "a class with a finalizer is not modelled yet"
  -- `__slots__`, and whether instances get a dict, as `type_new_get_slots` and `type_new_slots`
  -- check them, in their order.  The instances get the best base's dict; a dict from another base
  -- is a gap.
  let baseDict ← instanceDictOf best
  let (slots, instanceDict) ← match ← dictFindStr ns "__slots__" with
    | some sv =>
      let items ← slotItems sv
      -- A base other than the best base may give the instances a dict that the best base doesn't.
      if !baseDict then
        for b in bases do
          if (← PyPure.identical b best) != .yes then
            if ← instanceDictOf b then
              PyPure.gap "an instance dict from a base other than the best base is not modelled yet"
      if !items.isEmpty then
        let (_, sz) ← itemsizeOf best
        if sz != 0 then
          raiseBuiltin "TypeError" s!"nonempty __slots__ not supported for subtype of '{← tpNameOf best}'"
      let mut names : Array String := #[]
      let mut addDict := false
      for x in items do
        let some n ← str? x |
          raiseBuiltin "TypeError" s!"__slots__ items must be strings, not '{← typeName x}'"
        match asciiIdentifier? n with
        | some true => pure ()
        | some false => raiseBuiltin "TypeError" "__slots__ must be identifiers"
        | none => PyPure.gap "a non-ASCII name in __slots__ is not modelled yet"
        if n == "__dict__" then
          if baseDict || addDict then
            raiseBuiltin "TypeError" "__dict__ slot disallowed: we already got one"
          addDict := true
        if n == "__weakref__" then PyPure.gap "a __weakref__ slot is not modelled yet"
        names := names.push n
      let own := names.filter (· != "__dict__") |>.map (mangle name ·)
      for n in own do
        -- The class body's own `__qualname__` and `__classcell__` are removed before they could
        -- act as class variables.
        if n != "__qualname__" && n != "__classcell__" && (← dictFindStr ns n).isSome then
          raiseBuiltin "ValueError" s!"'{n}' in __slots__ conflicts with class variable"
      pure (own.qsort (· < ·), addDict || baseDict)
    | none => pure (#[], true)
  -- `type_new_set_name`, after the slots.
  if name.toList.contains '\x00' then raiseBuiltin "ValueError" "type name must not contain null characters"
  -- `__new__` is a static method, and `__init_subclass__` and `__class_getitem__` are class
  -- methods, when they are plain functions.
  for (n, wrap) in [("__new__", true), ("__init_subclass__", false), ("__class_getitem__", false)] do
    if let some f ← dictFindStr ns n then
      if (← PyReads.objView f) matches some (.func ..) then
        let w ← PyPure.allocObj (PyPure.imm (m := m) (.builtin (if wrap then .staticmethod else .classmethod)))
          (if wrap then .staticmethod (some f) else .classmethod (some f))
        PyWrites.dictSet ns (strKey (m := m) n) w none fun _ => pure false
  let qualname ← match ← dictFindStr ns "__qualname__" with
    | some q => match ← str? q with
      | some s => pure s
      | none => raiseBuiltin "TypeError" s!"type __qualname__ must be a str, not {← typeName q}"
    | none => pure name
  discard <| PyWrites.dictDelete ns (strKey (m := m) "__qualname__") none fun _ => pure false
  -- The MRO, which `PyType_Ready` computes after all these checks.
  let tail ← c3Tail bases
  let solid ← if slots.isEmpty then solidBaseOf best else pure (PyPure.imm (m := m) .none)
  let modName ← match ← dictFindStr ns "__module__" with
    | some mv => pure ((← str? mv).getD "")
    | none => pure ""
  let cls ← PyPure.allocObj mcls <| .cls
    { name, qualname, «module» := modName, bases, mroTail := tail, ns, solidBase := solid,
      instanceDict, slots }
  -- A `member` descriptor for each slot, at its index in the instances' layout, which puts the
  -- slots of the classes after this one in the MRO first.
  let offset ← slotCountOf tail.toList
  for h : i in [0:slots.size] do
    let n := slots[i]
    let d ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .member_descriptor)) (.member cls n (offset + i))
    PyWrites.dictSet ns (strKey (m := m) n) d none fun _ => pure false
  if (← dictFindStr ns "__doc__").isNone then
    PyWrites.dictSet ns (strKey (m := m) "__doc__") (PyPure.imm (m := m) .none) none fun _ => pure false
  -- A class that defines `__eq__` and not `__hash__` is unhashable, as `type_ready` sets it.
  if (← dictFindStr ns "__eq__").isSome && (← dictFindStr ns "__hash__").isNone then
    PyWrites.dictSet ns (strKey (m := m) "__hash__") (PyPure.imm (m := m) .none) none fun _ => pure false
  -- `__set_name__` on the namespace's values, in order; an exception gets CPython 3.12's note.
  for (k, v, _) in ← PyReads.dictEntries ns do
    if let some setName ← lookupType (← PyReads.classOf v) "__set_name__" then
      tryCatch (discard <| callFound setName v (← PyReads.classOf v) #[cls, k] (← PyPure.allocDict))
        fun x => do
          -- CPython's `%.100s` cuts the class name at 100 bytes of its UTF-8 text.
          let shown ← if name.utf8ByteSize ≤ 100 then pure name
            else if name.toList.all (·.toNat < 128) then pure (String.ofList (name.toList.take 100))
            else PyPure.gap "a note that cuts a non-ASCII class name is not modelled yet"
          let note := s!"Error calling __set_name__ on '{← typeName v}' instance {← checkRepr k} in '{shown}'"
          addNoteTo x (PyPure.imm (m := m) (.str (.ofString note)))
          throw x
  -- The parent's `__init_subclass__`, with the keywords.
  match ← lookupMro tail.toList "__init_subclass__" with
  | some f =>
    -- `super(cls, cls).__init_subclass__`: `super_getattro` binds with no object.
    let g ← descrGetN dispatchDepth f none cls
    discard <| callN dispatchDepth g (PyPure.imm (m := m) (.tuple #[])) kwargs
  | none => pure ()
  pure cls

/-- `type.__init__(cls, *args)`: 1 or 3 arguments, then nothing. -/
def typeInit [PyWrites m V] (_self args kwargs : V) : m V := do
  let xs ← tupleItems args
  -- `type_init`: keywords only with three arguments.
  if xs.size == 1 && (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" "type.__init__() takes no keyword arguments"
  if xs.size != 1 && xs.size != 3 then
    raiseBuiltin "TypeError" "type.__init__() takes 1 or 3 arguments"
  pure (PyPure.imm (m := m) .none)

/-- **`__build_class__(func, name, *bases, metaclass=None, **kwds)`**. -/
def buildClass [PyWrites m V] [PyNew m V] (_self args kwargs : V) : m V := do
  let xs ← tupleItems args
  let some func := xs[0]? | raiseBuiltin "TypeError" "__build_class__: not enough arguments"
  let some nameV := xs[1]? | raiseBuiltin "TypeError" "__build_class__: not enough arguments"
  match ← PyReads.objView func with
  | some (.func _ _ _ body) =>
    -- CPython runs a function's code with the namespace as its locals; a translated class body
    -- takes it as its argument instead, and any other function stops with a gap.
    if !body then PyPure.gap "__build_class__ of a function that is not a class body is not modelled yet"
  | _ => raiseBuiltin "TypeError" "__build_class__: func must be a function"
  if (← str? nameV).isNone then raiseBuiltin "TypeError" "__build_class__: name is not a string"
  let origBases := xs.extract 2 xs.size
  -- `__mro_entries__` of the bases that are not classes.
  let mut bases := #[]
  let mut changed := false
  for b in origBases do
    if ← isType b then bases := bases.push b; continue
    -- `update_bases` reads the attribute with the attribute protocol, as `getattr` does.
    let me? ← tryCatch (some <$> getAttr b "__mro_entries__") fun x => do
      if ← isAttributeError x then pure none else throw x
    match me? with
    | none => bases := bases.push b
    | some me =>
      let r ← callN dispatchDepth me (PyPure.imm (m := m) (.tuple #[PyPure.imm (m := m) (.tuple origBases)]))
        (← PyPure.allocDict)
      let some (.tuple rs) ← PyPure.immView r |
        raiseBuiltin "TypeError" "__mro_entries__ must return a tuple"
      bases := bases ++ rs
      changed := true
  -- The metaclass and the other keywords.
  let kws ← kwEntries kwargs
  let given := kws.findSome? fun (k, v) => if k == "metaclass" then some v else none
  let rest := kws.filter (·.1 != "metaclass")
  let mcls ← match given, bases[0]? with
    | some mc, _ => if ← isType mc then calculateMeta mc bases else pure mc
    | none, some b => do calculateMeta (← PyReads.classOf b) bases
    | none, none => pure (PyPure.imm (m := m) (.builtin .type))
  let restKw ← dictOfEntries rest
  let basesV := PyPure.imm (m := m) (.tuple bases)
  -- The namespace, from `mcls.__prepare__` read with the attribute protocol, which
  -- `type.__prepare__` makes an empty dict.
  let prepare ← tryCatch (some <$> getAttr mcls "__prepare__") fun x => do
    if ← isAttributeError x then pure none else throw x
  let prepare ← match prepare with
    | some p =>
      if (← PyPure.immView p) matches some (.bound _ .type "__prepare__" _) then pure none
      else pure (some p)
    | none => pure none
  let ns ← match prepare with
    | some f =>
      let r ← callN dispatchDepth f (PyPure.imm (m := m) (.tuple #[nameV, basesV])) restKw
      if !(← isDict r) then PyPure.gap "a __prepare__ that returns a mapping other than a dict"
      pure r
    | none => PyPure.allocDict
  -- A body whose methods use `__class__` returns the mark `Py.classCreating`, where CPython's
  -- returns the cell.  The model fills the cell after `__build_class__` returns, so only the
  -- built-in `type` gives it CPython's class: with any other metaclass, user code could see the
  -- namespace without `__classcell__`, or the cell would get another value.
  let r ← callN dispatchDepth func (PyPure.imm (m := m) (.tuple #[ns])) (← PyPure.allocDict)
  if (← PyPure.undefName? r) == some Py.classCreating &&
      !((← PyPure.immView mcls) matches some (.builtin .type)) then
    PyPure.gap "a class that uses __class__ or super(), made by a metaclass other than type"
  if changed then
    PyWrites.dictSet ns (strKey (m := m) "__orig_bases__") (PyPure.imm (m := m) (.tuple origBases))
      none fun _ => pure false
  callN dispatchDepth mcls (PyPure.imm (m := m) (.tuple #[nameV, basesV, ns])) restKw

/-- Whether the class `t` overrides `object`'s method `name`. -/
def overrides [PyReads m V] (t : V) (name : String) : m Bool := do
  match ← lookupType t name with
  | some f => return !((← PyPure.immView f) matches some (.descr .object _ _) ||
      (← PyPure.immView f) matches some (.bound _ .object _ _))
  | none => pure false

/-- Whether a call has arguments beyond the first. -/
def excessArgs [PyReads m V] (args kwargs : V) : m Bool := do
  return (← tupleItems args).size > 1 || (← PyReads.dictLen kwargs) > 0

/-- Whether the `tp_new` of the class `cls` is `object_new`: it is a built-in type's `tp_new`
(`tpNewOf`) that makes instances, and that type's `__new__` is `object`'s own, as for `object`
and for a built-in type written in Python that defines none (`_Helper`). -/
def tpNewIsObject [PyReads m V] (cls : V) : m Bool := do
  match ← tpNewOf tpNewFuel cls with
  | .slot _ => pure false
  | .builtin b => do
    -- A type that refuses instances has no `tp_new` at all, though its MRO gives `object.__new__`.
    if b.noInstances then return false
    let some f ← lookupType (PyPure.imm (m := m) (.builtin b)) "__new__" |
      PyPure.gap s!"the __new__ of the built-in type {b.info.name}"
    return (← PyPure.immView f) matches some (.bound _ .object "__new__" _)

/-- **`object.__new__(cls, *args, **kwargs)`**: a new instance, with CPython's errors for excess
arguments, which test the class's `tp_new` (`tpNewIsObject`) and its `__init__`. -/
def objectNew [PyWrites m V] [PyNew m V] (_self args kwargs : V) : m V := do
  let xs ← tupleItems args
  let some cls := xs[0]? | raiseBuiltin "TypeError" "object.__new__(): not enough arguments"
  if !(← isType cls) then
    raiseBuiltin "TypeError" s!"object.__new__(X): X is not a type object ({← typeName cls})"
  if ← excessArgs args kwargs then
    if !(← tpNewIsObject cls) then
      raiseBuiltin "TypeError" "object.__new__() takes exactly one argument (the type to instantiate)"
    if !(← overrides cls "__init__") then
      raiseBuiltin "TypeError" s!"{← classNameOf cls}() takes no arguments"
  -- The layout is object's, with the slots of user classes added.
  if (← itemsizeOf cls).1 != "object" then
    PyPure.gap "object.__new__ of a class whose layout is not object's"
  let some mro ← mroOf cls | PyPure.gap "object.__new__ of a value that is not a class"
  PyReads.allocInstance cls .plain #[] (Array.replicate (← slotCountOf mro.toList) none)

/-- **`object.__init__(self, *args, **kwargs)`**, with CPython's errors for excess arguments, which
test the class's `__init__` and its `tp_new` (`tpNewIsObject`). -/
def objectInit [PyWrites m V] (self args kwargs : V) : m V := do
  let xs ← tupleItems args
  if xs.size > 0 || (← PyReads.dictLen kwargs) > 0 then
    let t ← PyReads.classOf self
    if ← overrides t "__init__" then
      raiseBuiltin "TypeError" "object.__init__() takes exactly one argument (the instance to initialize)"
    if ← tpNewIsObject t then
      raiseBuiltin "TypeError"
        s!"{← classTpName t}.__init__() takes exactly one argument (the instance to initialize)"
  pure (PyPure.imm (m := m) .none)

/-- `object.__init_subclass__()`: no keywords. -/
def objectInitSubclass [PyWrites m V] (self args kwargs : V) : m V := do
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" s!"{← classQualnameOf self}.__init_subclass__() takes no keyword arguments"
  let xs ← tupleItems args
  if xs.size > 0 then
    raiseBuiltin "TypeError" s!"{← classQualnameOf self}.__init_subclass__() takes no arguments ({xs.size} given)"
  pure (PyPure.imm (m := m) .none)

/-- `object.__setattr__(self, name, value)`, without a user `__setattr__`. -/
def objectSetattr [PyWrites m V] (self args kwargs : V) : m V := do
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" "wrapper __setattr__() takes no keyword arguments"
  let xs ← tupleItems args
  -- `wrap_setattr`'s message starts with a space.
  let #[nameV, val] := xs | raiseBuiltin "TypeError" s!" expected 2 arguments, got {xs.size}"
  -- CPython's `hackcheck`, before the name is checked: a class's attributes are its metaclass's
  -- to write.
  if ← isType self then
    raiseBuiltin "TypeError" s!"can't apply this __setattr__ to {← classTpName (← PyReads.classOf self)} object"
  let some name ← str? nameV |
    raiseBuiltin "TypeError" s!"attribute name must be string, not '{← typeName nameV}'"
  genericSetAttr self (← PyReads.classOf self) name (some val)
  pure (PyPure.imm (m := m) .none)

/-- `object.__delattr__(self, name)`, without a user `__delattr__`. -/
def objectDelattr [PyWrites m V] (self args kwargs : V) : m V := do
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" "wrapper __delattr__() takes no keyword arguments"
  let xs ← tupleItems args
  let #[nameV] := xs | raiseBuiltin "TypeError" s!"expected 1 argument, got {xs.size}"
  -- CPython's `hackcheck`, before the name is checked.
  if ← isType self then
    raiseBuiltin "TypeError" s!"can't apply this __delattr__ to {← classTpName (← PyReads.classOf self)} object"
  let some name ← str? nameV |
    raiseBuiltin "TypeError" s!"attribute name must be string, not '{← typeName nameV}'"
  genericSetAttr self (← PyReads.classOf self) name none
  pure (PyPure.imm (m := m) .none)

/-- `object.__getattribute__(self, name)`, without a user `__getattribute__`. -/
def objectGetattribute [PyWrites m V] (self args kwargs : V) : m V := do
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" "wrapper __getattribute__() takes no keyword arguments"
  let xs ← tupleItems args
  let #[nameV] := xs | raiseBuiltin "TypeError" s!"expected 1 argument, got {xs.size}"
  let some name ← str? nameV |
    raiseBuiltin "TypeError" s!"attribute name must be string, not '{← typeName nameV}'"
  -- On a class, `PyObject_GenericGetAttr` reads the class's own namespace as an instance dict,
  -- without its MRO, which the model doesn't follow.
  if ← isType self then
    PyPure.gap "object.__getattribute__ of a class is not modelled yet"
  -- `PyObject_GenericGetAttr` is the generic lookup for every kind of object, which the model
  -- follows only for a plain instance and a plain immediate.
  let plainImm := match ← PyPure.immView self with
    | some (.method ..) | some (.bound ..) | some (.descr ..) => false
    | some _ => true
    | none => false
  if !plainImm && !((← PyReads.objView self) matches some .inst) then
    PyPure.gap "object.__getattribute__ of this kind of object is not modelled yet"
  genericGetAttr self (← PyReads.classOf self) name

/-- The arguments of a slot wrapper `name` that takes `n` of them: CPython's `wrapper_call` rejects
keywords, and `check_num_args` any other count. -/
def wrapperArgs [PyReads m V] (name : String) (n : Nat) (args kwargs : V) : m (Array V) := do
  if (← PyReads.dictLen kwargs) > 0 then
    raiseBuiltin "TypeError" s!"wrapper {name}() takes no keyword arguments"
  let xs ← tupleItems args
  if xs.size != n then
    raiseBuiltin "TypeError" s!"expected {n} argument{if n == 1 then "" else "s"}, got {xs.size}"
  pure xs

/-- `object.__eq__(self, other)`: `True` for the same object, else `NotImplemented`. -/
def objectEq [PyWrites m V] (self args kwargs : V) : m V := do
  let #[other] ← wrapperArgs "__eq__" 1 args kwargs | PyPure.modelInvariant "wrapperArgs"
  match ← PyPure.identical self other with
  | .yes => pure (PyPure.imm (m := m) (.bool true))
  | .no => pure (PyPure.imm (m := m) .notImplemented)
  | .unknown => PyPure.gap "the identity of two values that CPython may cache"

/-- `object.__ne__(self, other)`: the inverse of the type's `__eq__`, unless that gives
`NotImplemented`. -/
def objectNe [PyWrites m V] (self args kwargs : V) : m V := do
  let #[other] ← wrapperArgs "__ne__" 1 args kwargs | PyPure.modelInvariant "wrapperArgs"
  -- The type's `tp_richcompare` for `==`.  For a user class, `slot_tp_richcompare` swallows an
  -- exception raised while the dunder is bound; a built-in type's own slot runs no user code.
  let r? ← if ← isUserObject self then trySlot self other "__eq__" (swallow := true)
    else callSpecial? self "__eq__" #[other]
  match r? with
  | some r =>
    if ← isNotImpl r then pure r else pure (PyPure.imm (m := m) (.bool !(← truthy r)))
  | none => pure (PyPure.imm (m := m) .notImplemented)

/-- `object.__lt__` and the other orderings: `NotImplemented`. -/
def objectNotImpl [PyWrites m V] (name : String) (_self args kwargs : V) : m V := do
  discard <| wrapperArgs name 1 args kwargs
  pure (PyPure.imm (m := m) .notImplemented)

/-- `object.__hash__(self)`: its address. -/
def objectHash [PyWrites m V] (self args kwargs : V) : m V := do
  discard <| wrapperArgs "__hash__" 0 args kwargs
  PyPure.hashValue (← PyPure.addrHash self)

/-- A new object of the class `cls`, a built-in type or a subclass of one, with the built-in state
`obj`: an instance of a subclass gets the `__dict__` of its class's layout, and so does a
`classmethod` or `staticmethod`; a subclass with slots stops with a gap. -/
def allocOfClass [PyWrites m V] (cls : V) (obj : NewObj V) : m V := do
  let o ← PyPure.allocObj cls obj
  if let some (.builtin b) ← PyPure.immView cls then
    -- A `classmethod` or `staticmethod` object has a `__dict__` of its own.
    if b == .classmethod || b == .staticmethod then discard <| PyWrites.objEnsureDict o
    return o
  let some mro ← mroOf cls | PyPure.gap "a class without an MRO"
  if (← slotCountOf mro.toList) > 0 then
    PyPure.gap "an instance of a subclass of this built-in type with slots is not modelled yet"
  if let some cd ← classData? cls then
    if cd.instanceDict then discard <| PyWrites.objEnsureDict o
  pure o

/-- **`type.__call__(cls, *args, **kwargs)`**, CPython's `type_call`, which a metaclass's own
`__call__` reaches through `super().__call__`: no second dispatch to the metaclass. -/
def typeCallBody [PyWrites m V] (self args kwargs : V) : m V :=
  typeCallN dispatchDepth false self args kwargs

/-- **`super(T, obj)`**: the zero-argument form is the translator's. -/
def superNew [PyWrites m V] (_self args kwargs : V) : m V := do
  -- `super_init`'s `_PyArg_NoKeywords`, before its arguments are parsed.
  if (← PyReads.dictLen kwargs) > 0 then raiseBuiltin "TypeError" "super() takes no keyword arguments"
  let xs ← tupleItems args
  let #[cls, thisType, obj] := xs |
    if xs.size == 1 then PyPure.gap "super() without arguments outside a method is not modelled yet"
    else PyPure.gap "super with one argument is not modelled yet"
  if !(← isType thisType) then
    raiseBuiltin "TypeError" s!"super() argument 1 must be a type, not {← typeName thisType}"
  -- `super(C, None)` is an unbound super object.
  if (← PyPure.immView obj) matches some .none then
    PyPure.gap "an unbound super object is not modelled yet"
  -- CPython's `supercheck`: `obj` a subclass of the type, else an instance of it, else an object
  -- whose `__class__` is another class that is a subclass of it.
  let asType ← if ← isType obj then isSubclass obj thisType else pure false
  if !asType && !(← isSubclass (← PyReads.classOf obj) thisType) then
    -- `_PyObject_LookupAttr`: an `AttributeError` means no `__class__`.
    let ca? ← tryCatch (some <$> getAttr obj "__class__") fun x => do
      if ← isAttributeError x then pure none else throw x
    if let some ca := ca? then
      if (← isType ca) && (← PyPure.identical ca (← PyReads.classOf obj)) != .yes then
        if ← isSubclass ca thisType then
          PyPure.gap "super() of an object whose __class__ is another class is not modelled yet"
    raiseBuiltin "TypeError" "super(type, obj): obj must be an instance or subtype of type"
  allocOfClass cls (.super thisType obj)

/-- `super.__init__`: the object is complete after `__new__`. -/
def superInit [PyWrites m V] (self args kwargs : V) : m V := do
  -- A class call of `super` runs `__init__` with the arguments that `__new__` used, which leaves
  -- the object as it is; a call with other arguments sets it up again.
  if (← PyReads.dictLen kwargs) > 0 then PyPure.gap "super.__init__ with keywords is not modelled yet"
  let xs ← tupleItems args
  if let some (.super t o) ← PyReads.objView self then
    if let #[t', o'] := xs then
      if (← PyPure.identical t t') == .yes && (← PyPure.identical o o') == .yes then
        return PyPure.imm (m := m) .none
  PyPure.gap "super.__init__ with other arguments than its own is not modelled yet"

/-- The positional argument `i` of `xs`, or the keyword `name` of `kws`, or `None`. -/
def argAt [PyPure m V] (xs : Array V) (kws : Array (String × V)) (i : Nat) (name : String) : V :=
  (xs[i]?).getD ((kws.findSome? fun (k, v) => if k == name then some v else none).getD
    (PyPure.imm (m := m) .none))

/-- `property.__new__(cls, *args, **kwargs)`: an empty property of `cls`; `__init__` fills it. -/
def propertyNew [PyWrites m V] (_self args _kwargs : V) : m V := do
  let xs ← tupleItems args
  let some cls := xs[0]? | PyPure.gap "property.__new__ without a class"
  let none' := PyPure.imm (m := m) .none
  allocOfClass cls (.property none' none' none' none')

/-- What a callable `f`'s `__doc__` is, for the wrappers that copy it: `some d` for a value the
attribute protocol reads (an `AttributeError` meaning `None`); `none` for a function object or a
built-in, whose `__doc__` the model doesn't hold. -/
def callableDoc? [PyCalls m V] (f : V) : m (Option V) := do
  if (← PyPure.immView f).isSome then return none
  if (← PyReads.objView f) matches some (.func ..) then return none
  tryCatch (some <$> getAttr f "__doc__") fun x => do
    if ← isAttributeError x then pure (some (PyPure.imm (m := m) .none)) else throw x

/-- **`property.__init__(self, fget=None, fset=None, fdel=None, doc=None)`**, CPython's
`property_init_impl`: the four parts, and with no `doc`, the getter's `__doc__` (`callableDoc?`).
An instance of a subclass gets the docstring through its own `__doc__` attribute, a slot or its
`__dict__`. A docstring from a getter whose `__doc__` the model doesn't hold stops with a gap where
it is read: for a subclass at once, for a property when its `__doc__` is read. -/
def propertyInit [PyWrites m V] (self args kwargs : V) : m V := do
  -- On an instance of a subclass, `property_init` writes `__doc__` with the attribute protocol.
  if !((← PyPure.immView (← PyReads.classOf self)) matches some (.builtin _)) then
    PyPure.gap "property.__init__ on an instance of a subclass is not modelled yet"
  let sig : BuiltinSig :=
    { name := "property", qualname := "property", style := .keywords, maxpos := 4,
      kwnames := #["fget", "fset", "fdel", "doc"] }
  let b ← bindBuiltinArgs sig args kwargs
  let none' := PyPure.imm (m := m) .none
  let get (i : Nat) : V := (b.params[i]?.bind id).getD none'
  let (fget, fset, fdel, doc) := (get 0, get 1, get 2, get 3)
  let isNone (v : V) : m Bool := return (← PyPure.immView v) matches some .none
  let exact := (← PyPure.immView (← PyReads.classOf self)) matches some (.builtin .property)
  let doc' ← if (← isNone doc) && !(← isNone fget) then
      match ← callableDoc? fget with
      | some d => pure d
      | none =>
        if !exact then PyPure.gap "a property subclass's docstring from its getter is not modelled yet"
        pure none'
    else pure doc
  PyWrites.stateSet self (.property fget fset fdel doc')
  if !exact then setAttr self "__doc__" (some doc')
  pure none'



/-- `property.__set_name__(self, owner, name)`: nothing that the model reads. -/
def propertySetName [PyWrites m V] (_self args kwargs : V) : m V := do
  if (← tupleItems args).size != 2 || (← PyReads.dictLen kwargs) > 0 then
    PyPure.gap "property.__set_name__ with other than two arguments is not modelled yet"
  pure (PyPure.imm (m := m) .none)

/-- `p.setter(f)` (`which = 1`) and `p.deleter(f)` (`which = 2`): a new property, `p` with `f` as
its setter or deleter. -/
def propertyCopy [PyWrites m V] (which : Nat) (self args kwargs : V) : m V := do
  let name := if which == 1 then "setter" else "deleter"
  let b ← bindBuiltinArgs { name, qualname := s!"property.{name}", style := .methO } args kwargs
  let #[some f] := b.params | PyPure.modelInvariant "property: the binder's assumption failed"
  if !((← PyPure.immView (← PyReads.classOf self)) matches some (.builtin .property)) then
    PyPure.gap "a copy of an instance of a subclass of property is not modelled yet"
  let some (.property fget fset fdel doc) ← PyReads.objView self |
    PyPure.gap "property: the receiver is not a property"
  -- CPython's `property_copy` calls `property(fget, fset, fdel, doc)` with `doc` cleared when it
  -- came from the getter, which the model doesn't record for a getter whose `__doc__` runs code.
  if (← PyPure.immView fget).isNone && !((← PyReads.objView fget) matches some (.func ..)) then
    PyPure.gap "a copy of a property whose getter is not a function is not modelled yet"
  let p ← allocOfClass (PyPure.imm (m := m) (.builtin .property)) (.property fget fset fdel doc)
  let parts := if which == 1 then #[fget, f, fdel, doc] else #[fget, fset, f, doc]
  discard <| propertyInit p (PyPure.imm (m := m) (.tuple parts)) (← PyPure.allocDict)
  pure p

/-- `classmethod.__new__` and `staticmethod.__new__`: an empty object of `cls`; `__init__` fills
it. -/
def wrapperNew [PyWrites m V] (static : Bool) (_self args _kwargs : V) : m V := do
  let xs ← tupleItems args
  let some cls := xs[0]? | PyPure.gap "classmethod.__new__ without a class"
  allocOfClass cls (if static then .staticmethod none else .classmethod none)

/-- The attributes that `classmethod` and `staticmethod` copy from their callable
(`functools_wraps`). -/
def wrapsNames : List String := ["__module__", "__name__", "__qualname__", "__doc__", "__annotations__"]

/-- **`classmethod.__init__(self, f)`** and **`staticmethod.__init__`**, CPython's `cm_init` and
`sm_init`: the callable, then `functools_wraps`, which copies `wrapsNames` from it that it has. A
function object's `__module__` and `__name__` and a built-in function's names are copied; the
attributes that the model doesn't hold for them gap where they are read (`getAttrCore`); any other
callable's are read and written with the attribute protocol. -/
def wrapperInit [PyWrites m V] (static : Bool) (self args kwargs : V) : m V := do
  let n := if static then "staticmethod" else "classmethod"
  -- On an instance of a subclass, `functools_wraps` writes with the subclass's own protocol.
  if !((← PyPure.immView (← PyReads.classOf self)) matches some (.builtin _)) then
    PyPure.gap s!"{n}.__init__ on an instance of a subclass is not modelled yet"
  if (← PyReads.dictLen kwargs) > 0 then raiseBuiltin "TypeError" s!"{n}() takes no keyword arguments"
  let xs ← tupleItems args
  let #[f] := xs | raiseBuiltin "TypeError" s!"{n} expected 1 argument, got {xs.size}"
  PyWrites.stateSet self (if static then .staticmethod (some f) else .classmethod (some f))
  let str (s : String) : V := PyPure.imm (m := m) (.str (.ofString s))
  match ← PyPure.immView f with
  | some (.builtin b) =>
    for (k, v) in [("__module__", b.info.module), ("__name__", b.info.name),
        ("__qualname__", b.info.qualname)] do
      setAttr self k (some (str v))
  | some _ => PyPure.gap s!"a {n} of a built-in method is not modelled yet"
  | none => match ← PyReads.objView f with
    | some (.func name mo _ _) =>
      setAttr self "__module__" (some mo)
      setAttr self "__name__" (some (str name))
    | _ =>
      -- Reading an attribute of an object of exactly a built-in type runs no user code, so the
      -- copy waits: what it would give gaps where it is read (`getAttrCore`).
      if (← PyPure.immView (← PyReads.classOf f)) matches some (.builtin _) then
        return PyPure.imm (m := m) .none
      for k in wrapsNames do
        let v ← tryCatch (some <$> getAttr f k) fun x => do
          if ← isAttributeError x then pure none else throw x
        if let some v := v then setAttr self k (some v)
  pure (PyPure.imm (m := m) .none)


/-- CPython's `object_isinstance`: whether the class of `obj`, or failing that its `__class__`
attribute (read with the attribute protocol, an `AttributeError` meaning none), is a subclass of
the class `cls`. -/
def objectIsinstance [PyCalls m V] (obj cls : V) : m Bool := do
  if !(← isType cls) then
    if ← isUserObject cls then
      PyPure.gap "isinstance with a second argument that is an object, not a class"
    raiseBuiltin "TypeError" "isinstance() arg 2 must be a type, a tuple of types, or a union"
  let t ← PyReads.classOf obj
  if ← isSubclass t cls then return true
  let icls ← tryCatch (some <$> getAttr obj "__class__") fun x => do
    if ← isAttributeError x then pure none else throw x
  match icls with
  | some ic =>
    if (← PyPure.identical ic t) != .yes && (← isType ic) then isSubclass ic cls else pure false
  | none => pure false

/-- `isinstance(obj, cls)`, CPython's `PyObject_IsInstance`: an exact match of `obj`'s class; for
a class whose metaclass is `type`, `object_isinstance`; each class of a tuple, one C level
deeper; else the metaclass's `__instancecheck__`, one C level deeper. -/
def isinstanceN [PyCalls m V] : Nat → V → V → m Bool
  | 0, _, _ => PyPure.gap "isinstance over tuples nested deeper than the model follows"
  | n + 1, obj, cls => do
    if (← PyPure.identical (← PyReads.classOf obj) cls) == .yes then return true
    let mt ← PyReads.classOf cls
    if (← PyPure.immView mt) matches some (.builtin .type) then return ← objectIsinstance obj cls
    if let some (.tuple cs) ← PyPure.immView cls then
      for c in cs do
        if ← PyReads.withDepth 1 (isinstanceN n obj c) then return true
      return false
    match ← lookupType mt "__instancecheck__" with
    | some ic => PyReads.withDepth 1 do
      if (← PyPure.immView ic) matches some (.descr .type _ _) then objectIsinstance obj cls
      else truthy (← callFound ic cls mt #[obj] (← PyPure.allocDict))
    | none => objectIsinstance obj cls

/-- The `isinstance` built-in. -/
def isinstanceFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig : BuiltinSig :=
    { name := "isinstance", qualname := "isinstance", style := .posOnly, posonly := 2,
      minpos := 2, maxpos := 2 }
  let b ← bindBuiltinArgs sig args kwargs
  let #[some obj, some cls] := b.params | PyPure.modelInvariant "isinstance: the binder's assumption failed"
  pure (PyPure.imm (m := m) (.bool (← isinstanceN dispatchDepth obj cls)))

end

end

end StrataPython.Dyn.Sem.Builtins
