/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Typing

set_option autoImplicit false

/-!
# The model of `dataclasses`

A port of the parts of CPython 3.12's `Lib/dataclasses.py` that programs use: `dataclass` with its
options, `field`, `Field`, `FrozenInstanceError`, `MISSING` and `replace`. `_process_class` runs in
CPython's order, through the record's combinators, so user code (a default's descriptor, its
`__class__` and `__hash__`, `__set_name__`) runs as in CPython. The methods that CPython generates
with `exec` are native functions of the model whose bodies do what the generated source does: they
keep what CPython bakes into the source when the class is decorated (the field names, defaults and
factories, the class and `FrozenInstanceError`), and they read the globals that the source reads
(`hash`, `type`, `super`, `NotImplemented`) from the class's module at each call. `ClassVar`,
`InitVar` and `KW_ONLY` stop with a gap, and so do the options `slots` and `weakref_slot`.
-/

namespace StrataPython.Dyn.Sem.Modules

open Proto Builtins

@[expose] public section

/-- The native key of the function or method `name` of `dataclasses`. -/
def dcKey (name : String) : String := s!"dataclasses.{name}"

/-- A class of `dataclasses` (`moduleSpec`). -/
def dcSpec (qualname : String) (entries : Array Entry) (instanceDict : Bool := false)
    (slots : Array String := #[]) (instanceWritesGap : Bool := false) : ClassSpec :=
  moduleSpec "dataclasses" qualname entries instanceDict slots instanceWritesGap

/-- The base of `dataclasses.FrozenInstanceError`. -/
def frozenErrorBase : Builtin := .AttributeError

/-- `dataclasses.FrozenInstanceError`, a subclass of `AttributeError`. -/
def frozenErrorSpec : ClassSpec := dcSpec "FrozenInstanceError" #[] (instanceDict := true)

/-- `dataclasses._MISSING_TYPE`, the class of `MISSING`. -/
def missingTypeSpec : ClassSpec := dcSpec "_MISSING_TYPE" #[] (instanceDict := true)

/-- `dataclasses._HAS_DEFAULT_FACTORY_CLASS`, whose instance's `repr` is `<factory>`. -/
def hasFactorySpec : ClassSpec :=
  dcSpec "_HAS_DEFAULT_FACTORY_CLASS" (instanceDict := true)
    #[.native "__repr__" (dcKey "_HAS_DEFAULT_FACTORY_CLASS.__repr__") .function]

/-- `dataclasses._FIELD_BASE`, the class of `_FIELD`, `_FIELD_CLASSVAR` and `_FIELD_INITVAR`. -/
def fieldBaseSpec : ClassSpec :=
  dcSpec "_FIELD_BASE" (instanceDict := true) (instanceWritesGap := true)
    #[.native "__repr__" (dcKey "_FIELD_BASE.__repr__") .function]

/-- The slots of `dataclasses._DataclassParams`, as `__slots__` declares them. -/
def paramsSlots : Array String :=
  #["init", "repr", "eq", "order", "unsafe_hash", "frozen", "match_args", "kw_only", "slots",
    "weakref_slot"]

/-- The names in their member order (sorted). -/
def sortedNames (xs : Array String) : Array String := xs.qsort (· < ·)

/-- `dataclasses._DataclassParams`, a class's `__dataclass_params__`. -/
def paramsSpec : ClassSpec :=
  dcSpec "_DataclassParams" (slots := sortedNames paramsSlots) (instanceWritesGap := true)
    (#[.native "__repr__" (dcKey "_DataclassParams.__repr__") .function,
      .strs "__slots__" paramsSlots] ++ paramsSlots.map Entry.slot)

/-- The slots of `dataclasses.Field`, as `__slots__` declares them. -/
def fieldSlots : Array String :=
  #["name", "type", "default", "default_factory", "repr", "hash", "init", "compare", "metadata",
    "kw_only", "_field_type"]

/-- `dataclasses.Field`. Its `metadata` slot holds a `mappingproxy` in CPython that the model
doesn't make, so its member is a gap; so is its `__repr__`, which shows `MISSING`'s address. Its `__class_getitem__`,
`classmethod(types.GenericAlias)`, is a gap: the model's `GenericAlias` class can't be called. -/
def fieldSpec : ClassSpec :=
  dcSpec "Field" (slots := sortedNames fieldSlots) (instanceWritesGap := true)
    (#[.native "__set_name__" (dcKey "Field.__set_name__") .function, .strs "__slots__" fieldSlots] ++
      (fieldSlots.filter (· != "metadata")).map Entry.slot)

section
variable {m : Type → Type 1} {V : Type}

/-! ## The classes and the module's objects -/

/-- `dataclasses.FrozenInstanceError`, whose base is `frozenErrorBase`. -/
def frozenErrorCls [PyWrites m V] [PyNew m V] : m V :=
  modelClassWith frozenErrorSpec (typeV (m := m)) #[PyPure.imm (m := m) (.builtin frozenErrorBase)]



/-- The index of the slot `name` of `Field` in its instances. -/
def fieldSlot (name : String) : Nat := ((sortedNames fieldSlots).idxOf? name).getD 0

/-- The slot `name` of the `Field` `f`. -/
def fieldGet [PyReads m V] (f : V) (name : String) : m V := do
  let some v ← PyReads.slotGet f (fieldSlot name) | PyPure.modelInvariant s!"a Field without its {name}"
  pure v

/-- Set the slot `name` of the `Field` `f`, as the port's own assignments do. -/
def fieldSet [PyWrites m V] (f : V) (name : String) (v : V) : m Unit :=
  PyWrites.slotSet f (fieldSlot name) v

/-- Whether `v` is `MISSING`. -/
def isMissing [PyReads m V] (v : V) : m Bool := do
  return (← PyPure.identical v (← modelGlobal "dataclasses" "MISSING")) == .yes

/-- **`Field(default, default_factory, init, repr, hash, compare, metadata, kw_only)`**, with
`name`, `type` and `_field_type` `None`; a `metadata` other than `None` stops with a gap. -/
def newField [PyWrites m V] [PyNew m V] (default factory init repr hash compare metadata kwOnly : V) :
    m V := pyFrame do
  if !((← PyPure.immView metadata) matches some .none) then
    PyPure.gap "field(metadata=...) is not modelled yet"
  let none := PyPure.imm (m := m) .none
  let byName : List (String × V) :=
    [("name", none), ("type", none), ("default", default), ("default_factory", factory),
      ("repr", repr), ("hash", hash), ("init", init), ("compare", compare), ("metadata", none),
      ("kw_only", kwOnly), ("_field_type", none)]
  let slots := (sortedNames fieldSlots).map fun n => if n == "metadata" then Option.none else byName.lookup n
  PyReads.allocInstance (← modelClass fieldSpec) .plain #[] slots

/-- Whether `v` is an exact `bool`, the only kind of option that the model takes: CPython reads an
option's truth several times, which could run user code. -/
def boolOption [PyReads m V] (name : String) (v : V) : m Bool := do
  match ← PyPure.immView v with
  | some (.bool b) => pure b
  | _ => PyPure.gap s!"a dataclass option {name} that is not a bool is not modelled yet"

/-- The dataclass options, in `dataclass`'s order. -/
def optionNames : Array String :=
  #["init", "repr", "eq", "order", "unsafe_hash", "frozen", "match_args", "kw_only", "slots",
    "weakref_slot"]

/-- The value of the global `name` of the module `mod`, through the builtins, as the generated
source reads it; a missing one raises CPython's `NameError`. -/
def sourceGlobal [PyReads m V] (mod name : String) : m V := do
  if let some v ← PyReads.globalGet mod name then return v
  if let some v ← PyReads.builtinGet name then return v
  raiseBuiltin "NameError" s!"name '{name}' is not defined"

/-! ## The generated methods -/

/-- How the generated `__init__` sets a field (`_field_init`). -/
inductive FieldInit where
  /-- No assignment: a field with `init=False` and no factory. -/
  | skip
  /-- The argument. -/
  | arg
  /-- The factory's call when the argument is `_HAS_DEFAULT_FACTORY`, else the argument. -/
  | factoryUnlessGiven
  /-- The factory's call: a field with `init=False` and a factory. -/
  | factory
  deriving DecidableEq

/-- The number that encodes `k` in a native's captured values. -/
def FieldInit.code : FieldInit → Nat
  | .skip => 0 | .arg => 1 | .factoryUnlessGiven => 2 | .factory => 3

/-- The `FieldInit` that `n` encodes. -/
def FieldInit.ofCode : Nat → FieldInit
  | 1 => .arg | 2 => .factoryUnlessGiven | 3 => .factory | _ => .skip

/-- What a generated method keeps from the time the class is decorated, as CPython bakes it into
the generated source: the class, the field names it uses, the module whose globals it reads (and
the module name of the functions), and, by method, the rest. -/
structure GenInfo (V : Type) where
  cls : V
  names : Array String
  «module» : String
  /-- `__init__`: how each field of `names` is set, with its factory. -/
  inits : Array (FieldInit × V) := #[]
  frozen : Bool := false
  postInit : Bool := false
  selfName : String := "self"
  /-- `__init__`: the standard and the keyword-only parameters, and the annotation of each
  (standard first). -/
  stdParams : Array String := #[]
  kwParams : Array String := #[]
  types : Array V := #[]
  /-- `__repr__`: the list of the objects whose `repr` runs (`_recursive_repr`). -/
  guard : Option V := none
  /-- The frozen `__setattr__` and `__delattr__`: the class `FrozenInstanceError`. -/
  frozenError : Option V := none

/-- The names in the tuple `v`. -/
def strTuple [PyReads m V] (v : V) : m (Array String) := do
  let some (.tuple ns) ← PyPure.immView v | PyPure.modelInvariant "a tuple of names"
  ns.mapM fun n => do
    let some t ← str? n | PyPure.modelInvariant "a name that is no str"
    pure t

/-- The info that the native `fn` captured (`genFunction`'s layout). -/
def genInfo [PyReads m V] (fn : V) : m (GenInfo V) := do
  let some (.native nf) ← PyReads.objView fn | PyPure.modelInvariant "a generated method without its native"
  let #[cls, namesV, modV, initsV, flagsV, stdV, kwV, typesV, guardV, errV] := nf.captured |
    PyPure.modelInvariant "a generated method without its info"
  let some «module» ← str? modV | PyPure.modelInvariant "a generated method's module"
  let some (.tuple is) ← PyPure.immView initsV | PyPure.modelInvariant "generated field inits"
  let inits ← is.mapM fun kv => do
    let some (.tuple #[k, v]) ← PyPure.immView kv | PyPure.modelInvariant "a generated field init"
    let some (.int ki) ← PyPure.immView k | PyPure.modelInvariant "a generated field init"
    pure (FieldInit.ofCode ki.toNat, v)
  let some (.tuple #[fz, pi, sn]) ← PyPure.immView flagsV | PyPure.modelInvariant "generated flags"
  let some (.bool frozen) ← PyPure.immView fz | PyPure.modelInvariant "a generated flag"
  let some (.bool postInit) ← PyPure.immView pi | PyPure.modelInvariant "a generated flag"
  let some selfName ← str? sn | PyPure.modelInvariant "a generated self name"
  let opt (v : V) : m (Option V) := do
    return if (← PyPure.immView v) matches some .none then none else some v
  let names ← strTuple namesV
  let std ← strTuple stdV
  let kw ← strTuple kwV
  let types ← tupleItems typesV
  let guard ← opt guardV
  let frozenError ← opt errV
  let mut info : GenInfo V := { cls := cls, names := names, «module» := «module» }
  info := { info with inits := inits, frozen := frozen, postInit := postInit }
  info := { info with selfName := selfName, stdParams := std, kwParams := kw }
  info := { info with types := types, guard := guard, frozenError := frozenError }
  pure info

/-- A generated method of the class `cls`: a native function `key`, named `name`, with the
qualified name `cls.__qualname__.name` (`_set_qualname`), and the module name `funcModule` (the
`__name__` of the globals it runs in). -/
def genFunction [PyWrites m V] [PyNew m V] (info : GenInfo V) (funcModule key name : String)
    (defaults kwdefaults : Option V := none) : m V := do
  let some cd ← classData? info.cls | PyPure.modelInvariant "a dataclass that is no class"
  let tup (xs : Array V) : V := PyPure.imm (m := m) (.tuple xs)
  let strs (xs : Array String) : V := tup (xs.map (strValue (m := m) ·))
  let inits := info.inits.map fun (k, v) => tup #[PyPure.imm (m := m) (.int k.code), v]
  let none := PyPure.imm (m := m) .none
  let captured : Array V := #[info.cls, strs info.names, strValue (m := m) info.module, tup inits,
    tup #[PyPure.imm (m := m) (.bool info.frozen), PyPure.imm (m := m) (.bool info.postInit),
      strValue (m := m) info.selfName],
    strs info.stdParams, strs info.kwParams, tup info.types, info.guard.getD none, info.frozenError.getD none]
  let nd : NativeData V :=
    { key := key, kind := .function, captured := captured, name := name,
      qualname := s!"{cd.qualname}.{name}", «module» := funcModule, defaults := defaults,
      kwdefaults := kwdefaults, gapped := ((functionNames.lookup key).getD []).toArray }
  allocNative nd

/-- The tuple `(obj.a, obj.b, ...)` of the fields `names`, read in order. -/
def fieldTuple [PyCalls m V] (obj : V) (names : Array String) : m V := do
  return PyPure.imm (m := m) (.tuple (← names.mapM (getAttr obj ·)))

/-- `__repr__`'s body: `self.__class__.__qualname__ + f"(a={self.a!r}, ...)"`. -/
def reprBody [PyCalls m V] (info : GenInfo V) (self : V) : m V := pyFrame do
  let qn ← getAttr (← getAttr self "__class__") "__qualname__"
  let some qnText ← str? qn |
    PyPure.gap "the repr of a dataclass whose class's __qualname__ is not a str is not modelled yet"
  let mut parts : Array String := #[]
  for n in info.names do
    parts := parts.push s!"{n}={← reprTextOf (← getAttr self n)}"
  return strValue (m := m) s!"{qnText}({", ".intercalate parts.toList})"

/-- The bodies of the generated methods, by native key. -/
def genBody [PyWrites m V] [PyNew m V] (key : String) (fn args kwargs : V) : m V := do
  let bad {α : Type} : m α := PyPure.modelInvariant "a bound call"
  let info ← genInfo fn
  let some cd ← classData? info.cls | PyPure.modelInvariant "a dataclass that is no class"
  let q (name : String) := s!"{cd.qualname}.{name}"
  -- The arguments bound to the parameters of the method that `key` names.
  let bound (params : Array String) : m (Array V) :=
    bindPy (q (key.drop "dataclasses.".length).toString) params args kwargs
  let none := PyPure.imm (m := m) .none
  match key with
  | "dataclasses.__init__" =>
    let some (.native nf) ← PyReads.objView fn | PyPure.modelInvariant "a native"
    let dfl ← match nf.defaults with
      | some d => tupleItems d
      | Option.none => pure #[]
    let kwd ← match nf.kwdefaults with
      | some d => PyReads.dictEntries d
      | Option.none => pure #[]
    -- The parameters: the standard init fields, then `*`, then the keyword-only ones.
    let std := info.stdParams
    let kw := info.kwParams
    let mut defaults : Array (Option V) := #[Option.none]
    let nreq := std.size - dfl.size
    for i in [:std.size] do
      defaults := defaults.push (if i < nreq then Option.none else dfl[i - nreq]?)
    -- The keyword defaults by name, read once: each parameter's lookup is then a pure scan, with no
    -- bind per entry.
    let kwdByName ← kwd.filterMapM fun (k, v, _) => do return (← str? k).map (·, v)
    for n in kw do
      defaults := defaults.push ((kwdByName.find? (·.1 == n)).map (·.2))
    let names := #[info.selfName] ++ std ++ kw
    let vals ← bindPyFull (q "__init__") names defaults 0 (1 + std.size) args kwargs
    let some self := vals[0]? | bad
    let hasFactory ← modelGlobal "dataclasses" "_HAS_DEFAULT_FACTORY"
    for (n, (kind, factory)) in info.names.zip info.inits do
      let arg := match names.idxOf? n with
        | some i => vals[i]?
        | Option.none => Option.none
      let value ← match kind, arg with
        | .arg, some a => pure (some a)
        | .factoryUnlessGiven, some a =>
          if (← PyPure.identical a hasFactory) == .yes then
            some <$> callN dispatchDepth factory (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
          else pure (some a)
        | .factory, _ =>
          some <$> callN dispatchDepth factory (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
        | _, _ => pure Option.none
      if let some v := value then
        if info.frozen then genericSetAttr self (← PyReads.classOf self) n (some v)
        else setAttr self n (some v)
    if info.postInit then
      let f ← getAttr self "__post_init__"
      discard <| callN dispatchDepth f (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
    pure none
  | "dataclasses.__repr__" =>
    let #[self] ← bound #["self"] | bad
    -- `_recursive_repr`'s `wrapper`: a re-entry for the same object gives `...`.
    useBuiltin "id"
    let some guard := info.guard | PyPure.modelInvariant "a __repr__ without its guard"
    let some (running, _) ← PyReads.listView guard | PyPure.modelInvariant "a repr guard that is no list"
    if ← running.anyM fun x => return (← PyPure.identical x self) == .yes then
      return strValue (m := m) "..."
    PyWrites.listAppend guard self
    let drop : m Unit := do
      let some (now, _) ← PyReads.listView guard | PyPure.modelInvariant "a repr guard that is no list"
      if let some i ← indexOf self now then PyWrites.listSplice guard i (i + 1) #[]
    let r ← tryCatch (reprBody info self) fun x => do drop; throw x
    drop
    pure r
  | "dataclasses.__hash__" =>
    let #[self] ← bound #["self"] | bad
    let h ← sourceGlobal info.module "hash"
    let t ← fieldTuple self info.names
    if (← PyPure.immView h) matches some (.builtin .hash) then
      -- The generated source calls the built-in `hash`, a C function: one C level.
      return ← PyPure.hashValue (← PyReads.withDepth 1 (Proto.hash t))
    callN dispatchDepth h (PyPure.imm (m := m) (.tuple #[t])) (← PyPure.allocDict)
  | "dataclasses.__setattr__" | "dataclasses.__delattr__" =>
    let setting := key == "dataclasses.__setattr__"
    let ps := if setting then #["self", "name", "value"] else #["self", "name"]
    let xs ← bound ps
    let some self := xs[0]? | bad
    let some nameV := xs[1]? | bad
    let ty ← sourceGlobal info.module "type"
    let t ← if (← PyPure.immView ty) matches some (.builtin .type) then PyReads.classOf self
      else callN dispatchDepth ty (PyPure.imm (m := m) (.tuple #[self])) (← PyPure.allocDict)
    let hit ← do
      if (← PyPure.identical t info.cls) == .yes then pure true
      else if info.names.isEmpty then pure false
      else
        let some (.str ns) ← PyPure.immView nameV |
          PyPure.gap "a frozen dataclass attribute name that is not a str is not modelled yet"
        pure (info.names.contains ns.s)
    if hit then
      let what := if setting then "cannot assign to field" else "cannot delete field"
      let some fe := info.frozenError | PyPure.modelInvariant "a frozen method without its error"
      PyReads.raiseNew fe #[strValue (m := m) s!"{what} {← reprTextOf nameV}"] #[]
    let sup ← sourceGlobal info.module "super"
    let s ← callN dispatchDepth sup (PyPure.imm (m := m) (.tuple #[info.cls, self])) (← PyPure.allocDict)
    let f ← getAttr s (if setting then "__setattr__" else "__delattr__")
    callN dispatchDepth f (PyPure.imm (m := m) (.tuple (xs.extract 1 xs.size))) (← PyPure.allocDict)
  | _ =>
    -- The comparisons: `if other.__class__ is self.__class__: return (...) OP (...)`.
    let #[self, other] ← bound #["self", "other"] | bad
    let oc ← getAttr other "__class__"
    let sc ← getAttr self "__class__"
    if (← PyPure.identical oc sc) != .yes then
      return ← sourceGlobal info.module "NotImplemented"
    let a ← fieldTuple self info.names
    let b ← fieldTuple other info.names
    let op : Arith.CmpOp := match key with
      | "dataclasses.__lt__" => .lt
      | "dataclasses.__le__" => .le
      | "dataclasses.__gt__" => .gt
      | "dataclasses.__ge__" => .ge
      | _ => .eq
    richCompareV op a b

/-! ## `_process_class` -/

/-- `_set_new_attribute(cls, name, value)`: whether the class's namespace already has `name`;
else the value is set. -/
def setNewAttribute [PyWrites m V] (cls : V) (name : String) (value : V) : m Bool := do
  let some cd ← classData? cls | PyPure.modelInvariant "a dataclass that is no class"
  if (← dictFindStr cd.ns name).isSome then return true
  setAttr cls name (some value)
  return false

/-- `getattr(v, name, d)`: the attribute, or `d` when reading it raises `AttributeError`. -/
def getAttrOr [PyCalls m V] (v : V) (name : String) (d : V) : m V := do
  useBuiltin "getattr"
  return (← lookupAttr? v name).getD d

/-- Whether a `str` annotation could name `ClassVar`, `InitVar` or `KW_ONLY` (`_is_type`):
`module.name` where the class's module's global `module` is `typing` or `dataclasses` and `name`
is a name of that module that the model doesn't bind, which stops with a gap; a non-ASCII
annotation stops with a gap too, since `_MODULE_IDENTIFIER_RE`'s `\w` is Unicode. -/
def checkStrAnnotation [PyReads m V] (mod : String) (ann : String) : m Unit := do
  if !ann.toList.all (·.toNat < 128) then
    PyPure.gap "a non-ASCII str annotation of a dataclass field is not modelled yet"
  let isW (c : Char) := c.isAlphanum || c == '_'
  -- `\s` of `re` for an ASCII string.
  let isS (c : Char) := c == ' ' || (c.toNat ≥ 9 && c.toNat ≤ 13) || (c.toNat ≥ 28 && c.toNat ≤ 31)
  let s := ann.toList.dropWhile isS
  let w1 := s.takeWhile isW
  let after := (s.drop w1.length).dropWhile isS
  if w1.isEmpty || after.head? != some '.' then return
  let rest := (after.drop 1).dropWhile isS
  let w2 := String.ofList (rest.takeWhile isW)
  let some g ← PyReads.globalGet mod (String.ofList w1) | return
  for modName in ["typing", "dataclasses"] do
    if let some md ← PyReads.moduleGet modName then
      if (← PyPure.identical g md) == .yes then
        if let some (.module _ gapped _ _) ← PyReads.objView md then
          if gapped.contains w2 then
            PyPure.gap s!"a str annotation {modName}.{w2} of a dataclass field is not modelled yet"

/-- **`_get_field(cls, a_name, a_type, default_kw_only)`**: the class attribute as the default (a
`Field` itself, or a member descriptor meaning none), the name, type and kind, the keyword-only
flag, and the mutable-default check. -/
def getField [PyWrites m V] [PyNew m V] (cls : V) (mod : String) (name : String) (aType kwOnly : V) :
    m V := pyFrame do
  let missing ← modelGlobal "dataclasses" "MISSING"
  let default ← getAttrOr cls name missing
  useBuiltin "isinstance"
  let fieldCls ← modelClass fieldSpec
  let f ← if ← isinstanceN dispatchDepth default fieldCls then do
      if !(← isSubclass (← PyReads.classOf default) fieldCls) then
        PyPure.gap "a dataclass default that passes for a Field through __class__ is not modelled yet"
      pure default
    else do
    let d ← if ← isinstanceN dispatchDepth default (PyPure.imm (m := m) (.builtin .member_descriptor))
      then pure missing else pure default
    let t := PyPure.imm (m := m) (.bool true)
    newField d missing t t (PyPure.imm (m := m) .none) t (PyPure.imm (m := m) .none) missing
  fieldSet f "name" (strValue (m := m) name)
  fieldSet f "type" aType
  fieldSet f "_field_type" (← modelGlobal "dataclasses" "_FIELD")
  -- `ClassVar`, `InitVar` and `KW_ONLY` can't be reached but through a `str` annotation.
  if let some t ← str? aType then checkStrAnnotation mod t
  if ← isMissing (← fieldGet f "kw_only") then fieldSet f "kw_only" kwOnly
  -- CPython reads the truth of these options several times, which could run user code.
  for opt in ["init", "repr", "compare", "kw_only"] do
    if !((← PyPure.immView (← fieldGet f opt)) matches some (.bool _)) then
      PyPure.gap s!"a field option {opt} that is not a bool is not modelled yet"
  if !((← PyPure.immView (← fieldGet f "hash")) matches some (.bool _) | some .none) then
    PyPure.gap "a field option hash that is not a bool or None is not modelled yet"
  let dflt ← fieldGet f "default"
  let h ← getAttr (← getAttr dflt "__class__") "__hash__"
  if (← PyPure.immView h) matches some .none then
    useBuiltin "type"
    raiseBuiltin "ValueError"
      s!"mutable default {← strTextOf (← PyReads.classOf dflt)} for field {name} is not allowed: use default_factory"
  pure f

/-- The `__init__` that `_init_fn` generates, for the fields `fields` (name and `Field`), the
standard and keyword-only init fields, and the class's flags. -/
def initFn [PyWrites m V] [PyNew m V] (cls : V) (mod funcModule : String) (fields : Array (String × V))
    (std kw : Array (String × V)) (frozen postInit : Bool) (selfName : String) : m V := pyFrame do
  let hasFactory ← modelGlobal "dataclasses" "_HAS_DEFAULT_FACTORY"
  let mut seenDefault := false
  for (n, f) in std do
    if ← truthy (← fieldGet f "init") then
      if !(← isMissing (← fieldGet f "default")) || !(← isMissing (← fieldGet f "default_factory")) then
        seenDefault := true
      else if seenDefault then
        raiseBuiltin "TypeError" s!"non-default argument {← reprTextOf (strValue (m := m) n)} follows default argument"
  let mut inits : Array (FieldInit × V) := #[]
  for (_, f) in fields do
    let init ← truthy (← fieldGet f "init")
    let factory ← fieldGet f "default_factory"
    let kind : FieldInit := if !(← isMissing factory) then (if init then .factoryUnlessGiven else .factory)
      else if init then .arg else .skip
    inits := inits.push (kind, factory)
  let paramDefault (f : V) : m (Option V) := do
    let d ← fieldGet f "default"
    if !(← isMissing d) then return some d
    if !(← isMissing (← fieldGet f "default_factory")) then return some hasFactory
    return Option.none
  let mut dfl : Array V := #[]
  for (_, f) in std do
    if let some d ← paramDefault f then dfl := dfl.push d
  let kwd ← PyPure.allocDict
  for (n, f) in kw do
    if let some d ← paramDefault f then PyNew.dictSetNew kwd (strValue (m := m) n) d none fun _ => pure false
  let types ← (std ++ kw).mapM fun (_, f) => fieldGet f "type"
  let info : GenInfo V :=
    { cls := cls, names := fields.map (·.1), «module» := mod, inits := inits, frozen := frozen,
      postInit := postInit, selfName := selfName, stdParams := std.map (·.1), kwParams := kw.map (·.1),
      types := types }
  genFunction info funcModule "dataclasses.__init__" "__init__"
    (if dfl.isEmpty then Option.none else some (PyPure.imm (m := m) (.tuple dfl)))
    (if (← PyReads.dictLen kwd) == 0 then Option.none else some kwd)

/-- **`inspect.formatannotation(annotation)`**: a `typing` object by its `repr` without the
`typing.` prefixes, a `GenericAlias` by its `str`, a class by `module.qualname` (`qualname` for a
builtin or a `None` module), anything else by `repr`. A `__module__` that is not an exact `str` or
`None` stops with a gap: CPython compares it with `==`. The annotation's `__class__` is `object`'s
(`processClass` checks it), so `isinstance` runs no user code. -/
def formatAnnotation [PyCalls m V] (a : V) : m String := do
  let md ← getAttrOr a "__module__" (PyPure.imm (m := m) .none)
  let mdText ← match ← PyPure.immView md with
    | some (.str t) => pure (some t.s)
    | some .none => pure Option.none
    | _ => PyPure.gap "a dataclass docstring annotation whose __module__ is not a str is not modelled yet"
  if mdText == some "typing" then
    let r ← reprTextOf a
    if !r.toList.all (·.toNat < 128) then
      PyPure.gap "a dataclass docstring with a non-ASCII annotation is not modelled yet"
    -- `re.sub(r'[\w\.]+', ...)`: each run of word characters and dots loses its `typing.` prefix.
    let isW (c : Char) := c.isAlphanum || c == '_' || c == '.'
    let strip (run : String) : String := if run.startsWith "typing." then (run.drop 7).toString else run
    let mut out := ""
    let mut run := ""
    for c in r.toList do
      if isW c then run := run.push c
      else
        out := (out ++ strip run).push c
        run := ""
    return out ++ strip run
  if (← gaParts? a).isSome then return ← strTextOf a
  if ← isType a then
    let qn ← strOf! (← getAttr a "__qualname__")
    return match mdText with
      | some "builtins" | Option.none => qn
      | some t => s!"{t}.{qn}"
  reprTextOf a

/-- **`str(inspect.signature(cls))` with every `' -> None'` removed**, for a class whose first own
`__init__` along its MRO is this model's generated one, or whose MRO has only `object`'s
`__init__` and `__new__`; any other case stops with a gap, a built-in base other than `object`
before the first class with its own `__init__` included. The annotations are the ones that the
generated `__init__` keeps; each one's formatting runs three Python frames deep in CPython
(`Signature.__str__`, `Parameter.__str__`, `formatannotation`), and each default's `repr` two. -/
def docSignature [PyCalls m V] (cls : V) : m String := do
  let some mro ← mroOf cls | PyPure.modelInvariant "a dataclass without its MRO"
  if (← PyPure.identical (← PyReads.classOf cls) (typeV (m := m))) != .yes then
    PyPure.gap "the docstring of a dataclass whose metaclass is not type is not modelled yet"
  let mut initOwner : Option V := Option.none
  for c in mro do
    if let some (.builtin b) ← PyPure.immView c then
      -- A built-in before the first class with its own `__init__` gives the signature.
      if b != .object && initOwner.isNone then
        PyPure.gap "the docstring of a dataclass with a built-in base is not modelled yet"
      continue
    let some cd ← classData? c | continue
    for n in ["__signature__", "_partialmethod", "__new__"] do
      if (← dictFindStr cd.ns n).isSome then
        PyPure.gap s!"the docstring of a dataclass whose MRO defines {n} is not modelled yet"
    if initOwner.isNone then
      if let some i ← dictFindStr cd.ns "__init__" then initOwner := some i
    if let some d ← dictFindStr cd.ns "__doc__" then
      if let some t ← str? d then
        if (t.splitOn "\n--\n\n").length > 1 then
          PyPure.gap "the docstring of a dataclass with a base's text signature is not modelled yet"
  match initOwner with
  | Option.none => return "()"
  | some i =>
    let some (.native nf) ← PyReads.objView i |
      PyPure.gap "the docstring of a dataclass whose __init__ is not the generated one is not modelled yet"
    if nf.key != "dataclasses.__init__" then
      PyPure.gap "the docstring of a dataclass whose __init__ is not the generated one is not modelled yet"
    let info ← genInfo i
    let dfl ← match nf.defaults with
      | some d => tupleItems d
      | Option.none => pure #[]
    let kwd ← match nf.kwdefaults with
      | some d => PyReads.dictEntries d
      | Option.none => pure #[]
    let fmt (n : String) (t : V) (d : Option V) : m String := do
      let ann ← PyReads.withPyDepth 3 (formatAnnotation t)
      match d with
      | some v => return s!"{n}: {ann} = {← PyReads.withPyDepth 2 (reprTextOf v)}"
      | Option.none => return s!"{n}: {ann}"
    let mut parts : Array String := #[]
    let nreq := info.stdParams.size - dfl.size
    for (n, i) in info.stdParams.zipIdx do
      let some t := info.types[i]? | PyPure.modelInvariant "an init param without its annotation"
      parts := parts.push (← fmt n t (if i < nreq then Option.none else dfl[i - nreq]?))
    if !info.kwParams.isEmpty then parts := parts.push "*"
    let kwdByName ← kwd.filterMapM fun (k, v, _) => do return (← str? k).map (·, v)
    for (n, i) in info.kwParams.zipIdx do
      let some t := info.types[info.stdParams.size + i]? | PyPure.modelInvariant "an init param without its annotation"
      parts := parts.push (← fmt n t ((kwdByName.find? (·.1 == n)).map (·.2)))
    let sig := "(" ++ ", ".intercalate parts.toList ++ ")"
    return "".intercalate (sig.splitOn " -> None")

/-- **A walk over the dict `d`'s live entries**, as a `for` loop over it or its `items()` runs:
`RuntimeError` when its size changes; a change of its keys at the same size, where CPython's
table layout decides what the walk sees, stops with a gap. -/
def liveWalk [PyCalls m V] (d : V) (body : V → V → m Unit) : m Unit := do
  let len0 ← PyReads.dictLen d
  let keys0 := (← PyReads.dictFlags d).2
  let size ← PyReads.dictEntriesSize d
  for i in [:size + 1] do
    if (← PyReads.dictLen d) != len0 then
      raiseBuiltin "RuntimeError" "dictionary changed size during iteration"
    if (← PyReads.dictFlags d).2 != keys0 then
      PyPure.gap "a walk over a dict whose keys change at the same size is not modelled yet"
    if i ≥ size then return
    if let .entry k v _ ← PyReads.dictEntryAt d i then body k v

/-- **`_process_class(cls, ...)`** with the options `opts` (in `optionNames`' order). -/
def processClass [PyWrites m V] [PyNew m V] (cls : V) (opts : Array V) : m V := pyFrame do
  let #[initV, reprV, eqV, orderV, unsafeV, frozenV, matchV, kwOnlyV, slotsV, weakV] := opts |
    PyPure.modelInvariant "dataclass options"
  let init ← boolOption "init" initV
  let repr ← boolOption "repr" reprV
  let eq ← boolOption "eq" eqV
  let order ← boolOption "order" orderV
  let unsafeHash ← boolOption "unsafe_hash" unsafeV
  let frozen ← boolOption "frozen" frozenV
  let matchArgs ← boolOption "match_args" matchV
  discard <| boolOption "kw_only" kwOnlyV
  if (← boolOption "slots" slotsV) || (← boolOption "weakref_slot" weakV) then
    PyPure.gap "dataclass(slots=True) and dataclass(weakref_slot=True) are not modelled yet"
  let some cd ← classData? cls | PyPure.gap "dataclass of a value that is not a class is not modelled yet"
  if (← PyPure.identical (← PyReads.classOf cls) (typeV (m := m))) != .yes then
    PyPure.gap "a dataclass whose metaclass is not type is not modelled yet"
  -- The generated methods' globals: `sys.modules[cls.__module__]`.
  let some modV ← dictFindStr cd.ns "__module__" |
    PyPure.gap "a dataclass without __module__ in its namespace is not modelled yet"
  let some (.str modS) ← PyPure.immView modV |
    PyPure.gap "a dataclass whose __module__ is not a str is not modelled yet"
  let mod := modS.s
  if mod.startsWith "<" || (← PyReads.moduleGet mod).isNone then
    PyPure.gap "a dataclass whose __module__ is not a loaded module is not modelled yet"
  -- The generated functions' `__module__` is their globals' `__name__`.
  let funcModule ← match ← PyReads.globalGet mod "__name__" with
    | some nv => match ← PyPure.immView nv with
      | some (.str t) => pure t.s
      | _ => PyPure.gap "a dataclass module whose __name__ is not a str is not modelled yet"
    | Option.none => PyPure.gap "a dataclass module without __name__ is not modelled yet"
  let params ← PyReads.allocInstance (← modelClass paramsSpec) .plain #[]
    ((sortedNames paramsSlots).map fun n => (optionNames.idxOf? n).bind (opts[·]?))
  setAttr cls "__dataclass_params__" (some params)
  -- The fields of the dataclass bases, in reverse MRO order.
  let fieldCls ← modelClass fieldSpec
  let put (xs : Array (String × V)) (n : String) (v : V) : Array (String × V) :=
    match xs.findIdx? (·.1 == n) with
    | some i => xs.set! i (n, v)
    | Option.none => xs.push (n, v)
  let mut fields : Array (String × V) := #[]
  let mut anyFrozenBase := false
  let mut hasDataclassBases := false
  let some mro ← mroOf cls | PyPure.modelInvariant "a class without its MRO"
  for b in (mro.extract 1 mro.size).reverse do
    let bf ← getAttrOr b "__dataclass_fields__" (PyPure.imm (m := m) .none)
    if (← PyPure.immView bf) matches some .none then continue
    hasDataclassBases := true
    if !(← isDict bf) then PyPure.gap "a dataclass base whose __dataclass_fields__ is not a dict"
    for (_, f, _) in ← PyReads.dictEntries bf do
      if !(← isSubclass (← PyReads.classOf f) fieldCls) then
        PyPure.gap "a dataclass base whose fields are not Field objects is not modelled yet"
      let some n ← str? (← fieldGet f "name") | PyPure.gap "a dataclass base field without a str name"
      fields := put fields n f
    if ← truthy (← getAttr (← getAttr b "__dataclass_params__") "frozen") then anyFrozenBase := true
  -- `inspect.get_annotations(cls)`.
  let anns ← match ← dictFindStr cd.ns "__annotations__" with
    | Option.none => pure #[]
    | some a =>
      if (← PyPure.immView a) matches some .none then pure #[] else
      if !(← isDict a) then
        -- `isinstance(ann, dict)`: a dict subclass passes, and so does an object whose class
        -- defines `__class__`; `dict(ann)` then could run user code.
        if (← builtinBase? a) == some .dict then
          PyPure.gap "a dataclass __annotations__ that is an instance of a dict subclass is not modelled yet"
        if (← PyPure.immView a).isNone then
          if let some d ← lookupType (← PyReads.classOf a) "__class__" then
            if !((← PyPure.immView d) matches some (.descr .object "__class__" _)) then
              PyPure.gap "a dataclass __annotations__ whose class defines __class__ is not modelled yet"
        raiseBuiltin "ValueError" s!"{← reprTextOf cls}.__annotations__ is neither a dict nor None"
      (← PyReads.dictEntries a).mapM fun (k, v, _) => do
        let some n ← str? k | PyPure.gap "a dataclass annotation whose name is not a str"
        pure (n, v)
  -- `isinstance(annotation, str)` and the docstring's checks read each annotation's `__class__`,
  -- which runs no user code only when it is `object`'s.
  for (_, t) in anns do
    -- `isinstance(annotation, str)` is true for a str subclass, whose value the checks of `ClassVar`,
    -- `InitVar` and `KW_ONLY` would then read.
    if (← builtinBase? t) == some .str && (← str? t).isNone then
      PyPure.gap "a dataclass annotation that is an instance of a str subclass is not modelled yet"
    if (← PyPure.immView t).isNone then
      match ← lookupType (← PyReads.classOf t) "__class__" with
      | some d =>
        if !((← PyPure.immView d) matches some (.descr .object "__class__" _)) then
          PyPure.gap "a dataclass annotation whose class defines __class__ is not modelled yet"
      | Option.none => pure ()
  let mut got : Array V := #[]
  for (n, t) in anns do
    got := got.push (← getField cls mod n t kwOnlyV)
  -- Each field by its name after every `_get_field` ran: one `Field` may serve two annotations.
  let mut clsFields : Array (String × V) := #[]
  for f in got do
    let some n ← str? (← fieldGet f "name") | PyPure.modelInvariant "a field without its name"
    clsFields := clsFields.push (n, f)
  for (n, f) in clsFields do
    fields := put fields n f
    if ← isinstanceN dispatchDepth (← getAttrOr cls n (PyPure.imm (m := m) .none)) fieldCls then
      let d ← fieldGet f "default"
      useBuiltin (if ← isMissing d then "delattr" else "setattr")
      if ← isMissing d then setAttr cls n Option.none else setAttr cls n (some d)
  -- `for name, value in cls.__dict__.items()`: the live namespace.
  liveWalk cd.ns fun k v => do
    if ← isinstanceN dispatchDepth v fieldCls then
      let some n ← str? k | PyPure.gap "a dataclass namespace name that is not a str"
      if !anns.any (·.1 == n) then
        raiseBuiltin "TypeError" s!"{← reprTextOf k} is a field but has no type annotation"
  if hasDataclassBases then
    if anyFrozenBase && !frozen then
      raiseBuiltin "TypeError" "cannot inherit non-frozen dataclass from a frozen one"
    if !anyFrozenBase && frozen then
      raiseBuiltin "TypeError" "cannot inherit frozen dataclass from a non-frozen one"
  let fieldsDict ← PyPure.allocDict
  for (n, f) in fields do PyNew.dictSetNew fieldsDict (strValue (m := m) n) f none fun _ => pure false
  setAttr cls "__dataclass_fields__" (some fieldsDict)
  -- CPython's generated source takes each field name as a parameter or a local: a name that is
  -- not an identifier, a keyword, or one of the source's own names fails there.
  for (n, _) in fields do
    if identifierKind n != some (true, false) || n.startsWith "__dataclass_" || n == "__debug__" then
      PyPure.gap "a dataclass field name that the generated source can't take is not modelled yet"
  let classHash ← dictFindStr cd.ns "__hash__"
  let hasExplicitHash ← match classHash with
    | Option.none => pure false
    | some h =>
      if (← PyPure.immView h) matches some .none then
        pure !((← dictFindStr cd.ns "__eq__").isSome)
      else pure true
  if order && !eq then raiseBuiltin "ValueError" "eq must be true if order is true"
  let mut std : Array (String × V) := #[]
  let mut kw : Array (String × V) := #[]
  for (n, f) in fields do
    if ← truthy (← fieldGet f "init") then
      if ← truthy (← fieldGet f "kw_only") then kw := kw.push (n, f) else std := std.push (n, f)
  let mkInfo (names : Array String) : GenInfo V := { cls := cls, names := names, «module» := mod }
  if init then
    let postInit ← hasAttr cls "__post_init__"
    let selfName := if fields.any (·.1 == "self") then "__dataclass_self__" else "self"
    discard <| setNewAttribute cls "__init__"
      (← initFn cls mod funcModule fields std kw frozen postInit selfName)
  if repr then
    let flds ← fields.filterM fun (_, f) => do truthy (← fieldGet f "repr")
    let guard ← PyPure.allocList #[]
    discard <| setNewAttribute cls "__repr__"
      (← genFunction { mkInfo (flds.map (·.1)) with guard := some guard } funcModule
        "dataclasses.__repr__" "__repr__")
  let cmpNames ← (← fields.filterM fun (_, f) => do truthy (← fieldGet f "compare")).mapM (pure ·.1)
  if eq then
    discard <| setNewAttribute cls "__eq__"
      (← genFunction (mkInfo cmpNames) funcModule "dataclasses.__eq__" "__eq__")
  if order then
    for name in ["__lt__", "__le__", "__gt__", "__ge__"] do
      if ← setNewAttribute cls name
          (← genFunction (mkInfo cmpNames) funcModule s!"dataclasses.{name}" name) then
        raiseBuiltin "TypeError"
          s!"Cannot overwrite attribute {name} in class {cd.name}. Consider using functools.total_ordering"
  if frozen then
    let fe ← frozenErrorCls
    for name in ["__setattr__", "__delattr__"] do
      if ← setNewAttribute cls name
          (← genFunction { mkInfo (fields.map (·.1)) with frozenError := some fe } funcModule
            s!"dataclasses.{name}" name) then
        raiseBuiltin "TypeError" s!"Cannot overwrite attribute {name} in class {cd.name}"
  -- `_hash_action[unsafe_hash, eq, frozen, has_explicit_hash]`.
  let action : Nat := match unsafeHash, eq, frozen, hasExplicitHash with
    | false, true, false, false => 1
    | false, true, true, false => 2
    | true, _, _, false => 2
    | true, _, _, true => 3
    | _, _, _, _ => 0
  match action with
  | 1 => setAttr cls "__hash__" (some (PyPure.imm (m := m) .none))
  | 2 =>
    let hashNames ← (← fields.filterM fun (_, f) => do
      let h ← fieldGet f "hash"
      if (← PyPure.immView h) matches some .none then truthy (← fieldGet f "compare") else truthy h).mapM
        (pure ·.1)
    setAttr cls "__hash__"
      (some (← genFunction (mkInfo hashNames) funcModule "dataclasses.__hash__" "__hash__"))
  | 3 => raiseBuiltin "TypeError" s!"Cannot overwrite attribute __hash__ in class {cd.name}"
  | _ => pure ()
  -- The docstring: `cls.__name__ + str(inspect.signature(cls))`.
  if !(← truthy (← getAttr cls "__doc__")) then
    let sig ← tryCatch (docSignature cls) fun x => do
      let tc ← isTypeErrorExc x
      let ve ← isSubclass (← PyReads.classOf x) (PyPure.imm (m := m) (.builtin .ValueError))
      if tc || ve then pure "" else throw x
    setOnClass cls "__doc__" (strValue (m := m) (cd.name ++ sig))
  if matchArgs then
    discard <| setNewAttribute cls "__match_args__"
      (PyPure.imm (m := m) (.tuple (std.map fun (n, _) => strValue (m := m) n)))
  -- `abc.update_abstractmethods(cls)`, which does nothing unless `hasattr(cls,
  -- "__abstractmethods__")`: for a class of `type`, `type`'s getset reads the class's own namespace.
  if (← dictFindStr cd.ns "__abstractmethods__").isSome then
    PyPure.gap "a dataclass with __abstractmethods__ is not modelled yet"
  pure cls

/-! ## The module's functions -/

/-- `dataclass`'s parameters after `cls`, and their defaults. -/
def dataclassDefaults [PyPure m V] : Array (Option V) :=
  let t := some (PyPure.imm (m := m) (.bool true))
  let f := some (PyPure.imm (m := m) (.bool false))
  #[t, t, t, f, f, f, t, f, f, f]

/-- **`replace(obj, /, **changes)`**: the fields' current values for the ones not changed, then
`obj.__class__(**changes)`. -/
def replaceBody [PyWrites m V] [PyNew m V] (obj changes : V) : m V := pyFrame do
  useBuiltin "hasattr"
  useBuiltin "type"
  if !(← hasAttr (← PyReads.classOf obj) "__dataclass_fields__") then
    raiseBuiltin "TypeError" "replace() should be called on dataclass instances"
  let fs ← getAttr obj "__dataclass_fields__"
  if !(← isDict fs) then PyPure.gap "replace of a dataclass whose __dataclass_fields__ is not a dict"
  let fieldCls ← modelClass fieldSpec
  let classvar ← modelGlobal "dataclasses" "_FIELD_CLASSVAR"
  liveWalk fs fun _ f => do
    if !(← isSubclass (← PyReads.classOf f) fieldCls) then
      PyPure.gap "replace of a dataclass whose fields are not Field objects is not modelled yet"
    if (← PyPure.identical (← fieldGet f "_field_type") classvar) == .yes then return
    let nameV ← fieldGet f "name"
    let some (.str n) ← PyPure.immView nameV | PyPure.gap "a dataclass field whose name is not a str"
    let given := (← dictFindStr changes n.s).isSome
    if !(← truthy (← fieldGet f "init")) then
      if given then
        raiseBuiltin "ValueError"
          s!"field {n.s} is declared with init=False, it cannot be specified with replace()"
      return
    if !given then
      PyWrites.dictSet changes nameV (← getAttr obj n.s) none fun _ => pure false
  callN dispatchDepth (← getAttr obj "__class__") (PyPure.imm (m := m) (.tuple #[])) changes

/-- The bodies of the functions of `dataclasses` and of its classes' methods, by native key. -/
def dataclassesBody [PyWrites m V] [PyNew m V] (key : String) (fn args kwargs : V) : m V := do
  let none := PyPure.imm (m := m) .none
  match key with
  | "dataclasses.dataclass" =>
    let xs ← bindPyFull "dataclass" (#["cls"] ++ optionNames) (#[some none] ++ dataclassDefaults (m := m))
      1 1 args kwargs
    let some cls := xs[0]? | PyPure.modelInvariant "a bound call"
    let opts := xs.extract 1 xs.size
    if (← PyPure.immView cls) matches some .none then
      -- `@dataclass(...)`: `wrap`, which keeps the options.
      let nd : NativeData V :=
        { key := "dataclasses.dataclass.<locals>.wrap", kind := .function, captured := opts,
          name := "wrap", qualname := "dataclass.<locals>.wrap", «module» := "dataclasses" }
      return ← allocNative nd
    -- `wrap(cls)`, one Python frame deeper.
    pyFrame (processClass cls opts)
  | "dataclasses.dataclass.<locals>.wrap" =>
    let #[cls] ← bindPy "dataclass.<locals>.wrap" #["cls"] args kwargs | PyPure.modelInvariant "a bound call"
    let some (.native nf) ← PyReads.objView fn | PyPure.modelInvariant "a native"
    processClass cls nf.captured
  | "dataclasses.field" =>
    let missing ← modelGlobal "dataclasses" "MISSING"
    let t := some (PyPure.imm (m := m) (.bool true))
    let xs ← bindPyFull "field"
      #["default", "default_factory", "init", "repr", "hash", "compare", "metadata", "kw_only"]
      #[some missing, some missing, t, t, some none, t, some none, some missing] 0 0 args kwargs
    let #[default, factory, init, repr, hashV, compare, metadata, kwOnly] := xs |
      PyPure.modelInvariant "a bound call"
    if !(← isMissing default) && !(← isMissing factory) then
      raiseBuiltin "ValueError" "cannot specify both default and default_factory"
    newField default factory init repr hashV compare metadata kwOnly
  | "dataclasses.replace" =>
    let xs ← bindPyFull "replace" #["obj"] #[Option.none] 1 1 args kwargs (varKw := true)
    let #[obj, changes] := xs | PyPure.modelInvariant "a bound call"
    replaceBody obj changes
  | "dataclasses._HAS_DEFAULT_FACTORY_CLASS.__repr__" =>
    let #[_] ← bindPy "_HAS_DEFAULT_FACTORY_CLASS.__repr__" #["self"] args kwargs |
      PyPure.modelInvariant "a bound call"
    return strValue (m := m) "<factory>"
  | "dataclasses._FIELD_BASE.__repr__" =>
    let #[self] ← bindPy "_FIELD_BASE.__repr__" #["self"] args kwargs | PyPure.modelInvariant "a bound call"
    getAttr self "name"
  | "dataclasses._DataclassParams.__repr__" =>
    let #[self] ← bindPy "_DataclassParams.__repr__" #["self"] args kwargs |
      PyPure.modelInvariant "a bound call"
    let mut parts : Array String := #[]
    for n in paramsSlots do parts := parts.push s!"{n}={← reprTextOf (← getAttr self n)}"
    return strValue (m := m) s!"_DataclassParams({",".intercalate parts.toList})"
  | "dataclasses.Field.__set_name__" =>
    let #[self, owner, name] ← bindPy "Field.__set_name__" #["self", "owner", "name"] args kwargs |
      PyPure.modelInvariant "a bound call"
    let d ← getAttr self "default"
    let func ← getAttrOr (← PyReads.classOf d) "__set_name__" none
    if ← truthy func then
      discard <| callN dispatchDepth func (PyPure.imm (m := m) (.tuple #[d, owner, name])) (← PyPure.allocDict)
    pure none
  | _ => genBody key fn args kwargs

/-- The names that the model's module `dataclasses` binds. -/
def dataclassesAttrNames : List String :=
  ["__name__", "dataclass", "field", "Field", "FrozenInstanceError", "replace", "MISSING",
    "_MISSING_TYPE", "_HAS_DEFAULT_FACTORY", "_HAS_DEFAULT_FACTORY_CLASS", "_FIELD",
    "_FIELD_CLASSVAR", "_FIELD_INITVAR", "_FIELD_BASE", "_DataclassParams", "_FIELDS", "_PARAMS",
    "_POST_INIT_NAME"]

/-- **`import dataclasses`**: the module, made at its first import after a check that the builtins
are unchanged, with every other name of CPython's `vars(dataclasses)` as a gap. -/
def importDataclasses [PyWrites m V] [PyNew m V] (_self _args _kwargs : V) : m V := do
  if !(← builtinsUnchanged) then
    PyPure.gap "an import of dataclasses after the program changed the builtins is not modelled yet"
  let fn (name : String) : m V :=
    allocNative { key := dcKey name, kind := .function, name, qualname := name, «module» := "dataclasses" }
  let missingCls ← modelClass missingTypeSpec
  let factoryCls ← modelClass hasFactorySpec
  let fieldBase ← modelClass fieldBaseSpec
  let fieldKind (n : String) : m V :=
    PyReads.allocInstance fieldBase .plain #[("name", strValue (m := m) n)] #[]
  let attrs : Array (String × V) := #[("__name__", strValue (m := m) "dataclasses"),
    ("dataclass", ← fn "dataclass"), ("field", ← fn "field"), ("Field", ← modelClass fieldSpec),
    ("FrozenInstanceError", ← frozenErrorCls), ("replace", ← fn "replace"),
    ("MISSING", ← PyReads.allocInstance missingCls .plain #[] #[]), ("_MISSING_TYPE", missingCls),
    ("_HAS_DEFAULT_FACTORY", ← PyReads.allocInstance factoryCls .plain #[] #[]),
    ("_HAS_DEFAULT_FACTORY_CLASS", factoryCls),
    ("_FIELD", ← fieldKind "_FIELD"), ("_FIELD_CLASSVAR", ← fieldKind "_FIELD_CLASSVAR"),
    ("_FIELD_INITVAR", ← fieldKind "_FIELD_INITVAR"), ("_FIELD_BASE", fieldBase),
    ("_DataclassParams", ← modelClass paramsSpec),
    ("_FIELDS", strValue (m := m) "__dataclass_fields__"),
    ("_PARAMS", strValue (m := m) "__dataclass_params__"),
    ("_POST_INIT_NAME", strValue (m := m) "__post_init__")]
  let gapped := ((moduleNames.lookup "dataclasses").getD []).toArray.filter (!dataclassesAttrNames.contains ·)
  let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module)) (.module "dataclasses" gapped true attrs)
  PyReads.moduleAdd "dataclasses" mod
  pure mod

end

/-- **The rules of `dataclasses`**: its import and the bodies of its functions. -/
def dataclassesImpls : Impls where
  method
    | .module, n => if n == importHook "dataclasses" then some fun {_} {_} [_] [_] => importDataclasses else none
    | _, _ => none
  native key :=
    if key.startsWith "dataclasses." then some fun {_} {_} [_] [_] fn args kwargs =>
      pyFunctionCall (dataclassesBody key fn args kwargs)
    else none

end

end StrataPython.Dyn.Sem.Modules
