/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Modules.Common
public import StrataPython.Dyn.Sem.Modules.Names

set_option autoImplicit false

/-!
# The classes of the model of `typing`

The classes of CPython 3.12's `typing` that the modelled objects reach, as the model's classes
describe them: their methods (natives of kind `function`, as CPython's are Python functions), their
slots and texts, and the names of their `vars()` that the model doesn't hold, which are every other
name of `Names.lean`'s table. All of them stop with a gap when a program subclasses them or writes
to them; the instances that a subscription cache may hold stop with a gap on every write too.
-/

namespace StrataPython.Dyn.Sem.Modules

@[expose] public section

/-- The native key of the function `name` of the class `cls` of `typing`. -/
def typingKey (cls name : String) : String := s!"typing.{cls}.{name}"

/-- The text of `Names.lean`'s table under `key`. -/
def genText (key : String) : String := (texts.lookup key).getD ""

/-- The names of `vars()` of CPython's class `key` that `entries` doesn't bind. -/
def gappedOf (key : String) (entries : Array Entry) : Array String :=
  ((classNames.lookup key).getD []).toArray.filter fun n => !entries.any (·.name == n)

/-- The methods `names` of the class `cls` of `typing`, as Python functions. -/
def typingMethods (cls : String) (names : Array String) : Array Entry :=
  names.map fun n => Entry.native n (typingKey cls n) .function

/-- A class of `typing`: its spec, with `__module__` and the texts of its `vars()`, and every other
name of CPython's `vars()` of the class that `entries` doesn't bind as a gap. -/
def typingSpec (qualname : String) (entries : Array Entry) (instanceDict : Bool := false)
    (slots : Array String := #[]) (instanceWritesGap : Bool := false) : ClassSpec :=
  let key := s!"typing.{qualname}"
  let doc := match texts.lookup s!"{key}.__doc__" with
    | some t => #[Entry.str "__doc__" t]
    | none => if entries.any (·.name == "__doc__") then #[] else #[Entry.none "__doc__"]
  let all := entries ++ #[Entry.str "__module__" "typing"] ++ doc
  { name := qualname, qualname, «module» := "typing", writesGap := true, instanceWritesGap,
    instanceDict, asBase := .gap, slots, entries := all, gapped := gappedOf key all }

/-- `typing._Final`, the base of the classes that a program may not subclass. -/
def finalSpec : ClassSpec := typingSpec "_Final" #[.strs "__slots__" #["__weakref__"]]

/-- `typing._NotIterable`, whose `__iter__` is `None`. -/
def notIterableSpec : ClassSpec :=
  typingSpec "_NotIterable" #[.strs "__slots__" #[], .none "__iter__"]

/-- `typing._SpecialForm`: `Optional`, `Union`, `NotRequired`, `Required`, `TypeGuard`, with the
slots `__doc__`, `_getitem` and `_name`. -/
def specialFormSpec : ClassSpec :=
  typingSpec "_SpecialForm" (instanceWritesGap := true)
    (slots := #["__doc__", "_getitem", "_name"])
    (typingMethods "_SpecialForm" #["__getattr__", "__mro_entries__", "__repr__", "__call__",
      "__or__", "__ror__", "__instancecheck__", "__subclasscheck__"] ++
    #[.cached "__getitem__" (typingKey "_SpecialForm" "__getitem__"),
      .strs "__slots__" #["_name", "__doc__", "_getitem"], .slot "__doc__", .slot "_getitem",
      .slot "_name"])

/-- `typing._BaseGenericAlias`, the base of the aliases, whose instances have a dict. -/
def baseGenericAliasSpec : ClassSpec :=
  typingSpec "_BaseGenericAlias" (instanceDict := true) (instanceWritesGap := true)
    (typingMethods "_BaseGenericAlias" #["__call__", "__getattr__", "__setattr__",
      "__instancecheck__", "__subclasscheck__"])

/-- `typing._GenericAlias`: a subscripted alias, such as `List[int]` and `TypeGuard[int]`. -/
def genericAliasSpec : ClassSpec :=
  typingSpec "_GenericAlias" (instanceDict := true) (instanceWritesGap := true)
    (typingMethods "_GenericAlias" #["__eq__", "__hash__", "__or__", "__ror__", "__repr__"])

/-- `typing._SpecialGenericAlias`: `List`, `Dict` and `Set`. -/
def specialGenericAliasSpec : ClassSpec :=
  typingSpec "_SpecialGenericAlias" (instanceDict := true) (instanceWritesGap := true)
    (typingMethods "_SpecialGenericAlias" #["__repr__", "__subclasscheck__", "__or__", "__ror__"] ++
    #[.cached "__getitem__" (typingKey "_SpecialGenericAlias" "__getitem__")])

/-- `typing._TupleType`: `Tuple`. -/
def tupleTypeSpec : ClassSpec :=
  typingSpec "_TupleType" (instanceDict := true) (instanceWritesGap := true)
    #[.cached "__getitem__" (typingKey "_TupleType" "__getitem__")]

/-- `typing._UnionGenericAlias`: `Union[int, str]` and `Optional[int]`. -/
def unionGenericAliasSpec : ClassSpec :=
  typingSpec "_UnionGenericAlias" (instanceDict := true) (instanceWritesGap := true)
    (typingMethods "_UnionGenericAlias" #["__eq__", "__hash__", "__repr__", "__instancecheck__",
      "__subclasscheck__"])

/-- The slots of `typing.ForwardRef`, in the order of their members. -/
def forwardRefSlots : Array String :=
  #["__forward_arg__", "__forward_code__", "__forward_evaluated__", "__forward_is_argument__",
    "__forward_is_class__", "__forward_module__", "__forward_value__"]

/-- `typing.ForwardRef`: a string annotation. Its `__forward_code__` holds a code object in CPython,
so its member is a gap. -/
def forwardRefSpec : ClassSpec :=
  typingSpec "ForwardRef" (slots := forwardRefSlots) (instanceWritesGap := true)
    (typingMethods "ForwardRef" #["__eq__", "__hash__", "__or__", "__ror__", "__repr__"] ++
    #[.strs "__slots__" #["__forward_arg__", "__forward_code__", "__forward_evaluated__",
        "__forward_value__", "__forward_is_argument__", "__forward_is_class__",
        "__forward_module__"]] ++
    (forwardRefSlots.filter (· != "__forward_code__")).map Entry.slot)

/-- `typing._AnyMeta`, the metaclass of `Any`. -/
def anyMetaSpec : ClassSpec :=
  typingSpec "_AnyMeta" (instanceDict := true) (typingMethods "_AnyMeta" #["__instancecheck__", "__repr__"])

/-- `typing.Any`, whose `__new__` refuses to make an `Any`. -/
def anySpec : ClassSpec :=
  typingSpec "Any" (instanceDict := true) #[.staticNative "__new__" (typingKey "Any" "__new__")]

/-- `typing._TypedDictMeta`, the metaclass of the `TypedDict` classes: its `__call__` is `dict`, and
its `__instancecheck__` is its `__subclasscheck__`. -/
def typedDictMetaSpec : ClassSpec :=
  typingSpec "_TypedDictMeta" (instanceDict := true)
    #[.staticNative "__new__" (typingKey "_TypedDictMeta" "__new__"), .builtin "__call__" .dict,
      .native "__subclasscheck__" (typingKey "_TypedDictMeta" "__subclasscheck__") .function,
      .sameAs "__instancecheck__" "__subclasscheck__"]

/-- `typing._TypedDict`, the class that `TypedDict.__mro_entries__` gives, named `TypedDict`. -/
def typedDictSpec : ClassSpec := typingSpec "TypedDict" (instanceDict := true) #[]

/-- The special forms of `typing` that the model has. -/
def specialForms : List String := ["Optional", "Union", "NotRequired", "Required", "TypeGuard"]

/-- The special generic aliases of `typing` that the model has: the name, the origin and the number
of parameters. -/
def specialAliases : List (String × Builtin × Nat) :=
  [("List", .list, 1), ("Dict", .dict, 2), ("Set", .«set», 1)]

end

end StrataPython.Dyn.Sem.Modules
