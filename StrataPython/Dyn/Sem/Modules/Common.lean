/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Dunders
public import StrataPython.Dyn.Sem.Proto.Attrs
public import StrataPython.Dyn.Sem.Builtins.Classes
public import StrataPython.Dyn.Sem.Modules.Names

set_option autoImplicit false

/-!
# What the models of library modules share

The models of library modules port CPython's code to the record of primitives. This file holds
what they share:

* `lookupAttr?`, CPython's `_PyObject_LookupAttr`: an attribute read whose `AttributeError` means
  "none";
* the store classes that these models make, once per run (`modelClass`), with their methods as
  native functions, and the receiver of such a method (`nativeRecv`).
-/

namespace StrataPython.Dyn.Sem.Modules

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- **`_PyObject_LookupAttr(v, name)`**: the attribute, or `none` when reading it raises
`AttributeError`; any other exception propagates. -/
def lookupAttr? [PyCalls m V] (v : V) (name : String) : m (Option V) :=
  tryCatch (some <$> getAttrRaw v name) fun x => do
    if ← isAttributeError x then pure none else throw x

/-- The object `name` of the model's module `mod`, which a port reads from the module's globals;
the module exists, since an object of it exists. -/
def modelGlobal [PyReads m V] (mod name : String) : m V := do
  let some md ← PyReads.moduleGet mod | PyPure.modelInvariant s!"an object of {mod} before {mod}"
  let some (.module _ _ _ (.made attrs)) ← PyReads.objView md |
    PyPure.modelInvariant s!"{mod} is not a module that a piece made"
  let some (_, v) := attrs.find? (·.1 == name) | PyPure.modelInvariant s!"{mod} has no {name}"
  pure v

/-- The class that `type()` gives for a native function of the kind `k`. -/
def nativeClass : NativeKind → Builtin
  | .function => .function
  | .wrapperDescriptor => .wrapper_descriptor
  | .methodWrapper => .«method-wrapper»
  | .builtinFunctionOrMethod => .builtin_function_or_method
  | .methodDescriptor => .method_descriptor

/-- A new native function: its body is the assembly's native body of `key`. -/
def allocNative [PyPure m V] (nd : NativeData V) : m V :=
  PyPure.allocObj (PyPure.imm (m := m) (.builtin (nativeClass nd.kind))) (.native nd)

/-- The receiver and the arguments of a call of a native method `fn`: a bound one
(`method-wrapper`, `builtin_function_or_method`) captured its receiver last; an unbound one takes it
as its first argument, and without one raises CPython's `TypeError`. -/
def nativeRecv [PyReads m V] (fn args : V) : m (V × V) := do
  let some (.native nf) ← PyReads.objView fn |
    PyPure.modelInvariant "a native method's body called without its native"
  match nf.kind with
  | .methodWrapper | .builtinFunctionOrMethod =>
    let some r := nf.captured.back? | PyPure.modelInvariant "a bound native without its receiver"
    pure (r, args)
  | _ =>
    let xs ← tupleItems args
    let some r := xs[0]? |
      if nf.kind == .methodDescriptor then
        raiseBuiltin "TypeError" s!"unbound method {nf.qualname}() needs an argument"
      else
        raiseBuiltin "TypeError" s!"descriptor '{nf.name}' of '{← ownerName nf}' object needs an argument"
    pure (r, PyPure.imm (m := m) (.tuple (xs.extract 1 xs.size)))
where
  ownerName (nf : NativeData V) : m String := do
    match nf.owner with
    | some o => tpNameOf o
    | none => pure nf.qualname

/-- An entry of a model's class namespace. -/
inductive Entry where
  /-- A method with the native body `key`, of the native kind `kind`. -/
  | native (name key : String) (kind : NativeKind)
  /-- A Python function of the model (a native of kind `function`) that keeps a cache: it captures
  a new empty list. -/
  | cached (name key : String)
  /-- A `staticmethod` of a Python function of the model. -/
  | staticNative (name key : String)
  | str (name text : String)
  | none (name : String)
  /-- A tuple of `str`s, such as `__slots__`. -/
  | strs (name : String) (items : Array String)
  /-- The member descriptor of the class's own slot `name`. -/
  | slot (name : String)

/-- The name that an entry binds. -/
def Entry.name : Entry → String
  | .native n _ _ | .cached n _ | .staticNative n _ | .str n _ | .none n | .strs n _ | .slot n => n

/-- How a model describes one of its classes: CPython's names, its flags, the native methods and
values of its namespace, the names of its own slots in the order of their members, and the names
of its `vars()` that the model doesn't hold, whose lookup stops with a gap. -/
structure ClassSpec where
  name : String
  qualname : String
  «module» : String
  tpName : Option String := none
  immutable : Bool := false
  writesGap : Bool := false
  instanceWritesGap : Bool := false
  instanceDict : Bool := false
  asBase : BaseRule := .allowed
  cType : Bool := false
  slots : Array String := #[]
  entries : Array Entry
  gapped : Array String := #[]

/-- Every name of the class's `vars()`: those its namespace holds, and those whose lookup stops
with a gap. -/
def ClassSpec.names (spec : ClassSpec) : List String :=
  spec.entries.toList.map (·.name) ++ spec.gapped.toList

/-- The name of the module of the module table that keeps the model's class `qualname` of the
module `mod`, one object per run. No import statement can spell it, so no program reaches the
module itself. A rule that reads the module table by a name that a program gives (a future
`sys.modules` or `__import__`) must skip the names that start with `<`. -/
def modelClassModule (mod qualname : String) : String := s!"<the model's class {mod}.{qualname}>"

/-- The model's class of `spec` in this run, if it was made already. -/
def modelClass? [PyReads m V] (spec : ClassSpec) : m (Option V) := do
  let some mod ← PyReads.moduleGet (modelClassModule spec.module spec.qualname) | return none
  match ← PyReads.objView mod with
  | some (.module _ _ _ (.made attrs)) =>
    if let some (_, c) := attrs.find? (·.1 == "class") then return some c
    PyPure.modelInvariant s!"the module of the model's class {spec.qualname} has no class"
  | _ => PyPure.modelInvariant s!"the module of the model's class {spec.qualname} is not a module"

/-- The class that `spec` describes, with the metaclass `mcls` and the bases `bases`, made at its
first use in a run, with its methods as native functions: later uses get the same object, which a
module of the module table keeps. Its MRO is C3's over `bases`. -/
def modelClassWith [PyWrites m V] [PyNew m V] (spec : ClassSpec) (mcls : V) (bases : Array V) :
    m V := do
  if let some c ← modelClass? spec then return c
  let key := modelClassModule spec.module spec.qualname
  let ns ← PyPure.allocDict
  let tail ← c3Tail bases
  let solid ← if !spec.slots.isEmpty then pure (PyPure.imm (m := m) .none)
    else match bases[0]? with
      | some b => solidBaseOf b
      | none => PyPure.modelInvariant s!"the model's class {spec.qualname} without a base"
  let c ← PyPure.allocObj mcls <| .cls
    { name := spec.name, qualname := spec.qualname, «module» := spec.module, bases,
      mroTail := tail, ns, solidBase := solid, instanceDict := spec.instanceDict,
      slots := spec.slots, immutable := spec.immutable, gapped := spec.gapped,
      writesGap := spec.writesGap, instanceWritesGap := spec.instanceWritesGap,
      tpName := spec.tpName, asBase := spec.asBase, cType := spec.cType }
  -- The namespace is filled after the class exists, so that each method knows its owner. The
  -- members of the class's own slots follow the slots of the classes after it in the MRO.
  let offset ← slotCountOf tail.toList
  let fnData (name k : String) (captured : Array V) : NativeData V :=
    { key := k, kind := .function, captured, name, qualname := spec.qualname ++ "." ++ name,
      «module» := spec.module }
  for e in spec.entries do
    let v ← match e with
      | .native name k kind =>
        let nd : NativeData V :=
          { key := k, kind := kind, name := name, qualname := spec.qualname ++ "." ++ name,
            «module» := spec.module, owner := some c }
        allocNative nd
      | .cached name k => do
        -- `functools.wraps` gives CPython's wrapper a `__dict__`; its names stop with a gap.
        let gapped := ((functionNames.lookup k).getD []).toArray
        allocNative { fnData name k #[← PyPure.allocList #[]] with gapped }
      | .staticNative name k => do
        let f ← allocNative (fnData name k #[])
        PyPure.allocObj (PyPure.imm (m := m) (.builtin .staticmethod)) (.staticmethod (some f))
      | .str _ text => pure (PyPure.imm (m := m) (.str (.ofString text)))
      | .none _ => pure (PyPure.imm (m := m) .none)
      | .strs _ items =>
        pure (PyPure.imm (m := m) (.tuple (items.map fun t => PyPure.imm (m := m) (.str (.ofString t)))))
      | .slot name =>
        match spec.slots.idxOf? name with
        | some i =>
          PyPure.allocObj (PyPure.imm (m := m) (.builtin .member_descriptor)) (.member c name (offset + i))
        | none => PyPure.modelInvariant s!"the model's class {spec.qualname} has no slot {name}"
    PyNew.dictSetNew ns (strKey (m := m) e.name) v none fun _ => pure false
  let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
    (.module key #[] true #[("class", c)])
  PyReads.moduleAdd key mod
  pure c

/-- The class that `spec` describes, a class of `type` with the base `object` (`modelClassWith`). -/
def modelClass [PyWrites m V] [PyNew m V] (spec : ClassSpec) : m V :=
  modelClassWith spec (PyPure.imm (m := m) (.builtin .type)) #[PyPure.imm (m := m) (.builtin .object)]

end

end

end StrataPython.Dyn.Sem.Modules
