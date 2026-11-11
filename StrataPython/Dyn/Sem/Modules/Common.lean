/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Dunders
public import StrataPython.Dyn.Sem.Proto.Attrs

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

/-- An entry of a model's class namespace: a native method, or a `str` value. -/
inductive Entry where
  /-- A method with the native body `key`, of the native kind `kind`. -/
  | native (name key : String) (kind : NativeKind)
  | str (name text : String)

/-- The name that an entry binds. -/
def Entry.name : Entry → String
  | .native n _ _ => n
  | .str n _ => n

/-- How a model describes one of its classes: CPython's names, its flags, the native methods and
values of its namespace, and the names of its `vars()` that the model doesn't hold, whose
lookup stops with a gap. Its base is `object`. -/
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

/-- The class that `spec` describes, made at its first use in a run, with its methods as native
functions: later uses get the same object, which a module of the module table keeps. -/
def modelClass [PyWrites m V] [PyNew m V] (spec : ClassSpec) : m V := do
  let key := modelClassModule spec.module spec.qualname
  if let some mod ← PyReads.moduleGet key then
    match ← PyReads.objView mod with
    | some (.module _ _ _ (.made attrs)) =>
      if let some (_, c) := attrs.find? (·.1 == "class") then return c
      PyPure.modelInvariant s!"the module of the model's class {spec.qualname} has no class"
    | _ => PyPure.modelInvariant s!"the module of the model's class {spec.qualname} is not a module"
  let ns ← PyPure.allocDict
  let obj := PyPure.imm (m := m) (.builtin .object)
  let c ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .type)) <| .cls
    { name := spec.name, qualname := spec.qualname, «module» := spec.module, bases := #[obj],
      mroTail := #[obj], ns, solidBase := obj, instanceDict := spec.instanceDict,
      immutable := spec.immutable, gapped := spec.gapped, writesGap := spec.writesGap,
      instanceWritesGap := spec.instanceWritesGap, tpName := spec.tpName, asBase := spec.asBase,
      cType := spec.cType }
  -- The namespace is filled after the class exists, so that each method knows its owner.
  for e in spec.entries do
    match e with
    | .native name k kind =>
      let nd : NativeData V :=
        { key := k, kind := kind, name := name, qualname := spec.qualname ++ "." ++ name,
          «module» := spec.module, owner := some c }
      let f ← allocNative nd
      PyNew.dictSetNew ns (strKey (m := m) name) f none fun _ => pure false
    | .str name text =>
      PyNew.dictSetNew ns (strKey (m := m) name) (PyPure.imm (m := m) (.str (.ofString text))) none
        fun _ => pure false
  let mod ← PyPure.allocObj (PyPure.imm (m := m) (.builtin .module))
    (.module key #[] true #[("class", c)])
  PyReads.moduleAdd key mod
  pure c

end

end

end StrataPython.Dyn.Sem.Modules
