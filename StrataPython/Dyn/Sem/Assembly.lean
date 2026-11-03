/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Concrete
public import StrataPython.Dyn.Sem.Proto.Calls
public import StrataPython.Dyn.Sem.Proto.Repr
public import StrataPython.Dyn.Sem.Builtins.Classes
public import StrataPython.Dyn.Sem.Builtins.Dunders
public import StrataPython.Dyn.Sem.Builtins.Exceptions
public import StrataPython.Dyn.Sem.Builtins.Iter
public import StrataPython.Dyn.Sem.Builtins.Strings
public import StrataPython.Dyn.Sem.Library.Iterators

set_option autoImplicit false

/-!
# The assembly of the built-in bodies

The semantics is built in pieces: these operation rules, and the models of library modules that
build on them. Each piece gives the bodies of the built-in callables that it models as a part, an
`Impls`; `Assembly.impls` joins the parts in the order the pieces build on each other, a part
filling only what the parts before it leave out. The record's instances at `PyM σ .calls` and `PyM σ
.writes` take their calls of built-ins from it (`callBuiltinWith`), so a rule's generic code reaches
every piece's bodies.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

@[expose] public section

/-- The parts joined: the first part that has a body for a key gives it. -/
def Impls.join (a b : Impls) : Impls where
  function f := (a.function f).orElse fun _ => b.function f
  method t n := (a.method t n).orElse fun _ => b.method t n
  native k := (a.native k).orElse fun _ => b.native k

/-- The body of `u.name` for an exception class `u` that has one of its own. -/
def excOwnImpl : Builtin → String → Option BuiltinImpl
  | .BaseException, "__new__" => some fun {_} {_} [_] [_] => Builtins.baseExcNew
  | .BaseException, "__init__" => some fun {_} {_} [_] [_] => Builtins.baseExcInit
  | .BaseException, "__str__" | .NameError, "__str__" | .AttributeError, "__str__" =>
    some fun {_} {_} [_] [_] => Builtins.baseExcStr
  | .BaseException, "__repr__" => some fun {_} {_} [_] [_] => Builtins.baseExcRepr
  | .BaseException, "add_note" => some fun {_} {_} [_] [_] => Builtins.addNote
  | .StopIteration, "__init__" => some fun {_} {_} [_] [_] => Builtins.stopIterationInit
  | .SystemExit, "__init__" => some fun {_} {_} [_] [_] => Builtins.systemExitInit
  | .NameError, "__init__" => some fun {_} {_} [_] [_] => Builtins.keywordFieldsInit "NameError" ["name"]
  | .AttributeError, "__init__" =>
    some fun {_} {_} [_] [_] => Builtins.keywordFieldsInit "AttributeError" ["name", "obj"]
  | .ImportError, "__init__" => some fun {_} {_} [_] [_] => Builtins.importErrorInit
  | .ImportError, "__str__" => some fun {_} {_} [_] [_] => Builtins.importErrorStr
  | .KeyError, "__str__" => some fun {_} {_} [_] [_] => Builtins.keyErrorStr
  | .OSError, "__new__" => some fun {_} {_} [_] [_] => Builtins.osErrorNew
  | .OSError, "__init__" => some fun {_} {_} [_] [_] => Builtins.osErrorInit
  | .OSError, "__str__" => some fun {_} {_} [_] [_] => Builtins.osErrorStr
  | .BaseExceptionGroup, "__new__" => some fun {_} {_} [_] [_] => Builtins.excGroupNew
  | .BaseExceptionGroup, "__init__" => some fun {_} {_} [_] [_] => Builtins.baseExcInit
  | .BaseExceptionGroup, "__str__" => some fun {_} {_} [_] [_] => Builtins.excGroupStr
  | _, _ => none

/-- The body of the exception class `t`'s entry `name`: that of the nearest class of `t`'s MRO with
one of its own. The unicode errors and the `SyntaxError` family have no bodies, so their entries
stop with a gap. -/
def excImpl (t : Builtin) (name : String) : Option BuiltinImpl :=
  if t.info.mro.any ([Builtin.UnicodeError, .SyntaxError].contains ·) then none
  else t.info.mro.toList.findSome? fun u => excOwnImpl u name

/-- This piece's bodies. -/
def opsImpls : Impls where
  function
    | .print => some fun {_} {_} [_] [_] _ args kwargs => do
        Proto.checkKwargs kwargs
        Proto.printCall args kwargs
    | .«__build_class__» => some fun {_} {_} [_] [_] => Builtins.buildClass
    | .isinstance => some fun {_} {_} [_] [_] => Builtins.isinstanceFn
    | .len => some fun {_} {_} [_] [_] => Builtins.lenFn
    | .iter => some fun {_} {_} [_] [_] => Builtins.iterFn
    | .next => some fun {_} {_} [_] [_] => Builtins.nextFn
    | .repr => some fun {_} {_} [_] [_] => Builtins.reprFn
    | _ => none
  method
    | .type, "__new__" => some fun {_} {_} [_] [_] => Builtins.typeNew
    | .type, "__init__" => some fun {_} {_} [_] [_] => Builtins.typeInit
    | .type, "__call__" => some fun {_} {_} [_] [_] => Builtins.typeCallBody
    | .object, "__new__" => some fun {_} {_} [_] [_] => Builtins.objectNew
    | .object, "__init__" => some fun {_} {_} [_] [_] => Builtins.objectInit
    | .object, "__init_subclass__" => some fun {_} {_} [_] [_] => Builtins.objectInitSubclass
    | .object, "__setattr__" => some fun {_} {_} [_] [_] => Builtins.objectSetattr
    | .object, "__delattr__" => some fun {_} {_} [_] [_] => Builtins.objectDelattr
    | .object, "__getattribute__" => some fun {_} {_} [_] [_] => Builtins.objectGetattribute
    | .object, "__eq__" => some fun {_} {_} [_] [_] => Builtins.objectEq
    | .object, "__hash__" => some fun {_} {_} [_] [_] => Builtins.objectHash
    | .object, "__ne__" => some fun {_} {_} [_] [_] => Builtins.objectNe
    | .object, "__lt__" => some fun {_} {_} [_] [_] => Builtins.objectNotImpl "__lt__"
    | .object, "__le__" => some fun {_} {_} [_] [_] => Builtins.objectNotImpl "__le__"
    | .object, "__gt__" => some fun {_} {_} [_] [_] => Builtins.objectNotImpl "__gt__"
    | .object, "__ge__" => some fun {_} {_} [_] [_] => Builtins.objectNotImpl "__ge__"
    | .super, "__new__" => some fun {_} {_} [_] [_] => Builtins.superNew
    | .super, "__init__" => some fun {_} {_} [_] [_] => Builtins.superInit
    | .property, "__new__" => some fun {_} {_} [_] [_] => Builtins.propertyNew
    | .property, "__init__" => some fun {_} {_} [_] [_] => Builtins.propertyInit
    | .property, "__set_name__" => some fun {_} {_} [_] [_] => Builtins.propertySetName
    | .property, "setter" => some fun {_} {_} [_] [_] => Builtins.propertyCopy 1
    | .property, "deleter" => some fun {_} {_} [_] [_] => Builtins.propertyCopy 2
    | .classmethod, "__new__" => some fun {_} {_} [_] [_] => Builtins.wrapperNew false
    | .classmethod, "__init__" => some fun {_} {_} [_] [_] => Builtins.wrapperInit false
    | .staticmethod, "__new__" => some fun {_} {_} [_] [_] => Builtins.wrapperNew true
    | .staticmethod, "__init__" => some fun {_} {_} [_] [_] => Builtins.wrapperInit true
    | t, name =>
      if t.info.mro.contains .BaseException then excImpl t name
      else ((Builtins.iterImpl t name).orElse fun _ => Builtins.stringImpl t name).orElse fun _ =>
        Builtins.dunderImpl t name

/-- `impls` with CPython's `tp_new_wrapper` checks before every built-in type's `__new__`, and its
body without them as `tp_new`, which a class call runs (`Proto.tpNewFor`). -/
def Impls.withNewCheck (impls : Impls) : Impls :=
  { impls with method := fun t n =>
      if n == "__new__" then (impls.method t n).map fun impl {_} {_} [_] [_] self args kwargs => do
        Builtins.tpNewCheck t args
        impl self args kwargs
      else if n == "tp_new" then impls.method t "__new__"
      else impls.method t n }

/-- The bodies of `Library`'s built-in functions and methods. -/
def libraryImpls : Impls where
  function := Library.iterablesFunction
  method := Library.iteratorsMethod

/-- Each piece's part, in the order the pieces build on each other. -/
def Assembly.parts : List Impls := [opsImpls, libraryImpls]

/-- The bodies of every piece, in the order the pieces build on each other. -/
def Assembly.impls : Impls := (Assembly.parts.foldr Impls.join {}).withNewCheck

/-- The keys that two of `parts` both fill: the built-in functions, the names of every built-in
type's attribute table, the hooks `typeGetItemHook` and `unionArgsHook`, and the getset hook
(`getsetHook`) of every getset of those tables.  A native
function's key and a module's import hook (`importHook`) belong to the piece that makes them,
since their names can't be listed here. -/
def Impls.overlaps (parts : List Impls) : List String :=
  let count (f : Impls → Bool) := (parts.filter f).length
  let fns := Builtin.allConstants.toList.filterMap fun b =>
    if count (fun p => (p.function b).isSome) > 1 then some b.info.name else none
  let keys := Builtin.allConstants.toList.flatMap (fun t => t.ownNames.toList.map (t, ·.1)) ++
    [(.type, typeGetItemHook), (.object, unionArgsHook)] ++
    Builtin.allConstants.toList.flatMap fun t =>
      (t.ownNames.toList.filter (·.2 == .getset)).map fun (n, _) => (t, getsetHook n)
  let methods := keys.filterMap fun (t, n) =>
    if count (fun p => (p.method t n).isSome) > 1 then some s!"{t.info.name}.{n}" else none
  fns ++ methods

variable {σ : Type} [Store σ] [Decode σ]

/-- **The joined loop state of every piece's step machines**, the state of `py.call`'s activations
as a list of frames: one constructor per piece. -/
inductive PyLoopState (V : Type) where
  | ops (s : Proto.OpsLoopState V)
  | library (s : Library.LoopState V)

instance {V : Type} : HasLoopPart (PyLoopState V) (Proto.OpsLoopState V) where
  inj := .ops
  proj | .ops s => some s | _ => none
  proj_inj _ := rfl
  inj_of_proj s p h := by cases s <;> simp at h; cases h; rfl

instance {V : Type} : HasLoopPart (PyLoopState V) (Library.LoopState V) where
  inj := .library
  proj | .library s => some s | _ => none
  proj_inj _ := rfl
  inj_of_proj s p h := by cases s <;> simp at h; cases h; rfl

/-- How deep the machines' starts and resumes may nest inside one step of `py.call`: a bound on the
nesting within a step, not on the length of a run, which `Again` carries from step to step. A deeper
nesting stops with a gap, where CPython would raise `RecursionError`. Built-in calls have their own
bound, `builtinFuel`. -/
def machinesFuel : Nat := 10000

instance {fr : Bool} : PyWrites (PyM σ .writes fr) Value :=
  writesRecord (callBuiltinWith Assembly.impls builtinFuel)

instance {fr : Bool} : PyCalls (PyM σ .calls fr) Value :=
  callsRecord (callBuiltinWith Assembly.impls builtinFuel)

/-- **CPython's checks of an unbound call of the built-in callable `f` on `args`**, which run before
its C function and so before a step machine's first step: `tp_new_wrapper`'s for `t.__new__`, and
the descriptor's check of its `self` or its class. -/
def startChecks {m : Type → Type 1} {V : Type} [PyReads m V] (f args : V) : m Unit := do
  match ← PyPure.immView f with
  | some (.bound _ t "__new__" k) => if k != .tpNew then Builtins.tpNewCheck t args
  | some (.descr t name kind) =>
    if kind == .method || kind == .slotWrapper then
      discard <| Proto.descrSelf t name (kind == .slotWrapper) args
    else if kind == .classMethod then
      discard <| Proto.classDescrSelf t name args
  | _ => pure ()

mutual
/-- **The first step of every piece's step machine of a built-in callable**, with the fuel `n` for
the nested calls, after `startChecks`: `Library`'s machines, whose calls start and resume with
one unit less. -/
def machinesStart : Nat → Value → Value → Value →
    PyM σ .writes true (Option (CallStep (PyLoopState Value) Value))
  | 0, _, _, _ => PyM.gap "a call dispatch nested deeper than the model follows"
  | n + 1, f, args, kwargs => do
    startChecks f args
    letI : PyMachines (PyM σ .writes true) Value (PyLoopState Value) :=
      { startStep := machinesStart n, resume := machinesResume n }
    Library.machineStart f args kwargs

/-- **The resume entry of every piece**, with the fuel `n` for the nested resumes: the frames of
`Proto.OpsLoopState` resume through `Proto.opsResume` and `Library`'s through
`Library.machineResume`, whose inner machines start and resume with one unit
less. -/
def machinesResume : Nat → PyLoopState Value → List (PyLoopState Value) →
    PyM σ .writes true (CallStep (PyLoopState Value) Value)
  | 0, _, _ => PyM.gap "frames resumed deeper than the model follows"
  | n + 1, s, rest =>
    letI : PyMachines (PyM σ .writes true) Value (PyLoopState Value) :=
      { startStep := machinesStart n, resume := machinesResume n }
    match s with
    | .ops f => Proto.opsResume f rest
    | .library f => Library.machineResume f rest
end

instance : PyMachines (PyM σ .writes true) Value (PyLoopState Value) :=
  { startStep := machinesStart machinesFuel, resume := machinesResume machinesFuel }

end

end StrataPython.Dyn.Sem
