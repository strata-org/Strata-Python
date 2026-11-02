/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Concrete
public import StrataPython.Dyn.Sem.Proto.Calls
public import StrataPython.Dyn.Sem.Builtins.Classes
public import StrataPython.Dyn.Sem.Builtins.Dunders

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

/-- This piece's bodies. -/
def opsImpls : Impls where
  function
    | .print => some fun {_} {_} [_] [_] _ args kwargs => do
        Proto.checkKwargs kwargs
        Proto.printCall args kwargs
    | .«__build_class__» => some fun {_} {_} [_] [_] => Builtins.buildClass
    | .isinstance => some fun {_} {_} [_] [_] => Builtins.isinstanceFn
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
    | t, name => Builtins.dunderImpl t name

/-- `impls` with CPython's `tp_new_wrapper` checks before every built-in type's `__new__`. -/
def Impls.withNewCheck (impls : Impls) : Impls :=
  { impls with method := fun t n =>
      if n == "__new__" then (impls.method t n).map fun impl {_} {_} [_] [_] self args kwargs => do
        Builtins.tpNewCheck t args
        impl self args kwargs
      else impls.method t n }

/-- Each piece's part, in the order the pieces build on each other. -/
def Assembly.parts : List Impls := [opsImpls]

/-- The bodies of every piece, in the order the pieces build on each other. -/
def Assembly.impls : Impls := (Assembly.parts.foldr Impls.join {}).withNewCheck

/-- The keys that two of `parts` both fill: the built-in functions, and the names of every
built-in type's attribute table; a native function's key belongs to the piece that makes it. -/
def Impls.overlaps (parts : List Impls) : List String :=
  let count (f : Impls → Bool) := (parts.filter f).length
  let fns := Builtin.allConstants.toList.filterMap fun b =>
    if count (fun p => (p.function b).isSome) > 1 then some b.info.name else none
  let methods := Builtin.allConstants.toList.flatMap fun t =>
    (t.ownNames.toList.map (·.1)).filterMap fun n =>
      if count (fun p => (p.method t n).isSome) > 1 then some s!"{t.info.name}.{n}" else none
  fns ++ methods

variable {σ : Type} [Store σ] [Decode σ]

instance {fr : Bool} : PyWrites (PyM σ .writes fr) Value :=
  writesRecord (callBuiltinWith Assembly.impls builtinFuel)

instance {fr : Bool} : PyCalls (PyM σ .calls fr) Value :=
  callsRecord (callBuiltinWith Assembly.impls builtinFuel)

end

end StrataPython.Dyn.Sem
