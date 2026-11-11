/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Builtins.Classes
public import StrataPython.Dyn.Sem.Library.Iterables
public import StrataPython.Dyn.Sem.Library.Signatures
public import StrataPython.Dyn.Sem.Proto.Repr

set_option autoImplicit false

/-!
# Built-in functions over one or two values, and the numeric dunders of `int` and `float`

Generic over the record, CPython 3.12's `getattr`, `hasattr`, `setattr`, `callable`,
`issubclass`, `hash`, `abs`, `divmod` and `hex` (`Python/bltinmodule.c`, `Objects/abstract.c`),
and the `__abs__`, `__divmod__`, `__rdivmod__`, `__int__`, `__float__` and `__trunc__` entries of
`int` and `float` (`Objects/longobject.c`, `Objects/floatobject.c`), which `bool` and the user
subclasses of `int` and `float` inherit.
-/

namespace StrataPython.Dyn.Sem.Library

open Proto Builtins

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The parameters of a call bound by `sig`, which must hold exactly `n` of them. -/
def params [PyReads m V] (sig : BuiltinSig) (n : Nat) (args kwargs : V) : m (Array (Option V)) := do
  let b ← bindBuiltinArgs sig args kwargs
  unless b.params.size == n do
    PyPure.modelInvariant s!"{sig.name}: the binder gave a parameter array of another shape"
  return b.params

/-- The value of the argument `i`, which the binder must have given. -/
def given [PyPure m V] (name : String) (ps : Array (Option V)) (i : Nat) : m V := do
  let some (some v) := ps[i]? | PyPure.modelInvariant s!"{name}: a required argument is missing"
  return v

/-- The name of an attribute, as `PyObject_GetAttr` takes it: a `str`. An instance of a `str`
subclass stops with a gap: CPython looks it up as the dict key that it is, which runs its own
`__hash__` and `__eq__`, and `setattr` stores it as the key. -/
def attrName [PyReads m V] (v : V) : m String := do
  if let some s ← str? v then return s
  if (← PyReads.strView v).isSome then
    PyPure.gap "an attribute name that is an instance of a subclass of str is not modelled yet"
  raiseBuiltin "TypeError" s!"attribute name must be string, not '{← typeName v}'"

/-! ## Attributes -/

/-- **`getattr(object, name[, default])`**, CPython's `builtin_getattr`: with `default`, an
`AttributeError` gives it, and any other exception propagates. -/
def getattrFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.getattr
  let ps ← params sig 3 args kwargs
  let obj ← given "getattr" ps 0
  let name ← attrName (← given "getattr" ps 1)
  match ps[2]? with
  | some (some d) =>
    tryCatch (getAttr obj name) fun x => do
      if ← isAttributeError x then pure d else throw x
  | _ => getAttr obj name

/-- **`hasattr(obj, name)`**, CPython's `builtin_hasattr_impl`: `False` on an `AttributeError`;
any other exception propagates. -/
def hasattrFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.hasattr
  let ps ← params sig 2 args kwargs
  let obj ← given "hasattr" ps 0
  let name ← attrName (← given "hasattr" ps 1)
  let r ← tryCatch (do discard <| getAttr obj name; pure true) fun x => do
    if ← isAttributeError x then pure false else throw x
  return PyPure.imm (m := m) (.bool r)

/-- **`setattr(obj, name, value)`**, CPython's `builtin_setattr_impl`. -/
def setattrFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.setattr
  let ps ← params sig 3 args kwargs
  let obj ← given "setattr" ps 0
  let name ← attrName (← given "setattr" ps 1)
  setAttr obj name (some (← given "setattr" ps 2))
  return PyPure.imm (m := m) .none

/-! ## Classes and calls -/

/-- **`PyCallable_Check(v)`**: whether `v`'s type has `tp_call`. A user class's instance has it
when the class has `__call__`, whatever its value, since `type_new` fills the slot from the
name. -/
def isCallable [PyReads m V] (v : V) : m Bool := do
  match ← PyPure.immView v with
  | some (.builtin b) =>
    match b.info.kind with
    | .type | .function => return true
    -- The names that `site` adds (`exit`, `quit`, `help`, `copyright`, `credits`, `license`) are
    -- callable objects; the builtins' `__spec__` is a module spec, which isn't.
    | .other => return b != .«__spec__»
  | some (.descr _ _ k) =>
    match k with
    | .method | .slotWrapper | .classMethod | .staticMethod => return true
    | .getset | .member => return false
    | .tpNew => PyPure.modelInvariant "callable() of a class call's own callee"
  | some (.bound _ _ _ .tpNew) => PyPure.modelInvariant "callable() of a class call's own callee"
  | some (.bound ..) | some (.method ..) => return true
  | some _ => return false
  | none =>
    match ← PyReads.objView v with
    | some (.func ..) | some (.native _) | some (.cls _) | some (.staticmethod _) => return true
    | some .inst => return (← lookupType (← PyReads.classOf v) "__call__").isSome
    | some (.iter _) | some (.module ..) | some (.property ..) | some (.classmethod _)
    | some (.super ..) | some (.mappingProxy ..) | some (.dictProxy _) | some (.member ..)
    | some (.exc _) =>
      return (← lookupType (← PyReads.classOf v) "__call__").isSome
    | some (.opaque ..) => PyPure.gap "callable() of this object is not modelled yet"
    | none =>
      -- A list, a dict, a set or another container, whose built-in type has no `tp_call`; an
      -- instance of a user subclass of one has it only through `__call__`.
      return (← lookupType (← PyReads.classOf v) "__call__").isSome

/-- **`callable(obj)`**. -/
def callableFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.callable
  let ps ← params sig 1 args kwargs
  return PyPure.imm (m := m) (.bool (← isCallable (← given "callable" ps 0)))

/-- Whether `v` is a class (`PyType_Check`): a built-in type, or a class object of any
metaclass. -/
def isTypeValue [PyReads m V] (v : V) : m Bool := do
  if ← isClass v then return true
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return false
  return (← PyReads.objView v) matches some (.cls _)

/-- `recursive_issubclass(derived, cls)` for two classes, and the `TypeError`s of an argument
that is not a class. Any other object that has `__bases__` (`check_class`, which reads the
attribute of any object) stops with a gap. -/
def recursiveIssubclass [PyCalls m V] (derived cls : V) : m Bool := do
  if (← isTypeValue derived) && (← isTypeValue cls) then return ← isSubclass derived cls
  let hasBases (v : V) : m Bool := do
    return (← tryCatch (do discard <| getAttr v "__bases__"; pure true) fun x => do
      if ← isAttributeError x then pure false else throw x)
  unless ← isTypeValue derived do
    if ← hasBases derived then PyPure.gap "issubclass() of an object with __bases__ is not modelled"
    raiseBuiltin "TypeError" "issubclass() arg 1 must be a class"
  if ← hasBases cls then PyPure.gap "issubclass() of an object with __bases__ is not modelled"
  raiseBuiltin "TypeError" "issubclass() arg 2 must be a class, a tuple of classes, or a union"

/-- **`issubclass(derived, cls)`**, CPython's `object_issubclass`: an exact `type` `cls` checks
the MRO; a union's arguments, and each class of a tuple, one C level deeper; else the metaclass's
`__subclasscheck__`. -/
def issubclassN [PyCalls m V] : Nat → V → V → m Bool
  | 0, _, _ => PyPure.gap "issubclass over tuples nested deeper than the model follows"
  | n + 1, derived, cls => do
    if (← PyPure.immView (← PyReads.classOf cls)) matches some (.builtin .type) then
      if (← PyPure.identical derived cls) == .yes then return true
      return ← recursiveIssubclass derived cls
    -- `_PyUnion_Check`: a union, an opaque object, stands for the tuple of its arguments.
    let cls ← if (← PyReads.objView cls) matches some (.opaque ..) then
        let hook := PyPure.imm (m := m) (.bound cls .object unionArgsHook .method)
        let args ← PyCalls.callBuiltin hook (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
        pure (if (← PyPure.immView args) matches some (.tuple _) then args else cls)
      else pure cls
    -- `PyTuple_Check`: a tuple, or an instance of a subclass of one.
    let cs? ← match ← PyPure.immView cls with
      | some (.tuple cs) => pure (some cs)
      | some _ => pure none
      | none => PyReads.tupleView cls
    if let some cs := cs? then
      for c in cs do
        if ← PyReads.withDepth 1 (issubclassN n derived c) then return true
      return false
    let mt ← PyReads.classOf cls
    match ← lookupType mt "__subclasscheck__" with
    | some sc => PyReads.withDepth 1 do
      if (← PyPure.immView sc) matches some (.descr .type _ _) then recursiveIssubclass derived cls
      else truthy (← callFound "__subclasscheck__" sc cls mt #[derived] (← PyPure.allocDict))
    | none => recursiveIssubclass derived cls

/-- **`issubclass(cls, class_or_tuple)`**. -/
def issubclassFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.issubclass
  let ps ← params sig 2 args kwargs
  let r ← issubclassN dispatchDepth (← given "issubclass" ps 0) (← given "issubclass" ps 1)
  return PyPure.imm (m := m) (.bool r)

/-! ## Numbers -/

/-- **`hash(obj)`**: `PyObject_Hash`, as the record's `hashValue` turns a hash into an `int`. -/
def hashFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.hash
  let ps ← params sig 1 args kwargs
  PyPure.hashValue (← hash (← given "hash" ps 0))

/-- **`abs(x)`**: `PyNumber_Absolute`, the unary operator's protocol. -/
def absFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.abs
  let ps ← params sig 1 args kwargs
  unaryOp .abs (← given "abs" ps 0)

/-- The argument `v` as a `Py_ssize_t`, as Argument Clinic's converter takes it: through
`__index__`, with CPython's `TypeError` and `OverflowError`. -/
def ssizeArg [PyCalls m V] (v : V) : m Int := do
  let some n ← indexValue? v |
    raiseBuiltin "TypeError" s!"'{← typeName v}' object cannot be interpreted as an integer"
  if n > (Format.ssizeMax : Int) || n < Arith.ssizeMin then
    raiseBuiltin "OverflowError" "Python int too large to convert to C ssize_t"
  return n

/-- `divmod` of two numbers as a tuple of two numbers, with CPython's errors. -/
def numDivmod [PyCalls m V] (a b : Arith.Num) : m V := do
  match Arith.divmod a b with
  | .ok (q, r) =>
    let v (n : Arith.Num) : V := match n with
      | .int i => PyPure.imm (m := m) (.int i)
      | .bool x => PyPure.imm (m := m) (.bool x)
      | .float f => PyPure.imm (m := m) (.float f)
    return PyPure.imm (m := m) (.tuple #[v q, v r])
  | .error f => ofFailure f

/-- **`divmod(a, b)`**, `PyNumber_Divmod`: two numbers directly; else `__divmod__` and
`__rdivmod__` by the binary protocol; else `TypeError`. -/
def divmodFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.divmod
  let ps ← params sig 2 args kwargs
  let a ← given "divmod" ps 0
  let b ← given "divmod" ps 1
  symCheck a b
  if !(← isUserObject a) && !(← isUserObject b) then
    if let (some x, some y) := (← numOf? a, ← numOf? b) then return ← numDivmod x y
  if (← isUserObject a) || (← isUserObject b) then
    if let some r ← binaryDunder "__divmod__" "__rdivmod__" a b then return r
  otherCheck a b
  raiseBuiltin "TypeError"
    s!"unsupported operand type(s) for divmod(): '{← typeName a}' and '{← typeName b}'"

/-- **`hex(x)`**, `PyNumber_ToBase(x, 16)`: `x` through `PyNumber_Index`. -/
def hexFn [PyWrites m V] (_self args kwargs : V) : m V := do
  let sig := Signatures.hex
  let ps ← params sig 1 args kwargs
  let x ← given "hex" ps 0
  let some n ← indexValue? x |
    raiseBuiltin "TypeError" s!"'{← typeName x}' object cannot be interpreted as an integer"
  let s := if n < 0 then s!"-0x{String.ofList (Nat.toDigits 16 n.natAbs)}"
    else s!"0x{String.ofList (Nat.toDigits 16 n.toNat)}"
  return strValue (m := m) s

/-! ## The numeric dunders of `int` and `float` -/

/-- The `n` arguments of a slot wrapper `name` of `int` or `float`, after `self`, with
`check_num_args`'s errors. -/
def wrapperArgs [PyReads m V] (name : String) (n : Nat) (args kwargs : V) : m (Array V) := do
  let b ← bindBuiltinArgs { name, qualname := name, style := .wrapper, maxpos := n } args kwargs
  return b.params.filterMap id

/-- `self`'s number, for a slot of the built-in type `t`; a model invariant when the descriptor
check let another value through. -/
def selfNum [PyReads m V] (t : String) (self : V) : m Arith.Num := do
  let some x ← numOf? self | PyPure.modelInvariant s!"a slot of {t} on a value that is not a number"
  return x

/-- The other operand of a binary slot of `int` (`int` or `bool` only, `CHECK_BINOP`) or of
`float` (`int`, `bool` or `float`, `CONVERT_TO_DOUBLE`): none gives `NotImplemented`. -/
def otherNum [PyReads m V] (isFloat : Bool) (v : V) : m (Option Arith.Num) := do
  match ← numOf? v with
  | some (.float f) => return if isFloat then some (.float f) else none
  | n => return n

/-- **`int.__divmod__` and `float.__divmod__`** (`rev` for `__rdivmod__`). -/
def numDivmodSlot [PyWrites m V] (isFloat rev : Bool) (self args kwargs : V) : m V := do
  let t := if isFloat then "float" else "int"
  let xs ← wrapperArgs (if rev then "__rdivmod__" else "__divmod__") 1 args kwargs
  let some o := xs[0]? | PyPure.modelInvariant "a binary slot without its operand"
  let x ← selfNum t self
  let some y ← otherNum isFloat o | return PyPure.imm (m := m) .notImplemented
  let a ← if isFloat then Arith.Num.float <$> ofExceptFloat x else pure x
  if rev then numDivmod y a else numDivmod a y
where
  ofExceptFloat (x : Arith.Num) : m UInt64 := do
    match x.toFloat with
    | .ok f => pure f
    | .error e => ofFailure e

/-- An `int` value of the number `n`. -/
def intValue [PyPure m V] (n : Int) : V := PyPure.imm (m := m) (.int n)

/-- **`int.__abs__`, `__int__`, `__trunc__` and `__float__`** (`__trunc__` a method, the others
slot wrappers): the exact `int` (an instance of a
subclass gives a plain `int`), and its `float` with `OverflowError` for a large one. -/
def intUnarySlot [PyWrites m V] (name : String) (self args kwargs : V) : m V := do
  if name == "__trunc__" then noArgsMethod .int "__trunc__" self args kwargs
  else discard <| wrapperArgs name 0 args kwargs
  let i ← match ← selfNum "int" self with
    | .int i => pure i
    | .bool b => pure (if b then 1 else 0)
    | .float _ => PyPure.modelInvariant "an int slot on a float"
  match name with
  | "__abs__" => return intValue (m := m) i.natAbs
  | "__float__" =>
    match Format.intToFloat i with
    | .ok f => return PyPure.imm (m := m) (.float f)
    | .error e => ofFailure e
  | _ => return intValue (m := m) i

/-- **`float.__abs__`, `__float__`, `__int__` and `__trunc__`**: an exact `float` (an instance of
a subclass gives a plain `float`), or its truncation with CPython's errors for `inf` and `nan`. -/
def floatUnarySlot [PyWrites m V] (name : String) (self args kwargs : V) : m V := do
  if name == "__trunc__" then noArgsMethod .float "__trunc__" self args kwargs
  else discard <| wrapperArgs name 0 args kwargs
  let .float f ← selfNum "float" self | PyPure.modelInvariant "a float slot on another number"
  match name with
  | "__abs__" => return PyPure.imm (m := m) (.float (Arith.fabs f))
  | "__float__" => return PyPure.imm (m := m) (.float f)
  | _ =>
    match Arith.floatToInt f with
    | .ok i => return intValue (m := m) i
    | .error e => ofFailure e

/-- This file's bodies of the built-in functions. -/
def functionsFunction : Builtin → Option BuiltinImpl
  | .getattr => some fun {_} {_} [_] [_] => getattrFn
  | .hasattr => some fun {_} {_} [_] [_] => hasattrFn
  | .setattr => some fun {_} {_} [_] [_] => setattrFn
  | .callable => some fun {_} {_} [_] [_] => callableFn
  | .issubclass => some fun {_} {_} [_] [_] => issubclassFn
  | .hash => some fun {_} {_} [_] [_] => hashFn
  | .abs => some fun {_} {_} [_] [_] => absFn
  | .divmod => some fun {_} {_} [_] [_] => divmodFn
  | .hex => some fun {_} {_} [_] [_] => hexFn
  | _ => none

/-- This file's bodies of the numeric dunders of `int` and `float`. -/
def numbersMethod : Builtin → String → Option BuiltinImpl
  | .int, "__divmod__" => some fun {_} {_} [_] [_] => numDivmodSlot false false
  | .int, "__rdivmod__" => some fun {_} {_} [_] [_] => numDivmodSlot false true
  | .float, "__divmod__" => some fun {_} {_} [_] [_] => numDivmodSlot true false
  | .float, "__rdivmod__" => some fun {_} {_} [_] [_] => numDivmodSlot true true
  | .int, n =>
    if ["__abs__", "__int__", "__trunc__", "__float__"].contains n then
      some fun {_} {_} [_] [_] => intUnarySlot n
    else none
  | .float, n =>
    if ["__abs__", "__int__", "__trunc__", "__float__"].contains n then
      some fun {_} {_} [_] [_] => floatUnarySlot n
    else none
  | _, _ => none

end

end

end StrataPython.Dyn.Sem.Library
