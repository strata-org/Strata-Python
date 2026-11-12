/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Mapping

set_option autoImplicit false

/-!
# `repr`, `str`, `ascii` and `format`

Generic over the record of primitives, CPython 3.12's `PyObject_Repr`, `PyObject_Str`,
`PyObject_ASCII` and `PyObject_Format`, and the `__repr__` of the built-in types:

* `reprOf v`: one C level deeper, the type's `__repr__`, whose result must be a `str`.  A user
  `__repr__` is called; a built-in type's runs on the value's built-in part (`builtinRepr`).  A
  list, dict, set or tuple enters the `repr` guard (`Py_ReprEnter`), so that one met again inside
  its own `repr` prints as `[...]`, `{...}`, `set(...)` or `(...)`.  The semantics can't tell a
  tuple from an equal one, so a tuple met inside the `repr` of a tuple with the same items stops
  with a gap.
* `strOf v`: an exact `str` as it is; else, one C level deeper, the type's `__str__`, whose
  result must be a `str`: `object`'s runs the type's `__repr__`, `str`'s copies the `str` part.
* `asciiOf v`: `repr`, with its non-ASCII characters escaped.
* `formatOf v spec`: an exact `str`, or the `str` of an exact `int`, for an empty spec; else the
  type's `__format__`, whose result must be a `str`: `int`'s, `float`'s and `str`'s run the format
  spec language of `Format` on the built-in part (`str`'s stops with a gap on an instance of a
  subclass of `str`), and `object`'s takes only an empty spec.

A `repr` that shows an address (`object.__repr__`, functions, modules, methods) stops with a gap.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

section
variable {m : Type → Type 1} {V : Type}

/-- The `str` whose text is `s`. -/
def strValue [PyPure m V] (s : String) : V := PyPure.imm (m := m) (.str (.ofString s))

/-- The text of `v` if it is a `str` or an instance of a subclass of `str` (`PyUnicode_Check`). -/
def strText? [PyReads m V] (v : V) : m (Option String) := do
  match ← PyPure.immView v with
  | some (.str s) => pure (some s.s)
  | some _ => pure none
  | none => return (← PyReads.strView v).map (·.s)

/-- The number of `v`, an `int`, `bool` or `float` or an instance of a subclass of `int` or `float`. -/
def numOf? [PyReads m V] (v : V) : m (Option Arith.Num) := do
  match ← PyPure.immView v with
  | some (.int i) => pure (some (.int i))
  | some (.bool x) => pure (some (.bool x))
  | some (.float f) => pure (some (.float f))
  | some _ => pure none
  | none => PyReads.numView v

/-- The octets of `v`, a `bytes` or an instance of a subclass of `bytes`. -/
def bytesPart? [PyReads m V] (v : V) : m (Option (Array UInt8)) := do
  match ← PyPure.immView v with
  | some (.bytes x) => pure (some x)
  | some _ => pure none
  | none => PyReads.bytesView v

/-- `r`, the result of the dunder `name`, if it is a `str`; else CPython's `TypeError`. -/
def checkStrResult [PyReads m V] (name : String) (r : V) : m V := do
  if (← strText? r).isNone then
    raiseBuiltin "TypeError" s!"{name} returned non-string (type {← typeName r})"
  pure r

/-- The text of `r`, a result that `checkStrResult` has checked. -/
def textOf [PyReads m V] (r : V) : m String := do
  let some s ← strText? r | PyPure.modelInvariant "a repr or str that is not a str"
  pure s

/-- The decimal text of `i`, or CPython's `ValueError` past the digit limit. -/
def intText [PyCalls m V] (i : Int) : m String :=
  match Format.intRepr i with
  | .ok s => pure s
  | .error f => ofFailure f

/-- `s`, or `Format.tooLong`'s gap when it is longer than `Format.maxLength`. -/
def boundedText [PyCalls m V] (s : String) : m String :=
  if s.length > Format.maxLength then ofFailure Format.tooLong else pure s

/-- A tuple's `repr` from its elements' `repr`s: in parentheses, with a trailing comma for one
element. -/
def tupleBody (parts : Array String) : String :=
  if parts.size == 1 then s!"({parts[0]!},)" else s!"({", ".intercalate parts.toList})"

/-- Whether the built-in type `b` is in the MRO of the class `t`: whether a dunder of `b`'s table
that `t` found applies to an instance of `t`, rather than having been taken by `t` from another
type (`__repr__ = int.__repr__`). -/
def builtinIn [PyReads m V] (t : V) (b : Builtin) : m Bool := do
  let some mro ← mroOf t | return false
  inMro (PyPure.imm (m := m) (.builtin b)) mro

/-- The steps that `list_repr` and `dict_repr` take at most, past which a walk stops with a gap. -/
def reprWalkFuel : Nat := 2 ^ 20

mutual
/-- **`repr(v)`**, CPython's `PyObject_Repr`, with `n` the steps left: one C level deeper, the
type's `__repr__` (`reprCore`), whose result must be a `str`. -/
def reprN [PyCalls m V] : Nat → V → m V
  | 0, _ => PyPure.gap "a repr nested deeper than the model follows"
  | n + 1, v => PyReads.withDepth 1 do checkStrResult "__repr__" (← reprCore n v)

/-- The type's `__repr__` of `v`, as `tp_repr` runs it: an immediate's (`immRepr`); a built-in
type's on the value's built-in part (`builtinRepr`), or its body in the tables where
`builtinRepr` has none; a user one called. -/
def reprCore [PyCalls m V] : Nat → V → m V
  | 0, _ => PyPure.gap "a repr nested deeper than the model follows"
  | n + 1, v => do
    if let some i ← PyPure.immView v then return strValue (m := m) (← immRepr n i)
    let t ← PyReads.classOf v
    let some f ← lookupType t "__repr__" | PyPure.modelInvariant "a type without __repr__"
    if let some (.descr b "__repr__" _) ← PyPure.immView f then
      if ← builtinIn t b then
        if let some s ← builtinRepr n b v then return strValue (m := m) s
    -- `slot_tp_repr`: an exception while the dunder binds is cleared, and CPython gives the
    -- default `repr`, which shows the address.
    let some g ← bindMaybe f v t |
      PyPure.gap "the default repr of an object whose __repr__ raises while it binds, which shows its address"
    callSlotN dispatchDepth "__repr__" f t g (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)

/-- `repr` of an immediate. -/
def immRepr [PyCalls m V] : Nat → Imm V → m String
  | 0, _ => PyPure.gap "a repr nested deeper than the model follows"
  | _ + 1, .none => pure "None"
  | _ + 1, .notImplemented => pure "NotImplemented"
  | _ + 1, .ellipsis => pure "Ellipsis"
  | _ + 1, .bool b => pure (if b then "True" else "False")
  | _ + 1, .int i => intText i
  | _ + 1, .float f => pure (Format.floatRepr f)
  | _ + 1, .str s => pure (Format.strRepr s.s)
  | _ + 1, .bytes b => pure (Format.bytesRepr b)
  | n + 1, .tuple xs => tupleRepr n (PyPure.imm (m := m) (.tuple xs)) xs
  | n + 1, .range a b c => do
    -- `range_repr`'s `%R` of each bound, a `repr` each.
    let ta ← textOf (← reprN n (PyPure.imm (m := m) (.int a)))
    let tb ← textOf (← reprN n (PyPure.imm (m := m) (.int b)))
    if c == 1 then return s!"range({ta}, {tb})"
    return s!"range({ta}, {tb}, {← textOf (← reprN n (PyPure.imm (m := m) (.int c)))})"
  | n + 1, .slice a b c => do
    return s!"slice({← textOf (← reprN n a)}, {← textOf (← reprN n b)}, {← textOf (← reprN n c)})"
  | _ + 1, .symHash _ => PyPure.gap "the repr of an int whose number depends on the hash seed is not modelled yet"
  | _ + 1, .builtin b => do
    if b.info.kind == .type then typeRepr (PyPure.imm (m := m) (.builtin b))
    else if b.info.kind == .function then pure s!"<built-in function {b.info.name}>"
    else PyPure.gap s!"the repr of the built-in {b.info.name} is not modelled yet"
  | _ + 1, .bound _ _ _ .tpNew => PyPure.modelInvariant "the repr of a type's tp_new"
  | _ + 1, .descr .. | _ + 1, .bound .. | _ + 1, .method .. =>
    PyPure.gap "the repr of a method or a descriptor of a built-in type is not modelled yet"
  | _ + 1, .traceback => PyPure.gap "the repr of a traceback shows its address"

/-- `tuple_repr` of the elements `xs`, whose guard key is `key`: `()`, `(...)` for a tuple met
again, else the `repr` of each element. -/
def tupleRepr [PyCalls m V] : Nat → V → Array V → m String
  | 0, _, _ => PyPure.gap "a repr nested deeper than the model follows"
  | n + 1, key, xs => do
    if xs.isEmpty then return "()"
    match ← PyReads.reprCheck key with
    | .hit => return "(...)"
    | .unknown => PyPure.gap "the repr of a tuple met again, or of an equal tuple, is not modelled yet"
    | .fresh => PyReads.withRepr key do
      let parts ← xs.toList.mapM fun x => do textOf (← reprN n x)
      boundedText (tupleBody parts.toArray)

/-- The `repr` of the built-in part of the object `v` by the `__repr__` of the built-in type `b`,
or `none` when the tables give that `__repr__`'s body. -/
def builtinRepr [PyCalls m V] : Nat → Builtin → V → m (Option String)
  | 0, _, _ => PyPure.gap "a repr nested deeper than the model follows"
  | n + 1, b, v => do
    match b with
    | .list => return some (← listRepr n v)
    | .dict => return some (← dictRepr n v)
    | .«set» | .«frozenset» => return some (← setRepr n v)
    | .tuple =>
      let some xs ← PyReads.tupleView v | PyPure.modelInvariant "tuple.__repr__ of a value that is not a tuple"
      return some (← tupleRepr n v xs)
    | .int | .bool | .float =>
      match ← numOf? v with
      | some (.int i) => return some (← intText i)
      | some (.bool x) => return some (if x then "True" else "False")
      | some (.float f) => return some (Format.floatRepr f)
      | none => PyPure.modelInvariant "a number's __repr__ of a value that is not a number"
    | .str =>
      let some s ← strText? v | PyPure.modelInvariant "str.__repr__ of a value that is not a str"
      return some (Format.strRepr s)
    | .bytes =>
      let some x ← bytesPart? v | PyPure.modelInvariant "bytes.__repr__ of a value that is not a bytes"
      return some (Format.bytesRepr x)
    | .type => return some (← typeRepr v)
    | .«classmethod» | .«staticmethod» =>
      -- `cm_repr` and `sm_repr`: `<classmethod(callable)>`.
      let f? ← match ← PyReads.objView v with
        | some (.classmethod f?) => pure f?
        | some (.staticmethod f?) => pure f?
        | _ => PyPure.modelInvariant "the repr of a value that is not a classmethod or a staticmethod"
      let some f := f? | PyPure.gap "the repr of an unset classmethod or staticmethod is not modelled yet"
      return some s!"<{b.info.name}({← textOf (← reprN n f)})>"
    | .object | .function | .module =>
      PyPure.gap "a repr that shows an object's address is not modelled yet"
    | _ => return none

/-- `list_repr`: `[]`, `[...]` for a list met again, else the `repr` of each element, the list
read again before each one, since a `__repr__` may change it. -/
def listRepr [PyCalls m V] : Nat → V → m String
  | 0, _ => PyPure.gap "a repr nested deeper than the model follows"
  | n + 1, v => do
    let some (xs, _) ← PyReads.listView v | PyPure.modelInvariant "list.__repr__ of a value that is not a list"
    if xs.isEmpty then return "[]"
    match ← PyReads.reprCheck v with
    | .hit => return "[...]"
    | .unknown => PyPure.gap "the repr of a tuple met again, or of an equal tuple, is not modelled yet"
    | .fresh => PyReads.withRepr v do
      let mut parts : List String := []
      let mut len := 1
      for i in [0:reprWalkFuel] do
        let some (ys, _) ← PyReads.listView v | PyPure.modelInvariant "a list that is no longer a list"
        let some x := ys[i]? | return "[" ++ ", ".intercalate parts.reverse ++ "]"
        let s ← textOf (← reprN n x)
        len := len + s.length + 2
        if len > Format.maxLength then ofFailure Format.tooLong
        parts := s :: parts
      PyPure.gap "a list that grows during its repr past the model's walk"

/-- `dict_repr`: `{...}` for a dict met again, `{}`, else `key: value` for each entry, the key's
`repr` first, the entries walked by position as `PyDict_Next` walks the live table. -/
def dictRepr [PyCalls m V] : Nat → V → m String
  | 0, _ => PyPure.gap "a repr nested deeper than the model follows"
  | n + 1, v => do
    match ← PyReads.reprCheck v with
    | .hit => return "{...}"
    | .unknown => PyPure.gap "the repr of a tuple met again, or of an equal tuple, is not modelled yet"
    | .fresh => PyReads.withRepr v do
      if (← PyReads.dictLen v) == 0 then return "{}"
      let (_, version) ← PyReads.dictFlags v
      let mut parts : List String := []
      let mut len := 1
      let mut pos := 0
      for _ in [0:reprWalkFuel] do
        compactGap v version
          "a dict whose entries may move during its repr is not modelled yet"
        let some (j, k, x) ← dictEntryFrom v pos | return "{" ++ ", ".intercalate parts.reverse ++ "}"
        let ks ← textOf (← reprN n k)
        let xs ← textOf (← reprN n x)
        len := len + ks.length + xs.length + 4
        if len > Format.maxLength then ofFailure Format.tooLong
        parts := s!"{ks}: {xs}" :: parts
        pos := j + 1
      PyPure.gap "a dict that grows during its repr past the model's walk"

/-- `set_repr`, for a set or a frozenset or an instance of a subclass of either: `T(...)` for one
met again, `T()` when empty, else the `repr` of the list of its members, in braces, after `T(`
unless it is an exact `set`.  An order that the model doesn't know stops with a gap. -/
def setRepr [PyCalls m V] : Nat → V → m String
  | 0, _ => PyPure.gap "a repr nested deeper than the model follows"
  | n + 1, v => do
    let t ← PyReads.classOf v
    let name ← tpNameOf t
    match ← PyReads.reprCheck v with
    | .hit => return s!"{name}(...)"
    | .unknown => PyPure.gap "the repr of a tuple met again, or of an equal tuple, is not modelled yet"
    | .fresh => PyReads.withRepr v do
      let some vw ← PyReads.setView v | PyPure.modelInvariant "set.__repr__ of a value that is not a set"
      if vw.unordered.isEmpty then return s!"{name}()"
      -- A set of one member has one order.
      let some ms := if vw.unordered.size ≤ 1 then some vw.unordered else vw.inOrder? |
        PyPure.gap "the repr of a set whose order the model doesn't know is not modelled yet"
      -- `PySequence_List`, then `PyObject_Repr` of that list: one C level deeper.
      let parts ← PyReads.withDepth 1 do ms.toList.mapM fun (x, _) => do textOf (← reprN n x)
      let body ← boundedText ("{" ++ ", ".intercalate parts ++ "}")
      if (← PyPure.immView t) matches some (.builtin .«set») then return body
      return s!"{name}({body})"
end

/-- The steps that a `repr` from the current C depth may take: four per nested level, the most
that one level takes (for a list: `reprN`, `reprCore`, `builtinRepr` and `listRepr`). -/
def reprFuel [PyReads m V] : m Nat := return 4 * (cDepthLimit + 1 - (← PyReads.depthC)) + 4

/-- **`repr(v)`**, CPython's `PyObject_Repr`. -/
def reprOf [PyCalls m V] (v : V) : m V := do reprN (← reprFuel) v

/-- The text of `repr(v)`. -/
def reprTextOf [PyCalls m V] (v : V) : m String := do textOf (← reprOf v)

/-- **`b.__repr__(v)`** called as a method, for the built-in type `b` and its instance `v`: the
`repr` of `v`'s built-in part (`int.__repr__(True)` is `1`).  `object.__repr__` shows an address,
so it stops with a gap. -/
def builtinReprOf [PyCalls m V] (b : Builtin) (v : V) : m V := do
  let n ← reprFuel
  match b, ← PyPure.immView v with
  | .object, _ => PyPure.gap "a repr that shows an object's address is not modelled yet"
  | .int, some (.bool x) => return strValue (m := m) (if x then "1" else "0")
  | _, some i => return strValue (m := m) (← immRepr n i)
  | _, none =>
    let some s ← builtinRepr n b v | PyPure.modelInvariant s!"no __repr__ body for {b.info.name}"
    return strValue (m := m) s

/-- The type's `__repr__` of `v`, as `object.__str__` runs it: `tp_repr`, with no check of its
result. -/
def reprCoreOf [PyCalls m V] (v : V) : m V := do reprCore (← reprFuel) v

/-- **`str(v)`**, CPython's `PyObject_Str`: an exact `str` as it is; else, one C level deeper,
the type's `__str__`, whose result must be a `str`.  `object.__str__` runs the type's `__repr__`
(`tp_repr`, without `PyObject_Repr`'s check), `str.__str__` gives the `str` part, and
`bytes.__str__` the `repr`. -/
def strOf [PyCalls m V] (v : V) : m V := do
  if (← PyPure.immView v) matches some (.str _) then return v
  let n ← reprFuel
  PyReads.withDepth 1 do
    let t ← PyReads.classOf v
    let some f ← lookupType t "__str__" | PyPure.modelInvariant "a type without __str__"
    match ← PyPure.immView f with
    | some (.descr .object "__str__" _) => checkStrResult "__str__" (← reprCore n v)
    | some (.descr .str "__str__" _) =>
      if let some s ← strText? v then return strValue (m := m) s
      checkStrResult "__str__" (← callFound "__str__" f v t #[] (← PyPure.allocDict))
    | some (.descr .bytes "__str__" _) =>
      if let some x ← bytesPart? v then return strValue (m := m) (Format.bytesRepr x)
      checkStrResult "__str__" (← callFound "__str__" f v t #[] (← PyPure.allocDict))
    | _ => checkStrResult "__str__" (← callFound "__str__" f v t #[] (← PyPure.allocDict))

/-- The text of `str(v)`. -/
def strTextOf [PyCalls m V] (v : V) : m String := do textOf (← strOf v)

/-- **`ascii(v)`**, CPython's `PyObject_ASCII`: `repr(v)`, as it is when it is ASCII, else with
its non-ASCII characters escaped. -/
def asciiOf [PyCalls m V] (v : V) : m V := do
  let r ← reprOf v
  let s ← textOf r
  if s.toList.all (·.toNat < 0x80) then return r
  return strValue (m := m) (← boundedText (Format.asciiEscape s))

/-- The `str` of a formatting's result `r`, or `ofFailure`'s error. -/
def formatResult [PyCalls m V] (r : Except Format.Failure String) : m V :=
  match r with
  | .ok s => return strValue (m := m) s
  | .error f => ofFailure f

/-- The `__format__` of the built-in type `b` on the value `v` of the class `t` with the spec
`sp`, or `none` when the tables give that `__format__`'s body.  An empty spec gives `str(v)` (the
`format_obj` of `int`, `float` and `str`, and `object.__format__`); `str`'s with another spec, on
an instance of a subclass of `str`, stops with a gap, since CPython may give that instance. -/
def builtinFormat [PyCalls m V] (b : Builtin) (v t : V) (sp : String) : m (Option V) := do
  match b with
  | .object =>
    if !sp.isEmpty then
      raiseBuiltin "TypeError" s!"unsupported format string passed to {Format.cTypeName (← tpNameOf t)}.__format__"
    return some (← strOf v)
  | .int | .float | .str =>
    if sp.isEmpty then
      -- `format_obj` writes `str(v)` through the unicode writer, which gives an empty instance of
      -- a subclass of `str` as the exact `''`, and any other one as it is.
      let r ← strOf v
      if (← PyPure.immView r).isNone && (← strText? r) == some "" then
        return some (strValue (m := m) "")
      return some r
    let tn ← tpNameOf t
    match b with
    | .str =>
      -- CPython gives an instance of a subclass of `str` itself when the spec changes nothing.
      if (← PyPure.immView v).isNone then
        PyPure.gap "str.__format__ of an instance of a subclass of str is not modelled yet"
      let some x ← strText? v | PyPure.modelInvariant "str.__format__ of a value that is not a str"
      return some (← formatResult (Format.formatStr x sp tn))
    | _ =>
      match ← numOf? v with
      | some (.int i) => return some (← formatResult (Format.formatInt i sp tn))
      | some (.bool x) => return some (← formatResult (Format.formatInt (if x then 1 else 0) sp tn))
      | some (.float f) => return some (← formatResult (Format.formatFloat f sp tn))
      | none => PyPure.modelInvariant "a number's __format__ of a value that is not a number"
  | _ => return none

/-- A `sep` or `end` keyword of `print`: a `str`, or `None` for the default `d`. -/
def printText [PyCalls m V] (what : String) (d : String) (v : V) : m String := do
  match ← PyPure.immView v with
  | some (.str s) => pure s.s
  | some .none => pure d
  | _ =>
    -- An instance of a subclass of `str` is accepted by CPython.
    userCheck v v
    raiseBuiltin "TypeError" s!"{what} must be None or a string, not {← typeName v}"

/-- **`print(*args, **kwargs)`**: the `str` of each argument (`strOf`), joined by `sep`, then `end`, written to
the output; `file` and `flush` stop with a gap.  As CPython's argument parsing does, an unknown
keyword raises before `sep` is checked, and `sep` is checked before `end`. -/
def printCall [PyWrites m V] (args kwargs : V) : m V := do
  let some (.tuple xs) ← PyPure.immView args | PyPure.modelInvariant "print: operand assumption failed"
  let mut sepV := none
  let mut endV := none
  for (k, v, _) in ← PyReads.dictEntries kwargs do
    let some (.str s) ← PyPure.immView k | raiseBuiltin "TypeError" "keywords must be strings"
    if s.s == "sep" then sepV := some v
    else if s.s == "end" then endV := some v
    else if s.s != "file" && s.s != "flush" then
      raiseBuiltin "TypeError" s!"'{s.s}' is an invalid keyword argument for print()"
  for (k, _, _) in ← PyReads.dictEntries kwargs do
    if let some (.str s) ← PyPure.immView k then
      if s.s == "file" || s.s == "flush" then
        PyPure.gap s!"print's keyword argument {s.s} is not modelled yet"
  let sep ← match sepV with | some v => printText "sep" " " v | none => pure " "
  let fin ← match endV with | some v => printText "end" "\n" v | none => pure "\n"
  -- Each argument is written as it is converted, as CPython does, so an error leaves the
  -- earlier ones written.
  for (x, i) in xs.toList.zipIdx do
    if i > 0 then PyWrites.write sep
    PyWrites.write (← strTextOf x)
  PyWrites.write fin
  pure (PyPure.imm (m := m) .none)

/-- **`BUILD_STRING`**: the concatenation of `parts`, each a `str`.  A part that is an instance of a
subclass of `str` (a `__format__` may give one) stops with a gap, since a `pure` operation reads
no object. -/
def concatStrs [PyPure m V] (parts : Array V) : m V := do
  let mut out := ""
  for p in parts do
    let some (.str s) ← PyPure.immView p |
      PyPure.gap "an f-string part that is an instance of a subclass of str is not modelled yet"
    out := out ++ s.s
    if out.length > Format.maxLength then PyPure.gap "not modelled: a result longer than 2 ^ 24 characters"
  return strValue (m := m) out

/-- **`format(v, spec)`**, CPython's `PyObject_Format`: for an empty spec, an exact `str` as it is
and an exact `int`'s `str`; else the type's `__format__` called with `spec`, whose result must be a
`str`. -/
def formatOf [PyCalls m V] (v spec : V) : m V := do
  let some sp ← strText? spec |
    raiseBuiltin "TypeError" s!"Format specifier must be a string, not {← typeName spec}"
  if sp.isEmpty then
    match ← PyPure.immView v with
    | some (.str _) => return v
    | some (.int _) => return ← strOf v
    | _ => pure ()
  let t ← PyReads.classOf v
  let some f ← lookupType t "__format__" | PyPure.modelInvariant "a type without __format__"
  if let some (.descr b "__format__" _) ← PyPure.immView f then
    if ← builtinIn t b then
      if let some r ← builtinFormat b v t sp then return r
  let r ← callFound "__format__" f v t #[spec] (← PyPure.allocDict)
  if (← strText? r).isNone then
    raiseBuiltin "TypeError" s!"__format__ must return a str, not {← typeName r}"
  pure r

end

end

end StrataPython.Dyn.Sem.Proto
