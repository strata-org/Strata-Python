/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Lookup
public import StrataPython.Dyn.Sem.Hash

set_option autoImplicit false

/-!
# Operators

Generic over the record of primitives, CPython 3.12's operators on the built-in immediates and
lists:

* `binaryOp`: the numbers (through `numBinary`), and `+` and `*` of `str`, `bytes`, `tuple` and
  `list` (`|` of two dicts and the operators of two sets are in `Proto/Containers.lean`);
* `unaryOp`, `truthy` and `notOp`;
* `richCompare`: the numbers (through `numCompare`), `str`, `bytes`, and `tuple` and `list` member
  by member (each member compared with the identity shortcut), `==` and `!=` of dicts entry by
  entry, sets by the subset order, and `==` and `!=` of values of two other kinds by identity.

A user object goes through its type's dunders, in the order of CPython's slots.  Any other case
raises CPython's `TypeError`, with its message, and an object of a built-in type whose operators
are not modelled yet (a `bytearray`, for example) stops with a gap.  A comparison of nested tuples counts its depth, as
CPython's C recursion count does, and stops with a gap before CPython's limit.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

/-- The depth of nested tuples that a hash follows (`hashN`), where it stops with a gap.  CPython
hashes nested tuples until its C recursion limit; nested comparisons count toward that limit
through `cDepthLimit` instead. -/
def compareDepth : Nat := 900

/-- The symbol of a binary operator in CPython's messages. -/
def binSymbol : Arith.BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .trueDiv => "/" | .floorDiv => "//" | .mod => "%"
  | .pow => "** or pow()" | .lshift => "<<" | .rshift => ">>" | .and => "&" | .or => "|"
  | .xor => "^"

/-- The symbol of an in-place operator in CPython's messages. -/
def inplaceSymbol : Arith.BinOp → String
  | .pow => "**="
  | op => binSymbol op ++ "="

/-- The symbol of a unary operator in CPython's messages. -/
def unarySymbol : Arith.UnaryOp → String
  | .neg => "unary -" | .pos => "unary +" | .invert => "unary ~" | .abs => "abs()"

/-- The symbol of a comparison in CPython's messages. -/
def cmpSymbol : Arith.CmpOp → String
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

/-- The comparison with its operands swapped: `a < b` is `b > a`. -/
def Arith.CmpOp.swap : Arith.CmpOp → Arith.CmpOp
  | .eq => .eq | .ne => .ne | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le

/-- Whether `op` holds for the order `o` of two values. -/
def holdsOrd (op : Arith.CmpOp) (o : Ordering) : Bool := op.holds (some o)

/-- The order of two arrays by `cmp` of their members, then by their sizes. -/
def lexOrd {α : Type} (cmp : α → α → Ordering) (xs ys : Array α) : Ordering :=
  let rec go : List α → List α → Ordering
    | [], [] => .eq
    | [], _ :: _ => .lt
    | _ :: _, [] => .gt
    | x :: xs, y :: ys => match cmp x y with
      | .eq => go xs ys
      | o => o
  go xs.toList ys.toList

section
variable {m : Type → Type 1} {V : Type}

/-- Whether `v` is an object whose type isn't built in. -/
def isUserObject [PyReads m V] (v : V) : m Bool := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return false
  return !((← PyPure.immView (← PyReads.classOf v)) matches some (.builtin _))

/-- A gap if either operand is a user object. -/
def userCheck [PyReads m V] (a b : V) : m Unit := do
  if (← isUserObject a) || (← isUserObject b) then PyPure.gap userGap

/-- The built-in types whose instances keep `object`'s `__eq__`, `__hash__` and `__bool__`: they
compare and hash by identity and are true.  A class (an instance of `type`) also has `|`, which
`binaryOpAs` gaps. -/
def hashesByAddr (b : Builtin) : Bool :=
  b.info.mro.contains .«BaseException» ||
  ["object", "type", "function", "module", "property", "classmethod", "staticmethod",
    "super"].contains b.info.name

/-- The elements of `v` if it is a list. -/
def listOf? [PyReads m V] (v : V) : m (Option (Array V)) := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return none
  return (← PyReads.listView v).map (·.1)

/-- The class of `v` if `v` is an object whose class is built in. -/
def builtinClass? [PyReads m V] (v : V) : m (Option Builtin) := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return none
  match ← PyPure.immView (← PyReads.classOf v) with
  | some (.builtin b) => pure (some b)
  | _ => pure none

/-- The built-in type that `v` is an instance of, or whose subclass's instance `v` is: the first
built-in type of the MRO of `v`'s class. -/
def builtinBase? [PyReads m V] (v : V) : m (Option Builtin) := do
  let t ← PyReads.classOf v
  if let some (.builtin b) ← PyPure.immView t then return some b
  let some mro ← mroOf t | return none
  for c in mro do
    if let some (.builtin b) ← PyPure.immView c then return some b
  return none

/-- The number `v`, or the built-in part of `v` when it is an instance of a subclass of `int` or
`float`, as an immediate; `none` for any other value. -/
def numPart? [PyReads m V] (v : V) : m (Option V) := do
  match ← PyPure.immView v with
  | some (.int _) | some (.bool _) | some (.float _) => return some v
  | some _ => return none
  | none =>
    if ← PyPure.isUndef v then return none
    return (← PyReads.numView v).map fun
      | .int i => PyPure.imm (m := m) (.int i)
      | .float f => PyPure.imm (m := m) (.float f)
      | .bool b => PyPure.imm (m := m) (.bool b)

/-- Whether `v` is a dict (not an instance of a subclass of `dict`). -/
def isDict [PyReads m V] (v : V) : m Bool := return (← builtinClass? v) matches some .dict

/-- Whether `v` is a frozenset, if it is a set or a frozenset (not an instance of a subclass). -/
def anySet? [PyReads m V] (v : V) : m (Option Bool) := do
  match ← builtinClass? v with
  | some .«set» => pure (some false)
  | some .«frozenset» => pure (some true)
  | _ => pure none

/-- Whether `v` is a dict or an instance of a subclass of `dict`. -/
def isDictLike [PyReads m V] (v : V) : m Bool := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return false
  return (← builtinBase? v) == some .dict

/-- `some frozen` if `v` is a set (`false`) or a frozenset (`true`), or an instance of a subclass
of one. -/
def anySetLike? [PyReads m V] (v : V) : m (Option Bool) := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return none
  match ← builtinBase? v with
  | some .«set» => pure (some false)
  | some .«frozenset» => pure (some true)
  | _ => pure none

/-- What the set `s` holds. -/
def setMembers [PyReads m V] (s : V) : m (SetView V) := do
  let some vw ← PyReads.setView s | PyPure.modelInvariant "setMembers: operand assumption failed"
  pure vw

/-- A gap if walking the dict `src`'s entries while inserting them into the dict or set `dst`
could run user code: CPython walks `src`'s live entries (and a dict update raises `RuntimeError`
when they change), and the model walks them as they were. -/
def guardDictWalk [PyReads m V] (src dst : V) : m Unit := do
  let dk ← if ← isDictLike dst then PyReads.dictWalkKinds dst else PyReads.setWalkKinds dst
  if WalkKinds.mayRunUser [← PyReads.dictWalkKinds src, dk] then
    PyPure.gap "a walk of a dict whose comparisons may run user code is not modelled yet"

/-- Whether a walk of the sets `sets`, comparing members, may run user code. -/
def mayRunUserWalk [PyReads m V] (sets : List V) : m Bool :=
  return WalkKinds.mayRunUser (← sets.mapM PyReads.setWalkKinds)

/-- The bound of a walk's steps over a table that the walk's comparisons may grow: it only ends
the recursion. -/
def walkFuel : Nat := 2 ^ 32

/-- A walk of the live table of the set `s` from slot `i` on, as CPython's `set_next` makes it:
`f k h` on each member `k` with its stored hash `h`, the table read again at each step, since a
comparison that `f` makes may change it; the walk stops where `f` gives `false`, and gives whether
it went to the end. A table whose layout is inexact stops it with a gap (`setSlotAt`). -/
def setWalkLive [PyReads m V] (s : V) (f : V → Hash → m Bool) : Nat → Nat → m Bool
  | 0, _ => PyPure.gap "a walk of a set whose table keeps growing"
  | fuel + 1, i => do
    match ← PyReads.setSlotAt s i with
    | .past => return true
    | .hole => setWalkLive s f fuel (i + 1)
    | .entry k h => if ← f k h then setWalkLive s f fuel (i + 1) else return false

/-- Whether every member of the set `a` is in the set `b`, `eqv` comparing members: CPython's
`set_issubset`, walking `a`'s live table when a comparison may run user code. -/
def setIsSubset [PyReads m V] (eqv : V → V → m Bool) (a b : V) : m Bool := do
  if (← PyReads.setLen a) > (← PyReads.setLen b) then return false
  if ← mayRunUserWalk [a, b] then
    return ← setWalkLive a (fun k h => PyReads.setFind b k (some h) fun stored => eqv stored k)
      walkFuel 0
  let va ← setMembers a
  for (k, h) in va.unordered do
    if !(← PyReads.setFind b k (some h) fun stored => eqv stored k) then return false
  return true

/-- `a op b` for two sets or frozensets: `==` by size and `set_issubset`, and the subset order. -/
def setCompare [PyReads m V] (eqv : V → V → m Bool) (op : Arith.CmpOp) (a b : V) : m Bool := do
  let na ← PyReads.setLen a
  let nb ← PyReads.setLen b
  -- CPython answers `==` of two frozensets (or instances of subclasses of `frozenset`) with
  -- different cached hashes without a walk.
  if (op == .eq || op == .ne) && na == nb && (← anySetLike? a) == some true &&
      (← anySetLike? b) == some true && (← mayRunUserWalk [a, b]) then
    PyPure.gap "== of two frozensets whose members may run user code is not modelled yet"
  match op with
  | .eq => return na == nb && (← setIsSubset eqv a b)
  | .ne => return !(na == nb && (← setIsSubset eqv a b))
  | .le => setIsSubset eqv a b
  | .ge => setIsSubset eqv b a
  | .lt => return na < nb && (← setIsSubset eqv a b)
  | .gt => return na > nb && (← setIsSubset eqv b a)

/-- Whether `v` is an object of a built-in type whose operators are not modelled yet: not a list
or a dict, and not of a type that `hashesByAddr`. -/
def isOtherObject [PyReads m V] (v : V) : m Bool := do
  if (← PyPure.immView v).isSome || (← PyPure.isUndef v) then return false
  if ← isUserObject v then return false
  if (← listOf? v).isSome then return false
  match ← builtinClass? v with
  | some .dict | some .«set» | some .«frozenset» => return false
  | some b => return !hashesByAddr b
  | none => return true

/-- A gap if either operand is an object whose type's operators are not modelled yet. -/
def otherCheck [PyReads m V] (a b : V) : m Unit := do
  if (← isOtherObject a) || (← isOtherObject b) then
    PyPure.gap "the operators of this built-in type are not modelled yet"

/-- CPython's `PyNumber_Index` on `v`: the `int` that it is (a `bool` as `0` or `1`, an instance
of a subclass of `int` as its number), or the `int` that its type's `__index__` gives; `none` if
its type has no `__index__`. -/
def indexValue? [PyCalls m V] (v : V) : m (Option Int) := do
  match ← PyPure.immViewAll v with
  | some (.int i) => return some i
  | some (.bool b) => return some (if b then 1 else 0)
  | some (.symHash _) => PyPure.gap "an index whose number depends on the hash seed"
  | some _ => return none
  | none =>
    if ← PyPure.isUndef v then return none
    if let some (.int i) ← PyReads.numView v then return some i
    if !(← isUserObject v) then return none
    let t ← PyReads.classOf v
    let some f ← lookupType t "__index__" | return none
    let g ← descrGetN dispatchDepth f (some v) t
    let r ← callN dispatchDepth g (PyPure.imm (m := m) (.tuple #[])) (← PyPure.allocDict)
    match ← PyPure.immView r with
    | some (.int i) => return some i
    | some (.bool _) => PyPure.gap indexWarnGap
    | _ =>
      if (← PyReads.numView r) matches some (.int _) then PyPure.gap indexWarnGap
      raiseBuiltin "TypeError" s!"__index__ returned non-int (type {← typeName r})"

/-- The repetition count of a sequence: `n` as `PyNumber_Index` converts it, a negative one
counted as `0`; `none` if `n` has no `__index__`.  A count that a C `Py_ssize_t` can't hold raises
`OverflowError`, as `PyNumber_AsSsize_t` does. -/
def repeatCount [PyCalls m V] (n : V) : m (Option Nat) := do
  let some i ← indexValue? n | return none
  if i < Arith.ssizeMin ∨ i > (Format.ssizeMax : Int) then
    raiseBuiltin "OverflowError" s!"cannot fit '{← typeName n}' into an index-sized integer"
  pure (some i.toNat)

/-- The `str`, `bytes` or `tuple` that `v` is, or that the built-in part of `v` is when `v` is an
instance of a subclass of one of them, as an immediate. -/
def seqImm? [PyReads m V] (v : V) : m (Option (Imm V)) := do
  match ← PyPure.immView v with
  | some (.str s) => return some (.str s)
  | some (.bytes b) => return some (.bytes b)
  | some (.tuple xs) => return some (.tuple xs)
  | some _ => return none
  | none =>
    if ← PyPure.isUndef v then return none
    if let some s ← PyReads.strView v then return some (.str s)
    if let some b ← PyReads.bytesView v then return some (.bytes b)
    if let some xs ← PyReads.tupleView v then return some (.tuple xs)
    return none

/-- The largest repetition that the model computes, in elements: beyond it, CPython may raise
`MemoryError`, which depends on the machine. -/
def maxRepeat : Nat := 2 ^ 28

/-- `xs * n`, as CPython repeats a sequence: empty for an empty `xs` or `n = 0`. -/
def repeatArray {α : Type} (xs : Array α) (n : Nat) : Array α :=
  if xs.isEmpty then #[] else (List.replicate n xs).foldl (· ++ ·) #[]

/-- `s * n` and `n * s` for a `str`, a `bytes`, a `tuple` or a list `s` and a count `n`; `none`
if the operands are not such a pair. -/
def repeatSeq [PyCalls m V] (s n : V) : m (Option V) := do
  -- The count is converted only for a sequence: `2**100 * None` raises `TypeError`.
  let isSeq := (← listOf? s).isSome || (← seqImm? s).isSome
  if !isSeq then return none
  let some k ← repeatCount n | return none
  if let some xs ← listOf? s then
    if xs.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
    return some (← PyPure.allocList (repeatArray xs k))
  match ← seqImm? s with
  | some (.str t) =>
    if t.s.isEmpty || k == 0 then return some (PyPure.imm (m := m) (.str (.ofString "")))
    if t.s.length * k > maxRepeat then PyPure.gap "a repetition too large to model"
    return some (PyPure.imm (m := m) (.str (.ofString (String.join (List.replicate k t.s)))))
  | some (.bytes b) =>
    if b.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
    return some (PyPure.imm (m := m) (.bytes (repeatArray b k)))
  | some (.tuple xs) =>
    if xs.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
    return some (PyPure.imm (m := m) (.tuple (repeatArray xs k)))
  | _ => return none

/-- `a + b` for two `str`s, two `bytes`, two `tuple`s or two lists, or instances of subclasses of
them; `none` otherwise. -/
def concatSeq [PyReads m V] (a b : V) : m (Option V) := do
  if let some xs ← listOf? a then
    if let some ys ← listOf? b then return some (← PyPure.allocList (xs ++ ys))
  match ← seqImm? a, ← seqImm? b with
  | some (.str x), some (.str y) => return some (PyPure.imm (m := m) (.str (x.append y)))
  | some (.bytes x), some (.bytes y) => return some (PyPure.imm (m := m) (.bytes (x ++ y)))
  | some (.tuple x), some (.tuple y) => return some (PyPure.imm (m := m) (.tuple (x ++ y)))
  | _, _ => return none

/-- The name of `v`'s type if it is a `str`, a `bytes`, a `tuple` or a list, or of the one of them
that `v`'s type derives from. -/
def seqName? [PyReads m V] (v : V) : m (Option String) := do
  match ← seqImm? v with
  | some (.str _) => pure (some "str")
  | some (.bytes _) => pure (some "bytes")
  | some (.tuple _) => pure (some "tuple")
  | some _ => pure none
  | none => return if (← listOf? v).isSome then some "list" else none

/-- A gap if either operand is an `int` whose number depends on the hash seed: the number fields
don't compute with it. -/
def symCheck [PyPure m V] (a b : V) : m Unit := do
  if (← PyPure.immViewAll a) matches some (.symHash _) || (← PyPure.immViewAll b) matches some (.symHash _) then
    PyPure.gap "arithmetic on a hash whose number the model does not know is not modelled yet"

/-- Whether `v` is a class: a built-in class, or an object whose class is a class. -/
def isClass [PyReads m V] (v : V) : m Bool := do
  match ← PyPure.immView v with
  | some (.builtin b) => pure (b.info.kind == .type)
  | some _ => pure false
  | none => return (← builtinClass? v) matches some .type

/-- Whether `v` is an instance of a class whose first built-in base is `object`: its operators are its
class's dunders and `object`'s, none of a built-in type's. -/
def isPlainUser [PyReads m V] (v : V) : m Bool := do
  if !(← isUserObject v) then return false
  let t ← PyReads.classOf v
  match ← classData? t with
  | some cd =>
    match ← PyPure.immView cd.solidBase with
    | some (.builtin b) => return b == .object
    -- A class with slots of its own is its own solid base: the first built-in type of its MRO
    -- decides.
    | _ =>
      let some mro ← mroOf t | return false
      for c in mro do
        if let some (.builtin b) ← PyPure.immView c then return b == .object
      return false
  | none => return false

/-- **`self.name(*args)`** for the special method `name` of `self`'s type, found on the type as
CPython's `lookup_maybe_method` finds it and bound to `self`; `none` if the type has none. -/
def callSpecial? [PyCalls m V] (self : V) (name : String) (args : Array V) : m (Option V) := do
  let t ← PyReads.classOf self
  match ← lookupType t name with
  | none => pure none
  | some f =>
    let g ← descrGetN dispatchDepth f (some self) t
    some <$> callSlotN dispatchDepth name f t g (PyPure.imm (m := m) (.tuple args)) (← PyPure.allocDict)

/-- Whether `v` is `NotImplemented`. -/
def isNotImpl [PyPure m V] (v : V) : m Bool :=
  return (← PyPure.immView v) matches some .notImplemented

/-- The forward and reflected dunders of a binary operator. -/
def binDunders : Arith.BinOp → String × String
  | .add => ("__add__", "__radd__") | .sub => ("__sub__", "__rsub__")
  | .mul => ("__mul__", "__rmul__") | .trueDiv => ("__truediv__", "__rtruediv__")
  | .floorDiv => ("__floordiv__", "__rfloordiv__") | .mod => ("__mod__", "__rmod__")
  | .pow => ("__pow__", "__rpow__") | .lshift => ("__lshift__", "__rlshift__")
  | .rshift => ("__rshift__", "__rrshift__") | .and => ("__and__", "__rand__")
  | .or => ("__or__", "__ror__") | .xor => ("__xor__", "__rxor__")

/-- The built-in sequence type and the name of the `+`, `*`, `+=` or `*=` that `f` is
(`list.__add__`, `str.__mul__`, `list.__iadd__`): CPython's `sq_concat`, `sq_repeat`,
`sq_inplace_concat` and `sq_inplace_repeat`, which the number protocol doesn't try; `none` for any
other `f`. -/
def seqSlot? [PyPure m V] (f : V) : m (Option (Builtin × String)) := do
  match ← PyPure.immView f with
  | some (.descr t n _) =>
    if [Builtin.list, .tuple, .str, .bytes].contains t &&
        ["__add__", "__mul__", "__rmul__", "__iadd__", "__imul__"].contains n then
      return some (t, n)
    return none
  | _ => return none

/-- Whether `f`, found as `name` on the type of `self`, is a sequence's slot (`seqSlot?`) and
`self` is a value of that built-in sequence type: then the sequence protocol handles it, not the
number protocol. On an object of another type, the slot is called as any dunder is: CPython's type
check raises, and the model stops with a gap where it binds the slot (`descrGetN`).

An instance of a subclass of that sequence counts as a value of it only when the slot is found
under its own name and no user class of its MRO defines a dunder of the slot's family: `__add__`,
`__radd__` or `__iadd__` for `+`, and `__mul__`, `__rmul__` or `__imul__` for `*`. Otherwise
CPython's number slot may call the slot, which the model doesn't follow, so it stops with a gap.
`__iadd__` and `__imul__` are separate in-place slots, so the gap on them is conservative. -/
def seqSlotApplies [PyReads m V] (f self : V) (name : String) : m Bool := do
  let some (t, n) ← seqSlot? f | return false
  if !(← isUserObject self) then return true
  let some mro ← mroOf (← PyReads.classOf self) | return false
  if !(← inMro (PyPure.imm (m := m) (.builtin t)) mro) then return false
  if n != name then
    PyPure.gap s!"a {t.info.name} slot found as {name} on an instance of a subclass of {t.info.name} is not modelled yet"
  let family := if n == "__add__" || n == "__iadd__" then ["__add__", "__radd__", "__iadd__"]
    else ["__mul__", "__rmul__", "__imul__"]
  for c in mro do
    if let some cd ← classData? c then
      for d in family do
        if (← dictFindStr cd.ns d).isSome then
          PyPure.gap s!"a {t.info.name} slot on an instance of a subclass of {t.info.name} with its own {d} is not modelled yet"
  return true

/-- The built-in types whose binary and comparison slots give `NotImplemented` for an operand that
is a plain user object: the exceptions, the iterators, and the types listed here. The sequences'
`+` and `*`, the `%` of `str` and `bytes`, and the in-place slots of `list` and `dict` take other
operands, but other rules handle them before (`seqSlotApplies`, `printfFirst?`, `inplaceOp`). -/
def givesNotImpl (b : Builtin) : Bool :=
  b.info.mro.contains .BaseException || b.info.name.endsWith "iterator" ||
  [Builtin.NoneType, .NotImplementedType, .ellipsis, .bool, .int, .float, .complex, .str, .bytes,
    .tuple, .range, .slice, .list, .dict, .set, .frozenset, .type, .object, .function,
    .builtin_function_or_method, .method, .«method-wrapper», .wrapper_descriptor,
    .method_descriptor, .classmethod_descriptor, .getset_descriptor, .member_descriptor, .module,
    .cell, .property, .classmethod, .staticmethod, .super, .zip, .enumerate, .reversed, .filter,
    .map, .dict_values, .traceback, .«_sitebuiltins.Quitter», .«_sitebuiltins._Helper»,
    .«_sitebuiltins._Printer»].contains b

/-- One side of CPython's `binary_op1` and `do_richcompare`: the dunder `name` of `self`'s type,
a user function or a built-in type's slot, called with `other`; `none` when the type has no such
dunder (a sequence's own `+` and `*` on a value of that sequence, which CPython tries after the
numbers, count as none: `seqSlotApplies`) or it gave `NotImplemented`.  With `swallow`, as
`slot_tp_richcompare` does, an exception raised while the
dunder is bound to `self` counts as none too. -/
def trySlot [PyCalls m V] (self other : V) (name : String) (swallow : Bool := false) :
    m (Option V) := do
  -- A built-in value's own slot can take only another built-in value or an instance of a
  -- subclass of a built-in type: against a plain user object it gives `NotImplemented`, for the
  -- types of `givesNotImpl`. Another type's own slot may not (a `mappingproxy`'s forward to its
  -- dict, a `ModuleSpec`'s `__eq__` reads the other operand's attributes, a dict view's set
  -- operators take any iterable), so it stops with a gap.
  if !(← isUserObject self) && ((← isPlainUser other) || !(← isUserObject other)) then
    if let some (.builtin b) ← PyPure.immView (← PyReads.classOf self) then
      if !givesNotImpl b then
        let cls := PyPure.imm (m := m) (.builtin b)
        let ownSlot (n : String) : m Bool := do
          let some f ← lookupType cls n | return false
          return !((← PyPure.immView f) matches some (.descr .object _ _))
        -- `object.__ne__` calls the type's own `__eq__`.
        if (← ownSlot name) || (name == "__ne__" && (← ownSlot "__eq__")) then
          PyPure.gap s!"the {name} of a {b.info.name} with a user object is not modelled yet"
    return none
  let t ← PyReads.classOf self
  let some f ← lookupType t name | return none
  if ← seqSlotApplies f self name then return none
  let g? ← if swallow then bindMaybe f self t
    else some <$> descrGetN dispatchDepth f (some self) t
  let some g := g? | return none
  let r ← callSlotN dispatchDepth name f t g (PyPure.imm (m := m) (.tuple #[other])) (← PyPure.allocDict)
  if ← isNotImpl r then pure none else pure (some r)

/-- Whether `tb` is a proper subclass of `ta` whose reflected dunder `rev` is its own: CPython's
`method_is_overloaded`. -/
def overridesReflected [PyReads m V] (ta tb : V) (rev : String) : m Bool := do
  let some mro ← mroOf tb | return false
  if !(← inMro ta mro) then return false
  match ← lookupType tb rev, ← lookupType ta rev with
  | some x, some y => return (← PyPure.identical x y) != .yes
  | some _, none => return true
  | _, _ => return false

/-- CPython's `binary_op1` when an operand is a user object: the forward dunder of `a`'s
type and the reflected one of `b`'s, the reflected first when `b`'s type is a proper subclass of
`a`'s that overrides it; `none` when both give `NotImplemented`. -/
def binaryDunder [PyCalls m V] (fwd rev : String) (a b : V) : m (Option V) := do
  let ta ← PyReads.classOf a
  let tb ← PyReads.classOf b
  let sameType := (← PyPure.identical ta tb) == .yes
  let revFirst ← if sameType || !(← isUserObject b) then pure false
    else overridesReflected ta tb rev
  if revFirst then
    if let some r ← trySlot b a rev then return some r
    trySlot a b fwd
  else
    if let some r ← trySlot a b fwd then return some r
    if sameType then return none
    trySlot b a rev

/-- What `binary_op1` and CPython's operator functions do after the number slots: `+` and `*` of
sequences, with the messages of their `sq_concat` and `sq_repeat`; otherwise `TypeError`
("unsupported operand type(s) for +: 'int' and 'str'"), whose message names the operator by
`sym`. -/
def binaryTail [PyCalls m V] (sym : String) (op : Arith.BinOp) (a b : V) : m V := do
  otherCheck a b
  if op == .or && ((← isClass a) || (← isClass b)) then
    PyPure.gap "`|` of a class, which makes a union type, is not modelled yet"
  if op == .or && (← isDict a) && (← isDict b) then
    PyPure.modelInvariant "`|` of two dicts is `orOp`"
  if (op == .or || op == .and || op == .sub || op == .xor) &&
      (← anySet? a).isSome && (← anySet? b).isSome then
    PyPure.modelInvariant "an operator of two sets is `setOp`"
  match op with
  | .add =>
    if let some v ← concatSeq a b then return v
    match ← seqName? a with
    | some "bytes" =>
      -- A `bytes` concatenates any object with the buffer protocol, which a class gets from
      -- `__buffer__` in 3.12.
      if (← lookupType (← PyReads.classOf b) "__buffer__").isSome then
        PyPure.gap "a bytes concatenation with an object that has __buffer__ is not modelled yet"
      raiseBuiltin "TypeError" s!"can't concat {← typeName b} to bytes"
    | some t => raiseBuiltin "TypeError" s!"can only concatenate {t} (not \"{← typeName b}\") to {t}"
    | none => pure ()
  | .mul =>
    if let some v ← repeatSeq a b then return v
    if let some v ← repeatSeq b a then return v
    if (← seqName? a).isSome then
      raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName b}'"
    if (← seqName? b).isSome then
      raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName a}'"
  | _ => pure ()
  let msg := s!"unsupported operand type(s) for {sym}: '{← typeName a}' and '{← typeName b}'"
  raiseBuiltin "TypeError" msg

/-- `a % b` when `a`'s `__mod__` is `str`'s or `bytes`'s own, in `binary_op1`'s order: the
`__rmod__` of `b` first when `b`'s type is a proper subclass of `a`'s that overrides it; then `a`'s
slot, which formats whatever `b` is (`unicode_mod`, `bytes_mod`).  `none` for any other `a % b`. -/
def printfFirst? [PyCalls m V] (op : Arith.BinOp) (a b : V) : m (Option V) := do
  if op != .mod then return none
  let ta ← PyReads.classOf a
  let some f ← lookupType ta "__mod__" | return none
  let some (.descr t "__mod__" _) ← PyPure.immView f | return none
  if t != .str && t != .bytes then return none
  if ← isUserObject b then
    if ← overridesReflected ta (← PyReads.classOf b) "__rmod__" then
      if let some r ← trySlot b a "__rmod__" then return some r
  return some (← callFound "__mod__" f a ta #[b] (← PyPure.allocDict))

/-- `a op b`, CPython's `binary_op1`: the numbers, a user object's dunders in the order of CPython's
slots, then `+` and `*`
of sequences, with the messages of their `sq_concat` and `sq_repeat`; otherwise `TypeError`
("unsupported operand type(s) for +: 'int' and 'str'"), whose message names the operator by
`sym`. -/
def binaryOpAs [PyCalls m V] (sym : String) (op : Arith.BinOp) (a b : V) : m V := do
  if let some v ← PyReads.numBinary op a b then return v
  symCheck a b
  if let some r ← printfFirst? op a b then return r
  if (← isUserObject a) || (← isUserObject b) then
    let (fwd, rev) := binDunders op
    if let some r ← binaryDunder fwd rev a b then return r
  binaryTail sym op a b

/-- `a op b`, as `binaryOpAs`. -/
def binaryOp [PyCalls m V] (op : Arith.BinOp) (a b : V) : m V := binaryOpAs (binSymbol op) op a b

/-- `a @ b`, with `sym` naming the operator: a user object's `__matmul__` and `__rmatmul__`; no
built-in type has it. -/
def matMultOpAs [PyCalls m V] (sym : String) (a b : V) : m V := do
  if (← isUserObject a) || (← isUserObject b) then
    if let some r ← binaryDunder "__matmul__" "__rmatmul__" a b then return r
  otherCheck a b
  raiseBuiltin "TypeError" s!"unsupported operand type(s) for {sym}: '{← typeName a}' and '{← typeName b}'"

/-- `a @ b`. -/
def matMultOp [PyCalls m V] (a b : V) : m V := matMultOpAs "@" a b

/-- `op a`: the numbers, and a user object's dunder; otherwise `TypeError` ("bad operand type for unary
-: 'str'"). -/
def unaryOp [PyCalls m V] (op : Arith.UnaryOp) (a : V) : m V := do
  if let some v ← PyReads.numUnary op a then return v
  symCheck a a
  if ← isUserObject a then
    let name := match op with
      | .neg => "__neg__" | .pos => "__pos__" | .invert => "__invert__" | .abs => "__abs__"
    if let some r ← callSpecial? a name #[] then return r
  otherCheck a a
  raiseBuiltin "TypeError" s!"bad operand type for {unarySymbol op}: '{← typeName a}'"

/-- `bool(v)`: `None` and the zeros and empty sequences are false; a user object's `__bool__`, then
its `__len__`, decide. -/
def truthy [PyCalls m V] (v : V) : m Bool := do
  match ← PyPure.immViewAll v with
  | some .none => pure false
  | some (.bool b) => pure b
  | some (.int i) => pure (i != 0)
  | some (.float f) => pure !(Arith.isZero f)
  | some (.str s) => pure !s.s.isEmpty
  | some (.bytes b) => pure !b.isEmpty
  | some (.tuple xs) => pure !xs.isEmpty
  | some (.range a b c) => pure (rangeLen a b c != 0)
  | some (.symHash _) => PyPure.gap "the truth of a hash whose number the model does not know"
  | some .notImplemented =>
    -- CPython warns, and the warning records itself in the module's `__warningregistry__`.
    PyPure.gap "the truth of NotImplemented, which warns, is not modelled yet"
  | some _ => pure true
  | none =>
    if ← PyPure.isUndef v then PyPure.gap "the truth of an undefined value"
    if ← isUserObject v then
      -- `__bool__`, which must give a `bool`, else `__len__`, else true.
      if let some r ← callSpecial? v "__bool__" #[] then
        match ← PyPure.immView r with
        | some (.bool b) => return b
        | _ => raiseBuiltin "TypeError" s!"__bool__ should return bool, returned {← typeName r}"
      if let some r ← callSpecial? v "__len__" #[] then
        -- `slot_sq_length`: the result as `PyNumber_Index` converts it, then a `Py_ssize_t`.
        let some n ← indexValue? r |
          raiseBuiltin "TypeError" s!"'{← typeName r}' object cannot be interpreted as an integer"
        if n < 0 then raiseBuiltin "ValueError" "__len__() should return >= 0"
        if n > (Format.ssizeMax : Int) then
          raiseBuiltin "OverflowError" "cannot fit 'int' into an index-sized integer"
        return n != 0
      return true
    if let some xs ← listOf? v then return !xs.isEmpty
    if ← isDict v then return (← PyReads.dictLen v) != 0
    if (← anySet? v).isSome then return (← PyReads.setLen v) != 0
    otherCheck v v
    pure true

/-- `not v`. -/
def notOp [PyCalls m V] (v : V) : m Bool := (! ·) <$> truthy v

/-- `x is y or x == y`, as CPython compares the members of a container, with `eq` for `==`.  Where
`is` is unknown and `==` is false, the two may be one NaN in CPython, which is equal to itself
there: a gap. -/
def sameOrEq [PyPure m V] (eq : V → V → m Bool) (x y : V) : m Bool := do
  let same ← PyPure.identical x y
  if same matches .yes then return true
  if ← eq x y then return true
  if same matches .unknown then
    PyPure.gap "comparing values whose identity is unknown and that are not equal (a NaN)"
  return false

/-- A step that hands control back to the machine (a read of the world that changes nothing), so
that a walk over a long container whose comparisons run no request doesn't grow the native stack
with each member. -/
def pauseStep [PyReads m V] : m Unit := discard PyReads.depthC

/-- The first pair of members of `xs` and `ys` below `n`, from position `i` on, that are not
equal, `is` first and then `eq`; walked by position, with `fuel` above the positions left. -/
def firstDiff [PyPure m V] (eq : V → V → m Bool) (xs ys : Array V) (n : Nat) :
    Nat → Nat → m (Option (V × V))
  | 0, _ => PyPure.modelInvariant "firstDiff: the fuel ran out"
  | fuel + 1, i => do
    if i ≥ n then return none
    match xs[i]?, ys[i]? with
    | some x, some y =>
      if ← sameOrEq eq x y then firstDiff eq xs ys n fuel (i + 1) else pure (some (x, y))
    | _, _ => pure none

/-- The first position below both sizes at which the members of the lists `a` and `b` are not
equal (by `eqv`, after the identity shortcut), as `list_richcompare` walks them: both lists are
read again at each step, since a member's `__eq__` may change them; `none` when a list ends
first. -/
def listDiffLive [PyReads m V] (eqv : V → V → m Bool) (a b : V) : Nat → Nat → m (Option Nat)
  | 0, _ => PyPure.gap "a walk of a list that doesn't end"
  | fuel + 1, i => do
    let some xs ← listOf? a | PyPure.modelInvariant "a list compared that stopped being a list"
    let some ys ← listOf? b | PyPure.modelInvariant "a list compared that stopped being a list"
    match xs[i]?, ys[i]? with
    | some x, some y =>
      if ← sameOrEq eqv x y then listDiffLive eqv a b fuel (i + 1) else return some i
    | _, _ => return none

/-- `a op b` for two lists, as CPython's `list_richcompare`: different sizes are unequal; else the
first position whose members differ decides (`listDiffLive`), `==` and `!=` at once, and an
ordering by `last` on the two members, read again; with no such position, or when the comparison
that found it shrank a list past it, the sizes decide. -/
def listCompareLive [PyReads m V] {α : Type} (eqv : V → V → m Bool) (last : V → V → m α)
    (ofBool : Bool → α) (op : Arith.CmpOp) (a b : V) : m α := do
  let size (v : V) : m Nat := do
    let some xs ← listOf? v | PyPure.modelInvariant "a list compared that stopped being a list"
    pure xs.size
  if (← size a) != (← size b) && (op == .eq || op == .ne) then return ofBool (op == .ne)
  let some i ← listDiffLive eqv a b walkFuel 0 |
    return ofBool (holdsOrd op (compare (← size a) (← size b)))
  -- The comparison that stopped the walk may have shrunk a list: then the sizes decide.
  let sa ← size a
  let sb ← size b
  if i ≥ sa || i ≥ sb then return ofBool (holdsOrd op (compare sa sb))
  match op with
  | .eq => return ofBool false
  | .ne => return ofBool true
  | _ =>
    let some x := (← listOf? a).bind (·[i]?) | PyPure.modelInvariant "a list item"
    let some y := (← listOf? b).bind (·[i]?) | PyPure.modelInvariant "a list item"
    last x y

/-- CPython's default comparison, when no dunder gives a result: identity for `==` and `!=`,
`TypeError` for an ordering. -/
def richDefault [PyReads m V] (op : Arith.CmpOp) (a b : V) : m Bool := do
  match op with
  | .eq | .ne =>
    let same ← match ← PyPure.identical a b with
      | .yes => pure true
      | .no => pure false
      | .unknown => PyPure.gap "== of two values whose identity is unknown"
    return if op == .eq then same else !same
  | _ =>
    raiseBuiltin "TypeError"
      s!"'{cmpSymbol op}' not supported between instances of '{← typeName a}' and '{← typeName b}'"

/-- `xs op ys` for two tuples or two lists, comparing their members with `cmp`: the first position
where the members are not equal decides, else the sizes do. -/
def seqCompare [PyPure m V] (cmp : Arith.CmpOp → V → V → m Bool) (op : Arith.CmpOp)
    (xs ys : Array V) : m Bool := do
  let n := min xs.size ys.size
  match ← firstDiff (cmp .eq) xs ys n (n + 1) 0 with
  | none => return holdsOrd op (compare xs.size ys.size)
  | some (x, y) => match op with
    | .eq => return false
    | .ne => return true
    | _ => cmp op x y

/-- A gap, with the message `msg`, where a walk of the dict `d` by position, which started at the
keys version `version`, may have lost its place: `d`'s keys changed since, and either its entry
array may differ from CPython's (`dictLayout`), or it has a deleted entry and may have been resized.
CPython's resize compacts the entry array and moves the entries that the walk hasn't reached; the
model's table doesn't compact. While the array is CPython's (`DictTable.noteKey` marks a table
that CPython may have converted from `str` keys, which compacts it too), the smallest table holds 5
entries, holes included, before an insertion resizes it, so an array of at most 5 entries hasn't
been resized. -/
def compactGap [PyReads m V] (d : V) (version : Nat) (msg : String) : m Unit := do
  let (deleted, version') ← PyReads.dictFlags d
  if version' == version then return
  let (inexact, _) ← PyReads.dictLayout d
  if inexact || (deleted && (← PyReads.dictEntriesSize d) > 5) then PyPure.gap msg

/-- CPython's `dict_equal` from position `i` of `a`'s entry array on, for a walk that started at
`a`'s keys version `ver`: each live entry's key is looked up in `b` and the two values compared,
and the entry array is read again at each step, as CPython reads it, since a comparison may change
it (`compactGap`). -/
def dictEqualFrom [PyReads m V] (eqv : V → V → m Bool) (a b : V) (ver : Nat) : Nat → Nat → m Bool
  | 0, _ => PyPure.gap "a walk of a dict whose entry array keeps growing"
  | fuel + 1, i => do
    compactGap a ver "a dict whose entries may move during its comparison is not modelled yet"
    match ← PyReads.dictEntryAt a i with
    | .past => return true
    | .hole => dictEqualFrom eqv a b ver fuel (i + 1)
    | .entry k v h =>
      match ← PyReads.dictFind b k (some h) fun stored => eqv stored k with
      | none => return false
      | some w =>
        if !(← sameOrEq eqv v w) then return false
        dictEqualFrom eqv a b ver fuel (i + 1)

/-- `a == b` for two dicts, with `eqv` comparing keys and values: the same number of entries, and
each entry of `a`, in order, found in `b` by its stored hash with a value that is equal (`is`
first). -/
def dictEqual [PyReads m V] (eqv : V → V → m Bool) (a b : V) : m Bool := do
  if (← PyReads.dictLen a) != (← PyReads.dictLen b) then return false
  -- CPython walks an instance's `__dict__` in its class's order of shared keys.
  if (← PyReads.dictLayout a).2 && (← PyReads.dictLen a) > 1 then
    PyPure.gap "== of an instance's __dict__ with more than one attribute is not modelled yet"
  dictEqualFrom eqv a b (← PyReads.dictFlags a).2 walkFuel 0

/-- The dunder of a comparison. -/
def cmpDunder : Arith.CmpOp → String
  | .eq => "__eq__" | .ne => "__ne__" | .lt => "__lt__" | .le => "__le__" | .gt => "__gt__"
  | .ge => "__ge__"

/-- CPython's `do_richcompare` when an operand is a plain user object: the reflected comparison of
`b`'s type first when it is a proper subclass of `a`'s, then `a`'s comparison, then `b`'s
reflected one; `none` when all give `NotImplemented`. -/
def richDunder [PyCalls m V] (op : Arith.CmpOp) (a b : V) : m (Option V) := do
  let ta ← PyReads.classOf a
  let tb ← PyReads.classOf b
  let sameType := (← PyPure.identical ta tb) == .yes
  let revFirst ← if sameType then pure false else
    match ← mroOf tb with
    | some mro => inMro ta mro
    | none => pure false
  let rev := cmpDunder (Arith.CmpOp.swap op)
  if revFirst then
    if let some r ← trySlot b a rev (swallow := true) then return some r
  if let some r ← trySlot a b (cmpDunder op) (swallow := true) then return some r
  if revFirst then return none
  trySlot b a rev (swallow := true)

/-- `a op b`, one C level deeper (CPython's `PyObject_RichCompare`), with
`fuel` the nested levels left before `Depth.c` reaches its limit: the
numbers; `str` and `bytes` by their code points and octets; tuples and lists member by member, the first
members that are not equal (by `==` with the identity shortcut) deciding; `==` and `!=` of other
values by identity; otherwise `TypeError` ("'<' not supported between instances of 'int' and
'str'"). -/
def richCompareN [PyCalls m V] : Nat → Arith.CmpOp → V → V → m Bool
  | 0, _, _, _ => PyPure.gap "a comparison nested deeper than the model follows"
  | fuel + 1, op, a, b => do
    -- Two numbers compare without nesting, so their level isn't counted.
    if let some r ← PyPure.numCompare op a b then return r
    PyReads.withDepth 1 do
      symCheck a b
      match ← PyPure.immView a, ← PyPure.immView b with
      | some (.str x), some (.str y) => return holdsOrd op (compare x.s y.s)
      | some (.bytes x), some (.bytes y) => return holdsOrd op (lexOrd compare x y)
      | some (.range a₁ b₁ c₁), some (.range a₂ b₂ c₂) =>
        match op with
        | .eq | .ne =>
          -- Two ranges are equal when they give the same sequence.
          let n₁ := rangeLen a₁ b₁ c₁
          let n₂ := rangeLen a₂ b₂ c₂
          let same := n₁ == n₂ && (n₁ == 0 || (a₁ == a₂ && (n₁ == 1 || c₁ == c₂)))
          return if op == .eq then same else !same
        | _ =>
          let msg := s!"'{cmpSymbol op}' not supported between instances of 'range' and 'range'"
          raiseBuiltin "TypeError" msg
      | some (.slice a₁ b₁ c₁), some (.slice a₂ b₂ c₂) =>
        -- A slice compares as the tuple of its three parts.
        richCompareN fuel op (PyPure.imm (m := m) (.tuple #[a₁, b₁, c₁]))
          (PyPure.imm (m := m) (.tuple #[a₂, b₂, c₂]))
      | some (.tuple xs), some (.tuple ys) =>
        seqCompare (fun o x y => do pauseStep; richCompareN fuel o x y) op xs ys
      | _, _ =>
        if (← isUserObject a) || (← isUserObject b) then
          -- `PyObject_RichCompareBool`'s truth of a dunder's result; without one, `==` and `!=`
          -- compare identities.
          match ← richDunder op a b with
          | some r => return ← truthy r
          | none => return ← richDefault op a b
        if (← listOf? a).isSome && (← listOf? b).isSome then
          return ← listCompareLive (richCompareN fuel .eq) (richCompareN fuel op) id op a b
        if (op == .eq || op == .ne) && (← isDict a) && (← isDict b) then
          let same ← dictEqual (richCompareN fuel .eq) a b
          return if op == .eq then same else !same
        if (← anySet? a).isSome && (← anySet? b).isSome then
          return ← setCompare (richCompareN fuel .eq) op a b
        otherCheck a b
        match op with
        | .eq | .ne =>
          let same ← match ← PyPure.identical a b with
            | .yes => pure true
            | .no => pure false
            | .unknown => PyPure.gap "== of two equal values of this kind is not modelled yet"
          return if op == .eq then same else !same
        | _ =>
          let msg := s!"'{cmpSymbol op}' not supported between instances of '{← typeName a}' and '{← typeName b}'"
          raiseBuiltin "TypeError" msg

/-- `a op b`, as `richCompareN` from the top. -/
def richCompare [PyCalls m V] (op : Arith.CmpOp) (a b : V) : m Bool := do
  if let some r ← PyPure.numCompare op a b then return r
  -- The fuel only bounds the recursion: `Depth.c` reaches its limit first.
  richCompareN (cDepthLimit + 1 - (← PyReads.depthC)) op a b

/-- `a op b` as the operator gives it, with `fuel` the nested levels left: see `richCompareV`. -/
def richCompareVN [PyCalls m V] : Nat → Arith.CmpOp → V → V → m V
  | 0, _, _, _ => PyPure.gap "a comparison nested deeper than the model follows"
  | fuel + 1, op, a, b => do
    let boolV (r : Bool) : V := PyPure.imm (m := m) (.bool r)
    if let some r ← PyPure.numCompare op a b then return boolV r
    if (← isUserObject a) || (← isUserObject b) then
      -- One C level, as `PyObject_RichCompare` counts it.
      return ← PyReads.withDepth 1 do
        match ← richDunder op a b with
        | some r => pure r
        | none => boolV <$> richDefault op a b
    if op != .eq && op != .ne then
      -- An ordering of two tuples or two lists gives the members' own result.
      let eqv (x y : V) : m Bool := do truthy (← richCompareVN fuel .eq x y)
      if let some (.tuple xs) ← PyPure.immView a then
        if let some (.tuple ys) ← PyPure.immView b then
          return ← PyReads.withDepth 1 do
            let n := min xs.size ys.size
            match ← firstDiff (fun x y => do pauseStep; eqv x y) xs ys n (n + 1) 0 with
            | none => pure (boolV (holdsOrd op (compare xs.size ys.size)))
            | some (x, y) => richCompareVN fuel op x y
      if (← listOf? a).isSome && (← listOf? b).isSome then
        return ← PyReads.withDepth 1 (listCompareLive eqv (richCompareVN fuel op) boolV op a b)
    return boolV (← richCompare op a b)

/-- **`a op b`** as the operator gives it, CPython's `PyObject_RichCompare`: a user dunder's own
result, an ordering of tuples or lists the members' result, else the comparison of
`richCompare`. -/
def richCompareV [PyCalls m V] (op : Arith.CmpOp) (a b : V) : m V := do
  richCompareVN (cDepthLimit + 1 - (← PyReads.depthC)) op a b


/-- `not v`, as a `bool`. -/
def notValue [PyCalls m V] (v : V) : m V := (fun b => PyPure.imm (m := m) (.bool b)) <$> notOp v

end

end

end StrataPython.Dyn.Sem.Proto
