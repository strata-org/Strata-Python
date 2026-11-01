/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Values
public import StrataPython.Dyn.Sem.Hash

set_option autoImplicit false

/-!
# Operators on built-in values

Generic over the record of primitives, CPython 3.12's operators on the built-in immediates and
lists:

* `binaryOp`: the numbers (through `numBinary`), and `+` and `*` of `str`, `bytes`, `tuple` and
  `list` (`|` of two dicts and the operators of two sets are in `Proto/Containers.lean`);
* `unaryOp`, `truthy` and `notOp`;
* `richCompare`: the numbers (through `numCompare`), `str`, `bytes`, and `tuple` and `list` member
  by member (each member compared with the identity shortcut), `==` and `!=` of dicts entry by
  entry, sets by the subset order, and `==` and `!=` of values of two other kinds by identity.

Any other case raises CPython's `TypeError`, with its message.  A user object stops with a gap
until the dunder lookup of a type exists, and so does an object of a built-in type whose
operators are not modelled yet (a `bytearray`, for example).  A comparison of nested tuples counts its depth, as
CPython's C recursion count does, and stops with a gap before CPython's limit.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

/-- The gap of a value whose type is a user class. -/
def userGap : String := "the dunder protocol of a user class is not modelled yet"

/-- The depth of nested comparisons that the model follows.  CPython follows nested tuples until
its C recursion limit, near a depth of 10000, and then raises `RecursionError`; the model stops
with a gap at this depth, before CPython's limit. -/
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

/-- The name of `v`'s type in CPython's messages; a gap for a user class. -/
def typeName [PyReads m V] (v : V) : m String := do
  match ← PyPure.immView (← PyReads.classOf v) with
  | some (.builtin b) => pure (if b.info.tpName.isEmpty then b.info.name else b.info.tpName)
  | _ => PyPure.gap userGap

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

/-- Whether `v` is a dict (not an instance of a subclass of `dict`). -/
def isDict [PyReads m V] (v : V) : m Bool := return (← builtinClass? v) matches some .dict

/-- Whether `v` is a frozenset, if it is a set or a frozenset (not an instance of a subclass). -/
def anySet? [PyReads m V] (v : V) : m (Option Bool) := do
  match ← builtinClass? v with
  | some .«set» => pure (some false)
  | some .«frozenset» => pure (some true)
  | _ => pure none

/-- What the set `s` holds. -/
def setMembers [PyReads m V] (s : V) : m (SetView V) := do
  let some vw ← PyReads.setView s | PyPure.modelInvariant "setMembers: operand assumption failed"
  pure vw

/-- A gap if walking a set while comparing with the members of the sets `sets` (the walked one
included) could run user code: CPython walks the live table, which user code may change, and the
model walks the members as they were when the walk started.  It takes constant time per set. -/
def guardWalk [PyReads m V] (sets : List V) : m Unit := do
  for s in sets do
    if ← PyReads.setHasUser s then
      PyPure.gap "a walk of a set whose comparisons may run user code is not modelled yet"

/-- Whether every member of the set `a` is in the set `b`, `eqv` comparing members: CPython's
`set_issubset`. -/
def setIsSubset [PyReads m V] (eqv : V → V → m Bool) (a b : V) : m Bool := do
  if (← PyReads.setLen a) > (← PyReads.setLen b) then return false
  guardWalk [a, b]
  let va ← setMembers a
  for (k, h) in va.unordered do
    if !(← PyReads.setFind b k (some h) fun stored => eqv stored k) then return false
  return true

/-- `a op b` for two sets or frozensets: `==` by size and `set_issubset`, and the subset order. -/
def setCompare [PyReads m V] (eqv : V → V → m Bool) (op : Arith.CmpOp) (a b : V) : m Bool := do
  let na ← PyReads.setLen a
  let nb ← PyReads.setLen b
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
  if (← listOf? v).isSome then return false
  match ← builtinClass? v with
  | some .dict | some .«set» | some .«frozenset» => return false
  | some b => return !hashesByAddr b
  | none => return true

/-- A gap if either operand is an object whose type's operators are not modelled yet. -/
def otherCheck [PyReads m V] (a b : V) : m Unit := do
  if (← isOtherObject a) || (← isOtherObject b) then
    PyPure.gap "the operators of this built-in type are not modelled yet"

/-- The repetition count of a sequence: an `int` or a `bool`, of which a negative one counts as
`0`; `none` if `n` is neither.  A count that a C `Py_ssize_t` can't hold raises `OverflowError`,
as `PyNumber_AsSsize_t` does. -/
def repeatCount [PyReads m V] (n : V) : m (Option Nat) := do
  match ← PyPure.immView n with
  | some (.int i) =>
    if i < Arith.ssizeMin ∨ i > (Format.ssizeMax : Int) then
      raiseBuiltin "OverflowError" "cannot fit 'int' into an index-sized integer"
    pure (some i.toNat)
  | some (.bool b) => pure (some (if b then 1 else 0))
  | some (.symHash _) => PyPure.gap "a repetition count whose number depends on the hash seed"
  | _ => pure none

/-- The largest repetition that the model computes, in elements: beyond it, CPython may raise
`MemoryError`, which depends on the machine. -/
def maxRepeat : Nat := 2 ^ 28

/-- `xs * n`, as CPython repeats a sequence: empty for an empty `xs` or `n = 0`. -/
def repeatArray {α : Type} (xs : Array α) (n : Nat) : Array α :=
  if xs.isEmpty then #[] else (List.replicate n xs).foldl (· ++ ·) #[]

/-- `s * n` and `n * s` for a `str`, a `bytes`, a `tuple` or a list `s` and a count `n`; `none`
if the operands are not such a pair. -/
def repeatSeq [PyReads m V] (s n : V) : m (Option V) := do
  -- The count is converted only for a sequence: `2**100 * None` raises `TypeError`.
  let isSeq := (← listOf? s).isSome ||
    (← PyPure.immView s) matches some (.str _) | some (.bytes _) | some (.tuple _)
  if !isSeq then return none
  let some k ← repeatCount n | return none
  if let some xs ← listOf? s then
    if xs.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
    return some (← PyPure.allocList (repeatArray xs k))
  match ← PyPure.immView s with
  | some (.str t) =>
    if t.s.length * k > maxRepeat then PyPure.gap "a repetition too large to model"
    if t.s.isEmpty then return some s
    return some (PyPure.imm (m := m) (.str (.ofString (String.join (List.replicate k t.s)))))
  | some (.bytes b) =>
    if b.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
    return some (PyPure.imm (m := m) (.bytes (repeatArray b k)))
  | some (.tuple xs) =>
    if xs.size * k > maxRepeat then PyPure.gap "a repetition too large to model"
    return some (PyPure.imm (m := m) (.tuple (repeatArray xs k)))
  | _ => return none

/-- `a + b` for two `str`s, two `bytes`, two `tuple`s or two lists; `none` otherwise. -/
def concatSeq [PyReads m V] (a b : V) : m (Option V) := do
  if let some xs ← listOf? a then
    if let some ys ← listOf? b then return some (← PyPure.allocList (xs ++ ys))
  match ← PyPure.immView a, ← PyPure.immView b with
  | some (.str x), some (.str y) => return some (PyPure.imm (m := m) (.str (.ofString (x.s ++ y.s))))
  | some (.bytes x), some (.bytes y) => return some (PyPure.imm (m := m) (.bytes (x ++ y)))
  | some (.tuple x), some (.tuple y) => return some (PyPure.imm (m := m) (.tuple (x ++ y)))
  | _, _ => return none

/-- The name of `v`'s type if it is a `str`, a `bytes`, a `tuple` or a list. -/
def seqName? [PyReads m V] (v : V) : m (Option String) := do
  match ← PyPure.immView v with
  | some (.str _) => pure (some "str")
  | some (.bytes _) => pure (some "bytes")
  | some (.tuple _) => pure (some "tuple")
  | some _ => pure none
  | none => return if (← listOf? v).isSome then some "list" else none

/-- A gap if either operand is an `int` whose number depends on the hash seed: the number fields
don't compute with it. -/
def symCheck [PyPure m V] (a b : V) : m Unit := do
  if (← PyPure.immView a) matches some (.symHash _) || (← PyPure.immView b) matches some (.symHash _) then
    PyPure.gap "arithmetic on a hash whose number the model does not know is not modelled yet"

/-- Whether `v` is a class: a built-in class, or an object whose class is a class. -/
def isClass [PyReads m V] (v : V) : m Bool := do
  match ← PyPure.immView v with
  | some (.builtin b) => pure (b.info.kind == .type)
  | some _ => pure false
  | none => return (← builtinClass? v) matches some .type

/-- `a op b` for built-in values, CPython's `binary_op1` on them: the numbers, then `+` and `*`
of sequences, with the messages of their `sq_concat` and `sq_repeat`; otherwise `TypeError`
("unsupported operand type(s) for +: 'int' and 'str'"), whose message names the operator by
`sym`. -/
def binaryOpAs [PyReads m V] (sym : String) (op : Arith.BinOp) (a b : V) : m V := do
  if let some v ← PyReads.numBinary op a b then return v
  symCheck a b
  userCheck a b
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
    | some "bytes" => raiseBuiltin "TypeError" s!"can't concat {← typeName b} to bytes"
    | some t => raiseBuiltin "TypeError" s!"can only concatenate {t} (not \"{← typeName b}\") to {t}"
    | none => pure ()
  | .mul =>
    if let some v ← repeatSeq a b then return v
    if let some v ← repeatSeq b a then return v
    if (← seqName? a).isSome then
      raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName b}'"
    if (← seqName? b).isSome then
      raiseBuiltin "TypeError" s!"can't multiply sequence by non-int of type '{← typeName a}'"
  | .mod =>
    if (← PyPure.immView a) matches some (.str _) || (← PyPure.immView a) matches some (.bytes _) then
      PyPure.gap "printf-style formatting is not modelled yet"
  | _ => pure ()
  let msg := s!"unsupported operand type(s) for {sym}: '{← typeName a}' and '{← typeName b}'"
  raiseBuiltin "TypeError" msg

/-- `a op b` for built-in values, as `binaryOpAs`. -/
def binaryOp [PyReads m V] (op : Arith.BinOp) (a b : V) : m V := binaryOpAs (binSymbol op) op a b

/-- `a @ b` for built-in values, with `sym` naming the operator: no built-in type has it. -/
def matMultOpAs [PyReads m V] (sym : String) (a b : V) : m V := do
  userCheck a b
  otherCheck a b
  raiseBuiltin "TypeError" s!"unsupported operand type(s) for {sym}: '{← typeName a}' and '{← typeName b}'"

/-- `a @ b` for built-in values. -/
def matMultOp [PyReads m V] (a b : V) : m V := matMultOpAs "@" a b

/-- `op a` for a built-in value: the numbers; otherwise `TypeError` ("bad operand type for unary
-: 'str'"). -/
def unaryOp [PyReads m V] (op : Arith.UnaryOp) (a : V) : m V := do
  if let some v ← PyReads.numUnary op a then return v
  symCheck a a
  userCheck a a
  otherCheck a a
  raiseBuiltin "TypeError" s!"bad operand type for {unarySymbol op}: '{← typeName a}'"

/-- `bool(v)` for a built-in value: `None` and the zeros and empty sequences are false. -/
def truthy [PyReads m V] (v : V) : m Bool := do
  match ← PyPure.immView v with
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
    userCheck v v
    if let some xs ← listOf? v then return !xs.isEmpty
    if ← isDict v then return (← PyReads.dictLen v) != 0
    if (← anySet? v).isSome then return (← PyReads.setLen v) != 0
    otherCheck v v
    pure true

/-- `not v`. -/
def notOp [PyReads m V] (v : V) : m Bool := (! ·) <$> truthy v

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

/-- The first pair of members that are not equal, `is` first and then `eq`. -/
def firstDiff [PyPure m V] (eq : V → V → m Bool) : List (V × V) → m (Option (V × V))
  | [] => pure none
  | (x, y) :: rest => do
    if ← sameOrEq eq x y then firstDiff eq rest else pure (some (x, y))

/-- `xs op ys` for two tuples or two lists, comparing their members with `cmp`: the first position
where the members are not equal decides, else the sizes do. -/
def seqCompare [PyPure m V] (cmp : Arith.CmpOp → V → V → m Bool) (op : Arith.CmpOp)
    (xs ys : Array V) : m Bool := do
  let n := min xs.size ys.size
  match ← firstDiff (cmp .eq) ((xs.extract 0 n).toList.zip (ys.extract 0 n).toList) with
  | none => return holdsOrd op (compare xs.size ys.size)
  | some (x, y) => match op with
    | .eq => return false
    | .ne => return true
    | _ => cmp op x y

/-- `a == b` for two dicts, with `eqv` comparing keys and values: the same number of entries, and
each entry of `a`, in order, found in `b` by its stored hash with a value that is equal (`is`
first). -/
def dictEqual [PyReads m V] (eqv : V → V → m Bool) (a b : V) : m Bool := do
  if (← PyReads.dictLen a) != (← PyReads.dictLen b) then return false
  for (k, v, h) in ← PyReads.dictEntries a do
    match ← PyReads.dictFind b k (some h) fun stored => eqv stored k with
    | none => return false
    | some w => if !(← sameOrEq eqv v w) then return false
  return true

/-- `a op b` for two built-in values, with `fuel` the depth of nested comparisons left: the
numbers; `str` and `bytes` by their code points and octets; tuples and lists member by member, the first
members that are not equal (by `==` with the identity shortcut) deciding; `==` and `!=` of other
values by identity; otherwise `TypeError` ("'<' not supported between instances of 'int' and
'str'"). -/
def richCompareN [PyReads m V] : Nat → Arith.CmpOp → V → V → m Bool
  | 0, _, _, _ => PyPure.gap "a comparison nested deeper than the model follows"
  | fuel + 1, op, a, b => do
    if let some r ← PyPure.numCompare op a b then return r
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
    | some (.tuple xs), some (.tuple ys) => seqCompare (richCompareN fuel) op xs ys
    | _, _ =>
      userCheck a b
      if let some xs ← listOf? a then
        if let some ys ← listOf? b then
          -- Lists of different lengths are not equal, before any member is compared.
          if xs.size != ys.size && (op == .eq || op == .ne) then return op == .ne
          return ← seqCompare (richCompareN fuel) op xs ys
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

/-- `a op b` for two built-in values, as `richCompareN` from the top. -/
def richCompare [PyReads m V] (op : Arith.CmpOp) (a b : V) : m Bool :=
  richCompareN compareDepth op a b

end

end

end StrataPython.Dyn.Sem.Proto
