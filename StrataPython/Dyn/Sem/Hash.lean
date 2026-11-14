/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Value

set_option autoImplicit false

/-!
# The hashes of built-in values

CPython 3.12's hash algorithms for the immediates whose hash is a fixed number: `int`, `bool`,
`float`, `None`, `tuple`, `frozenset`, `range` and `slice` (`Objects/longobject.c`,
`Python/pyhash.c`, `Objects/tupleobject.c`, `Objects/setobject.c`, `Objects/rangeobject.c`,
`Objects/sliceobject.c`).  A `str` or `bytes` hash depends on the hash seed, so it is symbolic,
with the bytes that CPython hashes as its source; an empty one hashes to `0` under every seed.

A tuple, a frozenset or a combined hash is exact when all its parts are, and symbolic otherwise.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- CPython's `_PyHASH_MODULUS`, `2^61 - 1`. -/
def hashModulus : Nat := 2 ^ 61 - 1

/-- A hash value as CPython returns it: `-1` is reserved for errors, so it becomes `-2`. -/
def fixMinusOne (h : Int) : Int := if h = -1 then -2 else h

/-- `hash(n)` for an `int` `n`: its absolute value modulo `2^61 - 1`, with `n`'s sign; `-1`
becomes `-2`. -/
def hashInt (n : Int) : Int :=
  let r : Int := (n.natAbs % hashModulus : Nat)
  fixMinusOne (if n < 0 then -r else r)

/-- `2^k * m` modulo `2^61 - 1`, for any integer `k`: `2^61` is `1` modulo `2^61 - 1`. -/
def mulPow2Mod (m : Nat) (k : Int) : Nat :=
  let e : Nat := (k % 61).toNat
  (m % hashModulus) * 2 ^ e % hashModulus

/-- `hash(x)` for a `float` `x` with IEEE 754 bits `bits`, as CPython's `_Py_HashDouble`: the
hash of the rational number that `x` is, so a whole `x` hashes as the equal `int` does; `314159`
for an infinity, with its sign.  `none` for a NaN, whose hash is its object's address. -/
def hashFloatBits (bits : UInt64) : Option Int :=
  let neg := bits >>> 63 == 1
  let expField := ((bits >>> 52) &&& 0x7ff).toNat
  let frac := (bits &&& 0xfffffffffffff).toNat
  if expField == 0x7ff then
    if frac == 0 then some (if neg then -314159 else 314159) else none
  else
    -- The value is `mant * 2^(exp - 1075)`, with the implicit bit for a normal number.
    let (mant, exp) := if expField == 0 then (frac, (1 : Int)) else (frac + 2 ^ 52, (expField : Int))
    let r : Int := mulPow2Mod mant (exp - 1075)
    some (fixMinusOne (if neg then -r else r))

/-- A hash as CPython's unsigned `Py_uhash_t`. -/
def toUHash (h : Int) : UInt64 := UInt64.ofInt h

/-- A `Py_uhash_t` as CPython's signed `Py_hash_t`. -/
def ofUHash (u : UInt64) : Int := if u.toNat < 2 ^ 63 then u.toNat else (u.toNat : Int) - 2 ^ 64

/-- CPython 3.12's xxHash mixing of the exact hashes `hs`, as `tuplehash` (with the length) and
`slicehash` (without it) do. -/
def xxHashExact (hs : List Int) (withLength : Bool) : Int :=
  let p1 : UInt64 := 11400714785074694791
  let p2 : UInt64 := 14029467366897019727
  let p5 : UInt64 := 2870177450012600261
  let rot (x : UInt64) : UInt64 := (x <<< 31) ||| (x >>> 33)
  let acc := hs.foldl (fun acc h => rot (acc + toUHash h * p2) * p1) p5
  let acc := if withLength then acc + (hs.length.toUInt64 ^^^ (p5 ^^^ (3527539 : UInt64))) else acc
  if acc == UInt64.ofInt (-1) then 1546275796 else ofUHash acc

/-- The exact numbers of `hs`, if every one is exact. -/
def Hash.allExact? : List Hash → Option (List Int)
  | [] => some []
  | .exact h :: rest => (Hash.allExact? rest).map (h :: ·)
  | .symbolic _ :: _ => none

/-- `Hash.allExact?` with an accumulator, so that a long list doesn't grow the native stack; the
compiled code of `Hash.allExact?` (`Hash.allExact?_eq_allExactTR`). -/
def Hash.allExactTR (hs : List Hash) : Option (List Int) := go hs []
where
  /-- The numbers of `hs` after the numbers `acc` (in reverse), if every hash of `hs` is exact. -/
  go : List Hash → List Int → Option (List Int)
    | [], acc => some acc.reverse
    | .exact h :: rest, acc => go rest (h :: acc)
    | .symbolic _ :: _, _ => none

/-- The accumulator of `Hash.allExactTR.go` comes first, reversed, in front of the numbers that
`Hash.allExact?` gives; by induction on the list. -/
private theorem Hash.allExactTR_go_eq (hs : List Hash) (acc : List Int) :
    Hash.allExactTR.go hs acc = (Hash.allExact? hs).map (acc.reverse ++ ·) := by
  induction hs generalizing acc with
  | nil => simp [Hash.allExactTR.go, Hash.allExact?]
  | cons h t ih => cases h <;> simp [Hash.allExactTR.go, Hash.allExact?, ih, Option.map_map,
      Function.comp_def]

/-- `Hash.allExact?` and its tail-recursive version `Hash.allExactTR` are the same function. -/
@[csimp] theorem Hash.allExact?_eq_allExactTR : @Hash.allExact? = @Hash.allExactTR := by
  funext hs; simp [Hash.allExactTR, Hash.allExactTR_go_eq]

/-- The hash of a tuple whose members have the hashes `hs`. -/
def tupleHash (hs : List Hash) : Hash :=
  match Hash.allExact? hs with
  | some ns => .exact (xxHashExact ns true)
  | none => .symbolic (.tuple hs)

/-- A hash that a value's `__hash__` combines from the hashes `parts`, named by `tag`: `exact` of
their numbers when every part is exact, else a symbolic hash from the tag and the parts.  Two
symbolic hashes are equal when their tags and parts are, so a tag must name one `exact` function
among all callers (`sliceHash` uses "slice", and a static method's hash "<staticmethod>"). -/
def combineHash (tag : String) (parts : List Hash) (exact : List Int → Int) : Hash :=
  match Hash.allExact? parts with
  | some ns => .exact (exact ns)
  | none => .symbolic (.combine tag parts)

/-- The hash of a slice whose bounds have the hashes `hs`: CPython 3.12's `slicehash`. -/
def sliceHash (hs : List Hash) : Hash :=
  match Hash.allExact? hs with
  | some ns => .exact (xxHashExact ns false)
  | none => .symbolic (.combine "slice" hs)

/-- CPython 3.12's `_shuffle_bits` of a member's hash, for `frozenset_hash`. -/
def frozensetShuffle (h : UInt64) : UInt64 :=
  ((h ^^^ (89869747 : UInt64)) ^^^ (h <<< (16 : UInt64))) * (3644798167 : UInt64)

/-- The `^` of the shuffled hashes `hs`: the part of `frozenset_hash` that reads the members. -/
def frozensetMix (hs : List Int) : UInt64 :=
  hs.foldl (fun acc x => acc ^^^ frozensetShuffle (toUHash x)) 0

/-- CPython 3.12's `frozenset_hash` over the exact hashes `hs` of the members: it depends only on
the members' hashes and their number, not on the table's layout. -/
def frozensetHashExact (hs : List Int) : Int :=
  let h := frozensetMix hs ^^^ ((hs.length.toUInt64 + 1) * 1927868237)
  let h := h ^^^ ((h >>> 11) ^^^ (h >>> 25))
  let h := h * 69069 + 907133923
  if h == UInt64.ofInt (-1) then 590923713 else ofUHash h

/-- The hash of a frozenset whose members have the hashes `hs`, in any order. -/
def frozensetHash (hs : List Hash) : Hash :=
  match Hash.allExact? hs with
  | some ns => .exact (frozensetHashExact ns)
  | none => .symbolic (.frozenset (hs.mergeSort (fun a b => compare a b != .gt)))

/-- The bytes that CPython hashes for a `str`: its PEP 393 buffer, Latin-1, UCS-2 or UCS-4
little-endian, by its widest character.  An ASCII `str`'s buffer is its UTF-8 bytes. -/
def strBuffer (s : PyStr) : List UInt8 :=
  if s.ascii then s.s.toUTF8.toList
  else
    let cs := s.s.toList
    let width := cs.foldl (fun w c => max w (if c.val < 256 then 1 else if c.val < 65536 then 2 else 4)) 1
    cs.flatMap fun c =>
      let v := c.val
      (List.range width).map fun i => (v >>> (8 * i).toUInt32).toUInt8

/-- `hash(s)` of a `str`: `0` if it is empty, else symbolic. -/
def strHash (s : PyStr) : Hash := if s.s.isEmpty then .exact 0 else .symbolic (.buffer (strBuffer s))

/-- `hash(b)` of a `bytes`: `0` if it is empty, else symbolic. -/
def bytesHash (b : Array UInt8) : Hash := if b.isEmpty then .exact 0 else .symbolic (.buffer b.toList)

/-- `hash(None)`: a constant in CPython 3.12 (gh-99540). -/
def noneHash : Int := 0xFCA86420

/-- The number of items of `range(start, stop, step)`, for a non-zero `step`. -/
def rangeLen (start stop step : Int) : Nat :=
  if step > 0 then ((stop - start + step - 1) / step).toNat
  else ((start - stop - step - 1) / (-step)).toNat

/-- What hashing a value here gives. -/
inductive HashResult where
  /-- Its hash. -/
  | hash (h : Hash)
  /-- CPython raises `TypeError: unhashable type`. -/
  | unhashable
  /-- It needs the store: an object, whose type's `__hash__` decides. -/
  | needsStore
  /-- The model can't tell, and the caller stops with a gap: a NaN or a traceback, whose hash is
  the address of an object that the immediate doesn't keep; a bound method, whose hash combines
  its `__self__` and its function; an `undef`, which has no hash. -/
  | unknown
  deriving DecidableEq, Repr, Inhabited

/-- The hash of the built-in constant `b`, by what CPython's hash of it depends on. -/
def builtinHash (b : Builtin) : HashResult :=
  match b.info.hash with
  | .addr => .hash (.symbolic (.const b))
  | .other => .hash (.symbolic (.builtinFn b))
  | .unhashable => .unhashable

mutual

/-- The hash of an immediate, as CPython 3.12 computes it.  A tuple or slice hashes its parts
from left to right, and the first part that has no hash here decides the result. -/
def Value.immHash : Value → HashResult
  | .none => .hash (.exact noneHash)
  | .bool b => .hash (.exact (if b then 1 else 0))
  | .int i => .hash (.exact (hashInt i))
  | .float bits => match hashFloatBits bits with
    | some h => .hash (.exact h)
    | Option.none => .unknown
  | .str s => .hash (strHash s)
  | .bytes b => .hash (bytesHash b)
  | .tuple elems => match Value.immHashes elems.toList [] with
    | .ok hs => .hash (tupleHash hs)
    | .error r => r
  | .range start stop step =>
    let n := rangeLen start stop step
    -- `range_hash` hashes `(len, start, step)`, with `None` for the parts that don't matter.
    let parts : List Hash :=
      if n == 0 then [.exact (hashInt 0), .exact noneHash, .exact noneHash]
      else if n == 1 then [.exact (hashInt 1), .exact (hashInt start), .exact noneHash]
      else [.exact (hashInt n), .exact (hashInt start), .exact (hashInt step)]
    .hash (tupleHash parts)
  | .slice lo hi step =>
    match Value.immHash lo, Value.immHash hi, Value.immHash step with
    | .hash a, .hash b, .hash c => .hash (sliceHash [a, b, c])
    | .hash _, .hash _, r => r
    | .hash _, r, _ => r
    | r, _, _ => r
  | .symHash src => .hash (.symbolic src.reduced)
  | .builtin b => builtinHash b
  | .notImplemented => .hash (.symbolic (.singleton false))
  | .ellipsis => .hash (.symbolic (.singleton true))
  -- CPython hashes a built-in type's `tp_new` as a bound built-in function, from its `__self__`
  -- and its C function, which the model doesn't compute.
  | .descr _ _ .tpNew => .unknown
  | .descr t name _ => .hash (.symbolic (.descr t name))
  -- A static method of a built-in type is the built-in function that `staticmethod.__get__`
  -- gives.  CPython hashes it from the type that holds it (its `m_self`; `__self__` reads `None`)
  -- and its C function: one hash per type and name, and not the descriptor's own.
  | .bound .none t name .staticMethod =>
    .hash (.symbolic (.combine "<staticmethod>" [.symbolic (.descr t name)]))
  | .obj _ => .needsStore
  | .undef _ | .bound .. | .method .. | .traceback => .unknown

/-- The hashes of `vs` after the hashes `acc` (in reverse), or the result of the first one that
has no hash here.  Tail-recursive, so that a long tuple doesn't grow the native stack. -/
def Value.immHashes : List Value → List Hash → Except HashResult (List Hash)
  | [], acc => .ok acc.reverse
  | v :: vs, acc => match Value.immHash v with
    | .hash h => Value.immHashes vs (h :: acc)
    | r => .error r

end

end

end StrataPython.Dyn.Sem
