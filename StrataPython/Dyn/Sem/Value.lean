/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Generated.Types

set_option autoImplicit false

/-!
# Python values

`Value` is every Python value of the semantics: an immediate, a built-in constant, or the id of
a mutable object of the store.

* A value whose type is exactly `NoneType`, `bool`, `int`, `float`, `str`, `bytes`, `tuple`,
  `range` or `slice` is always an immediate.  An instance of a user subclass of one of them is an
  object of the store.
* A `float` is kept as its IEEE 754 bits, so that two floats are equal exactly when their bits
  are.
* `symHash` is an `int` whose number the model doesn't know, because it depends on the hash seed
  or on an object's address: the result of `hash(x)` for a value whose hash is symbolic.
* A hash (`Hash`) is exact, or symbolic with a source (`HashSrc`).  Two hashes are equal under
  every seed when both are exact and equal, or both are symbolic with equal sources.

The theorems about hashes and their sources, and the lawfulness of `Value.beq`, are in
`ValueProps.lean`.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- The id of an object of the store: its index. -/
abbrev ObjId := Nat

/-- Whether every character of `s` is ASCII. -/
def isAscii (s : String) : Bool := s.toList.all fun c => c.val < 128

/-- A Python `str`: its text, and whether every character is ASCII, so that indexing an ASCII
string is by byte. -/
structure PyStr where
  s : String
  ascii : Bool
  ascii_eq : ascii = isAscii s
  deriving DecidableEq, Repr, Ord

instance : Hashable PyStr := ⟨fun p => hash p.s⟩

/-- The `str` whose text is `s`. -/
def PyStr.ofString (s : String) : PyStr := ⟨s, isAscii s, rfl⟩

instance : Inhabited PyStr := ⟨.ofString ""⟩

/-- What a descriptor of a built-in type is, which decides its `type()`. -/
inductive DescrKind where
  /-- A method, `method_descriptor`: `str.__dict__["upper"]`. -/
  | method
  /-- A slot wrapper, `wrapper_descriptor`: `int.__dict__["__add__"]`. -/
  | slotWrapper
  /-- `classmethod_descriptor`: `dict.__dict__["fromkeys"]`. -/
  | classMethod
  /-- A static method of a built-in type, a `staticmethod`: `str.__dict__["maketrans"]`. -/
  | staticMethod
  /-- `getset_descriptor`: `int.__dict__["real"]`. -/
  | getset
  /-- `member_descriptor`: `slice.__dict__["start"]`. -/
  | member
  /-- A built-in type's `tp_new` as `type_call` calls it, without `tp_new_wrapper`'s check: made
  only by a class call's path and handed at once to the call (`Proto.callTpNew`,
  `Proto.startTpNew`).  A call (`callN`), an identity test and a render of one stop with a
  model-invariant gap, and its hash is unknown; its `boundType` is a plain type name, which can't
  gap and reveals nothing. -/
  | tpNew
  deriving DecidableEq, Repr, Inhabited, Ord

instance : Hashable DescrKind := ⟨fun k => hash k.ctorIdx⟩

end

/-- What a symbolic hash is computed from, encoded as a list of numbers.  The semantics builds
one only with the functions of the namespace `HashSrc` below (their bodies are exposed, so that
rules that reach them can be registered), and two of them build equal sources exactly when they
are the same function applied to equal arguments, except that `reduced` gives back a source that
is already reduced.  The order is the order of the codes. -/
public structure HashSrc where
  mk ::
  code : List Nat

namespace HashSrc

/-- Two sources are equal when their codes are. -/
public theorem ext {a b : HashSrc} (h : a.code = b.code) : a = b := by
  cases a; cases b; simp_all

public instance : DecidableEq HashSrc := fun a b =>
  if h : a.code = b.code then isTrue (ext h) else isFalse fun e => h (e ▸ rfl)

public instance : Repr HashSrc := ⟨fun a n => reprPrec a.code n⟩
public instance : Hashable HashSrc := ⟨fun a => hash a.code⟩
public instance : Ord HashSrc := ⟨fun a b => compare a.code b.code⟩

end HashSrc

@[expose] public section

/-- A hash: the number CPython gives, or a symbol for a number that depends on the hash seed or
on an address. -/
inductive Hash where
  | exact (h : Int)
  | symbolic (src : HashSrc)
  deriving DecidableEq, Repr, Ord

instance : Hashable Hash := ⟨fun
  | .exact h => mixHash 0 (hash h)
  | .symbolic src => mixHash 1 (hash src)⟩

/-- An integer as two numbers: its sign and its absolute value. -/
def encodeInt (i : Int) : List Nat := [if i < 0 then 1 else 0, i.natAbs]

/-- A hash as numbers: a tag, then an exact hash's integer or a source's length and code. -/
def Hash.encode : Hash → List Nat
  | .exact h => 0 :: encodeInt h
  | .symbolic src => 1 :: src.code.length :: src.code

/-- `hs`, each prefixed by its own encoding's length, so that the list can be split again. -/
def encodeHashes (hs : List Hash) : List Nat :=
  hs.length :: hs.flatMap fun h => let c := h.encode; c.length :: c

/-- The parts of `encodeHashes`, after the count. -/
public def encodeParts (hs : List Hash) : List Nat := hs.flatMap fun h => h.encode.length :: h.encode

end

namespace HashSrc

@[expose] section

/-- The bytes that CPython hashes: a `bytes`' octets, or a `str`'s PEP 393 buffer. -/
public def buffer (b : List UInt8) : HashSrc := ⟨0 :: b.map (·.toNat)⟩
/-- The address of an object of the store. -/
public def addr (id : ObjId) : HashSrc := ⟨[1, id]⟩
/-- The address of a built-in constant whose hash is its address (`BuiltinHash.addr`). -/
public def const (b : Builtin) : HashSrc := ⟨[2, b.ctorIdx]⟩
/-- A tuple's hash, from its members' hashes. -/
public def tuple (parts : List Hash) : HashSrc := ⟨3 :: encodeHashes parts⟩
/-- A frozenset's hash, from its members' hashes, which the caller sorts. -/
public def frozenset (parts : List Hash) : HashSrc := ⟨4 :: encodeHashes parts⟩
/-- A hash that a value's `__hash__` combines from others, named by `tag`. -/
public def combine (tag : String) (parts : List Hash) : HashSrc :=
  ⟨5 :: tag.length :: (tag.toList.map (·.toNat) ++ encodeHashes parts)⟩
/-- `hash(n)` of an `int` `n` whose number is the hash `src`: CPython reduces it modulo
`2^61 - 1`.  Reducing again gives it back. -/
public def reduced (src : HashSrc) : HashSrc :=
  match src.code with
  | 6 :: _ => src
  | c => ⟨6 :: c⟩
/-- The address of `Ellipsis` (`true`) or of `NotImplemented` (`false`). -/
public def singleton (ellipsis : Bool) : HashSrc := ⟨[7, if ellipsis then 1 else 0]⟩
/-- Two addresses combined: the built-in function `b`'s hash, from its `__self__` and its C
function.  It is not an object's address. -/
public def builtinFn (b : Builtin) : HashSrc := ⟨[8, b.ctorIdx]⟩
/-- The address of the descriptor `name` of the built-in type `t`, the type whose `__dict__`
holds it (`bool.__add__ is int.__add__`, so its type is `int`). -/
public def descr (t : Builtin) (name : String) : HashSrc :=
  ⟨9 :: t.ctorIdx :: name.length :: name.toList.map (·.toNat)⟩

/-- Whether `src` is an object's address: two such sources of different objects never give equal
hashes, since live objects have different addresses. -/
public def isAddr (src : HashSrc) : Bool :=
  match src.code with
  | 1 :: _ | 2 :: _ | 7 :: _ | 9 :: _ => true
  | _ => false

/-- The tag that starts each constructor's code: different constructors build different sources. -/
public def tag (s : HashSrc) : Option Nat := s.code.head?

end

end HashSrc

@[expose] public section

/-- A Python value. -/
inductive Value where
  /-- A name not yet assigned. `name` is diagnostic only. -/
  | undef (name : String)
  | none
  | notImplemented
  | ellipsis
  | bool (b : Bool)
  | int (i : Int)
  /-- A `float`, by its IEEE 754 bits. -/
  | float (bits : UInt64)
  | str (s : PyStr)
  | bytes (b : Array UInt8)
  | tuple (elems : Array Value)
  | range (start stop step : Int)
  | slice (lo hi step : Value)
  /-- An `int` whose number depends on the hash seed or on an object's address. -/
  | symHash (src : HashSrc)
  /-- A built-in function, type or other built-in object. -/
  | builtin (b : Builtin)
  /-- A descriptor of the built-in type `t`, the type whose `__dict__` holds it:
  `str.__dict__["upper"]`. -/
  | descr (t : Builtin) (name : String) (kind : DescrKind)
  /-- A descriptor of the built-in type `t` (the type whose `__dict__` holds it) bound to `self`:
  `l.append`. -/
  | bound (self : Value) (t : Builtin) (name : String) (kind : DescrKind)
  /-- A Python function bound to `self`: `obj.m`. -/
  | method (func self : Value)
  /-- An opaque traceback. -/
  | traceback
  /-- An object of the store. -/
  | obj (id : ObjId)
  deriving Repr, Inhabited

/-- Structural equality of values, floats by their bits: a total function, so that rules that
compare values can be registered. -/
def Value.beq : Value → Value → Bool
  | .undef a, .undef b => a == b
  | .none, .none | .notImplemented, .notImplemented | .ellipsis, .ellipsis => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .float a, .float b => a == b
  | .str a, .str b => a == b
  | .bytes a, .bytes b => a == b
  | .tuple xs, .tuple ys =>
    xs.size == ys.size && (xs.attach.zip ys).all fun (⟨x, _⟩, y) => Value.beq x y
  | .range a b c, .range d e f => a == d && b == e && c == f
  | .slice a b c, .slice d e f => Value.beq a d && Value.beq b e && Value.beq c f
  | .symHash a, .symHash b => a == b
  | .builtin a, .builtin b => a == b
  | .descr t n k, .descr t' n' k' => t == t' && n == n' && k == k'
  | .bound s t n k, .bound s' t' n' k' => Value.beq s s' && t == t' && n == n' && k == k'
  | .method f s, .method f' s' => Value.beq f f' && Value.beq s s'
  | .traceback, .traceback => true
  | .obj a, .obj b => a == b
  | _, _ => false
termination_by a => sizeOf a
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

instance : BEq Value := ⟨Value.beq⟩

/-- A hash of a value that agrees with `Value.beq`: a total function, so that rules that index
values can be registered. -/
def Value.hashV : Value → UInt64
  | .undef a => mixHash 0 (hash a)
  | .none => 1
  | .notImplemented => 2
  | .ellipsis => 3
  | .bool b => mixHash 4 (hash b)
  | .int i => mixHash 5 (hash i)
  | .float f => mixHash 6 (hash f)
  | .str s => mixHash 7 (hash s)
  | .bytes b => mixHash 8 (hash b)
  | .tuple xs => xs.attach.foldl (fun acc ⟨x, _⟩ => mixHash acc (Value.hashV x)) 9
  | .range a b c => mixHash 10 (mixHash (hash a) (mixHash (hash b) (hash c)))
  | .slice a b c => mixHash 11 (mixHash a.hashV (mixHash b.hashV c.hashV))
  | .symHash a => mixHash 12 (hash a)
  | .builtin b => mixHash 13 (hash b)
  | .descr t n k => mixHash 14 (mixHash (hash t) (mixHash (hash n) (hash k)))
  | .bound s t n k => mixHash 15 (mixHash s.hashV (mixHash (hash t) (mixHash (hash n) (hash k))))
  | .method f s => mixHash 16 (mixHash f.hashV s.hashV)
  | .traceback => 17
  | .obj id => mixHash 18 (hash id)
termination_by v => sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := Array.sizeOf_lt_of_mem ‹_ ∈ xs›; omega)

instance : Hashable Value := ⟨Value.hashV⟩

/-- The `float` `f`. -/
def Value.ofFloat (f : Float) : Value := .float f.toBits

/-- The `str` whose text is `s`. -/
def Value.ofString (s : String) : Value := .str (.ofString s)

end

end StrataPython.Dyn.Sem
