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

Key theorems: `Hash.encode_inj` and `encodeHashes_inj` (the encoding of hashes determines them);
the injectivity of each kind of source other than `reduced` (`HashSrc.buffer_inj` and its
siblings) and their distinct tags (`HashSrc.tag_buffer` and its siblings), so that two sources
are equal only when the same kind is applied to equal arguments; `HashSrc.reduced_reduced`.
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
  deriving DecidableEq, Repr, Hashable, Ord

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
  deriving DecidableEq, Repr, Inhabited, Hashable, Ord

end

/-- What a symbolic hash is computed from, encoded as a list of numbers.  Only the functions of
the namespace `HashSrc` below build one (its constructor is private), and two of them build equal
sources exactly when they are the same function applied to equal arguments, except that
`reduced` gives back a source that is already reduced.  The order is the order of the codes. -/
public structure HashSrc where
  private mk ::
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
  deriving DecidableEq, Repr, Hashable, Ord

/-- An integer as two numbers: its sign and its absolute value. -/
def encodeInt (i : Int) : List Nat := [if i < 0 then 1 else 0, i.natAbs]

/-- A hash as numbers: a tag, then an exact hash's integer or a source's length and code. -/
def Hash.encode : Hash → List Nat
  | .exact h => 0 :: encodeInt h
  | .symbolic src => 1 :: src.code.length :: src.code

/-- `hs`, each prefixed by its own encoding's length, so that the list can be split again. -/
def encodeHashes (hs : List Hash) : List Nat :=
  hs.length :: hs.flatMap fun h => let c := h.encode; c.length :: c

/-- `encodeInt` is injective. -/
public theorem encodeInt_inj {a b : Int} (h : encodeInt a = encodeInt b) : a = b := by
  simp only [encodeInt, List.cons.injEq, and_true] at h
  obtain ⟨hs, hn⟩ := h
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp [ha, hb] at hs <;> omega

/-- A hash's encoding determines it. -/
public theorem Hash.encode_inj {a b : Hash} (h : a.encode = b.encode) : a = b := by
  cases a <;> cases b <;> simp [Hash.encode] at h
  · rw [encodeInt_inj h]
  · rename_i s t; rw [HashSrc.ext h.2]

/-- The parts of `encodeHashes`, after the count. -/
public def encodeParts (hs : List Hash) : List Nat := hs.flatMap fun h => h.encode.length :: h.encode

/-- The parts of two lists of hashes of one length, followed by anything, determine the lists. -/
public theorem encodeParts_append_inj : ∀ {hs hs' : List Hash} {r r' : List Nat},
    hs.length = hs'.length → encodeParts hs ++ r = encodeParts hs' ++ r' → hs = hs' ∧ r = r'
  | [], [], _, _, _, h => by simpa [encodeParts] using h
  | a :: as, b :: bs, r, r', hl, h => by
    simp only [encodeParts, List.flatMap_cons, List.cons_append, List.append_assoc,
      List.cons.injEq] at h
    obtain ⟨hlen, h⟩ := h
    obtain ⟨hab, hrest⟩ := List.append_inj h hlen
    have hab' := Hash.encode_inj hab
    obtain ⟨h1, h2⟩ := encodeParts_append_inj (by simpa using hl) hrest
    exact ⟨by rw [hab', h1], h2⟩

/-- `encodeHashes` is injective. -/
public theorem encodeHashes_inj {hs hs' : List Hash} (h : encodeHashes hs = encodeHashes hs') : hs = hs' := by
  simp only [encodeHashes, List.cons.injEq] at h
  have hparts := encodeParts_append_inj (r := []) (r' := []) h.1 (by simpa [encodeParts] using h.2)
  exact hparts.1

end

namespace HashSrc

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

/-- A buffer source starts with its own tag. -/
public theorem tag_buffer (b : List UInt8) : (buffer b).tag = some 0 := by
  unfold tag buffer; rfl
/-- A address source starts with its own tag. -/
public theorem tag_addr (id : ObjId) : (addr id).tag = some 1 := by
  unfold tag addr; rfl
/-- A constant source starts with its own tag. -/
public theorem tag_const (b : Builtin) : (const b).tag = some 2 := by
  unfold tag const; rfl
/-- A tuple source starts with its own tag. -/
public theorem tag_tuple (ps : List Hash) : (tuple ps).tag = some 3 := by
  unfold tag tuple; rfl
/-- A frozenset source starts with its own tag. -/
public theorem tag_frozenset (ps : List Hash) : (frozenset ps).tag = some 4 := by
  unfold tag frozenset; rfl
/-- A combined source starts with its own tag. -/
public theorem tag_combine (t : String) (ps : List Hash) : (combine t ps).tag = some 5 := by
  unfold tag combine; rfl
/-- A singleton source starts with its own tag. -/
public theorem tag_singleton (e : Bool) : (singleton e).tag = some 7 := by
  unfold tag singleton; rfl
/-- A built-in function source starts with its own tag. -/
public theorem tag_builtinFn (b : Builtin) : (builtinFn b).tag = some 8 := by
  unfold tag builtinFn; rfl
/-- A descriptor source starts with its own tag. -/
public theorem tag_descr (t : Builtin) (n : String) : (descr t n).tag = some 9 := by
  unfold tag descr; rfl

/-- A source that `reduced` makes starts with the tag `6`. -/
public theorem tag_reduced (src : HashSrc) : src.reduced.tag = some 6 := by
  unfold tag reduced
  split
  · rename_i hc; simp [hc]
  · rfl

/-- `reduced` is injective on the sources it doesn't give back: those not reduced already. -/
public theorem reduced_inj {a b : HashSrc} (ha : a.tag ≠ some 6) (hb : b.tag ≠ some 6)
    (h : a.reduced = b.reduced) : a = b := by
  rcases a with ⟨ca⟩
  rcases b with ⟨cb⟩
  have hca : ∀ t, ca ≠ 6 :: t := fun t e => ha (by simp [tag, e])
  have hcb : ∀ t, cb ≠ 6 :: t := fun t e => hb (by simp [tag, e])
  have hra : reduced ⟨ca⟩ = ⟨6 :: ca⟩ := by
    unfold reduced; split
    · rename_i t e; exact absurd e (hca t)
    · rfl
  have hrb : reduced ⟨cb⟩ = ⟨6 :: cb⟩ := by
    unfold reduced; split
    · rename_i t e; exact absurd e (hcb t)
    · rfl
  rw [hra, hrb] at h
  have hc := congrArg code h
  simp only [List.cons.injEq, true_and] at hc
  rw [hc]

/-- Equal buffer sources have equal bytes. -/
public theorem buffer_inj {a b : List UInt8} (h : buffer a = buffer b) : a = b := by
  have hc := congrArg code h
  simp only [buffer, List.cons.injEq, true_and] at hc
  exact (List.map_inj_right (fun x y hxy => UInt8.toNat_inj.mp hxy)).mp hc

/-- Equal address sources are of one object. -/
public theorem addr_inj {a b : ObjId} (h : addr a = addr b) : a = b := by
  have hc := congrArg code h
  simpa [addr] using hc

/-- `ctorIdx` is injective on built-in constants. -/
public theorem _root_.StrataPython.Dyn.Sem.Builtin.ctorIdx_inj {a b : Builtin}
    (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← Builtin.ofNat_ctorIdx a, h, Builtin.ofNat_ctorIdx]

/-- Equal constant sources are of one constant. -/
public theorem const_inj {a b : Builtin} (h : const a = const b) : a = b := by
  have hc := congrArg code h
  simp only [const, List.cons.injEq, and_true, true_and] at hc
  exact Builtin.ctorIdx_inj hc

/-- Equal built-in function sources are of one function. -/
public theorem builtinFn_inj {a b : Builtin} (h : builtinFn a = builtinFn b) : a = b := by
  have hc := congrArg code h
  simp only [builtinFn, List.cons.injEq, and_true, true_and] at hc
  exact Builtin.ctorIdx_inj hc

/-- Equal tuple sources have equal parts. -/
public theorem tuple_inj {a b : List Hash} (h : tuple a = tuple b) : a = b := by
  have hc := congrArg code h
  simp only [tuple, List.cons.injEq, true_and] at hc
  exact encodeHashes_inj hc

/-- Equal frozenset sources have equal parts. -/
public theorem frozenset_inj {a b : List Hash} (h : frozenset a = frozenset b) : a = b := by
  have hc := congrArg code h
  simp only [frozenset, List.cons.injEq, true_and] at hc
  exact encodeHashes_inj hc

/-- Equal singleton sources are of one singleton. -/
public theorem singleton_inj {a b : Bool} (h : singleton a = singleton b) : a = b := by
  have hc := congrArg code h
  cases a <;> cases b <;> simp_all [singleton]

/-- A string's characters as numbers determine it. -/
private theorem chars_inj {a b : String}
    (h : a.toList.map (·.toNat) = b.toList.map (·.toNat)) : a = b := by
  have hl : a.toList = b.toList := (List.map_inj_right (fun x y hxy => Char.toNat_inj.mp hxy)).mp h
  exact String.toList_inj.mp hl

/-- Equal combined sources have equal tags and parts. -/
public theorem combine_inj {t t' : String} {a b : List Hash} (h : combine t a = combine t' b) :
    t = t' ∧ a = b := by
  have hc := congrArg code h
  simp only [combine, List.cons.injEq] at hc
  have hl := hc.2.1
  have hrest := hc.2.2
  have hlen : (t.toList.map (·.toNat)).length = (t'.toList.map (·.toNat)).length := by
    simp only [List.length_map, String.length_toList, hl]
  obtain ⟨hchars, hparts⟩ := List.append_inj hrest hlen
  exact ⟨chars_inj hchars, encodeHashes_inj hparts⟩

/-- Equal descriptor sources are of one descriptor. -/
public theorem descr_inj {t t' : Builtin} {n n' : String} (h : descr t n = descr t' n') :
    t = t' ∧ n = n' := by
  have hc := congrArg code h
  simp only [descr, List.cons.injEq] at hc
  obtain ⟨-, hi, -, hchars⟩ := hc
  exact ⟨Builtin.ctorIdx_inj hi, chars_inj hchars⟩

/-- Reducing a reduced source gives it back. -/
public theorem reduced_reduced (s : HashSrc) : s.reduced.reduced = s.reduced := by
  rcases s with ⟨c⟩
  cases c with
  | nil => rfl
  | cons x xs =>
    by_cases hx : x = 6
    · subst hx; rfl
    · simp [reduced, hx]

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
  deriving BEq, Repr, Inhabited, Hashable

/-- The `float` `f`. -/
def Value.ofFloat (f : Float) : Value := .float f.toBits

/-- The `str` whose text is `s`. -/
def Value.ofString (s : String) : Value := .str (.ofString s)

end

end StrataPython.Dyn.Sem
