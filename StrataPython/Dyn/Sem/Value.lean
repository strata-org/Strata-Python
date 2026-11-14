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

/-- A Python `str`: its text, whether every character is ASCII, so that indexing an ASCII string
is by byte, and its characters, computed once when a non-ASCII string is first indexed, so that
indexing it is by position.  The text decides the other fields. -/
structure PyStr where
  s : String
  ascii : Bool
  ascii_eq : ascii = isAscii s
  chars : Thunk (Array Char)
  chars_eq : chars.get = s.toList.toArray

/-- Two `str`s with the same text are equal. -/
theorem PyStr.eq_of_s {a b : PyStr} (h : a.s = b.s) : a = b := by
  cases a with | mk s₁ a₁ ha₁ c₁ hc₁ => cases b with | mk s₂ a₂ ha₂ c₂ hc₂ =>
  cases h
  have hc : c₁ = c₂ := by
    cases c₁; cases c₂; simp only [Thunk.get] at hc₁ hc₂; congr; funext u; cases u; simp [hc₁, hc₂]
  subst ha₁ ha₂ hc; rfl

instance : DecidableEq PyStr := fun a b =>
  if h : a.s = b.s then isTrue (PyStr.eq_of_s h) else isFalse fun e => h (e ▸ rfl)

instance : Hashable PyStr := ⟨fun p => hash p.s⟩

/-- `str`s are ordered by their text, which decides the other fields. -/
instance : Ord PyStr := ⟨fun a b => compare a.s b.s⟩

instance : Repr PyStr where
  reprPrec p _ := Std.Format.bracket "{ "
    (f!"s := {repr p.s}," ++ Std.Format.line ++ f!"ascii := {repr p.ascii}," ++ Std.Format.line ++
      "ascii_eq := _") " }"

/-- The `str` whose text is `s`. -/
def PyStr.ofString (s : String) : PyStr :=
  ⟨s, isAscii s, rfl, Thunk.mk fun _ => s.toList.toArray, rfl⟩

/-- Whether the concatenation of two texts is ASCII. -/
private theorem isAscii_append (a b : String) : isAscii (a ++ b) = (isAscii a && isAscii b) := by
  simp [isAscii, String.toList_append, List.all_append]

/-- `x + y` for two `str`s: whether the result is ASCII comes from the two parts, without a scan
of the result. -/
def PyStr.append (x y : PyStr) : PyStr :=
  -- The thunk holds the new text only, not `x` and `y`, so that a chain of concatenations keeps
  -- no earlier text alive.
  let t := x.s ++ y.s
  ⟨t, x.ascii && y.ascii, by rw [x.ascii_eq, y.ascii_eq, isAscii_append],
    Thunk.mk fun _ => t.toList.toArray, rfl⟩

/-- `PyStr.append` gives the `str` whose text is the concatenation. -/
theorem PyStr.append_eq_ofString (x y : PyStr) : x.append y = .ofString (x.s ++ y.s) :=
  PyStr.eq_of_s rfl

/-- The character at position `i` of `t`, `i` in range: by byte for an ASCII string, else by
position in its characters. -/
def PyStr.charAt (t : PyStr) (i : Nat) : Char :=
  if t.ascii then String.Pos.Raw.get t.s ⟨i⟩ else t.chars.get.getD i ' '

/-- The number of characters of `t`. -/
def PyStr.length (t : PyStr) : Nat :=
  if t.ascii then t.s.utf8ByteSize else t.chars.get.size

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
  only in the bound form `.bound self t "__new__" .tpNew`, by a class call's path, and handed at
  once to the call (`Proto.callTpNew`, `Proto.startTpNew`); no attribute lookup gives it.  A
  call (`callN`), an identity test and a render of one stop with a model-invariant gap, and its
  hash is unknown; its `boundType` is a plain type name, which can't gap and reveals nothing. -/
  | tpNew
  deriving DecidableEq, Repr, Inhabited, Ord

instance : Hashable DescrKind := ⟨fun k => hash k.ctorIdx⟩

end

/-- What a symbolic hash is computed from: a tree of the functions of the namespace `HashSrc`
below, applied to their arguments.  A part of `tuple'`, `frozenset'` and `combine'` is a hash: an
exact one's number (`inl`) or a symbolic one's source (`inr`).  The semantics builds a source only
with the leaf constructors and the functions `tuple`, `frozenset`, `combine` and `reduced` (their
bodies are exposed, so that rules that reach them can be registered); two of them build equal
sources exactly when they are the same function applied to equal arguments, except that
`reduced` gives back a source that is already reduced.  A nested source shares its parts, so
building one costs only its own constructor.  The order goes by `code`, the source as a list of
numbers; equality (`decEqSrc`) and `Hashable` (`shash`) walk the tree. -/
public inductive HashSrc where
  /-- The bytes that CPython hashes: a `bytes`' octets, or a `str`'s PEP 393 buffer. -/
  | buffer (b : ByteArray)
  /-- The address of an object of the store. -/
  | addr (id : ObjId)
  /-- The address of a built-in constant whose hash is its address (`BuiltinHash.addr`). -/
  | const (b : Builtin)
  /-- A tuple's hash, from its members' hashes (`tuple`). -/
  | tuple' (parts : List (Int ⊕ HashSrc))
  /-- A frozenset's hash, from its members' hashes (`frozenset`). -/
  | frozenset' (parts : List (Int ⊕ HashSrc))
  /-- A hash that a value's `__hash__` combines from others, named by `tag` (`combine`). -/
  | combine' (tag : String) (parts : List (Int ⊕ HashSrc))
  /-- `hash(n)` of an `int` `n` whose number is the hash `src` (`reduced`). -/
  | reduced' (src : HashSrc)
  /-- The address of `Ellipsis` (`true`) or of `NotImplemented` (`false`). -/
  | singleton (ellipsis : Bool)
  /-- Two addresses combined: the built-in function `b`'s hash, from its `__self__` and its C
  function.  It is not an object's address. -/
  | builtinFn (b : Builtin)
  /-- The address of the descriptor `name` of the built-in type `t`, the type whose `__dict__`
  holds it (`bool.__add__ is int.__add__`, so its type is `int`). -/
  | descr (t : Builtin) (name : String)

@[expose] public section

/-- An integer as two numbers: its sign and its absolute value. -/
def encodeInt (i : Int) : List Nat := [if i < 0 then 1 else 0, i.natAbs]

namespace HashSrc

mutual
/-- A source as numbers: a tag per constructor, then its arguments; each part of a list is
prefixed by its encoding's length, so that the list can be split again. -/
def code : HashSrc → List Nat
  | buffer b => 0 :: b.data.toList.map (·.toNat)
  | addr id => [1, id]
  | const b => [2, b.ctorIdx]
  | tuple' ps => 3 :: ps.length :: partsCode ps
  | frozenset' ps => 4 :: ps.length :: partsCode ps
  | combine' t ps => 5 :: t.length :: (t.toList.map (·.toNat) ++ ps.length :: partsCode ps)
  | reduced' s => 6 :: s.code
  | singleton e => [7, if e then 1 else 0]
  | builtinFn b => [8, b.ctorIdx]
  | descr t n => 9 :: t.ctorIdx :: n.length :: n.toList.map (·.toNat)

/-- A part as numbers: a tag, then an exact hash's integer or a source's length and code. -/
def partCode : Int ⊕ HashSrc → List Nat
  | .inl h => 0 :: encodeInt h
  | .inr s => 1 :: s.code.length :: s.code

/-- Parts as numbers, each prefixed by its encoding's length. -/
def partsCode : List (Int ⊕ HashSrc) → List Nat
  | [] => []
  | p :: ps => (partCode p).length :: partCode p ++ partsCode ps
end

mutual
/-- Equality of sources, by structural recursion. It is written by hand because
`deriving DecidableEq` doesn't apply to `HashSrc`, a nested inductive through
`List (Int ⊕ HashSrc)`, in Lean 4.34. -/
def decEqSrc : (a b : HashSrc) → Decidable (a = b)
  | buffer x, buffer y =>
    if h : x = y then isTrue (h ▸ rfl)
    else isFalse (fun e => h (HashSrc.buffer.inj e))
  | addr x, addr y =>
    if h : x = y then isTrue (h ▸ rfl)
    else isFalse (fun e => h (HashSrc.addr.inj e))
  | const x, const y =>
    if h : x = y then isTrue (h ▸ rfl)
    else isFalse (fun e => h (HashSrc.const.inj e))
  | tuple' ps, tuple' qs => match decEqParts ps qs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (HashSrc.tuple'.inj e))
  | frozenset' ps, frozenset' qs => match decEqParts ps qs with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (HashSrc.frozenset'.inj e))
  | combine' t ps, combine' u qs =>
    if ht : t = u then
      match decEqParts ps qs with
      | isTrue h => isTrue (ht ▸ h ▸ rfl)
      | isFalse h => isFalse (fun e => h (HashSrc.combine'.inj e).2)
    else isFalse (fun e => ht (HashSrc.combine'.inj e).1)
  | reduced' x, reduced' y => match decEqSrc x y with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (HashSrc.reduced'.inj e))
  | singleton x, singleton y =>
    if h : x = y then isTrue (h ▸ rfl)
    else isFalse (fun e => h (HashSrc.singleton.inj e))
  | builtinFn x, builtinFn y =>
    if h : x = y then isTrue (h ▸ rfl)
    else isFalse (fun e => h (HashSrc.builtinFn.inj e))
  | descr t n, descr u k =>
    if h : t = u ∧ n = k then isTrue (by obtain ⟨rfl, rfl⟩ := h; rfl)
    else isFalse (fun e => h (HashSrc.descr.inj e))
  -- Different constructors.
  | buffer .., addr .. | buffer .., const .. | buffer .., tuple' .. | buffer .., frozenset' ..
  | buffer .., combine' .. | buffer .., reduced' .. | buffer .., singleton ..
  | buffer .., builtinFn .. | buffer .., descr .. | addr .., buffer .. | addr .., const ..
  | addr .., tuple' .. | addr .., frozenset' .. | addr .., combine' .. | addr .., reduced' ..
  | addr .., singleton .. | addr .., builtinFn .. | addr .., descr .. | const .., buffer ..
  | const .., addr .. | const .., tuple' .. | const .., frozenset' .. | const .., combine' ..
  | const .., reduced' .. | const .., singleton .. | const .., builtinFn .. | const .., descr ..
  | tuple' .., buffer .. | tuple' .., addr .. | tuple' .., const .. | tuple' .., frozenset' ..
  | tuple' .., combine' .. | tuple' .., reduced' .. | tuple' .., singleton ..
  | tuple' .., builtinFn .. | tuple' .., descr .. | frozenset' .., buffer ..
  | frozenset' .., addr .. | frozenset' .., const .. | frozenset' .., tuple' ..
  | frozenset' .., combine' .. | frozenset' .., reduced' .. | frozenset' .., singleton ..
  | frozenset' .., builtinFn .. | frozenset' .., descr .. | combine' .., buffer ..
  | combine' .., addr .. | combine' .., const .. | combine' .., tuple' ..
  | combine' .., frozenset' .. | combine' .., reduced' .. | combine' .., singleton ..
  | combine' .., builtinFn .. | combine' .., descr .. | reduced' .., buffer ..
  | reduced' .., addr .. | reduced' .., const .. | reduced' .., tuple' ..
  | reduced' .., frozenset' .. | reduced' .., combine' .. | reduced' .., singleton ..
  | reduced' .., builtinFn .. | reduced' .., descr .. | singleton .., buffer ..
  | singleton .., addr .. | singleton .., const .. | singleton .., tuple' ..
  | singleton .., frozenset' .. | singleton .., combine' .. | singleton .., reduced' ..
  | singleton .., builtinFn .. | singleton .., descr .. | builtinFn .., buffer ..
  | builtinFn .., addr .. | builtinFn .., const .. | builtinFn .., tuple' ..
  | builtinFn .., frozenset' .. | builtinFn .., combine' .. | builtinFn .., reduced' ..
  | builtinFn .., singleton .. | builtinFn .., descr .. | descr .., buffer .. | descr .., addr ..
  | descr .., const .. | descr .., tuple' .. | descr .., frozenset' .. | descr .., combine' ..
  | descr .., reduced' .. | descr .., singleton .. | descr .., builtinFn .. => isFalse nofun
/-- Equality of parts. -/
def decEqPart : (p q : Int ⊕ HashSrc) → Decidable (p = q)
  | .inl a, .inl b => if h : a = b then isTrue (h ▸ rfl) else isFalse (fun e => h (Sum.inl.inj e))
  | .inr a, .inr b => match decEqSrc a b with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => h (Sum.inr.inj e))
  | .inl _, .inr _ => isFalse (fun e => by cases e)
  | .inr _, .inl _ => isFalse (fun e => by cases e)
/-- Equality of lists of parts. -/
def decEqParts : (ps qs : List (Int ⊕ HashSrc)) → Decidable (ps = qs)
  | [], [] => isTrue rfl
  | p :: ps, q :: qs => match decEqPart p q with
    | isTrue h => match decEqParts ps qs with
      | isTrue h' => isTrue (h ▸ h' ▸ rfl)
      | isFalse h' => isFalse (fun e => h' (List.cons.inj e).2)
    | isFalse h => isFalse (fun e => h (List.cons.inj e).1)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
end

instance : DecidableEq HashSrc := decEqSrc

mutual
/-- A source's hash, for tables of hashes, by structural recursion. -/
def shash : HashSrc → UInt64
  | buffer b => mixHash 0 (hash b)
  | addr id => mixHash 1 (hash id)
  | const b => mixHash 2 (hash b.ctorIdx)
  | tuple' ps => mixHash 3 (shashParts ps)
  | frozenset' ps => mixHash 4 (shashParts ps)
  | combine' t ps => mixHash 5 (mixHash (hash t) (shashParts ps))
  | reduced' s => mixHash 6 (shash s)
  | singleton e => mixHash 7 (hash e)
  | builtinFn b => mixHash 8 (hash b.ctorIdx)
  | descr t n => mixHash 9 (mixHash (hash t.ctorIdx) (hash n))
/-- The hash of a list of parts. -/
def shashParts : List (Int ⊕ HashSrc) → UInt64
  | [] => 11
  | .inl a :: ps => mixHash (hash a) (shashParts ps)
  | .inr s :: ps => mixHash (shash s) (shashParts ps)
end

instance : Inhabited HashSrc := ⟨addr 0⟩
instance : Repr HashSrc := ⟨fun a n => reprPrec a.code n⟩
instance : Hashable HashSrc := ⟨shash⟩
instance : Ord HashSrc := ⟨fun a b => compare a.code b.code⟩

end HashSrc

/-- A hash: the number CPython gives, or a symbol for a number that depends on the hash seed or
on an address. -/
inductive Hash where
  | exact (h : Int)
  | symbolic (src : HashSrc)
  deriving DecidableEq, Repr, Ord

instance : Hashable Hash := ⟨fun
  | .exact h => mixHash 0 (hash h)
  | .symbolic src => mixHash 1 (hash src)⟩

/-- A hash as a part of a source. -/
def Hash.toPart : Hash → Int ⊕ HashSrc
  | .exact h => .inl h
  | .symbolic s => .inr s

end

namespace HashSrc

@[expose] section

/-- A tuple's hash, from its members' hashes. -/
public def tuple (parts : List Hash) : HashSrc := tuple' (parts.map Hash.toPart)
/-- A frozenset's hash, from its members' hashes, which the caller sorts. -/
public def frozenset (parts : List Hash) : HashSrc := frozenset' (parts.map Hash.toPart)
/-- A hash that a value's `__hash__` combines from others, named by `tag`. -/
public def combine (tag : String) (parts : List Hash) : HashSrc :=
  combine' tag (parts.map Hash.toPart)
/-- `hash(n)` of an `int` `n` whose number is the hash `src`: CPython reduces it modulo
`2^61 - 1`.  Reducing again gives it back. -/
public def reduced (src : HashSrc) : HashSrc :=
  match src with
  | reduced' _ => src
  | _ => reduced' src

/-- Whether `src` is an object's address: two such sources of different objects never give equal
hashes, since live objects have different addresses. -/
public def isAddr : HashSrc → Bool
  | addr _ | const _ | singleton _ | descr .. => true
  | _ => false

/-- The tag that starts each constructor's code (`code`'s head): different constructors build
different sources. -/
public def tag : HashSrc → Option Nat
  | buffer _ => some 0 | addr _ => some 1 | const _ => some 2 | tuple' _ => some 3
  | frozenset' _ => some 4 | combine' .. => some 5 | reduced' _ => some 6 | singleton _ => some 7
  | builtinFn _ => some 8 | descr .. => some 9

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
