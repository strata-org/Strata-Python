/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Value

set_option autoImplicit false

/-!
# Immediates as generic code sees them

`Imm V` is a value that is not an object, with `V` where it holds values: one constructor per
kind of immediate of `Value`.  The record of primitives makes a `V` from an `Imm V` and views a
`V` as one, so that generic code never names `Value` or an object id.

`SymInt` is an `int` whose number is unknown: a hash source with the proof that no store object's
address is inside it (`HashSrc.storeAddrFree`).  CPython reuses a freed object's address, so an
`int` made from such an address could compare wrongly with another; and generic code can't forge
one that names an object.

The round trip between `Imm Value` and `Value` is proved in `ImmProps.lean`.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- The constructor indices of the built-in constants that CPython can free: the names that
`site` adds to builtins after the interpreter copies the builtins dict, and `__loader__` and
`__spec__`.  Every other built-in constant lives as long as the interpreter. -/
def Builtin.freeableIdx : List Nat :=
  [Builtin.exit, .quit, .help, .copyright, .credits, .license, .BuiltinImporter, .__spec__].map
    (·.ctorIdx)

namespace HashSrc

mutual
/-- Whether the code of a source holds no store object's address, through `tuple`, `frozenset`,
`combine` and `reduced`; the address of a freeable built-in constant counts as one.  It fails
closed: a code without the shape of a constructor's code gives `false`. -/
def codeFree : List Nat → Bool
  | 0 :: bs => bs.all (· < 256)
  | [2, i] => i < Builtin.allConstants.size && !Builtin.freeableIdx.contains i
  | [7, b] => b ≤ 1
  | [8, i] => i < Builtin.allConstants.size
  | 9 :: t :: len :: cs => t < Builtin.allConstants.size && cs.length == len
  | 3 :: rest => hashesFree rest
  | 4 :: rest => hashesFree rest
  | 5 :: tl :: rest => tl ≤ rest.length && hashesFree (rest.drop tl)
  | 6 :: c => c.head? != some 6 && codeFree c
  | _ => false
termination_by l => l.length
decreasing_by all_goals first | omega | (simp only [List.length_drop, List.length_cons]; omega)

/-- Whether `encodeHashes`' output, a count and that many parts, holds no store object's
address. -/
def hashesFree : List Nat → Bool
  | n :: parts => partsFree n parts
  | [] => false
termination_by l => l.length

/-- Whether exactly `n` parts of `encodeHashes`, and nothing after them, hold no store object's
address. -/
def partsFree : Nat → List Nat → Bool
  | 0, [] => true
  | n + 1, len :: rest =>
    len ≤ rest.length && encFree (rest.take len) && partsFree n (rest.drop len)
  | _, _ => false
termination_by _ l => l.length
decreasing_by all_goals first | omega | (simp only [List.length_drop, List.length_take, List.length_cons]; omega)

/-- Whether one hash's encoding holds no store object's address. -/
def encFree : List Nat → Bool
  | [0, sign, _] => sign ≤ 1
  | 1 :: n :: c => c.length == n && codeFree c
  | _ => false
termination_by l => l.length
decreasing_by all_goals first | omega | (simp only [List.length_cons]; omega)
end

/-- Whether no store object's address is inside `src`. -/
def storeAddrFree (src : HashSrc) : Bool := codeFree src.code

end HashSrc

/-- An `int` whose number is unknown, from a hash source that holds no store object's address. -/
abbrev SymInt : Type := { src : HashSrc // src.storeAddrFree = true }

/-- A value that is not an object, with `V` where it holds values. -/
inductive Imm (V : Type) where
  | none
  | notImplemented
  | ellipsis
  | bool (b : Bool)
  | int (i : Int)
  /-- A `float`, by its IEEE 754 bits. -/
  | float (bits : UInt64)
  | str (s : PyStr)
  | bytes (b : Array UInt8)
  | tuple (elems : Array V)
  | range (start stop step : Int)
  | slice (lo hi step : V)
  | symHash (n : SymInt)
  | builtin (b : Builtin)
  | descr (t : Builtin) (name : String) (kind : DescrKind)
  | bound (self : V) (t : Builtin) (name : String) (kind : DescrKind)
  | method (func self : V)
  | traceback
  deriving Repr, Inhabited

/-- The immediate `i` as a value. -/
def Imm.toValue : Imm Value → Value
  | .none => .none
  | .notImplemented => .notImplemented
  | .ellipsis => .ellipsis
  | .bool b => .bool b
  | .int i => .int i
  | .float f => .float f
  | .str s => .str s
  | .bytes b => .bytes b
  | .tuple xs => .tuple xs
  | .range a b c => .range a b c
  | .slice a b c => .slice a b c
  | .symHash n => .symHash n.1
  | .builtin b => .builtin b
  | .descr t n k => .descr t n k
  | .bound s t n k => .bound s t n k
  | .method f s => .method f s
  | .traceback => .traceback

/-- `v` as an immediate: `none` for an object, an unassigned value, and a symbolic hash value
whose source holds a store object's address. -/
def Value.toImm? : Value → Option (Imm Value)
  | .undef _ | .obj _ => Option.none
  | .none => some .none
  | .notImplemented => some .notImplemented
  | .ellipsis => some .ellipsis
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .float f => some (.float f)
  | .str s => some (.str s)
  | .bytes b => some (.bytes b)
  | .tuple xs => some (.tuple xs)
  | .range a b c => some (.range a b c)
  | .slice a b c => some (.slice a b c)
  | .symHash src => if h : src.storeAddrFree then some (.symHash ⟨src, h⟩) else Option.none
  | .builtin b => some (.builtin b)
  | .descr t n k => some (.descr t n k)
  | .bound s t n k => some (.bound s t n k)
  | .method f s => some (.method f s)
  | .traceback => some .traceback

end

end StrataPython.Dyn.Sem
