/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Hash
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Hash
import StrataPython.Dyn.Sem.Imm
meta import StrataPython.Dyn.Sem.Imm

set_option autoImplicit false

/-!
# The hashes of built-in values

Each expected number is what CPython 3.12.15 prints for `hash(x)`.
-/

namespace StrataPython.Dyn.Sem.HashTest

open StrataPython.Dyn.Sem

/-- The exact hash of `v`, if it has one. -/
def exactHash (v : Value) : Option Int :=
  match v.immHash with
  | .hash (.exact h) => some h
  | _ => none

/-- The hash of `v`, if it has one here. -/
def hashOf? (v : Value) : Option Hash :=
  match v.immHash with
  | .hash h => some h
  | _ => none

-- `int`: modulo `2^61 - 1`, with the sign, and `-1` becomes `-2`.
#guard exactHash (.int 0) == some 0
#guard exactHash (.int (-1)) == some (-2)
#guard exactHash (.int (-2)) == some (-2)
#guard exactHash (.int (2 ^ 61 - 1)) == some 0
#guard exactHash (.int (2 ^ 61)) == some 1
#guard exactHash (.int (-(2 ^ 61))) == some (-2)
#guard exactHash (.int (2 ^ 100)) == some 549755813888
#guard exactHash (.int (-(2 ^ 100) + 5)) == some (-549755813883)

-- `float`: the hash of the rational number, the same as an equal `int`'s.
#guard exactHash (.ofFloat 0.0) == some 0
#guard exactHash (.ofFloat (-0.0)) == some 0
#guard exactHash (.ofFloat 1.5) == some 1152921504606846977
#guard exactHash (.ofFloat (-1.5)) == some (-1152921504606846977)
#guard exactHash (.ofFloat 0.1) == some 230584300921369408
#guard exactHash (.ofFloat 1e300) == some 1224995262755759164
#guard exactHash (.float 1) == some 16777216  -- 5e-324, the smallest subnormal
#guard exactHash (.ofFloat (1.0 / 0.0)) == some 314159
#guard exactHash (.ofFloat (-1.0 / 0.0)) == some (-314159)
#guard exactHash (.ofFloat (2.0 ^ (61 : Float))) == some 1
#guard exactHash (.ofFloat (1.0 / 3.0)) == some 768614336404564608
-- A NaN's hash is its object's address: no hash here.
#guard (Value.ofFloat (0.0 / 0.0)).immHash == .unknown

-- `tuple`: CPython 3.12's xxHash mixing.
#guard exactHash (.tuple #[]) == some 5740354900026072187
#guard exactHash (.tuple #[.int 1]) == some (-6644214454873602895)
#guard exactHash (.tuple #[.int 1, .int 2]) == some (-3550055125485641917)
#guard exactHash (.tuple #[.int 1, .tuple #[.int 2, .int 3]]) == some 7267574591690527098
#guard exactHash (.tuple #[.int (-1)]) == some 8078679518589016365
#guard exactHash (.tuple #[.none]) == some 9181102132670838864
#guard exactHash (.tuple #[.bool true, .bool false, .ofFloat 1.5]) == some (-7155322998463821790)

-- `frozenset`: from the members' hashes, in any order.
#guard (frozensetHash []) == .exact 133146708735736
#guard (frozensetHash [.exact 1]) == .exact (-558064481276695278)
#guard (frozensetHash [.exact 1, .exact 2, .exact 3]) == .exact (-272375401224217160)
#guard (frozensetHash [.exact 3, .exact 1, .exact 2]) == .exact (-272375401224217160)
-- A hash combined 9,000 levels deep, as a nested generic alias's is: built, checked, hashed and
-- compared in linear time, since each level shares the one below it.
def deepCombine : Nat → Hash
  | 0 => .symbolic (.const .int)
  | n + 1 => combineHash "alias" [.symbolic (.const .list), deepCombine n] fun _ => 0
#guard match deepCombine 9000 with
  | .symbolic s => s.storeAddrFree && s.tag == some 5
  | .exact _ => false
#guard hash (deepCombine 9000) == hash (deepCombine 9000) && deepCombine 9000 == deepCombine 9000
#guard deepCombine 9000 != deepCombine 8999
-- A hash that uses the hash below it twice at each of 12 levels, whose walks visit each use
-- (`docs/PythonToDyn.md`): checked, hashed and compared.
def sharedCombine : Nat → Hash
  | 0 => .symbolic (.const .int)
  | n + 1 => let h := sharedCombine n; combineHash "node" [h, h] fun _ => 0
#guard match sharedCombine 12 with
  | .symbolic s => s.storeAddrFree && s.tag == some 5
  | .exact _ => false
#guard hash (sharedCombine 12) != hash (sharedCombine 11) && sharedCombine 12 == sharedCombine 12
#guard sharedCombine 12 != sharedCombine 11
-- A symbolic frozenset hash doesn't depend on the order of its members' hashes.
#guard frozensetHash [.symbolic (.buffer [97].toByteArray), .exact 1, .symbolic (.tuple [.symbolic (.const .int)])] ==
  frozensetHash [.symbolic (.tuple [.symbolic (.const .int)]), .symbolic (.buffer [97].toByteArray), .exact 1]
#guard (frozensetHash [.exact (-2)]) == .exact 6776983852052281967

-- `range` and `slice`.
#guard exactHash (.range 0 0 1) == some 2676694398852732306
#guard exactHash (.range 0 5 1) == some 5795932985296280846
#guard exactHash (.range 1 10 3) == some (-9160968616009628824)
#guard exactHash (.range 3 4 1) == some 3985224588053030672
#guard exactHash (.slice (.int 1) (.int 2) (.int 3)) == some (-2340833382717974474)
#guard exactHash (.slice .none .none .none) == some 4032618106351268893
-- Negative steps.
#guard exactHash (.range 10 0 (-3)) == some (-4187782621229172137)
#guard exactHash (.range 0 10 (-1)) == some 2676694398852732306
#guard exactHash (.range 5 4 (-7)) == some (-7048428680432378585)
#guard rangeLen 10 0 (-3) == 4 && rangeLen 0 10 (-1) == 0 && rangeLen 5 4 (-7) == 1
-- The results that would be `-1` become CPython's fixed values.
#guard exactHash (.tuple #[.int 17, .int (-1555522700513432331)]) == some 1546275796
#guard exactHash (.slice (.int 1) (.int 0) (.int (-1089274793304957731))) == some 1546275796
#guard frozensetHash [.exact 1, .exact 1070027782356453732] == .exact 590923713
-- A slice of a `str` has a symbolic hash.
#guard hashOf? (.slice (.ofString "a") (.int 1) .none) == some (.symbolic (.combine "slice" [strHash (.ofString "a"), .exact 1, .exact noneHash]))

-- A static method of a built-in type hashes as the built-in function it is, one per type and
-- name, and not as the descriptor that holds it.
#guard hashOf? (.bound .none .str "maketrans" .staticMethod)
  == some (.symbolic (.combine "<staticmethod>" [.symbolic (.descr .str "maketrans")]))
#guard hashOf? (.bound .none .str "maketrans" .staticMethod)
  != hashOf? (.descr .str "maketrans" .staticMethod)
#guard hashOf? (.bound .none .str "maketrans" .staticMethod)
  != hashOf? (.bound .none .bytes "maketrans" .staticMethod)

-- `None`, `bool`, and the empty `str` and `bytes`.
#guard exactHash .none == some 4238894112
#guard exactHash (.bool true) == some 1
#guard exactHash (.bool false) == some 0
#guard exactHash (.ofString "") == some 0
#guard exactHash (.bytes #[]) == some 0

-- A `str` and a `bytes` with the same buffer share a source: `hash("zzz") == hash(b"zzz")` and
-- `hash("Ā") == hash(b"\x00\x01")` under every seed.
#guard (Value.ofString "zzz").immHash == (Value.bytes #[122, 122, 122]).immHash
#guard (Value.ofString "Ā").immHash == (Value.bytes #[0, 1]).immHash
#guard (Value.ofString "a").immHash != (Value.ofString "b").immHash
-- PEP 393 buffers: a narrow character is widened by a wider one in the same `str`.
#guard (strBuffer (.ofString "aĀ")).toList == [97, 0, 0, 1]
#guard (strBuffer (.ofString "😀")).toList == [0x00, 0xF6, 0x01, 0x00]
#guard (strBuffer (.ofString "é")).toList == [0xE9]
#guard (strBuffer (.ofString "ab")).toList == [97, 98]
#guard (PyStr.ofString "abc").ascii && !(PyStr.ofString "é").ascii

-- Equal tuples and frozensets of `str`s share a source.
#guard (Value.tuple #[.ofString "a", .int 1]).immHash == (Value.tuple #[.ofString "a", .int 1]).immHash
#guard frozensetHash [strHash (.ofString "a"), strHash (.ofString "b")]
  == frozensetHash [strHash (.ofString "b"), strHash (.ofString "a")]

-- Built-in constants: a type hashes by its address, a built-in function by its own source, and
-- `__spec__` is unhashable.
#guard Value.immHash (.builtin .int) == .hash (.symbolic (.const .int))
#guard Value.immHash (.builtin .len) == .hash (.symbolic (.builtinFn .len))
#guard Value.immHash (.builtin .«__spec__») == .unhashable
#guard (HashSrc.const .int).isAddr && !(HashSrc.builtinFn .len).isAddr
#guard (HashSrc.addr 3).isAddr && (HashSrc.singleton true).isAddr && !(HashSrc.buffer [1].toByteArray).isAddr
-- `Ellipsis` and `NotImplemented` hash by their addresses, so a tuple of them hashes too.
#guard hashOf? (.tuple #[.ellipsis]) == some (.symbolic (.tuple [.symbolic (.singleton true)]))
#guard Value.immHash .notImplemented == .hash (.symbolic (.singleton false))
-- A descriptor hashes by its address.
#guard Value.immHash (.descr .int "__add__" .slotWrapper) == .hash (.symbolic (.descr .int "__add__"))
#guard (HashSrc.descr .int "__add__").isAddr

/-- A descriptor of a built-in type hashes by its address, which its type and name identify. A
built-in type's `tp_new` is the exception: its hash is unknown here. -/
example (t : Builtin) (name : String) (k : DescrKind) :
    (Value.descr t name k).immHash =
      if k = .tpNew then .unknown else .hash (.symbolic (.descr t name)) := by
  cases k <;> simp [Value.immHash]

-- Not modelled yet: a bound method's hash combines its `__self__` and its function.
#guard Value.immHash (.method (.obj 0) (.obj 1)) == .unknown
#guard Value.immHash (.bound (.obj 0) .list "append" .method) == .unknown
-- Kept symbolic, although CPython gives 399283329322573 under every seed: the two equal sources
-- cancel out.
#guard frozensetHash [strHash (.ofString "zzz"), bytesHash #[122, 122, 122]] matches .symbolic _
-- The first part that has no hash here decides a tuple's result.
#guard Value.immHash (.tuple #[.int 1, .builtin .«__spec__», .obj 0]) == .unhashable
#guard Value.immHash (.tuple #[.int 1, .obj 0, .builtin .«__spec__»]) == .needsStore
#guard Value.immHash (.tuple #[.traceback]) == .unknown

-- `hash()` of a symbolic hash value is reduced once; reducing again gives it back.
#guard (Value.symHash (.buffer [97].toByteArray)).immHash == .hash (.symbolic (HashSrc.buffer [97].toByteArray).reduced)
#guard (Value.symHash (HashSrc.buffer [97].toByteArray).reduced).immHash == .hash (.symbolic (HashSrc.buffer [97].toByteArray).reduced)
#guard (HashSrc.buffer [97].toByteArray).reduced != HashSrc.buffer [97].toByteArray

-- `combineHash`: `exact` of the parts' numbers when every part is exact, else a symbolic hash from
-- the tag and the parts.
#guard combineHash "t" [.exact 1, .exact 2] (fun ns => ns.foldl (· + ·) 10) == .exact 13
#guard combineHash "t" [.exact 1, .symbolic (HashSrc.buffer [97].toByteArray)] (fun _ => 0) ==
  .symbolic (HashSrc.combine "t" [.exact 1, .symbolic (HashSrc.buffer [97].toByteArray)])
#guard combineHash "t" [] (fun _ => 5) == .exact 5

end StrataPython.Dyn.Sem.HashTest
