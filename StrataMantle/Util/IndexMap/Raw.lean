module
public import Std.Data.HashMap
import all Init.Data.Array.Basic

set_option autoImplicit false


/-! ### `Array.idxOf?` at `EquivBEq` keys

Core's `idxOf?` API requires `LawfulBEq` ("the verification API for `idxOf?` is
still incomplete", `Init/Data/Array/Find.lean:772`), but this map's keys are only
`EquivBEq`. These lemmas reduce `idxOf?` to `findIdx?`, whose API is
`BEq`-agnostic, and then restate what is needed on top.

No lemma here carries `@[simp]` or `@[grind]`: importing this module must not
change the simp normal form for `Array` downstream. Use them by name.
-/

namespace Array

variable {α} [BEq α]

/-- upstream_candidate: `idxOfAux` is `findFinIdx?`'s loop at `(· == v)`. Core has
    both definitions but never connects them, which is why its `idxOf?` lemmas
    cannot reuse the `findIdx?` API. -/
theorem idxOfAux_eq_findFinIdx?_loop (as : Array α) (v : α) (i : Nat) :
    idxOfAux as v i = findFinIdx?.loop (· == v) as i := by
  unfold idxOfAux findFinIdx?.loop
  if h : i < as.size then
    have ind := idxOfAux_eq_findFinIdx?_loop as v (i+1)
    grind
  else
    grind

/-- upstream_candidate: follows from `idxOfAux_eq_findFinIdx?_loop`; core states
    neither direction. -/
theorem finIdxOf?_eq_findFinIdx? (as : Array α) (v : α) :
    as.finIdxOf? v = as.findFinIdx? (· == v) :=
  idxOfAux_eq_findFinIdx?_loop as v 0

/-- upstream_candidate: the bridge that makes core's `findIdx?` API available for
    `idxOf?` without `LawfulBEq`. -/
theorem idxOf?_eq_findIdx? (as : Array α) (v : α) :
    as.idxOf? v = as.findIdx? (· == v) := by
  simp [idxOf?, finIdxOf?_eq_findFinIdx?, findIdx?_eq_map_findFinIdx?_val]

/-- upstream_candidate: `idxOf?` in the shape of `findIdx?_eq_some_iff_getElem` —
    the found position matches and no earlier one does. Core's
    `idxOf?_eq_some_iff` needs `LawfulBEq`. -/
theorem idxOf?_eq_some_iff_getElem {as : Array α} {v : α} {i : Nat} :
    as.idxOf? v = some i ↔
      ∃ h : i < as.size, (as[i] == v) ∧
        ∀ j (hji : j < i), ¬ (as[j]'(Nat.lt_trans hji h) == v) := by
  rw [idxOf?_eq_findIdx?, findIdx?_eq_some_iff_getElem]

theorem lt_size_of_idxOf?_eq_some {as : Array α} {v : α} {i : Nat}
    (h : as.idxOf? v = some i) : i < as.size :=
  (idxOf?_eq_some_iff_getElem.mp h).1

/-- upstream_candidate: `isSome_idxOf?` without `LawfulBEq`. -/
theorem isSome_idxOf?_eq_contains [PartialEquivBEq α] {xs : Array α} {a : α} :
    (xs.idxOf? a).isSome = xs.contains a := by
  unfold Array.idxOf?
  simp

/-- upstream_candidate: `BEq`-equal keys are found at the same position. -/
theorem idxOfAux_congr [PartialEquivBEq α] (as : Array α) {a b : α} (hab : a == b) (i : Nat) :
    idxOfAux as a i = idxOfAux as b i := by
  unfold idxOfAux
  if h : i < as.size then
    have ind := idxOfAux_congr as hab (i+1)
    have beq : (as[i] == a) = (as[i] == b) := BEq.congr_right hab
    grind
  else
    grind

theorem finIdxOf?_congr [PartialEquivBEq α] {as : Array α} {a b : α} (hab : a == b) :
    as.finIdxOf? a = as.finIdxOf? b := by
  unfold finIdxOf?
  exact idxOfAux_congr as hab 0

theorem idxOf?_congr [PartialEquivBEq α] {as : Array α} {a b : α} (hab : a == b) :
    as.idxOf? a = as.idxOf? b := by
  simp [idxOf?, finIdxOf?_congr hab]

/-- Keys found at the same position are `BEq`-equal. -/
theorem beq_of_idxOf?_eq_idxOf? [PartialEquivBEq α] {as : Array α} {a b : α} {i : Nat}
    (ha : as.idxOf? a = some i) (hb : as.idxOf? b = some i) : a == b := by
  have hba := (idxOf?_eq_some_iff_getElem.mp ha).2.1
  have hbb := (idxOf?_eq_some_iff_getElem.mp hb).2.1
  exact BEq.trans (BEq.symm hba) hbb

/-- upstream_candidate: with distinct elements, `idxOf?` inverts indexing.  The
    `Nodup` hypothesis is needed because `idxOf?` returns the *first* occurrence,
    so a later duplicate would have no position of its own. -/
theorem idxOf?_eq_some_iff_getElem?_of_nodup [LawfulBEq α] {as : Array α} {a : α} {i : Nat}
    (hnd : as.toList.Nodup) : as.idxOf? a = some i ↔ as[i]? = some a := by
  constructor
  · intro h
    obtain ⟨hlt, hbeq, -⟩ := idxOf?_eq_some_iff_getElem.mp h
    rw [getElem?_eq_getElem hlt, eq_of_beq hbeq]
  · intro h
    obtain ⟨hlt, hai⟩ := getElem?_eq_some_iff.mp h
    have hsome : (as.idxOf? a).isSome := by
      rw [isSome_idxOf?_eq_contains]
      exact contains_eq_true_of_mem (hai ▸ getElem_mem hlt)
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨hjlt, hjbeq, -⟩ := idxOf?_eq_some_iff_getElem.mp hj
    -- `Nodup` in indexed form: distinct positions hold distinct elements.
    have hne : ∀ p q : Nat, ∀ (hp : p < as.size) (hq : q < as.size), p < q →
        as[p]'hp ≠ as[q]'hq := by
      intro p q hp hq hpq
      have := List.pairwise_iff_getElem.mp hnd p q (by simpa using hp) (by simpa using hq) hpq
      simpa using this
    have heq : as[i]'hlt = as[j]'hjlt := hai.trans (eq_of_beq hjbeq).symm
    have hij : i = j := by
      rcases Nat.lt_trichotomy i j with hlt' | h | hgt'
      · exact absurd heq (hne i j hlt hjlt hlt')
      · exact h
      · exact absurd heq.symm (hne j i hjlt hlt hgt')
    rw [hj, hij]

/-- upstream_candidate: `idxOf?_push` without `LawfulBEq`, mirroring core's
    `findIdx?_push`. -/
theorem idxOf?_push (as : Array α) (a b : α) :
    (as.push a).idxOf? b = (as.idxOf? b).or (if a == b then some as.size else none) := by
  rw [idxOf?_eq_findIdx?, findIdx?_push, idxOf?_eq_findIdx?]

end Array

/-!
# IndexMap.Raw

An insertion-ordered map: `keys`/`vals` in insertion order plus a `HashMap` from
key to position. Unlike `Array (α × β)` lookup is O(1); unlike `Std.HashMap`
iteration order is deterministic.

The single coherence invariant is `index_def : ∀ k, index[k]? = keys.idxOf? k`.
It makes `index` lookups agree with `keys` and justifies the in-bounds `vals`
access in `get`, so `get` needs no `Option` and no `panic`. `Repr`/`BEq` look
only at `keys`/`vals`. `mk` is private; build values with
`empty`/`insert`/`ofArray`.
-/

namespace Strata

open Std (HashMap)

/-- An insertion-ordered, unique-keyed map. See module docs. -/
public structure IndexMap.Raw (α β : Type _) [BEq α] [Hashable α] where
  private mk ::
  /-- Keys in insertion order. -/
  keys : Array α
  /-- Values, positionally aligned with `keys`. -/
  vals : Array β
  private array_eq : vals.size = keys.size
  /-- No two keys are `BEq`-equal. -/
  keys_distinct : keys.toList.Pairwise (fun a b => (a == b) = false)
  /-- Position of each key in `keys`; see `index_def`. -/
  private index : HashMap α Nat
  private index_def : ∀(k : α), index[k]? = keys.idxOf? k

namespace IndexMap.Raw

public section

variable {α β : Type _} [hb : BEq α] [Hashable α]

/-- The number of entries. -/
@[expose]
protected def size (m : IndexMap.Raw α β) : Nat := m.keys.size

@[simp, grind =]
theorem size_keys (u : IndexMap.Raw α β) : u.keys.size = u.size := rfl

@[simp, grind =]
theorem size_vals (u : IndexMap.Raw α β) : u.vals.size = u.size := u.array_eq

/-- The positional form of `keys_distinct`: searching for the key at position `i`
    stops at `i`.  Every lemma about reachability goes through this. -/
theorem idxOf?_getElem_keys [ReflBEq α] (m : IndexMap.Raw α β) (i : Nat) (h : i < m.keys.size) :
    m.keys.idxOf? (m.keys[i]'h) = some i := by
  refine Array.idxOf?_eq_some_iff_getElem.mpr ⟨h, by simp, fun j hji => ?_⟩
  have hd := List.pairwise_iff_getElem.mp m.keys_distinct j i
    (by simpa using Nat.lt_trans hji h) (by simpa using h) hji
  rw [Array.getElem_toList, Array.getElem_toList] at hd
  simpa using hd

/-- `vals` as a `Vector`, so `get` indexes without a bounds side-goal. -/
private def valsV (m : IndexMap.Raw α β) : Vector β m.size :=
  ⟨m.vals, m.size_vals⟩

@[simp]
private theorem getElem_valsV (m : IndexMap.Raw α β) (i : Nat) (h : i < m.size) :
    m.valsV[i]'h = m.vals[i]'(by have := m.size_vals; omega) := rfl

/-- The empty map. -/
def empty : IndexMap.Raw α β := {
  keys := #[]
  vals := #[]
  array_eq := by simp
  keys_distinct := by simp
  index := {},
  index_def := by simp
}

instance : Inhabited (IndexMap.Raw α β) := ⟨empty⟩

instance : EmptyCollection (IndexMap.Raw α β) := ⟨empty⟩

/-- Normalise the named constructor to the `∅` spelling, so the `_empty` lemmas
    fire on both. -/
@[simp]
theorem empty_eq : (empty : IndexMap.Raw α β) = ∅ := rfl

@[simp]
private theorem keys_empty : (∅ : IndexMap.Raw α β).keys = #[] := rfl

@[simp]
private theorem vals_empty : (∅ : IndexMap.Raw α β).vals = #[] := rfl

@[simp]
private theorem index_empty : (∅ : IndexMap.Raw α β).index = {} := rfl

/-- Whether `key` is present. -/
protected def contains (m : IndexMap.Raw α β) (key : α) : Bool := m.index.contains key

/-- Key membership. -/
instance : Membership α (IndexMap.Raw α β) where
  mem m key := m.contains key

@[simp]
theorem mem_iff_contains {m : IndexMap.Raw α β} {key : α} :
    key ∈ m ↔ m.contains key := Iff.rfl

/-- No `LawfulBEq` needed: membership is the `Bool` lookup. -/
instance {m : IndexMap.Raw α β} {key : α} : Decidable (key ∈ m) :=
  inferInstanceAs (Decidable (m.contains key = true))

/-- Every member key is in the `index` cache, so `m.index[key]` is total on
    members. -/
private theorem mem_index_of_mem {m : IndexMap.Raw α β} {key : α} (mem : key ∈ m) :
    key ∈ m.index :=
  Std.HashMap.mem_iff_contains.mpr (mem_iff_contains.mp mem)

protected def beq [BEq β] (a b : IndexMap.Raw α β) : Bool :=
  a.keys == b.keys && a.vals == b.vals

/-- Equality compares `keys`/`vals` only; the `index` cache is ignored. -/
instance [BEq β] : BEq (IndexMap.Raw α β) where
  beq := IndexMap.Raw.beq

/-- The position of `key` in `keys`, or `none`. -/
@[inline]
def idxOf? (m : IndexMap.Raw α β) (key : α) : Option (Fin m.size) :=
  match h : m.index[key]? with
  | some idx =>
    have p : idx < m.size := Array.lt_size_of_idxOf?_eq_some (v := key) <| by
      have p1 := m.index_def key
      grind
    some ⟨idx, p⟩
  | none =>
    none

/-- Look up `key`, returning `none` if absent. O(1) via the `index` cache; the
    carried invariants guarantee the indexed position is in bounds. -/
@[inline]
def get? (m : IndexMap.Raw α β) (key : α) : Option β :=
  m.idxOf? key |>.map (m.valsV[·])

/-- `idxOf?` is the `keys`-position of the key: `index_def` in `Option (Fin _)`
    form. -/
theorem keys_idxOf?_eq_map_val_idxOf? (m : IndexMap.Raw α β) (key : α) :
    m.keys.idxOf? key = (m.idxOf? key).map Fin.val := by
  unfold IndexMap.Raw.idxOf?
  have p := m.index_def key
  split <;> grind

theorem idxOf?_eq_none_iff (m : IndexMap.Raw α β) (key : α) :
    m.idxOf? key = none ↔ m.keys.idxOf? key = none := by
  rw [keys_idxOf?_eq_map_val_idxOf? m key]
  simp

/-- `get?` in terms of the two arrays: find the key's position in `keys`, then
    read `vals` there. This is the bridge that reduces lookup reasoning to
    `Array` lemmas about `idxOf?`, `push` and `set`. -/
theorem get?_eq_bind_idxOf? (m : IndexMap.Raw α β) (key : α) :
    m.get? key = (m.keys.idxOf? key).bind (fun i => m.vals[i]?) := by
  rw [keys_idxOf?_eq_map_val_idxOf?, Option.bind_map]
  unfold IndexMap.Raw.get?
  cases m.idxOf? key <;> simp

@[simp]
theorem get?_empty (key : α) : (∅ : IndexMap.Raw α β).get? key = none := by
  rw [get?_eq_bind_idxOf?]; simp

@[simp]
theorem contains_empty (key : α) : (∅ : IndexMap.Raw α β).contains key = false := by
  simp [IndexMap.Raw.contains]

/-- Every entry is reachable: looking up the key at position `i` returns the
    value at position `i`.  This is what `keys_distinct` is for — with a shadowed
    key the later entry would be lost. -/
theorem get?_getElem_keys [ReflBEq α] (m : IndexMap.Raw α β) (i : Nat) (h : i < m.size) :
    m.get? (m.keys[i]'(by simpa using h)) = m.vals[i]? := by
  rw [get?_eq_bind_idxOf?, m.idxOf?_getElem_keys i (by simpa using h)]
  simp

/-- `keys_distinct` in propositional form, once `BEq` is equality. -/
theorem keys_nodup [LawfulBEq α] (m : IndexMap.Raw α β) : m.keys.toList.Nodup :=
  m.keys_distinct.imp (by simp_all)

/-- Look up `key`, returning `d` if absent. -/
protected def getD (m : IndexMap.Raw α β) (key : α) (d : β) : β :=
  match m.idxOf? key with
  | some idx => m.valsV[idx]
  | none => d

/-- Look up `key`, panicking if absent. Prefer `get?` or `m[key]` (with a
    membership proof); this is the `m[key]!` fallback. -/
def get! [Inhabited β] (m : IndexMap.Raw α β) (key : α) : β :=
  m.getD key default

def setIndex (m : IndexMap.Raw α β) (idx : Fin m.size) (val : β) : IndexMap.Raw α β :=
  let ⟨i, ilt⟩ := idx
  have ivb : i < m.vals.size := by rw [m.array_eq]; exact ilt
  { keys := m.keys
    vals := m.vals.set i val ivb
    array_eq := by simp
    keys_distinct := m.keys_distinct
    index := m.index
    index_def := m.index_def
  }

@[simp, grind =]
theorem keys_setIndex (m : IndexMap.Raw α β) (idx : Fin m.size) (val : β) :
    (m.setIndex idx val).keys = m.keys := by
  unfold IndexMap.Raw.setIndex; rfl

@[simp, grind =]
theorem vals_setIndex (m : IndexMap.Raw α β) (idx : Fin m.size) (val : β) :
    (m.setIndex idx val).vals =
      m.vals.set idx.val val (by
        have := m.array_eq; have := idx.isLt; simp only [IndexMap.Raw.size] at *; omega) := by
  unfold IndexMap.Raw.setIndex; rfl

/-- The entries in insertion order. -/
def toArray (m : IndexMap.Raw α β) : Array (α × β) :=
  Array.zip m.keys m.vals

/-- `Repr` shows `keys`/`vals` only; the `index` cache is not printed. -/
instance [Repr α] [Repr β] : Repr (IndexMap.Raw α β) where
  reprPrec m _ := "IndexMap.Raw.ofArray " ++ repr m.toArray

@[simp, grind =]
theorem size_toArray (u : IndexMap.Raw α β) : u.toArray.size = u.size := by
  have eq := u.array_eq
  simp [IndexMap.Raw.toArray]

theorem getElem_toArray (u : IndexMap.Raw α β) {i : Nat} (p : i < u.toArray.size) :
    u.toArray[i]'p = (u.keys[i]'(by grind), u.vals[i]'(by grind)) := by
  simp [IndexMap.Raw.toArray]

/-- `idxOf?` depends only on `keys`: equal key arrays give the same lookup (up
    to the `Fin _.size` cast induced by `keys.size = keys.size`). This is the one
    fact that lets `insert` descend — both branches and the chosen index agree. -/
theorem idxOf?_eq_of_keys_eq {a b : IndexMap.Raw α β} (keq : a.keys = b.keys) (key : α) :
    a.idxOf? key = ((by unfold IndexMap.Raw.size; grind : b.size = a.size) ▸ b.idxOf? key) := by
  unfold IndexMap.Raw.idxOf?
  have p := a.index_def key
  have q := b.index_def key
  grind

section

variable [EquivBEq α] [LawfulHashable α]

/-- The `keys` array and the `index` cache agree on membership. -/
@[simp, grind =]
theorem keys_contains_iff_contains {m : IndexMap.Raw α β} (k : α) :
   m.keys.contains k = m.contains k := by
  change (m.keys.contains k = m.index.contains k)
  simp only [
    Std.HashMap.contains_eq_isSome_getElem?,
    m.index_def k,
    Array.isSome_idxOf?_eq_contains
    ]

/-- Membership, which is the `index` lookup, also sees exactly the keys stored in
    `keys`. -/
theorem mem_iff_keys_contains {m : IndexMap.Raw α β} {key : α} :
    key ∈ m ↔ m.keys.contains key := by
  rw [mem_iff_contains, keys_contains_iff_contains]

/-- Membership in terms of key positions: `key` is present exactly when some
    index of `keys` holds a `BEq`-equal key. `Array.contains` compares its
    argument on the left, hence the `BEq.symm`s. -/
@[inline]
def idxOf (m : IndexMap.Raw α β) (key : α) (mem : key ∈ m) : Fin m.size :=
  have p : key ∈ m.index := mem_index_of_mem mem
  let idx := m.index[key]
  have p : idx < m.size := Array.lt_size_of_idxOf?_eq_some (v := key) <| by
    have p1 := m.index_def key
    grind
  ⟨idx, p⟩

/-- Look up `key`, given a proof it is present. Total (no `Option`): the
    membership proof plus the carried invariants justify the in-bounds access. -/
def get (m : IndexMap.Raw α β) (key : α) (mem : key ∈ m) : β := m.valsV[m.idxOf key mem]

/-- `m[key]?` is `get?`; `m[key]` is the total `get`. -/
instance : GetElem? (IndexMap.Raw α β) α β (fun m key => key ∈ m) where
  getElem := IndexMap.Raw.get
  getElem? := IndexMap.Raw.get?
  getElem! := IndexMap.Raw.get!

/-- The coherence invariant for `push`. Extracted from `push` itself so a change
    in a `simp` set breaks a theorem rather than a definition. -/
private theorem push_index_def (m : IndexMap.Raw α β) (key : α) (newIdx : Nat)
    (h : m.idxOf? key = none) (hidx : newIdx = m.keys.size) (k : α) :
    (m.index.insert key newIdx)[k]? = (m.keys.push key).idxOf? k := by
  have hnone : m.keys.idxOf? key = none := (m.idxOf?_eq_none_iff key).mp h
  simp only [Std.HashMap.getElem?_insert, Array.idxOf?_push]
  if keq : (key == k) = true then
    -- `key` is absent, so the `BEq`-equal `k` is too: the search falls through to
    -- the pushed position.
    have eq_none : m.keys.idxOf? k = none := by
      rw [← Array.idxOf?_congr keq]; exact hnone
    simp [keq, eq_none, hidx]
  else
    simp [keq, m.index_def k]

omit [LawfulHashable α] in
/-- The distinctness invariant for `push`. An absent key is `BEq`-distinct from
    every stored key: a `BEq`-equal key would be found at its own position, but
    the search for `key` finds nothing. -/
private theorem push_keys_distinct (m : IndexMap.Raw α β) (key : α)
    (h : m.idxOf? key = none) :
    (m.keys.push key).toList.Pairwise (fun a b => (a == b) = false) := by
  have hnone : m.keys.idxOf? key = none := (m.idxOf?_eq_none_iff key).mp h
  rw [Array.toList_push]
  refine List.pairwise_append.mpr ⟨m.keys_distinct, by simp, ?_⟩
  intro a ha b hb
  obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.mp ha
  simp only [List.mem_singleton] at hb
  subst hb
  refine Bool.eq_false_iff.mpr fun hab => ?_
  have : m.keys.idxOf? a = some j := by
    rw [← hja]; simpa using m.idxOf?_getElem_keys j (by simpa using hj)
  rw [Array.idxOf?_congr hab, hnone] at this
  simp at this

def push (m : IndexMap.Raw α β) (key : α) (val : β) (h : m.idxOf? key = none) :
    IndexMap.Raw α β :=
  let newIdx := m.size
  {
    keys := m.keys.push key
    vals := m.vals.push val
    array_eq := by simp
    keys_distinct := push_keys_distinct m key h
    index := m.index.insert key newIdx
    index_def := fun k => push_index_def m key newIdx h rfl k
  }

/-- Insert or overwrite. If `key` already exists its value is replaced in place
    (preserving position); otherwise the pair is appended. -/
def insert (m : IndexMap.Raw α β) (key : α) (val : β) : IndexMap.Raw α β :=
  match h : m.idxOf? key with
  | some i => m.setIndex i val
  | none => m.push key val h

/-- Build from an array of pairs, last value winning on duplicate keys. -/
def ofArray (pairs : Array (α × β)) : IndexMap.Raw α β :=
  pairs.foldl (init := empty) fun m (key, val) => m.insert key val

theorem contains_eq_of_keys_eq {a b : IndexMap.Raw α β} (keq : a.keys = b.keys)
    (key : α) : a.contains key = b.contains key := by
  simp [← keys_contains_iff_contains, keq]

theorem mem_iff_of_keys_eq {a b : IndexMap.Raw α β} (keq : a.keys = b.keys)
    (key : α) : key ∈ a ↔ key ∈ b := by
  rw [mem_iff_keys_contains, mem_iff_keys_contains, keq]

theorem idxOf_eq_of_keys_eq {a b : IndexMap.Raw α β} (keq : a.keys = b.keys)
    {key : α} (amem : key ∈ a) :
    a.idxOf key amem =
      cast (congrArg (Fin ·.size) keq.symm)
        (b.idxOf key (mem_iff_of_keys_eq keq key |>.mp amem)) := by
  have bmem : key ∈ b := mem_iff_of_keys_eq keq key |>.mp amem
  have aim : key ∈ a.index := mem_index_of_mem amem
  have bim : key ∈ b.index := mem_index_of_mem bmem
  change Fin.mk (a.index[key]'aim) _ = cast _ (Fin.mk (b.index[key]'bim) _)
  have u := IndexMap.Raw.index_def (α := α) (β := β)
  have v := b.index.getElem_eq_get_getElem? (h := bim)
  grind

@[simp, grind =]
theorem keys_push (m : IndexMap.Raw α β) (key : α) (val : β) (h) :
    (m.push key val h).keys = m.keys.push key := by
  unfold IndexMap.Raw.push; rfl

@[simp, grind =]
theorem vals_push (m : IndexMap.Raw α β) (key : α) (val : β) (h) :
    (m.push key val h).vals = m.vals.push val := by
  unfold IndexMap.Raw.push; rfl

/-- `insert`'s `keys` depend only on the input's `keys`. -/
theorem keys_insert_eq_of_keys_eq {a b : IndexMap.Raw α β} (key : α) (val : β)
    (keq : a.keys = b.keys) :
    (a.insert key val).keys = (b.insert key val).keys := by
  unfold IndexMap.Raw.insert
  have r := idxOf?_eq_of_keys_eq (key := key) keq
  grind

/-- `insert`'s `vals` depend only on the input's `keys` and `vals`. -/
theorem vals_insert_eq_of_vals_eq {a b : IndexMap.Raw α β} (key : α) (val : β)
    (keq : a.keys = b.keys) (veq : a.vals = b.vals) :
    (a.insert key val).vals = (b.insert key val).vals := by
  unfold IndexMap.Raw.insert
  have r := idxOf?_eq_of_keys_eq (key := key) keq
  grind

/-- Lookup after `insert`: the inserted key maps to the new value, and every key
    that is not `BEq`-equal to it is unaffected. -/
@[simp, grind =]
theorem get?_insert (m : IndexMap.Raw α β) (key : α) (val : β) (k : α) :
    (m.insert key val).get? k = if key == k then some val else m.get? k := by
  have hsz : m.vals.size = m.keys.size := by simp
  unfold IndexMap.Raw.insert
  split
  case h_1 i h =>
    have hk : m.keys.idxOf? key = some i.val := by
      rw [keys_idxOf?_eq_map_val_idxOf? m key, h]; rfl
    have hvlt : i.val < m.vals.size := by
      have h1 := i.isLt; have h2 := m.size_vals; omega
    simp only [get?_eq_bind_idxOf?, keys_setIndex, vals_setIndex]
    if hkk : (key == k) = true then
      have hk' : m.keys.idxOf? k = some i.val := by rw [← Array.idxOf?_congr hkk]; exact hk
      simp [hkk, hk']
    else
      -- Another key at the same position would be `BEq`-equal to `key`.
      have hne : ∀ j, m.keys.idxOf? k = some j → ¬ (i.val = j) := by
        intro j hj hji
        subst hji
        exact absurd (Array.beq_of_idxOf?_eq_idxOf? hk hj) (by simpa using hkk)
      match hk' : m.keys.idxOf? k with
      | none => simp [hkk]
      | some j => simp [hkk, hne j hk']
  case h_2 h =>
    have hk : m.keys.idxOf? key = none := (m.idxOf?_eq_none_iff key).mp h
    simp only [get?_eq_bind_idxOf?, keys_push, vals_push, Array.idxOf?_push]
    if hkk : (key == k) = true then
      have hk' : m.keys.idxOf? k = none := by rw [← Array.idxOf?_congr hkk]; exact hk
      simp [hkk, hk', hsz]
      grind
    else
      match hk' : m.keys.idxOf? k with
      | none => simp [hkk]
      | some j =>
        have hjlt : j < m.vals.size := by
          have := Array.lt_size_of_idxOf?_eq_some hk'; omega
        simp [hkk, Array.getElem?_push_lt hjlt]

/-- One normal form for the three spellings of presence: `get?`, `contains`, `∈`. -/
@[simp]
theorem isSome_get?_eq_contains {m : IndexMap.Raw α β} {key : α} :
    (m.get? key).isSome = m.contains key := by
  rw [get?_eq_bind_idxOf?, ← keys_contains_iff_contains, ← Array.isSome_idxOf?_eq_contains]
  cases hk : m.keys.idxOf? key with
  | none => simp
  | some i =>
    have hlt : i < m.vals.size := by
      have := Array.lt_size_of_idxOf?_eq_some hk
      have := m.size_keys; have := m.size_vals; omega
    simp only [Array.getElem?_eq_getElem hlt, Option.bind_some, Option.isSome_some]

@[simp, grind =]
theorem contains_insert {m : IndexMap.Raw α β} {key k : α} {val : β} :
    (m.insert key val).contains k = (key == k || m.contains k) := by
  rw [← isSome_get?_eq_contains, get?_insert, ← isSome_get?_eq_contains]
  split <;> simp_all

/-- The `∈` spelling of `contains_insert`; `contains_insert` is the `simp` form,
    since `mem_iff_contains` normalises `∈` away first. -/
theorem mem_insert {m : IndexMap.Raw α β} {key k : α} {val : β} :
    k ∈ m.insert key val ↔ key == k ∨ k ∈ m := by
  simp only [mem_iff_contains, contains_insert, Bool.or_eq_true]

omit [EquivBEq α] [LawfulHashable α] in
-- Pure `Option.map` fact; the section instances would be unused binders.
private theorem isSome_idxOf?_eq_isSome_idxOf? (m : IndexMap.Raw α β) (key : α) :
    (m.idxOf? key).isSome = (m.keys.idxOf? key).isSome := by
  rw [keys_idxOf?_eq_map_val_idxOf? m key, Option.isSome_map]

@[simp]
theorem isSome_idxOf?_eq_contains {m : IndexMap.Raw α β} {key : α} :
    (m.idxOf? key).isSome = m.contains key := by
  rw [isSome_idxOf?_eq_isSome_idxOf?, Array.isSome_idxOf?_eq_contains,
    keys_contains_iff_contains]

theorem idxOf?_eq_none_of_not_mem {m : IndexMap.Raw α β} {key : α} (h : ¬ key ∈ m) :
    m.idxOf? key = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_idxOf?_eq_contains]
  simpa using h

/-- Which branch `insert` takes, as a rewrite. -/
theorem insert_of_idxOf?_eq_some {m : IndexMap.Raw α β} {key : α} {val : β} {i : Fin m.size}
    (h : m.idxOf? key = some i) : m.insert key val = m.setIndex i val := by
  unfold IndexMap.Raw.insert
  split
  case h_1 i' h' => simp only [h, Option.some.injEq] at h'; subst h'; rfl
  case h_2 h' => simp [h] at h'

theorem insert_of_idxOf?_eq_none {m : IndexMap.Raw α β} {key : α} {val : β}
    (h : m.idxOf? key = none) : m.insert key val = m.push key val h := by
  unfold IndexMap.Raw.insert
  split
  case h_1 i' h' => simp [h] at h'
  case h_2 h' => rfl

/-- Inserting an absent key appends to `keys`, which is what makes `insert`
    order-preserving. -/
theorem keys_insert_of_not_mem {m : IndexMap.Raw α β} {key : α} (val : β) (h : ¬ key ∈ m) :
    (m.insert key val).keys = m.keys.push key := by
  rw [insert_of_idxOf?_eq_none (idxOf?_eq_none_of_not_mem h), keys_push]

theorem vals_insert_of_not_mem {m : IndexMap.Raw α β} {key : α} (val : β) (h : ¬ key ∈ m) :
    (m.insert key val).vals = m.vals.push val := by
  rw [insert_of_idxOf?_eq_none (idxOf?_eq_none_of_not_mem h), vals_push]

/-- Overwriting an existing key leaves `keys` — hence the iteration order —
    unchanged. -/
theorem keys_insert_of_mem {m : IndexMap.Raw α β} {key : α} (val : β) (h : key ∈ m) :
    (m.insert key val).keys = m.keys := by
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (by simpa using h : (m.idxOf? key).isSome)
  rw [insert_of_idxOf?_eq_some hi, keys_setIndex]

theorem mem_of_get?_eq_some {m : IndexMap.Raw α β} {key : α} {v : β}
    (h : m.get? key = some v) : key ∈ m := by
  rw [mem_iff_contains, ← isSome_idxOf?_eq_contains, isSome_idxOf?_eq_isSome_idxOf?]
  cases hk : m.keys.idxOf? key with
  | none => simp [get?_eq_bind_idxOf?, hk] at h
  | some _ => simp

/-- The proof-carrying `idxOf` agrees with `idxOf?`. -/
theorem idxOf?_eq_some_idxOf (m : IndexMap.Raw α β) (key : α) (mem : key ∈ m) :
    m.idxOf? key = some (m.idxOf key mem) := by
  have hg : m.index[key]? = some m.index[key] :=
    Std.HashMap.getElem?_eq_some_getElem (mem_index_of_mem mem)
  unfold IndexMap.Raw.idxOf? IndexMap.Raw.idxOf
  split
  case h_1 idx h =>
    rw [h] at hg
    have hidx : idx = m.index[key] := by simpa using hg
    subst hidx
    rfl
  case h_2 h => simp [h] at hg

/-- `get?` on a member is `some` of the total `get`. -/
theorem get?_eq_some_get (m : IndexMap.Raw α β) (key : α) (mem : key ∈ m) :
    m.get? key = some (m.get key mem) := by
  unfold IndexMap.Raw.get? IndexMap.Raw.get
  rw [idxOf?_eq_some_idxOf m key mem]
  rfl

end
end
end IndexMap.Raw
