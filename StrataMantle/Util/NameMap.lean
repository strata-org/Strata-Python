/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Name
public import StrataMantle.Util.NatTree23
import StrataMantle.NameProps

set_option autoImplicit false

/-!
# Maps and sets of names the kernel can search

`NameMap` is a `NatTree23` keyed by `Name.key`, which is injective (`Name.key_inj`), and
`NameSet` is a `NameMap Unit`.  A lookup computes one key and then compares `Nat` literals.

* `NameMap.ofArray?`, `NameSet.of?`: build one, failing if a name occurs twice.
* `NameMap.find?`, `NameMap.contains`, `n ∈ m`: look a name up.

`NameSet.of?_isSome_iff` is the duplicate check (`List.Nodup`) and `NameSet.mem_of?` says
what the set holds; `NameMap.ofArray?_isSome_iff`, `find?_ofArray?` and `mem_ofArray?` are the
map versions.
-/

namespace Strata.Mantle

public section

/-- A map from names: a 2-3 tree on `Name.key`. -/
structure NameMap (β : Type) where
  tree : NatTree23 β := .leaf

/-- A set of names: a `NameMap` with nothing at its keys. -/
abbrev NameSet := NameMap Unit

namespace NameMap

variable {β : Type}

instance : EmptyCollection (NameMap β) := ⟨{}⟩

/-- The value at `n`, if any. -/
@[expose] def find? (m : NameMap β) (n : Name) : Option β := m.tree.find? n.key

/-- Whether `n` is a key of `m`. -/
@[expose] def contains (m : NameMap β) (n : Name) : Bool := (m.find? n).isSome

instance : Membership Name (NameMap β) := ⟨fun m n => m.contains n = true⟩

instance (m : NameMap β) (n : Name) : Decidable (n ∈ m) :=
  inferInstanceAs (Decidable (m.contains n = true))

/-- `m` with `n` mapped to `x`, whether or not `n` was a key. -/
@[expose] def insert (m : NameMap β) (n : Name) (x : β) : NameMap β := ⟨m.tree.insert n.key x⟩

/-- `a` as a map, or `none` if a name occurs twice in it. -/
@[expose] def ofArray? : Array (Name × β) → Option (NameMap β)
  -- The kernel reduces the map on the list; compiled code runs `ofArrayFold?`.
  | ⟨l⟩ => (NatTree23.ofArray? ⟨l.map fun p => (p.1.key, p.2)⟩).map NameMap.mk

/-- `ofArray?` as a fold over the array. -/
def ofArrayFold? (a : Array (Name × β)) : Option (NameMap β) :=
  (a.foldlM (fun (t : NatTree23 β) p => t.insert? p.1.key p.2) .leaf).map NameMap.mk

/-- Compiled code runs `ofArrayFold?` for `ofArray?`. -/
@[csimp] theorem ofArray?_eq_ofArrayFold? : @ofArray? = @ofArrayFold? := by
  funext β a
  rcases a with ⟨l⟩
  simp only [ofArray?, ofArrayFold?, NatTree23.ofArray?, NatTree23.insertArray?_eq_foldlM,
    List.foldlM_toArray, List.foldlM_map]

/-! ## What a map holds -/

/-- Keys are distinct exactly when the names they come from are. -/
private theorem nodup_map_key {l : List Name} : (l.map Name.key).Nodup ↔ l.Nodup := by
  simp only [List.Nodup, ne_eq, List.pairwise_map, Name.key_eq_key]

/-- The keys of the tree `ofArray?` builds. -/
private theorem keys_eq {l : List (Name × β)} :
    (l.map fun p => (p.1.key, p.2)).map Prod.fst = (l.map Prod.fst).map Name.key := by
  simp only [List.map_map]
  rfl

/-- The duplicate check: `ofArray?` succeeds exactly when no name occurs twice. -/
theorem ofArray?_isSome_iff {a : Array (Name × β)} :
    (ofArray? a).isSome = true ↔ (a.toList.map Prod.fst).Nodup := by
  rcases a with ⟨l⟩
  rw [ofArray?, Option.isSome_map, NatTree23.ofArray?_isSome_iff, keys_eq, nodup_map_key]

/-- A lookup in `ofArray?`'s result is a lookup in `a`. -/
theorem find?_ofArray? {a : Array (Name × β)} {m : NameMap β} (h : ofArray? a = some m)
    (n : Name) (v : β) : m.find? n = some v ↔ (n, v) ∈ a := by
  rcases a with ⟨l⟩
  rw [ofArray?, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  rw [find?, NatTree23.find?_ofArray? ht, List.mem_toArray, List.mem_toArray]
  constructor
  · intro hm
    obtain ⟨⟨n', v'⟩, hp, he⟩ := List.mem_map.mp hm
    obtain ⟨hk, rfl⟩ := Prod.mk.inj he
    -- The tree holds `n'`'s key; `key_inj` makes `n'` the name looked up.
    obtain rfl := Name.key_inj hk
    exact hp
  · exact List.mem_map_of_mem

/-- `ofArray?`'s result has a name exactly when `a` does. -/
theorem mem_ofArray? {a : Array (Name × β)} {m : NameMap β} (h : ofArray? a = some m)
    (n : Name) : n ∈ m ↔ n ∈ a.map Prod.fst := by
  rcases a with ⟨l⟩
  rw [ofArray?, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  show (NatTree23.find? t n.key).isSome = true ↔ _
  rw [NatTree23.isSome_find?_ofArray? ht, List.map_toArray, List.mem_toArray, keys_eq,
    List.map_toArray, List.mem_toArray, List.mem_map]
  constructor
  · rintro ⟨y, hy, he⟩
    obtain rfl := Name.key_inj he
    exact hy
  · exact fun hn => ⟨n, hn, rfl⟩

end NameMap

namespace NameSet

/-- `ns` as a set, or `none` if a name occurs twice in it. -/
@[expose] def of? : Array Name → Option NameSet
  -- The kernel reduces the map on the list; compiled code runs `ofFold?`.
  | ⟨l⟩ => NameMap.ofArray? ⟨l.map fun n => (n, ())⟩

/-- `of?` as a fold over the array. -/
def ofFold? (ns : Array Name) : Option NameSet :=
  (ns.foldlM (fun (t : NatTree23 Unit) n => t.insert? n.key ()) .leaf).map NameMap.mk

/-- Compiled code runs `ofFold?` for `of?`. -/
@[csimp] theorem of?_eq_ofFold? : @of? = @ofFold? := by
  funext ns
  rcases ns with ⟨l⟩
  rw [of?, NameMap.ofArray?_eq_ofArrayFold?]
  simp only [NameMap.ofArrayFold?, ofFold?, List.foldlM_toArray, List.foldlM_map]

/-- The duplicate check: `of?` succeeds exactly when no name occurs twice. -/
theorem of?_isSome_iff {ns : Array Name} : (of? ns).isSome = true ↔ ns.toList.Nodup := by
  rcases ns with ⟨l⟩
  rw [of?, NameMap.ofArray?_isSome_iff]
  simp only [List.map_map, Function.comp_def, List.map_id_fun', id_eq]

/-- `of?`'s result holds exactly the names of `ns`. -/
theorem mem_of? {ns : Array Name} {s : NameSet} (h : of? ns = some s) (n : Name) :
    n ∈ s ↔ n ∈ ns := by
  rcases ns with ⟨l⟩
  rw [of?] at h
  rw [NameMap.mem_ofArray? h n]
  simp only [List.map_toArray, List.map_map, Function.comp_def, List.map_id_fun', id_eq,
    List.mem_toArray]

end NameSet

end

end Strata.Mantle
