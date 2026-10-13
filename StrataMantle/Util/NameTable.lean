/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Name
public import Std.Data.HashMap.Basic
import Std.Data.HashMap.Lemmas

set_option autoImplicit false

/-!
# Distinct names, found by hash

A `NameTable` is a row of slots, each a name or one reserved for a name chosen later, and a
`Std.HashMap` from each name to what it stands for.  No name fills two slots, so a reader
that meets names one by one gets the uniqueness `Func.WF` and `Module.Raw.WF` ask for without
a later check.

* `empty`: no slots;
* `get?`: what a name stands for;
* `insert?`: fill the next slot with a name, unless the table has it;
* `reserve`: leave the next slot for later;
* `insertAll?`: insert each name of a list, in order;
* `fill?`: the names, every reserved slot filled with a fresh one.

The map is for run time only: `NameSet` is the structure the kernel decides with.
-/

namespace Strata.Mantle

public section

/-- Names in slots, and a map from each to a value: its keys are the names, none twice. -/
structure NameTable (β : Type) where
  slots : Array (Option Name)
  map : Std.HashMap Name β
  mem_iff : ∀ n, map.contains n = true ↔ n ∈ slots.toList.filterMap id
  nodup : (slots.toList.filterMap id).Nodup

namespace NameTable

variable {β : Type}

/-- A list with no repeats, and a name not in it, extended by that name. -/
theorem nodup_append_singleton {l : List Name} {n : Name} (hn : n ∉ l) (h : l.Nodup) :
    (l ++ [n]).Nodup :=
  List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨by simpa using hn, by simpa using h⟩)

/-- The names in the slots, in order. -/
abbrev names (t : NameTable β) : List Name := t.slots.toList.filterMap id

/-- No slots. -/
def empty : NameTable β where
  slots := #[]
  map := {}
  mem_iff := by simp
  nodup := by simp

instance : EmptyCollection (NameTable β) := ⟨empty⟩

/-- The empty table has no names. -/
@[simp] theorem names_empty : (empty : NameTable β).names = [] := by simp [empty]

/-- The value at `n`, if the table has `n`. -/
def get? (t : NameTable β) (n : Name) : Option β := t.map[n]?

/-- `t` with `n` in the next slot, standing for `b`; `none` if `t` has `n` already. -/
def insert? (t : NameTable β) (n : Name) (b : β) : Option (NameTable β) :=
  if h : t.map.contains n then none
  else some {
    slots := t.slots.push (some n)
    map := t.map.insert n b
    mem_iff := fun m => by
      rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, t.mem_iff m,
        Array.toList_push, List.filterMap_append]
      simp [or_comm, @eq_comm _ n m]
    nodup := by
      rw [Array.toList_push, List.filterMap_append]
      exact nodup_append_singleton (fun hm => h ((t.mem_iff n).mpr hm)) t.nodup }

/-- Inserting a name appends it to the names. -/
theorem names_insert? {t t₁ : NameTable β} {n : Name} {b : β} (h : t.insert? n b = some t₁) :
    t₁.names = t.names ++ [n] := by
  unfold insert? at h
  split at h
  · contradiction
  · cases h
    simp [names]

/-- `t` with the next slot left for a name chosen later. -/
def reserve (t : NameTable β) : NameTable β where
  slots := t.slots.push none
  map := t.map
  mem_iff := fun m => by simpa using t.mem_iff m
  nodup := by simpa using t.nodup

/-- `t` with each of `l`'s names inserted in order, or the first one it already has. -/
def insertAll? (t : NameTable β) :
    (l : List (Name × β)) → Except (Name × β) {t₁ : NameTable β // t₁.names = t.names ++ l.map (·.1)}
  | [] => .ok ⟨t, by simp⟩
  | (n, b) :: l =>
    match h : t.insert? n b with
    | none => .error (n, b)
    | some t₁ => (t₁.insertAll? l).map fun ⟨t₂, h₂⟩ => ⟨t₂, by simp [h₂, names_insert? h]⟩

/-- The first of `fresh k`, `fresh (k + 1)`, …, at most `fuel` of them, that is not a key of
`map`, and the index after it. -/
def findFresh (map : Std.HashMap Name β) (fresh : Nat → Name) (k : Nat) :
    (fuel : Nat) → Option {p : Name × Nat // map.contains p.1 = false}
  | 0 => none
  | fuel + 1 =>
    if h : map.contains (fresh k) then findFresh map fresh (k + 1) fuel
    else some ⟨(fresh k, k + 1), by simpa using h⟩

/-- `fill?` from slot `rest` on, with `out` the names chosen so far. -/
def fillAux (fresh : Nat → Name) (b : β) (map : Std.HashMap Name β) (out : Array Name)
    (k : Nat) : (rest : List (Option Name)) →
    (∀ n, map.contains n = true ↔ n ∈ out.toList ++ rest.filterMap id) →
    (out.toList ++ rest.filterMap id).Nodup → Option {ns : Array Name // ns.toList.Nodup}
  | [], _, nd => some ⟨out, by simpa using nd⟩
  | some n :: rest, hm, nd =>
    fillAux fresh b map (out.push n) k rest (by simpa using hm) (by simpa using nd)
  | none :: rest, hm, nd =>
    match findFresh map fresh k (map.size + 1) with
    | none => none
    | some ⟨(f, k₁), hf⟩ =>
      have hf₁ : f ∉ out.toList ++ rest.filterMap id := fun hm₁ =>
        absurd ((hm f).mpr hm₁) (by simp [hf])
      fillAux fresh b (map.insert f b) (out.push f) k₁ rest
        (fun m => by
          rw [Std.HashMap.contains_insert, Bool.or_eq_true, beq_iff_eq, hm m, Array.toList_push]
          simp [or_left_comm, @eq_comm _ f m])
        (by
          rw [Array.toList_push, List.append_assoc, List.singleton_append]
          exact List.perm_middle.nodup_iff.mpr (List.nodup_cons.mpr ⟨hf₁, nd⟩))

/-- The names of every slot, distinct, each reserved one filled with the first `fresh k` that
the table does not have and no earlier slot took.  `none` only if `fresh` is not injective. -/
def fill? (t : NameTable β) (fresh : Nat → Name) (b : β) :
    Option {ns : Array Name // ns.toList.Nodup} :=
  fillAux fresh b t.map #[] 0 t.slots.toList (by simpa using t.mem_iff) (by simpa using t.nodup)

end NameTable

end

end Strata.Mantle
