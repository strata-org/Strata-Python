/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF

set_option autoImplicit false

/-!
# What a well-formed module's rules for ghosts give

`Module.Raw.WF` checks each ghost reference against `Module.Raw.ghostTable`, a map from each
ghost's name to its position and its type.  These theorems state what the rules give in terms of
the module's ghosts themselves.

## Main theorems

* `Module.Raw.WF.find?_ghostTable`: the map gives each ghost's position and type, and nothing
  else;
* `Module.Raw.WF.ghostRef_fits`: each ghost reference of a function or of a ghost names a ghost of
  the module, at the type of its cell;
* `Module.Raw.WF.initRef_before`: each ghost reference of an initializer names a ghost declared
  before the initializer's own.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} [base ≼ env] {α : Type}

/-- The map that a well-formed module checks ghost references against gives, for each ghost, its
position and its type, and nothing else. -/
theorem Module.Raw.WF.find?_ghostTable {m : Module.Raw env α} (h : m.WF) (n : Name) (i : Nat)
    (t : TypeExpr env) :
    m.ghostTable.find? n = some (i, t) ↔ ∃ g, m.ghosts[i]? = some g ∧ g.name = n ∧ g.type = t := by
  have hnd : (m.ghostSigs.toList.map Prod.fst).Nodup := by
    have hg := (List.nodup_append.mp (by simpa using h.ghostNamesUnique)).1
    have hmap := congrArg (List.map (fun g : Ghost env α => g.name))
      (List.zipIdx_map_fst 0 m.ghosts.toList)
    simp only [List.map_map, Function.comp_def] at hmap
    simpa [Module.Raw.ghostSigs, Module.Raw.ghostNames, Array.mapK_eq_map_fun, Function.comp_def,
      hmap] using hg
  obtain ⟨tbl, htbl⟩ := Option.isSome_iff_exists.mp (NameMap.ofArray?_isSome_iff.mpr hnd)
  rw [Module.Raw.ghostTable, htbl, Option.getD_some, NameMap.find?_ofArray? htbl,
    Module.Raw.ghostSigs, List.mem_toArray, List.mem_map]
  constructor
  · rintro ⟨⟨g, j⟩, hm, he⟩
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨g, by simpa using List.mk_mem_zipIdx_iff_getElem?.mp hm, rfl, rfl⟩
  · rintro ⟨g, hg, rfl, rfl⟩
    exact ⟨(g, i), List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hg), rfl⟩

/-- In a well-formed module, each ghost reference names a ghost of the module, at the type of the
ghost's cell, a `base.Ref` of the ghost's type. -/
theorem Module.Raw.WF.ghostRef_fits {m : Module.Raw env α} (h : m.WF) {u : GhostUse env}
    (hu : (∃ f ∈ m.funcs, u ∈ f.ghostRefs) ∨ ∃ g ∈ m.ghosts, u ∈ g.ghostRefs) :
    ∃ g ∈ m.ghosts, g.name = u.target ∧ u.type = Base.Ref g.type := by
  have hfit : u.Fits m.ghostTable := by
    rcases hu with ⟨f, hf, hu⟩ | ⟨g, hg, hu⟩
    · exact h.ghostRefs.1 f hf u hu
    · exact h.ghostRefs.2 g hg u hu
  obtain ⟨⟨i, t⟩, hp, hty⟩ := hfit
  obtain ⟨g, hg, hn, rfl⟩ := (h.find?_ghostTable u.target i t).mp hp
  exact ⟨g, Array.mem_of_getElem? hg, hn, hty⟩

/-- In a well-formed module, each ghost reference of the initializer of the ghost at position `i`
names a ghost at a position before `i`. -/
theorem Module.Raw.WF.initRef_before {m : Module.Raw env α} (h : m.WF) {i : Nat}
    {g : Ghost env α} (hg : m.ghosts[i]? = some g) {u : GhostUse env} (hu : u ∈ g.initRefs) :
    ∃ j < i, ∃ g', m.ghosts[j]? = some g' ∧ g'.name = u.target := by
  have hall : ∀ v ∈ g.ghostRefs, v.Fits m.ghostTable := h.ghostRefs.2 g (Array.mem_of_getElem? hg)
  obtain ⟨⟨j, t⟩, hp, -⟩ := hall u (Array.mem_append_left _ hu)
  have hbefore := h.ghostOrder (g, i) (List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa using hg))
    u (by simpa using hu)
  simp only [GhostUse.Before, hp, Option.all_some, decide_eq_true_eq] at hbefore
  obtain ⟨g', hg', hn, -⟩ := (h.find?_ghostTable u.target j t).mp hp
  exact ⟨j, hbefore, g', hg', hn⟩

end

end Strata.Dyn
