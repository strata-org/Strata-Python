/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Monad
public import StrataPython.Dyn.Sem.WorldProps
public import StrataPython.Dyn.Sem.StoreProps

set_option autoImplicit false

/-!
# Where the parts of the world hold refs

Properties of the `Refs` instances of `Monad.lean`, for the store and the module table: a new
object that a rule makes (`refsOK_alloc_lift`), an update of an object that adds no ref
(`refsOK_update`), the closure of a function object (`refsOK_closure`), and the global cells of a
module table (`valid_of_cell?`, `refsOK_withCell`) keep the refs valid or are valid.

The inputs of a region handle take exactly their number of values: `noValues_eq_some`,
`oneValue_eq_some` and `twoValues_eq_some`.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec Strata.Dyn.Exec.Effects

@[expose] public section

section
variable {σ : Type} [Store σ]

/-- A new object adds its own refs to the store's. -/
theorem refs_alloc (st : ObjStore σ) (o : Obj σ) :
    Refs.refs (σ := σ) (st.alloc o).1 = Refs.refs (σ := σ) st ++ Refs.refs (σ := σ) o := by
  simp [ObjStore.alloc, Refs.refs]

/-- An object that a rule makes holds no closure. -/
theorem refs_lift (o : ObjData) : Refs.refs (σ := σ) (ObjG.lift o : Obj σ) = [] := by
  obtain ⟨_, _, _, p⟩ := o
  cases p <;> first | rfl | (rename_i f; exact nomatch f)

/-- A new object that a rule makes keeps the store's refs valid. -/
theorem refsOK_alloc_lift {G : Typing} {st : ObjStore σ} (o : ObjData)
    (h : RefsOK (σ := σ) G st) : RefsOK (σ := σ) G (st.alloc (ObjG.lift o)).1 := by
  unfold RefsOK
  rw [refs_alloc, refs_lift, List.append_nil]
  exact h

/-- An update of an object by a function that adds no ref adds no ref to the store. -/
theorem refs_update_sub (st : ObjStore σ) (id : ObjId) (f : Obj σ → Obj σ)
    (hf : ∀ o, ∀ l ∈ Refs.refs (σ := σ) (f o), l ∈ Refs.refs (σ := σ) o) :
    ∀ l ∈ Refs.refs (σ := σ) (st.update id f), l ∈ Refs.refs (σ := σ) st := by
  intro l hl
  change l ∈ (st.objs.modify id f).toList.flatMap (Refs.refs (σ := σ)) at hl
  change l ∈ st.objs.toList.flatMap (Refs.refs (σ := σ))
  rw [List.mem_flatMap] at hl ⊢
  obtain ⟨x, hx, hlx⟩ := hl
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hx)
  have hi' : i < st.objs.size := by simpa using hi
  rw [Array.getElem_modify] at hlx
  split at hlx
  · exact ⟨st.objs[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi'), hf _ l hlx⟩
  · exact ⟨st.objs[i], Array.mem_toList_iff.mpr (Array.getElem_mem hi'), hlx⟩

/-- An update of an object by a function that adds no ref keeps the store's refs valid. -/
theorem refsOK_update {G : Typing} {st : ObjStore σ} (id : ObjId) (f : Obj σ → Obj σ)
    (hf : ∀ o, ∀ l ∈ Refs.refs (σ := σ) (f o), l ∈ Refs.refs (σ := σ) o)
    (h : RefsOK (σ := σ) G st) : RefsOK (σ := σ) G (st.update id f) :=
  fun l hl => h l (refs_update_sub st id f hf l hl)

/-- The closure of a function object of a store whose refs are valid is valid. -/
theorem refsOK_closure {G : Typing} {st : ObjStore σ} {id : ObjId} {f : FuncObj σ}
    (h : RefsOK (σ := σ) G st)
    (hget : ((st.get? id).map (·.payload) : Option (ObjPayload σ)) = some (.func f)) :
    RefsOK (σ := σ) G f.closure := by
  intro l hl
  simp only [ObjStore.get?, Option.map_eq_some_iff] at hget
  obtain ⟨o, ho, hp⟩ := hget
  apply h l
  change l ∈ st.objs.toList.flatMap (Refs.refs (σ := σ))
  rw [List.mem_flatMap]
  refine ⟨o, Array.mem_toList_iff.mpr (Array.mem_of_getElem? ho), ?_⟩
  change l ∈ Refs.refs (σ := σ) o.payload
  rw [hp]
  exact hl

/-- The refs of a module table are its global cells, each at the tag of `Value`. -/
theorem mem_modulesRefs [Decode σ] (tg : TagOf σ Value) (m : Modules σ) (l : Loc) :
    l ∈ @Refs.refs σ _ _ (modulesRefs tg) m ↔
      ∃ (k n : String) (r : Ref σ Value), m.cell? k n = some r ∧ l = .cell r.loc tg.tag := by
  change l ∈ m.map.toList.flatMap (fun e => e.2.cells.toList.map fun c => Loc.cell c.2.loc tg.tag) ↔ _
  simp only [List.mem_flatMap, List.mem_map, Modules.cell?, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨⟨k, e⟩, he, ⟨n, r⟩, hr, rfl⟩
    exact ⟨k, n, r, ⟨e, Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp he,
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hr⟩, rfl⟩
  · rintro ⟨k, n, r, ⟨e, he, hr⟩, rfl⟩
    exact ⟨(k, e), Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr he, (n, r),
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hr, rfl⟩

/-- A global cell of a module table whose refs are valid is valid, at the tag of `Value`. -/
theorem valid_of_cell? [Decode σ] (tg : TagOf σ Value) {G : Typing} {m : Modules σ}
    {module name : String} {r : Ref σ Value} (h : @RefsOK σ _ (Modules σ) (modulesRefs tg) G m)
    (hr : m.cell? module name = some r) : G.Valid r.loc tg.tag :=
  h (.cell r.loc tg.tag) ((mem_modulesRefs tg m _).mpr ⟨module, name, r, hr, rfl⟩)

/-- A new global cell that is valid keeps a module table's refs valid. -/
theorem refsOK_withCell [Decode σ] (tg : TagOf σ Value) {G : Typing} {m : Modules σ} (module name : String)
    (obj : ObjId) {r : Ref σ Value} (h : @RefsOK σ _ (Modules σ) (modulesRefs tg) G m)
    (hr : G.Valid r.loc tg.tag) :
    @RefsOK σ _ (Modules σ) (modulesRefs tg) G (m.withCell module name obj r) := by
  intro l hl
  obtain ⟨k, n, r', hr', rfl⟩ := (mem_modulesRefs tg _ l).mp hl
  rcases Modules.cell?_withCell _ _ _ _ _ k n r' hr' with h' | rfl
  · exact h _ ((mem_modulesRefs tg m _).mpr ⟨k, n, r', h', rfl⟩)
  · exact hr

/-- A function on payloads that adds no closure adds no ref to an object. -/
theorem keepsClosures_obj {f : ObjPayload σ → ObjPayload σ} (hf : KeepsClosures f) :
    ∀ o : Obj σ, ∀ l ∈ Refs.refs (σ := σ) ({ o with payload := f o.payload } : Obj σ),
      l ∈ Refs.refs (σ := σ) o :=
  fun o => hf o.payload

end

/-- `noValues` takes exactly the empty array. -/
theorem noValues_eq_some (a : Array Value) : noValues a = some () ↔ a = #[] := by
  rcases a with ⟨_ | ⟨x, l⟩⟩ <;> simp [noValues]

/-- `oneValue` takes exactly the arrays of one value, and gives that value. -/
theorem oneValue_eq_some (a : Array Value) (x : Value) : oneValue a = some x ↔ a = #[x] := by
  rcases a with ⟨_ | ⟨y, _ | ⟨z, l⟩⟩⟩ <;> simp [oneValue]

/-- `twoValues` takes exactly the arrays of two values, and gives them in order. -/
theorem twoValues_eq_some (a : Array Value) (x y : Value) :
    twoValues a = some (x, y) ↔ a = #[x, y] := by
  rcases a with ⟨_ | ⟨u, _ | ⟨v, _ | ⟨w, l⟩⟩⟩⟩ <;> simp [twoValues]

end

end StrataPython.Dyn.Sem
