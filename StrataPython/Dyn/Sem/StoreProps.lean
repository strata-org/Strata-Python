/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Store

set_option autoImplicit false

/-!
# Properties of the store

Allocating adds one object and keeps the others; updating an object keeps the size and the
other objects; a lifted payload is seen as itself.

Key theorems: `ObjStore.get?_alloc`, `ObjStore.get?_update_ne`, `ObjStore.get?_update_self`.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec

@[expose] public section

namespace ObjStore
variable {σ : Type} [Store σ]

/-- Allocating adds one object. -/
theorem size_alloc (s : ObjStore σ) (o : Obj σ) : (s.alloc o).1.size = s.size + 1 := by
  simp [alloc, size]

/-- Updating keeps the number of objects. -/
theorem size_update (s : ObjStore σ) (id : ObjId) (f : Obj σ → Obj σ) :
    (s.update id f).size = s.size := by
  simp [update, size]

/-- Allocating keeps every older object. -/
theorem get?_alloc_lt (s : ObjStore σ) (o : Obj σ) {id : ObjId} (h : id < s.size) :
    (s.alloc o).1.get? id = s.get? id := by
  simp [alloc, get?, Array.getElem?_push, show id ≠ s.objs.size from Nat.ne_of_lt h]

/-- The objects of a store with one more. -/
theorem get?_alloc (s : ObjStore σ) (o : Obj σ) (id : ObjId) :
    (s.alloc o).1.get? id = if id = s.size then some o else s.get? id := by
  simp only [alloc, get?, size, Array.getElem?_push]
  split <;> simp_all

/-- Updating one object keeps every other. -/
theorem get?_update_ne (s : ObjStore σ) {id id' : ObjId} (f : Obj σ → Obj σ) (h : id ≠ id') :
    (s.update id f).get? id' = s.get? id' := by
  simp [update, get?, Array.getElem?_modify, h]

/-- Updating an object changes it by `f`. -/
theorem get?_update_self (s : ObjStore σ) (id : ObjId) (f : Obj σ → Obj σ) :
    (s.update id f).get? id = (s.get? id).map f := by
  simp [update, get?, Array.getElem?_modify]

end ObjStore

/-- Seeing a lifted payload gives it back. -/
theorem PayloadG.data?_lift {F : Type} (p : PayloadData) :
    (p.lift : PayloadG F).data? = some p := by
  cases p <;> first | rfl | (rename_i f; exact nomatch f)

end

end StrataPython.Dyn.Sem
