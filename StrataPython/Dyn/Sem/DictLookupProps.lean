/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.DictLookup

set_option autoImplicit false

/-!
# Properties of the dict lookup's definitions

* `generatedCaptured_cls`, `generatedCaptured_names` and `generatedCaptured_module`: the data
  that `generatedCaptured` builds holds the class, the compared names and the module's name at
  the slots that the lookup's check reads.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- `generatedCaptured` holds the class at `generatedClsSlot`. -/
theorem generatedCaptured_cls {V : Type} (c n m : V) (rest : Array V) :
    (generatedCaptured c n m rest)[generatedClsSlot]? = some c := by
  rw [generatedCaptured, generatedClsSlot, Array.getElem?_append_left (by simp)]; rfl

/-- `generatedCaptured` holds the compared names at `generatedNamesSlot`. -/
theorem generatedCaptured_names {V : Type} (c n m : V) (rest : Array V) :
    (generatedCaptured c n m rest)[generatedNamesSlot]? = some n := by
  rw [generatedCaptured, generatedNamesSlot, Array.getElem?_append_left (by simp)]; rfl

/-- `generatedCaptured` holds the module's name at `generatedModuleSlot`. -/
theorem generatedCaptured_module {V : Type} (c n m : V) (rest : Array V) :
    (generatedCaptured c n m rest)[generatedModuleSlot]? = some m := by
  rw [generatedCaptured, generatedModuleSlot, Array.getElem?_append_left (by simp)]; rfl

end

end StrataPython.Dyn.Sem
