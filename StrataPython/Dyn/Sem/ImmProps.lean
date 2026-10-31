/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Imm

set_option autoImplicit false

/-!
# Properties of the immediates

`Imm.toImm?_toValue`: an immediate, made a value and viewed again, is itself.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- **The round trip**: an immediate, made a value and viewed again, is itself. -/
theorem Imm.toImm?_toValue (i : Imm Value) : i.toValue.toImm? = some i := by
  cases i with
  | symHash n => obtain ⟨src, h⟩ := n; simp [Imm.toValue, Value.toImm?, h]
  | _ => rfl

end

end StrataPython.Dyn.Sem
