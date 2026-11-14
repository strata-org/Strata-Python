/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Shape

set_option autoImplicit false

/-!
# Shapes for case lowering

Bodies are flat. Contract regions may remain nested, for example under old or a quantifier;
only their control flow is lowered. These shapes include frames and ghost regions.

`CasesInput` is what case lowering takes and `Cased` what it returns. Two theorems connect
them to other passes: `casesInput_cased` makes the result admissible input again, and
`demotable_cased` gives the two body shapes of `StrataDyn/Shape.lean` that demotion assumes.

The instances run only as compiled code. Besides the name tests of the body shapes,
`Terminator.CaseControl` looks the operation up in the environment's hash map, which the kernel
does not reduce.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} [base ≼ env] {α : Type}

/-- A base control terminator, or a datatype case with no regions. -/
@[expose] def Terminator.CaseControl (t : Terminator env α) : Prop :=
  t.PlainControl ∨ match t with
    | .apply _ r _ _ _ rs => r.caseAddr?.isSome ∧ rs.size = 0

instance (t : Terminator env α) : Decidable t.CaseControl := by
  unfold Terminator.CaseControl
  cases t
  infer_instance

/-- Every instruction of every function's body falls through: bodies have no nested regions
and no second exits. Specification instructions are not constrained. -/
@[expose] def FlatBodies (m : Module.Raw env α) : Prop :=
  ∀ fn ∈ m.funcs, ∀ b ∈ fn.blocks, ∀ i ∈ b.instrs, i.Plain

instance (m : Module.Raw env α) : Decidable (FlatBodies m) :=
  inferInstanceAs (Decidable (∀ fn ∈ m.funcs, ∀ b ∈ fn.blocks, ∀ i ∈ b.instrs, i.Plain))

/-- The input of Cases: flat bodies, and only base control or case terminators throughout,
specifications included. -/
@[expose] def CasesInput (m : Module.Raw env α) : Prop :=
  FlatBodies m ∧ ∀ b ∈ m.allBlocks, b.term.CaseControl

instance (m : Module.Raw env α) : Decidable (CasesInput m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The output of Cases: flat bodies, and only plain terminators with bare branch arms
throughout, specifications included. -/
@[expose] def Cased (m : Module.Raw env α) : Prop :=
  FlatBodies m ∧ ∀ b ∈ m.allBlocks, b.term.PlainControl ∧ b.term.BareBranch

instance (m : Module.Raw env α) : Decidable (Cased m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Lowered control is also admissible input: a second application needs no case accessors. -/
theorem casesInput_cased {m : Module.Raw env α} (h : Cased m) : CasesInput m :=
  ⟨h.1, fun b hb => .inl (h.2 b hb).1⟩

/-- Cases supplies the plain control and bare branches that demotion assumes of bodies. -/
theorem demotable_cased {m : Module.Raw env α} (h : Cased m) : PlainControl m ∧ BareBranches m :=
  ⟨fun fn hfn b hb => ⟨h.1 fn hfn b hb, (h.2 b (Module.Raw.mem_allBlocks hfn hb)).1⟩,
    fun _ hfn b hb => (h.2 b (Module.Raw.mem_allBlocks hfn hb)).2⟩

end

end Strata.Dyn
