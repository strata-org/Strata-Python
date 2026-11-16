/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF

set_option autoImplicit false

/-!
# Shapes of a module's bodies

A pass that lowers a module towards a target with less structure assumes its input in some
shape, and leaves its output in another.  Each shape here is a `Prop` of a function, with a
`Decidable` instance, and holds of a module when it holds of each of its functions.  A shape
speaks of a function's top-level blocks: contracts are left out.  The instances are for compiled
code: the kernel does not reduce the test of an operation's name, so `decide` proves none of them
but `NoBlockParams`.

* `PlainControl`: no instruction has successors or regions, and every terminator is a `jump`, a
  `branch` or `unreachable` (`ret` is a jump to `Label.exit`).  So every edge of a body is an
  edge of a terminator, which `Terminator.plain?` reads, and a body has no nested blocks.
* `BareBranches`: every arm of every `branch` passes no arguments (`Target.Raw.Bare`).  So only
  a `jump` passes arguments, to a block or to the body's exit.
* `NoBlockParams`: no block but each function's entry has parameters.

`Terminator.plain?` reads a terminator as data.  `Terminator.isControl`
(`StrataDyn/ContractRegion.lean`) is the weaker test that the contract rules use, which also
holds of a datatype's case instruction; no lemma links the two yet. A terminator's shape is
decided by name and arity (`Terminator.plain?`), the arity first, so that `plain?_jump` needs no
fact about the base's names beyond `a == a`.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} [base ≼ env] {α : Type}

/-! ## Plain control -/

/-- A `jump`, a `branch` or `unreachable`, as data: its kind and its edges. -/
inductive PlainTerm where
  | jump (k : Target.Raw)
  | branch (cond : ValId) (t f : Target.Raw)
  | unreachable

/-- The arms of a `branch`; another terminator has none. -/
@[expose] def PlainTerm.arms : PlainTerm → List Target.Raw
  | .branch _ t f => [t, f]
  | _ => []

/-- The terminator that `p` reads as, annotated `info`. -/
@[expose] def PlainTerm.term (info : α) : PlainTerm → Terminator env α
  | .jump k => .jump info k
  | .branch cond t f => .branch info cond t f
  | .unreachable => .unreachable info

/-- Which plain terminator `t` is, if any: a `base.jump` with one successor, a `base.branch`
with one operand and two successors, or a `base.unreachable` with neither, and no regions. -/
@[expose] def Terminator.plain? : Terminator env α → Option PlainTerm
  | .apply _ r _ args succs regions =>
    if !regions.isEmpty then none
    else match args.toList, succs.toList with
      | [], [k] => if r.name == (Base.jump.ref (e := env)).name then some (.jump k) else none
      | [c], [t, f] =>
        if r.name == (Base.branch.ref (e := env)).name then some (.branch c t f) else none
      | [], [] =>
        if r.name == (Base.unreachable.ref (e := env)).name then some .unreachable else none
      | _, _ => none

/-- `t` is a jump, a branch or `unreachable`. -/
@[expose] def Terminator.PlainControl (t : Terminator env α) : Prop := t.plain?.isSome

instance (t : Terminator env α) : Decidable t.PlainControl :=
  inferInstanceAs (Decidable (t.plain?.isSome = true))

/-- Expose the edge of a generated jump when proving a lowering leaves plain control. -/
theorem Terminator.plain?_jump (info : α) (k : Target.Raw) :
    (Terminator.jump (env := env) info k).plain? = some (.jump k) := by
  simp [Terminator.plain?, Terminator.jump]

/-- `i` falls through: it has no successors and no regions. -/
@[expose] def Instruction.Plain (i : Instruction env α) : Prop :=
  i.succs.size = 0 ∧ i.regions.size = 0

instance (i : Instruction env α) : Decidable i.Plain :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Every instruction of the block falls through, and it ends in a jump, a branch or
`unreachable`. -/
@[expose] def Block.PlainControl (b : Block env α) : Prop :=
  (∀ i ∈ b.instrs, i.Plain) ∧ b.term.PlainControl

instance (b : Block env α) : Decidable b.PlainControl :=
  inferInstanceAs (Decidable ((∀ i ∈ b.instrs, i.Plain) ∧ b.term.PlainControl))

/-- Every block of the function's body is in plain control. -/
@[expose] def Func.PlainControl (fn : Func env α) : Prop := ∀ b ∈ fn.blocks, b.PlainControl

instance (fn : Func env α) : Decidable fn.PlainControl :=
  inferInstanceAs (Decidable (∀ b ∈ fn.blocks, b.PlainControl))

/-- Every function's body is in plain control. -/
@[expose] def PlainControl (m : Module.Raw env α) : Prop := ∀ fn ∈ m.funcs, fn.PlainControl

instance (m : Module.Raw env α) : Decidable (PlainControl m) :=
  inferInstanceAs (Decidable (∀ fn ∈ m.funcs, fn.PlainControl))

/-! ## Bare branches -/

/-- The edge passes no arguments. -/
@[expose] def Target.Raw.Bare (k : Target.Raw) : Prop := k.args.size = 0

instance (k : Target.Raw) : Decidable k.Bare :=
  inferInstanceAs (Decidable (_ = _))

/-- If `t` is a branch, each of its arms is bare. -/
@[expose] def Terminator.BareBranch (t : Terminator env α) : Prop :=
  ∀ p ∈ t.plain?, ∀ k ∈ p.arms, k.Bare

instance (t : Terminator env α) : Decidable t.BareBranch :=
  inferInstanceAs (Decidable (∀ p ∈ t.plain?, ∀ k ∈ p.arms, k.Bare))

/-- Every arm of every branch of the function's body is bare. -/
@[expose] def Func.BareBranches (fn : Func env α) : Prop := ∀ b ∈ fn.blocks, b.term.BareBranch

instance (fn : Func env α) : Decidable fn.BareBranches :=
  inferInstanceAs (Decidable (∀ b ∈ fn.blocks, b.term.BareBranch))

/-- Every arm of every branch of every function's body is bare. -/
@[expose] def BareBranches (m : Module.Raw env α) : Prop := ∀ fn ∈ m.funcs, fn.BareBranches

instance (m : Module.Raw env α) : Decidable (BareBranches m) :=
  inferInstanceAs (Decidable (∀ fn ∈ m.funcs, fn.BareBranches))

/-! ## No block parameters -/

/-- No block of the function but its entry, `blocks[0]`, has parameters. -/
@[expose] def Func.NoBlockParams (fn : Func env α) : Prop :=
  ∀ b ∈ fn.blocks.toList.drop 1, b.params.size = 0

instance (fn : Func env α) : Decidable fn.NoBlockParams :=
  inferInstanceAs (Decidable (∀ b ∈ fn.blocks.toList.drop 1, b.params.size = 0))

/-- No block but each function's entry has parameters. -/
@[expose] def NoBlockParams (m : Module.Raw env α) : Prop := ∀ fn ∈ m.funcs, fn.NoBlockParams

instance (m : Module.Raw env α) : Decidable (NoBlockParams m) :=
  inferInstanceAs (Decidable (∀ fn ∈ m.funcs, fn.NoBlockParams))

end

end Strata.Dyn
