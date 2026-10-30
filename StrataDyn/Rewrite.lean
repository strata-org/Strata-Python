/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR

set_option autoImplicit false

/-!
# Rewriting the uses of values

`mapUses f` replaces every use of a value `v` by `f v`: each operand, and each argument an
edge passes, of every instruction and terminator, regions included.  Definitions (results,
block parameters) and everything else stay as they are.  A pass that removes a definition uses
it to point each use of the removed value at the value that replaces it.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-- `k` with `f` applied to each argument it passes. -/
@[expose] def Target.Raw.mapUses (f : ValId → ValId) (k : Target.Raw) : Target.Raw :=
  { k with args := k.args.map f }

mutual

/-- `t` with `f` applied to each use, regions included. -/
@[expose] def Terminator.mapUses (f : ValId → ValId) : Terminator env α → Terminator env α
  | .apply info r typeArgs args succs ⟨regions⟩ =>
    .apply info r typeArgs (args.map f) (succs.map (·.mapUses f)) ⟨Region.mapUsesList f regions⟩

/-- `i` with `f` applied to each use, regions included. -/
@[expose] def Instruction.mapUses (f : ValId → ValId) : Instruction env α → Instruction env α
  | .const info result c => .const info result c
  | .apply info result r typeArgs args succs ⟨regions⟩ =>
    .apply info result r typeArgs (args.map f) (succs.map (·.mapUses f))
      ⟨Region.mapUsesList f regions⟩

/-- `Instruction.mapUses` on each. -/
@[expose] def Instruction.mapUsesList (f : ValId → ValId) :
    List (Instruction env α) → List (Instruction env α)
  | [] => []
  | i :: is => i.mapUses f :: Instruction.mapUsesList f is

/-- `b` with `f` applied to each use of its instructions and terminator. -/
@[expose] def Block.mapUses (f : ValId → ValId) : Block env α → Block env α
  | ⟨label, params, ⟨instrs⟩, term, info⟩ =>
    ⟨label, params, ⟨Instruction.mapUsesList f instrs⟩, term.mapUses f, info⟩

/-- `Block.mapUses` on each. -/
@[expose] def Block.mapUsesList (f : ValId → ValId) : List (Block env α) → List (Block env α)
  | [] => []
  | b :: bs => b.mapUses f :: Block.mapUsesList f bs

/-- `r` with `f` applied to each use of its blocks. -/
@[expose] def Region.mapUses (f : ValId → ValId) : Region env α → Region env α
  | ⟨⟨blocks⟩⟩ => ⟨⟨Block.mapUsesList f blocks⟩⟩

/-- `Region.mapUses` on each. -/
@[expose] def Region.mapUsesList (f : ValId → ValId) :
    List (Region env α) → List (Region env α)
  | [] => []
  | r :: rs => r.mapUses f :: Region.mapUsesList f rs

end

/-- `fn` with `f` applied to each use of its body, regions included.  Its contract stays as it
is. -/
@[expose] def Func.mapUses (f : ValId → ValId) (fn : Func env α) : Func env α :=
  { fn with blocks := ⟨Block.mapUsesList f fn.blocks.toList⟩ }

end

end Strata.Dyn
