/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataDyn.Examples.While.Elab
import StrataDyn.Examples.While.Run
import StrataDyn.Env.WF
-- `#guard` runs the lowering and the engine as compiled code.
meta import StrataDyn.Examples.While.Elab
meta import StrataDyn.Examples.While.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# `#while … #end`

Precedence, a parse error, and the dialect's keywords staying out of Lean's token table.
-/

namespace Strata.Dyn.While.ElabTest

open Strata.Dyn.While Strata.Dyn.While.Ast

/-- How a run of `f` of `p` ends. -/
def runF (p : Program) : String :=
  match run p "f" #[] with
  | .ok o => showOutcome o
  | .error e => s!"lowering error: {e}"

/-! ## Precedence -/

-- `*` and `/` bind tighter than `+` and `-`, which associate to the left.
#guard runF #while fun f() : Int { return 1 + 2 * 3 - 8 / 2 - 1; } #end = "ok 2"

-- `!` binds tighter than `&&`, which binds tighter than `||`; comparisons tighter still.
#guard runF #while
    fun f() : Int { if (!true || 1 < 2 && 3 == 3) { return 1; } else { return 0; } }
  #end = "ok 1"

-- `::` associates to the right and binds looser than `+`.
#guard runF #while
    fun f() : Int { return case 1 + 1 :: 3 :: nil of nil => 0 | h :: t => h; }
  #end = "ok 2"

/-! ## Errors -/

/-- error: unexpected token ';'; expected While.Exp -/
#guard_msgs in
example : Program := #while fun f() : Int { return 1 +; } #end

/-! ## Keywords -/

-- The dialect's keywords are not Lean tokens.
def call (var raise nil : Nat) : Nat := var + raise + nil

example : call 1 2 3 = 6 := rfl

end Strata.Dyn.While.ElabTest
