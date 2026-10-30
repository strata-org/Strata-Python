/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
-- Private: the module's importers do not see the typed builder.
import StrataDyn.Build.Typed
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# Typed emitters, with the typed builder imported privately

A public environment's emitters name the typed builder, so they are public only when the
module's importers can see it, as in `TypedEmitTest`.  Here the module imports it privately, and
the public environment gets private emitters, which the module itself uses.
-/

namespace Strata.Dyn.TypedEmitPrivateTest

/-- A public child of `Base`. -/
public environment Pt extends Base where
  namespace pt
  open base
  insn twice [a] (x : a) : a
  insn loop [a] (x : a) (&body (i : Ref a) : Int) : Ref a
  end pt

-- Public emitters would name the privately imported `MonadBuild`, and fail to elaborate.
example (v : Val Pt.env Base.Int) : BuildM Pt.env Unit (Val Pt.env Base.Int) :=
  Pt.twice v
example (v : Val Pt.env Base.Int) : BuildM Pt.env Unit (Val Pt.env (Base.Ref Base.Int)) :=
  Pt.loop v (fun r exit => do
    let _ ← Base.refGet r
    Base.jump (exit.bind (← Emit.int (.str .base "k") 0)))

end Strata.Dyn.TypedEmitPrivateTest
