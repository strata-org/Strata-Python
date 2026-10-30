/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
public import StrataDyn.Exec
public import StrataDyn.Exec.Base
public import StrataDynTest.Exec.RuleHelpers
public import StrataDynTest.Exec.RecheckHiddenUse
public import StrataDynTest.Exec.RecheckHiddenDefs
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# What only the recheck sees

Each table here passes in this module, but each one's rule runs other code than its definition.
`swappedHereNI` and `privSwapped` were each compiled with a local `@[csimp]` swap whose lemma is
private to `RuleHelpers`, so this module sees neither the lemma nor the compiled code.  The
first lemma is true, and its target runs `lieRevP`; the second is false, proved by `sorry`.
`swappedI` was compiled with a swap whose lemma is public, but in a module that its own module
imports only privately, so this module doesn't see it either.  The recheck
(`recheckTableModules`) sees all three lemmas, and finds all three.  `faultSwappedNI` was
compiled with a true private swap too, whose target names `Fault.badCell`, a fault that only the
machine reports; the recheck finds it.  `initFive` is in another
module too, which this module sees without its `@[init]` attribute; the recheck finds it
(`StrataPythonTestExtra/DynRecheckTest.lean`).
-/

namespace Strata.Dyn.ExecTest.RecheckSwap

open Strata.Dyn.Exec

/-- A rule over a helper compiled with a true private swap, whose target runs other code. -/
environment SwLocal extends Base where
  namespace swLocal
  open base
  insn f (xs : Sequence Int) : Sequence Int
  end swLocal

#dyn_types SwLocal

@[dyn_sem SwLocal.f] def viaLocal (xs : Array Int) : Array Int := Helpers.swappedHereNI xs

#guard_msgs in
#dyn_sem_table LocalSem for SwLocal

/-- A rule over a helper compiled with a false private swap. -/
environment SwPrivate extends Base where
  namespace swPrivate
  open base
  insn f (x : Int) : Int
  end swPrivate

#dyn_types SwPrivate

@[dyn_sem SwPrivate.f] def viaPrivate (x : Int) : Int := Helpers.privSwapped x

#guard_msgs in
#dyn_sem_table PrivateSem for SwPrivate

/-- A rule over a helper compiled with a swap whose public lemma is in a module that the helper's
module imports only privately. -/
environment SwHidden extends Base where
  namespace swHidden
  open base
  insn f (xs : Sequence Int) : Sequence Int
  end swHidden

#dyn_types SwHidden

@[dyn_sem SwHidden.f] def viaHidden (xs : Array Int) : Array Int := HiddenUse.swappedI xs

#guard_msgs in
#dyn_sem_table HiddenSem for SwHidden

/-- A rule over another module's `@[init]` definition, which this module sees without its
attribute. -/
environment SwInit extends Base where
  namespace swInit
  open base
  insn f (x : Int) : Int
  end swInit

#dyn_types SwInit

@[dyn_sem SwInit.f] def viaInit (x : Int) : Int := x + HiddenLemma.initFive

#guard_msgs in
#dyn_sem_table InitSem for SwInit

/-- A rule over a helper compiled with a true private swap, whose target names a fault that only
the machine reports. -/
environment SwFault extends Base where
  namespace swFault
  open base
  insn f (x : Int) : Int
  end swFault

#dyn_types SwFault

@[dyn_sem SwFault.f] def viaFault {ε : Eff} {E : Type} (x : Int) : Sem ε E Int :=
  Helpers.faultSwappedNI x

#guard_msgs in
#dyn_sem_table FaultSem for SwFault

end Strata.Dyn.ExecTest.RecheckSwap
