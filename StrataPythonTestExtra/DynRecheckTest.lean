/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataDyn.Exec.Recheck

/-! # Every built table, checked again with every module's private declarations in view

`recheckTableModules` checks each built module that holds a table in its own process, which
imports the module alone, where every module, with its private declarations and compiled code, is
visible, and checks its tables again.  The findings must be exactly
the five deliberate ones of `StrataDynTest/Exec/RecheckSwapTest.lean`, which pass in their own
module.  It also prints the first loop that each library loop in `endingPartials` reaches, so that
a change of Lean's library shows here.  This file imports only the core, and runs after the build. -/

namespace Strata.Dyn.RecheckTest

/-- The findings the recheck must report, sorted. -/
private meta def expected : Array String := #[
  "the table Strata.Dyn.ExecTest.RecheckSwap.FaultSem, through Strata.Dyn.ExecTest.RecheckSwap.FaultSem.table, reaches Strata.Dyn.Exec.Fault.badCell (_private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.FaultSem.table → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.FaultSem.ops → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.FaultSem.impl.swFault.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.FaultSem.rule.swFault.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.viaFault → Strata.Dyn.ExecTest.Helpers.faultSwappedNI → Strata.Dyn.ExecTest.Helpers.gapP → Strata.Dyn.ExecTest.Helpers.gapOrBadCellP → Strata.Dyn.Exec.Fault.badCell), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible.",
  "the table Strata.Dyn.ExecTest.RecheckSwap.HiddenSem, through Strata.Dyn.ExecTest.RecheckSwap.HiddenSem.table, reaches Strata.Dyn.ExecTest.HiddenLemma.myRevI (_private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.HiddenSem.table → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.HiddenSem.ops → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.HiddenSem.impl.swHidden.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.HiddenSem.rule.swHidden.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.viaHidden → Strata.Dyn.ExecTest.HiddenUse.swappedI → Strata.Dyn.ExecTest.HiddenLemma.revI → Strata.Dyn.ExecTest.HiddenLemma.myRevI), which carries @[implemented_by Strata.Dyn.ExecTest.HiddenLemma.lieRevI]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead",
  "the table Strata.Dyn.ExecTest.RecheckSwap.InitSem, through Strata.Dyn.ExecTest.RecheckSwap.InitSem.table, reaches Strata.Dyn.ExecTest.HiddenLemma.initFive (_private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.InitSem.table → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.InitSem.ops → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.InitSem.impl.swInit.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.InitSem.rule.swInit.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.viaInit → Strata.Dyn.ExecTest.HiddenLemma.initFive), which carries @[init Strata.Dyn.ExecTest.HiddenLemma.initSeven]: a run uses the value that Strata.Dyn.ExecTest.HiddenLemma.initSeven computes, not the definition proofs read",
  "the table Strata.Dyn.ExecTest.RecheckSwap.LocalSem, through Strata.Dyn.ExecTest.RecheckSwap.LocalSem.table, reaches Strata.Dyn.ExecTest.Helpers.myRevP (_private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.LocalSem.table → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.LocalSem.ops → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.LocalSem.impl.swLocal.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.LocalSem.rule.swLocal.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.viaLocal → Strata.Dyn.ExecTest.Helpers.swappedHereNI → Strata.Dyn.ExecTest.Helpers.revP → Strata.Dyn.ExecTest.Helpers.myRevP), which carries @[implemented_by Strata.Dyn.ExecTest.Helpers.lieRevP]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead",
  "the table Strata.Dyn.ExecTest.RecheckSwap.PrivateSem, through Strata.Dyn.ExecTest.RecheckSwap.PrivateSem.table, reaches Strata.Dyn.ExecTest.Helpers.fPv (_private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.PrivateSem.table → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.PrivateSem.ops → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.PrivateSem.impl.swPrivate.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.PrivateSem.rule.swPrivate.f → _private.StrataDynTest.Exec.RecheckSwapTest.0.Strata.Dyn.ExecTest.RecheckSwap.viaPrivate → Strata.Dyn.ExecTest.Helpers.privSwapped → Strata.Dyn.ExecTest.Helpers.fPv), and the lemma _private.StrataDynTest.Exec.RuleHelpers.0.Strata.Dyn.ExecTest.Helpers.fPv_eq_gPv equates Strata.Dyn.ExecTest.Helpers.fPv with Strata.Dyn.ExecTest.Helpers.gPv, so a local @[csimp] swap may run Strata.Dyn.ExecTest.Helpers.gPv instead; _private.StrataDynTest.Exec.RuleHelpers.0.Strata.Dyn.ExecTest.Helpers.fPv_eq_gPv reaches the axiom sorryAx, but a rule may reach only propext, Classical.choice and Quot.sound",
  "the trusted library loop String.Slice.foldl reaches WellFounded.extrinsicFix₃ (String.Slice.foldl → Std.Iterators.Types.Map.instIteratorLoop → Std.IteratorLoop.defaultImplementation → Std.IterM.DefaultConsumers.forIn' → WellFounded.extrinsicFix₃)",
  "the trusted library loop String.Slice.isNat reaches WellFounded.extrinsicFix₃ (String.Slice.isNat → String.Slice.RevByteIterator.instForInCharOfMonad → Std.Iterators.Types.Map.instIteratorLoop → Std.IteratorLoop.defaultImplementation → Std.IterM.DefaultConsumers.forIn' → WellFounded.extrinsicFix₃)",
  "the trusted library loop String.Slice.toInt? reaches WellFounded.extrinsicFix₃ (String.Slice.toInt? → String.Slice.toNat? → String.Slice.foldl → Std.Iterators.Types.Map.instIteratorLoop → Std.IteratorLoop.defaultImplementation → Std.IterM.DefaultConsumers.forIn' → WellFounded.extrinsicFix₃)",
  "the trusted library loop String.Slice.toNat? reaches WellFounded.extrinsicFix₃ (String.Slice.toNat? → String.Slice.foldl → Std.Iterators.Types.Map.instIteratorLoop → Std.IteratorLoop.defaultImplementation → Std.IterM.DefaultConsumers.forIn' → WellFounded.extrinsicFix₃)"]

/-- A run's output without the loops of `endingPartials` that it prints. -/
private meta def own (out : String) : String :=
  "".intercalate ((out.splitOn "\n").filter (fun l => l != "" &&
    !l.startsWith "the trusted library loop ") |>.map (· ++ "\n"))

#eval show IO Unit from do
  let found ← Strata.Dyn.Exec.recheckTableModules ".lake/build/lib/lean" "." ".lake/build/bin/dynRecheck"
  IO.println s!"DynRecheckTest: {found.size} findings"
  unless found == expected do
    for f in found do IO.println f
    throw <| IO.userError "DynRecheckTest: the findings differ from the expected ones"

-- A module that holds a table but that the recheck did not find is a finding: here, the run
-- for `InheritTest`, which imports the While example's table, is told to leave that one out.
#eval show IO Unit from do
  let args := #[".lake/build/lib/lean", ".", "StrataDynTest.Exec.InheritTest", "--without",
    "StrataDyn.Examples.While.Env"]
  let r ← IO.Process.output { cmd := ".lake/build/bin/dynRecheck", args }
  unless own r.stdout == "StrataDyn.Examples.While.Env holds a table, but the recheck did not find it\n" do
    throw <| IO.userError s!"DynRecheckTest: the missed module is not reported:\n{r.stdout}{r.stderr}"

-- A trusted library loop that reaches no loop is a finding: here `List.length`, added to the list
-- for the run of `InheritTest`.
#eval show IO Unit from do
  let args := #[".lake/build/lib/lean", ".", "StrataDynTest.Exec.InheritTest", "--ending",
    "List.length"]
  let r ← IO.Process.output { cmd := ".lake/build/bin/dynRecheck", args }
  unless own r.stdout == "endingPartials lists List.length, but it reaches no loop that the check rejects: remove it\n" do
    throw <| IO.userError s!"DynRecheckTest: the stale entry is not reported:\n{r.stdout}{r.stderr}"

-- A run of the executable that fails is the recheck's failure, not a pass.
#eval show IO Unit from do
  let r ← (Strata.Dyn.Exec.recheckTableModules ".lake/build/lib/lean" "." "false").toBaseIO
  match r with
  | .ok _ => throw <| IO.userError "DynRecheckTest: a failed run of the recheck passed"
  | .error e =>
    -- `false` exits with 1 on the first module the recheck runs.
    let msg := toString e
    unless msg.startsWith "dynRecheck " && (msg.splitOn " failed (1):").length == 2 do
      throw <| IO.userError s!"DynRecheckTest: a failed run gave another error: {e}"

end Strata.Dyn.RecheckTest
