/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

meta import all StrataPython.PySpecPipeline
meta import all StrataPython.PyFactory
meta import all Strata.Languages.Core

meta section

/-! # Prelude Verification Test

Verify that all prelude procedures pass verification.
This ensures the Python runtime prelude is well-formed
after PrecondElim generates WF-checking procedures. -/

open Strata
namespace StrataPython.PreludeVerifyTest

/-- Build a full Core prelude program (Laurel-translated + Core-only parts). -/
private def preludeProgram (runtime : Laurel.Program) : IO Core.Program := do
  let (coreOption, _) ← StrataPython.translateCombinedLaurel runtime
  match coreOption with
  | some prog => return prog
  | none => return { decls := [] }

private def verifyPrelude (runtime : Laurel.Program) : IO (Array Message) := do
  let prog ← preludeProgram runtime
  IO.FS.withTempDir fun tempDir => do
    let r ← EIO.toIO (IO.Error.userError ∘ toString)
      (_root_.Core.verify prog tempDir
        (options := .quiet)
        (moreFns := StrataPython.RuntimeFactory)
        (externalPhases := [Strata.frontEndPhase]))
    return r.flatMap (fun vcr => (toMessage vcr []).toArray)

/-- info: #[] -/
#guard_msgs in
#eval verifyPrelude pythonRuntimeLaurelPart

/-- info: #[] -/
#guard_msgs in
#eval verifyPrelude <|
  StrataPython.combinePySpecLaurel
    pythonRuntimeLaurelPart pySpecRuntimeLaurelPart

end StrataPython.PreludeVerifyTest
end
