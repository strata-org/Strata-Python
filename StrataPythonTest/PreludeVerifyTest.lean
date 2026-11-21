/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

meta import all StrataPython.PySpecPipeline
meta import all StrataPython.PyFactory
meta import all Strata.Languages.Core
meta import all StrataPython.PythonRuntimeLaurelPart
import StrataLaurel.Implementation.Grammar.LaurelGrammar
import StrataLaurel.Implementation.Grammar.ConcreteToAbstractTreeTranslator
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Prelude Verification Test

Verify that all prelude procedures pass verification.
This ensures the Python runtime prelude is well-formed
after PrecondElim generates WF-checking procedures.

A user run trusts the contracts of the prelude's opaque procedures: a caller knows an opaque
procedure only through its contract, and the analysis of user code does not verify prelude
bodies. Each opaque prelude body is verified against its contract here instead, once, in
deductive and in bug-finding mode, and every check must be proved. -/

open Strata
namespace StrataPython.PreludeVerifyTest

/-- Build a full Core prelude program (Laurel-translated + Core-only parts). -/
private def preludeProgram (runtime : Laurel.LaurelProgram) : IO Core.Program := do
  let (coreOption, _) ← StrataPython.translateCombinedLaurel runtime
  match coreOption with
  | some prog => return prog
  | none => return { decls := [] }

private def verifyPrelude (runtime : Laurel.LaurelProgram) : IO (Array Message) := do
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

private def isOpaqueWithBody (p : Laurel.Procedure) : Bool :=
  match p.body with
  | .Opaque _ (some _) _ => true
  | _ => false

/-- An `.Opaque` procedure without an implementation, an `.Abstract` one and an `.External` one
    have no body to verify. -/
private def hasBody (p : Laurel.Procedure) : Bool :=
  match p.body with
  | .Opaque _ (some _) _ => true
  | .Opaque _ none _ | .Abstract _ | .External => false
  | _ => true

/-- The opaque procedures with a body of the prelude `runtime`, translated to Core together with
    the prelude declarations they depend on (`Laurel.filterPrelude`, as a user run gets the
    prelude); the number of opaque bodies; and the names of the procedures to verify: the opaque
    bodies and every procedure with a body that they depend on. Translating the whole prelude at
    once would need declarations that only a user's PySpec modules provide (`Core regex`), and
    translate to nothing. The check fails closed: a translation error, or a program without the
    opaque bodies, throws. -/
private def opaqueBodiesProgram (runtime : Laurel.LaurelProgram) :
    IO (Core.Program × Nat × List String) := do
  let (bodies, rest) := runtime.staticProcedures.partition isOpaqueWithBody
  if bodies.isEmpty then throw (IO.userError "the prelude has no opaque body to check")
  let user : Laurel.LaurelProgram := { staticProcedures := bodies, staticFields := [], types := [] }
  let deps ← IO.ofExcept (Laurel.filterPrelude { runtime with staticProcedures := rest } user)
  let (coreOption, errors) ← StrataPython.translateCombinedLaurel
    (StrataPython.combinePySpecLaurel deps user)
  let some prog := coreOption
    | throw (IO.userError s!"the opaque prelude bodies do not translate: {errors.map toString}")
  unless errors.isEmpty do
    throw (IO.userError s!"translating the opaque prelude bodies reports: {errors.map toString}")
  let coreNames : List String := prog.decls.filterMap fun d =>
    d.getProc?.map (Core.CoreIdent.toPretty ·.header.name)
  let missing := bodies.filter fun b => !coreNames.contains b.name.text
  unless missing.isEmpty do
    throw (IO.userError s!"opaque prelude bodies missing after translation: {missing.map (·.name.text)}")
  let names := ((bodies ++ deps.staticProcedures.filter hasBody).map (·.name.text)).filter
    coreNames.contains
  return (prog, bodies.length, names)

/-- The checks of the opaque bodies of the prelude `runtime` that are not proved: in deductive
    mode those that are not `isSuccess`, in bug-finding mode those that are not
    `isBugFindingSuccess`, each as its procedure-qualified label. -/
private def unprovedOpaqueBodyChecks (runtime : Laurel.LaurelProgram) (bugFinding : Bool) :
    IO (List String) := do
  let (prog, _, names) ← opaqueBodiesProgram runtime
  let base : Core.VerifyOptions := if bugFinding then
      { Core.VerifyOptions.quiet with checkMode := .bugFinding, checkLevel := .full }
    else .quiet
  let options := { base with proceduresToVerify := some names }
  IO.FS.withTempDir fun tempDir => do
    let rs ← EIO.toIO (IO.Error.userError ∘ toString)
      (_root_.Core.verify prog tempDir (options := options)
        (moreFns := StrataPython.RuntimeFactory)
        (externalPhases := [Strata.frontEndPhase]))
    let proved (r : Core.VCResult) : Bool :=
      if bugFinding then r.isBugFindingSuccess else r.isSuccess
    return (rs.filter (!proved ·)).toList.map fun r =>
      r.obligation.metadata.getPropertySummary.getD r.obligation.label

/-! Every check of every opaque prelude body is proved, in both modes. The counts show that the
check is not vacuous. The prelude declarations the opaque bodies depend on with a body of their
own are transparent functions today (`to_string_any`), which translate to Core functions rather
than procedures, so the procedures verified are the four opaque bodies. -/
/-- info: opaque bodies checked: 4, procedures verified: 4
deductive: []
bug-finding: [] -/
#guard_msgs in
#eval do
  let runtime := StrataPython.combinePySpecLaurel pythonRuntimeLaurelPart pySpecRuntimeLaurelPart
  let (_, nBodies, names) ← opaqueBodiesProgram runtime
  IO.println s!"opaque bodies checked: {nBodies}, procedures verified: {names.length}"
  IO.println s!"deductive: {← unprovedOpaqueBodyChecks runtime false}"
  IO.println s!"bug-finding: {← unprovedOpaqueBodyChecks runtime true}"

/-! The check catches an opaque prelude body that breaks its contract: `brokenLib` promises
`r > 0` and returns `0`. A caller that relies on the contract, as `usesBrokenLib` does, is
proved, because a user run trusts the contract; the check of the body is what fails, in both
modes. It also catches a broken prelude procedure that only an opaque body depends on: the
plain `helperT`, called from the opaque `wrapLib`, is verified too, and its assertion fails. -/
private def brokenPreludeDDM :=
#strata
program Laurel;
procedure brokenLib() returns (r: int)
  opaque
  ensures r > 0 summary "brokenLib's postcondition"
{
  r := 0
};
procedure usesBrokenLib() returns (y: int)
  opaque
{
  y := brokenLib();
  assert y > 0
};
procedure helperT() returns (r: int)
{
  assert 1 == 2 summary "helperT's broken assertion";
  r := 1
};
procedure wrapLib() returns (r: int)
  opaque
  ensures r > 0
{
  r := helperT()
};
#end

private def brokenPrelude : Laurel.LaurelProgram :=
  match Laurel.TransM.run (.file "brokenPrelude") (Laurel.parseProgram brokenPreludeDDM)
      (synthesized := true) with
  | .ok p => p
  | .error _ => default

/-- info: deductive: [helperT's broken assertion, brokenLib's postcondition]
bug-finding: [helperT's broken assertion, brokenLib's postcondition] -/
#guard_msgs in
#eval do
  let runtime := StrataPython.combinePySpecLaurel pythonRuntimeLaurelPart brokenPrelude
  IO.println s!"deductive: {← unprovedOpaqueBodyChecks runtime false}"
  IO.println s!"bug-finding: {← unprovedOpaqueBodyChecks runtime true}"

end StrataPython.PreludeVerifyTest
end
