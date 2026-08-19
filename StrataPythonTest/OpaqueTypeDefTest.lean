/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PythonToLaurel
meta import all StrataPython.FineGrainLaurel.Elaborate

meta section

/-! # Laurel's opaque types, as seen by the Python frontend

Laurel's `TypeDefinition` has an `Opaque` case (`opaque Set<T>` and friends), which the
frontend must classify rather than merely compile against. Two classifications matter and
neither is visible from a passing build:

* an opaque type IS a prelude *type name* — it must reach `PreludeInfo.types`, or `Set`
  silently drops out of the set the translator consults for known type names;
* an opaque type is NOT a constructor or a class — it must not reach `PreludeInfo`'s
  composite types, nor be registered as a callable in the elaborator's environment.

The subject is the real prelude, so these break if `CoreDefinitionsForLaurel` stops
declaring `Set` as well as if a classification arm regresses.

The `PySpecPipeline` type-name-collision loop's `.Opaque` arm is not pinned here: that loop
runs over every type in the program, so the prelude's `Set` traverses it on every Python spec
test. A *collision* on an opaque name is unreachable from Python, which cannot declare opaque
types — only the prelude can, and it declares `Set` once.
-/

namespace StrataPython.OpaqueTypeDef.Tests

open Strata.Laurel
open StrataPython
open StrataPython.ToLaurel
open Strata.FineGrainLaurel

/-- The prelude declares exactly one opaque type today; pin that so the expectations below
    cannot be satisfied vacuously by a prelude with no opaque types at all. -/
private def preludeOpaqueNames : List String :=
  coreDefinitionsForLaurel.types.filterMap fun td =>
    match td with
    | .Opaque ot => some ot.name.text
    | _ => none

private def prelude : PreludeInfo := PreludeInfo.ofLaurelProgram coreDefinitionsForLaurel

/-- The elaborator's environment must expose `Set`'s *operations* as callables while `Set`
    itself is not one. -/
private def elabEnv : ElabTypeEnv := buildElabEnvFromProgram coreDefinitionsForLaurel

/--
info: prelude opaque types: [Set]
Set in PreludeInfo.types: true
Set in PreludeInfo.compositeTypes: false
Set registered as an elaborator name: false
Set has class fields: false
setInsert registered as an elaborator name: true
-/
#guard_msgs in
#eval do
  IO.println s!"prelude opaque types: {preludeOpaqueNames}"
  IO.println s!"Set in PreludeInfo.types: {prelude.types.contains "Set"}"
  IO.println s!"Set in PreludeInfo.compositeTypes: {prelude.compositeTypes.contains "Set"}"
  IO.println s!"Set registered as an elaborator name: {elabEnv.names.contains "Set"}"
  IO.println s!"Set has class fields: {elabEnv.classFields.contains "Set"}"
  IO.println s!"setInsert registered as an elaborator name: {elabEnv.names.contains "setInsert"}"

end StrataPython.OpaqueTypeDef.Tests

end
