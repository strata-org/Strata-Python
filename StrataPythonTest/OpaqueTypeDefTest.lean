/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PythonToLaurel
meta import all StrataPython.FineGrainLaurel.Elaborate

meta section

/-! # Laurel's opaque types, as seen by the Python frontend

Laurel's `TypeDefinition` has an `Opaque` case (`opaque Set<T>`, `opaque Map<K, V>`), which
the frontend must classify rather than merely compile against. Two classifications matter and
neither is visible from a passing build:

* an opaque type IS a prelude *type name* — it must reach `PreludeInfo.types`, or `Set`/`Map`
  silently drop out of the set the translator consults for known type names;
* an opaque type is NOT a constructor or a class — it must not reach `PreludeInfo`'s
  composite types, nor be registered as a callable in the elaborator's environment.

The subject is the real prelude, so these break if `CoreDefinitionsForLaurel` stops
declaring these types as well as if a classification arm regresses.

`Map` is checked as the contrast: it is a type *alias* for `TotalMap K ($MapEntry V)`, not an
opaque sort, so it must not appear among the opaque names even though its operations are
callables like `Set`'s. `$MapEntry` — a real prelude datatype — must not be mistaken for an
opaque type either.

The `PySpecPipeline` type-name-collision loop's `.Opaque` arm is not pinned here: that loop
runs over every type in the program, so the prelude's opaque types traverse it on every
Python spec test. A *collision* on an opaque name is unreachable from Python, which cannot
declare opaque types — only the prelude can.
-/

namespace StrataPython.OpaqueTypeDef.Tests

open Strata.Laurel
open StrataPython
open StrataPython.ToLaurel
open Strata.FineGrainLaurel

/-- Pin the full list, so the expectations below cannot be satisfied vacuously by a prelude
    with no opaque types at all — and so adding one is a deliberate golden update. -/
private def preludeOpaqueNames : List String :=
  coreDefinitionsForLaurel.types.filterMap fun td =>
    match td with
    | .Opaque ot => some ot.name.text
    | _ => none

private def prelude : PreludeInfo := PreludeInfo.ofLaurelProgram coreDefinitionsForLaurel

/-- The elaborator's environment must expose the *operations* as callables while the opaque
    types themselves are not. -/
private def elabEnv : ElabTypeEnv := buildElabEnvFromProgram coreDefinitionsForLaurel

/--
info: prelude opaque types: [Set]
Set in PreludeInfo.types: true
Set in PreludeInfo.compositeTypes: false
Set registered as an elaborator name: false
Set has class fields: false
setInsert registered as an elaborator name: true
Map in PreludeInfo.types: true
Map in PreludeInfo.compositeTypes: false
Map registered as an elaborator name: false
Map has class fields: false
mapSet registered as an elaborator name: true
$MapEntry in PreludeInfo.types: true
$MapEntry is opaque: false
$MapPresent registered as an elaborator name: true
-/
#guard_msgs in
#eval do
  IO.println s!"prelude opaque types: {preludeOpaqueNames}"
  IO.println s!"Set in PreludeInfo.types: {prelude.types.contains "Set"}"
  IO.println s!"Set in PreludeInfo.compositeTypes: {prelude.compositeTypes.contains "Set"}"
  IO.println s!"Set registered as an elaborator name: {elabEnv.names.contains "Set"}"
  IO.println s!"Set has class fields: {elabEnv.classFields.contains "Set"}"
  IO.println s!"setInsert registered as an elaborator name: {elabEnv.names.contains "setInsert"}"
  IO.println s!"Map in PreludeInfo.types: {prelude.types.contains "Map"}"
  IO.println s!"Map in PreludeInfo.compositeTypes: {prelude.compositeTypes.contains "Map"}"
  IO.println s!"Map registered as an elaborator name: {elabEnv.names.contains "Map"}"
  IO.println s!"Map has class fields: {elabEnv.classFields.contains "Map"}"
  IO.println s!"mapSet registered as an elaborator name: {elabEnv.names.contains "mapSet"}"
  IO.println s!"$MapEntry in PreludeInfo.types: {prelude.types.contains "$MapEntry"}"
  IO.println s!"$MapEntry is opaque: {preludeOpaqueNames.contains "$MapEntry"}"
  IO.println s!"$MapPresent registered as an elaborator name: {elabEnv.names.contains "$MapPresent"}"

end StrataPython.OpaqueTypeDef.Tests

end
