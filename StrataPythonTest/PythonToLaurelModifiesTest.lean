/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PythonToLaurel

meta section

/-! # `translateFunction` modifies-group shapes

The two branches of `translateFunction` emit distinct load-bearing frames on
`Body.Opaque` and this distinction is only exercised incidentally end to end,
so both shapes are pinned here directly:

* **with a body** — one unguarded group whose sole target is the wildcard
  (`wildcardModifies`): the procedure may modify anything;
* **without a body** (hierarchy-class methods are translated this way) — one
  unguarded group with *empty* targets: the "nothing changes" frame. Zero
  groups would instead mean "unframed", so a mutation collapsing
  `[{ targets := [] }]` back to `[]` would silently unframe every bodiless
  procedure.
-/

namespace StrataPython.ToLaurel.Tests

open Strata
open Strata.Laurel
open StrataPython.ToLaurel

private def testDecl : PythonFunctionDecl :=
  { name := "f", args := [], kwargsName := none, ret := none }

private def isWildcardOnly (g : ModifiesGroup) : Bool :=
  match g.targets with
  | [t] => (t.val matches .All)
  | _ => false

private def describeGroup (g : ModifiesGroup) : String :=
  s!"unguarded: {g.guard.isNone}, " ++
    s!"empty targets: {g.targets.isEmpty}, wildcard-only: {isWildcardOnly g}"

private def describeGroups (body : Option (List (stmt SourceRange))) : String :=
  match translateFunction {} default testDecl body with
  | .error _ => "translation error"
  | .ok (proc, _) =>
    match proc.body with
    | .Opaque _ _ groups =>
      match groups with
      | [g] => s!"groups: 1, {describeGroup g}"
      | _ => s!"groups: {groups.length}"
    | _ => "unexpected body kind"

/--
info: with body: groups: 1, unguarded: true, empty targets: false, wildcard-only: true
no body: groups: 1, unguarded: true, empty targets: true, wildcard-only: false
-/
#guard_msgs in
#eval do
  IO.println s!"with body: {describeGroups (some [])}"
  IO.println s!"no body: {describeGroups none}"

end StrataPython.ToLaurel.Tests

end
