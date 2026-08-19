/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.Specs.Decls
public import StrataPython.Specs.Decorators

/-! # Native PySpec contract decorators

Recognizers for PySpec's unqualified contract decorators — `@requires`,
`@ensures`, `@admit`, `@modifies`, `@ghost` (per method) and `@invariant`
(per class) — built on the `Specs/Decorators.lean` framework. Each scheme
collects raw Python lambda bodies into a bundle; `Specs.lean` translates them
to `SpecExpr` via the same generic path used for `assert`. Two-state
`OLD(expr)` is an expression form accepted by post-state predicates
(`@ensures` and `@admit`), not a decorator-specific construct. -/

namespace StrataPython.Specs.Native

open StrataDDM (SourceRange)
open PySpecMClass (specError specWarning)
open Decorators (DecoratorForm DecoratorScheme expectLambda? warnUnknownBinders
  stringKeyword? exprKeyword? hasKeyword reportUnexpectedKeywords)

/-! ## Bundles produced by recognition -/

/-- A `@ghost(name="g", type=…, init=…)` declaration before its `type`/`init`
    expressions are resolved: the declared name, the raw (optional) Python type
    annotation and initializer expressions, and the decorator's source range. -/
public structure RawGhost where
  name : String
  type : Option (expr SourceRange) := none
  init : Option (expr SourceRange) := none
  loc : SourceRange
deriving Inhabited

/-- Native contract decorators recognized on a single function/method, with
    lambda bodies still as raw Python expressions (translated later, in the spec
    parser, under the assertion-building monad). -/
public structure MethodBundle where
  /-- `@requires` lambda bodies (preconditions). -/
  requires : Array (expr SourceRange) := #[]
  /-- `@ensures` lambda bodies (postconditions to verify against an
      implementation). -/
  ensures : Array (expr SourceRange) := #[]
  /-- `@admit` lambda bodies: postconditions the spec author explicitly
      acknowledges as unverified modeling assumptions. -/
  admitted : Array (expr SourceRange) := #[]
  /-- `@modifies` lambda bodies (frame targets — lvalue expressions). -/
  modifies : Array (expr SourceRange) := #[]
  /-- `@ghost(name="g", …)` declarations. -/
  ghosts : Array RawGhost := #[]
deriving Inhabited

/-! ## Recognition scheme -/

/-- Binder naming the procedure's return value inside an `@ensures` or `@admit`
    lambda. -/
public def resultBinder : String := "result"

/-- Recognize `@label(lambda <params>: <body>)`, warning about any keyword and any
    lambda binder outside `allowed`, then hand the body to `push`. Common shape of
    `@requires`/`@ensures`/`@modifies`. -/
private def absorbLambda {m : Type → Type} [Monad m] [PySpecMClass m]
    (label : String) (allowed : Array String) (form : DecoratorForm)
    (args : Array (expr SourceRange)) (bundle : MethodBundle)
    (push : expr SourceRange → MethodBundle) : m (Option MethodBundle) := do
  let some (body, binders) ← expectLambda? specError label form.loc args
    | return some bundle
  reportUnexpectedKeywords specError label #[] form.kwargs
  warnUnknownBinders form.loc binders allowed fun n =>
    s!"{label}: lambda parameter '{n}' is unbound at the use site"
  return some (push body)

/-- Read a required string-literal `name=` and check it against `existing`. Returns
    `none` (declining to add anything) on an absent name or a duplicate; the
    error, if any, is already reported. -/
private def uniqueName? {m : Type → Type} [Monad m] [PySpecMClass m]
    (label : String) (form : DecoratorForm) (existing : Array String)
    : m (Option String) := do
  let some name ← stringKeyword? label "name" form.kwargs
    -- `stringKeyword?` reports a non-string `name=`; only flag a truly absent one.
    | unless hasKeyword "name" form.kwargs do
        specError form.loc s!"{label} requires a name= keyword argument"
      return none
  if existing.contains name then
    specError form.loc s!"{label}: duplicate name=\"{name}\"; names must be unique"
    return none
  return some name

/-- The `DecoratorScheme` for native contract decorators on a function/method.
    `validParams` is the function's parameter list, used to flag lambda binders
    that bind nothing at the use site (a vacuous predicate).

    Only unqualified *call* decorators are considered; bare markers such as
    `@overload` are declined and left for the caller's overload handling. -/
public def methodScheme {m : Type → Type} [Monad m] [PySpecMClass m]
    (validParams : Array String) : DecoratorScheme m MethodBundle where
  init := {}
  absorb form bundle := do
    unless form.qualifier == none && form.isCall do return none
    let args := form.args.getD #[]
    match form.name with
    | "requires" =>
      absorbLambda "@requires" validParams form args bundle fun body =>
        { bundle with requires := bundle.requires.push body }
    | "ensures" =>
      absorbLambda "@ensures" (validParams.push resultBinder) form args bundle fun body =>
        { bundle with ensures := bundle.ensures.push body }
    | "admit" =>
      absorbLambda "@admit" (validParams.push resultBinder) form args bundle fun body =>
        { bundle with admitted := bundle.admitted.push body }
    | "modifies" =>
      absorbLambda "@modifies" validParams form args bundle fun body =>
        { bundle with modifies := bundle.modifies.push body }
    | "ghost" =>
      let type? ← exprKeyword? "@ghost" "type" form.kwargs
      let init? ← exprKeyword? "@ghost" "init" form.kwargs
      reportUnexpectedKeywords specError "@ghost" #["name", "type", "init"] form.kwargs
      unless args.isEmpty do
        specError form.loc "@ghost: takes no positional arguments (use name=, type=, init=)"
      let some name ← uniqueName? "@ghost" form (bundle.ghosts.map (·.name))
        | return some bundle
      return some { bundle with ghosts := bundle.ghosts.push { name, type := type?, init := init?, loc := form.loc } }
    | "snapshot" =>
      specError form.loc
        "@snapshot is no longer supported; use OLD(<expr>) inside an @ensures/@admit lambda instead"
      return some bundle
    | _ =>
      return none

/-- The sole binder permitted on an `@invariant` lambda. -/
public def selfBinder : String := "self"

/-- Native contract decorators recognized on a class (currently invariants),
    with predicate lambda bodies still as raw Python expressions. -/
public structure ClassBundle where
  /-- `@invariant(lambda self: pred)` lambda bodies. -/
  invariants : Array (expr SourceRange) := #[]
deriving Inhabited

/-- The `DecoratorScheme` for `@invariant(lambda self: …)` on a class. The lambda
    must take exactly one `self` binder. Declines anything else (e.g.
    `@exhaustive`) so the caller's existing handling applies. -/
public def classScheme {m : Type → Type} [Monad m] [PySpecMClass m]
    : DecoratorScheme m ClassBundle where
  init := {}
  absorb form bundle := do
    unless form.qualifier == none && form.isCall && form.name == "invariant" do
      return none
    let some (body, binders) ← expectLambda? specError "@invariant" form.loc (form.args.getD #[])
      | return some bundle
    reportUnexpectedKeywords specError "@invariant" #[] form.kwargs
    match binders with
    | #[b] =>
      if b == selfBinder then
        return some { bundle with invariants := bundle.invariants.push body }
      specWarning form.loc s!"@invariant: lambda binder must be '{selfBinder}', got '{b}'; invariant skipped"
      return some bundle
    | _ =>
      specWarning form.loc s!"@invariant: lambda must take exactly one '{selfBinder}' parameter; invariant skipped"
      return some bundle

end StrataPython.Specs.Native
