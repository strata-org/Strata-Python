/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.Specs.Diagnostics
public import StrataPython.ReadPython

/-!
# Decorator-recognition framework for PySpec

Generic gearing for recognizing PySpec decorator surfaces (`@requires`,
`@ensures`, `@overload`, …): `DecoratorScheme` provides a first-class recognizer
over an accumulator. Depends only on `PySpecMClass` and the Python AST, not the
spec pipeline.
-/

namespace StrataPython.Specs.Decorators

open StrataDDM (SourceRange)
open PySpecMClass (specError specWarning)

/-! ## Normalized decorator forms -/

/-- A decorator expression normalized across `@name`, `@mod.name`, `@name(...)`,
    and `@mod.name(...)`. -/
public structure DecoratorForm where
  /-- Qualifier of `@qualifier.name`; `none` for a bare `@name`. -/
  qualifier : Option String
  name : String
  /-- Positional call arguments; `none` for a bare `@name` (not applied as a
      call), `some` (possibly empty) for `@name(...)`. -/
  args : Option (Array (expr SourceRange)) := none
  kwargs : Array (keyword SourceRange) := #[]
  loc : SourceRange
deriving Inhabited

/-- `true` when this form is applied as a call (`@name(...)`). -/
public def DecoratorForm.isCall (f : DecoratorForm) : Bool :=
  f.args.isSome

/-- Normalize a decorator expression, or `none` if it is not a recognized shape. -/
public def DecoratorForm.ofExpr? (pyd : expr SourceRange) : Option DecoratorForm :=
  match pyd with
  | .Name loc ⟨_, name⟩ (.Load _) =>
    some { qualifier := none, name, loc }
  | .Attribute loc (.Name _ ⟨_, qual⟩ (.Load _)) ⟨_, attr⟩ (.Load _) =>
    some { qualifier := some qual, name := attr, loc }
  | .Call loc (.Name _ ⟨_, name⟩ (.Load _)) ⟨_, args⟩ ⟨_, kwargs⟩ =>
    some { qualifier := none, name, args := some args, kwargs, loc }
  | .Call loc (.Attribute _ (.Name _ ⟨_, qual⟩ (.Load _)) ⟨_, attr⟩ (.Load _))
      ⟨_, args⟩ ⟨_, kwargs⟩ =>
    some { qualifier := some qual, name := attr, args := some args, kwargs, loc }
  | _ => none

/-- `true` when this form is `@qualifier.name` (call or bare). -/
public def DecoratorForm.isQualifiedBy (f : DecoratorForm) (qualifier : String) : Bool :=
  f.qualifier == some qualifier

/-- The decorator's source name for diagnostics: `qualifier.name` or `name`. -/
public def DecoratorForm.display (f : DecoratorForm) : String :=
  match f.qualifier with
  | some q => s!"{q}.{f.name}"
  | none => f.name

/-! ## Call-argument helpers -/

/-- Binder names of a lambda's argument list (positional-only, positional, and
    keyword-only). -/
public def lambdaBinderNames (lamArgs : arguments SourceRange) : Array String :=
  let .mk_arguments _ ⟨_, posonly⟩ ⟨_, pos⟩ _ ⟨_, kwonly⟩ _ _ _ := lamArgs
  (posonly ++ pos ++ kwonly).map fun a => let .mk_arg _ ⟨_, n⟩ _ _ := a; n

/-- All parameter names of a function's argument list, including the `*args`
    (vararg) and `**kwargs` (kwarg) names. Used to compute the set of valid
    contract-lambda binders, so a binder matching the function's `**kwargs`
    parameter is not flagged as unbound. -/
public def functionParamNames (a : arguments SourceRange) : Array String :=
  let .mk_arguments _ ⟨_, posonly⟩ ⟨_, pos⟩ ⟨_, vararg⟩ ⟨_, kwonly⟩ _ ⟨_, kwarg⟩ _ := a
  let names := (posonly ++ pos ++ kwonly).map fun arg => let .mk_arg _ ⟨_, n⟩ _ _ := arg; n
  let names := match vararg with
    | some (.mk_arg _ ⟨_, n⟩ _ _) => names.push n
    | none => names
  match kwarg with
    | some (.mk_arg _ ⟨_, n⟩ _ _) => names.push n
    | none => names

/-- Extract the lambda body and binder names from `args[0]`. Reports via `report`
    (severity chosen by the caller) and returns `none` when the argument is
    missing or not a lambda. Warns (but still succeeds) when there are extra
    positional arguments after the lambda. -/
public def expectLambda? {m : Type → Type} [Monad m] [PySpecMClass m]
    (report : SourceRange → String → m Unit)
    (what : String) (loc : SourceRange) (args : Array (expr SourceRange))
    : m (Option (expr SourceRange × Array String)) := do
  if h : args.size ≥ 1 then
    match args[0] with
    | .Lambda _ lamArgs lamBody =>
      if args.size > 1 then
        specWarning loc s!"{what} ignores extra positional arguments after the lambda"
      return some (lamBody, lambdaBinderNames lamArgs)
    | _ => report loc s!"{what} expects a lambda as its first argument"; return none
  else
    report loc s!"{what} requires at least one argument"
    return none

/-- Warn about each lambda binder not in `allowed`; nothing binds it at the use
    site, so the predicate is vacuous. -/
public def warnUnknownBinders {m : Type → Type} [Monad m] [PySpecMClass m]
    (loc : SourceRange) (binders allowed : Array String)
    (describe : String → String) : m Unit := do
  for n in binders do
    unless allowed.contains n do specWarning loc (describe n)

/-- Read a required string-literal keyword `name=...` from a call's keywords,
    erroring on a duplicate or non-string value; `none` if absent. -/
public def stringKeyword? {m : Type → Type} [Monad m] [PySpecMClass m]
    (what : String) (key : String) (kwargs : Array (keyword SourceRange))
    : m (Option String) := do
  let mut value : Option String := none
  let mut seen := false
  for kw in kwargs do
    if let ⟨_, some ⟨_, k⟩⟩ := kw.arg then
      if k == key then
        if seen then
          specError kw.value.ann s!"{what}: duplicate {key}= keyword"
        seen := true
        match kw.value with
        | .Constant _ (.ConString _ ⟨_, s⟩) _ => if value.isNone then value := some s
        | _ => specError kw.value.ann s!"{what}: {key}= must be a string literal"
  return value

/-- Read an optional keyword `key=<expr>` whose value may be any expression (used
    for `@ghost(type=…, init=…)`, whose values are resolved later). Reports a
    duplicate via a `what`-prefixed error; returns `none` when the keyword is
    absent. -/
public def exprKeyword? {m : Type → Type} [Monad m] [PySpecMClass m]
    (what : String) (key : String) (kwargs : Array (keyword SourceRange))
    : m (Option (expr SourceRange)) := do
  let mut value : Option (expr SourceRange) := none
  for kw in kwargs do
    if let ⟨_, some ⟨_, k⟩⟩ := kw.arg then
      if k == key then
        if value.isSome then
          specError kw.value.ann s!"{what}: duplicate {key}= keyword"
        if value.isNone then value := some kw.value
  return value

/-- True when a keyword argument named `key` is present (regardless of its
    value). Used to distinguish an absent keyword from one present with an
    invalid value, so the two cases are not double-reported. -/
public def hasKeyword (key : String) (kwargs : Array (keyword SourceRange)) : Bool :=
  kwargs.any fun kw =>
    match kw.arg with
    | ⟨_, some ⟨_, k⟩⟩ => k == key
    | _ => false

/-- Report (via `report`, at a caller-chosen severity) each keyword whose name is
    not in `allowed`. -/
public def reportUnexpectedKeywords {m : Type → Type} [Monad m]
    (report : SourceRange → String → m Unit)
    (what : String) (allowed : Array String) (kwargs : Array (keyword SourceRange))
    : m Unit := do
  for kw in kwargs do
    if let ⟨_, some ⟨_, k⟩⟩ := kw.arg then
      unless allowed.contains k do
        report kw.value.ann s!"{what}: unexpected keyword '{k}'"

/-! ## Recognizer -/

/-- A first-class decorator recognizer over an accumulator `σ`. A decline
    (`none`) is necessarily a no-op — the accumulator is untouched — since the
    form may be offered to another scheme; a successful absorb returns the
    updated accumulator and owns the form. -/
public structure DecoratorScheme (m : Type → Type) (σ : Type) where
  /-- The empty accumulator, before any decorator is seen. -/
  init : σ
  /-- Try to absorb one normalized form; `none` declines it. -/
  absorb : DecoratorForm → σ → m (Option σ)

end StrataPython.Specs.Decorators
