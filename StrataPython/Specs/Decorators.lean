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
`@ensures`, `@overload`, …): `DecoratorScheme` provides composable recognizers
(`seq`/`run`). Depends only on `PySpecMClass` and the Python AST, not the spec
pipeline.
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

/-! ## Call-argument helpers -/

/-- Binder names of a lambda's argument list (positional-only, positional, and
    keyword-only). -/
public def lambdaBinderNames (lamArgs : arguments SourceRange) : Array String :=
  let .mk_arguments _ ⟨_, posonly⟩ ⟨_, pos⟩ _ ⟨_, kwonly⟩ _ _ _ := lamArgs
  (posonly ++ pos ++ kwonly).map fun a => let .mk_arg _ ⟨_, n⟩ _ _ := a; n

/-- Extract the lambda body and binder names from `args[0]`. Reports via `report`
    (severity chosen by the caller) and returns `none` when the argument is
    missing or not a lambda. -/
public def expectLambda? {m : Type → Type} [Monad m]
    (report : SourceRange → String → m Unit)
    (what : String) (loc : SourceRange) (args : Array (expr SourceRange))
    : m (Option (expr SourceRange × Array String)) := do
  if h : args.size ≥ 1 then
    match args[0] with
    | .Lambda _ lamArgs lamBody => return some (lamBody, lambdaBinderNames lamArgs)
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

/-! ## Composable recognizers -/

/-- A first-class decorator recognizer over an accumulator `σ`. A decline
    (`none`) is necessarily a no-op — the accumulator is untouched — since the
    form may be offered to another scheme; a successful absorb returns the
    updated accumulator and owns the form. -/
public structure DecoratorScheme (m : Type → Type) (σ : Type) where
  /-- The empty accumulator, before any decorator is seen. -/
  init : σ
  /-- Try to absorb one normalized form; `none` declines it. -/
  absorb : DecoratorForm → σ → m (Option σ)

/-- Compose two schemes: a form is offered to `a` first, then to `b` if `a`
    declines. -/
public def DecoratorScheme.seq {m : Type → Type} [Monad m] {σ₁ σ₂ : Type}
    (a : DecoratorScheme m σ₁) (b : DecoratorScheme m σ₂)
    : DecoratorScheme m (σ₁ × σ₂) where
  init := (a.init, b.init)
  absorb form := fun (s₁, s₂) => do
    match ← a.absorb form s₁ with
    | some s₁' => return some (s₁', s₂)
    | none => return (← b.absorb form s₂).map fun s₂' => (s₁, s₂')

/-- Fold a scheme over a decorator list; any form not absorbed (or not a
    recognized shape) is passed to `onUnknown`. -/
public def DecoratorScheme.run {m : Type → Type} [Monad m] {σ : Type}
    (scheme : DecoratorScheme m σ)
    (decorators : Array (expr SourceRange))
    (onUnknown : expr SourceRange → m Unit) : m σ :=
  decorators.foldlM (init := scheme.init) fun acc pyd =>
    match DecoratorForm.ofExpr? pyd with
    | none => do onUnknown pyd; return acc
    | some form => do
      match ← scheme.absorb form acc with
      | some acc' => return acc'
      | none => onUnknown pyd; return acc

end StrataPython.Specs.Decorators
