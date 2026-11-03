/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env.TypeExprElim

set_option autoImplicit false

/-!
# Independent denotation of Dyn types

Constructors receive interpreted arguments at their declared kinds. Variables are assigned
Lean types or lists of Lean types, and list literals splice list variables. The interpreter
does not refer to Core or translation; it is an instance of `TypeExpr.elim`, whose laws, in
`StrataDyn.Env.TypeExprElim`, let clients lift local interpretation laws without repeating
recursion over checked syntax.

The meanings of constructors are a parameter, `Constructors`, not yet the run-time semantics of
`StrataDyn/Exec`, whose model interprets tags and is indexed by the run token. Connecting the two
is a later step, and the function type `Fn` is handled there, since a Core representation of
closures belongs with the value lowering.
-/

namespace Strata.Dyn

public section

namespace TypeDenote

/-- Types mean Lean types; type lists mean lists of Lean types. -/
@[expose, reducible] def Value : Kind → Type 1
  | .type => Type
  | .list => List Type

/-- The contribution of a type or a type-list splice to a literal. -/
@[expose] def splice : ((k : Kind) × Value k) → List Type
  | ⟨.type, t⟩ => [t]
  | ⟨.list, ts⟩ => ts

/-- A semantic assignment to the variables of a Dyn scope. -/
abbrev Assignment (scope : Array Kind) :=
  (i : Nat) → (k : Kind) → scope[i]? = some k → Value k

/-- Meanings of resolved Dyn constructors, independent of any Core representation. -/
abbrev Constructors {α : Type} (env : Env α) :=
  {arity : Nat} → (r : TypeRef env arity) → TypeExpr.Arguments Value r.kinds → Type

/-- Interpret Dyn directly, including list literals and list-variable splicing. -/
@[expose] def denote {α : Type} {env : Env α} (constructors : Constructors env)
    {scope : Array Kind} (vars : Assignment scope) {k : Kind}
    (t : TypeExpr env scope k) : Value k :=
  t.elim vars constructors (fun es => es.toList.flatMap splice)

end TypeDenote
end
end Strata.Dyn
