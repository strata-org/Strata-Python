/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DSL.Syntax
public import StrataMantle.DSL.Model
public import StrataMantle.DSL.Check
public import StrataMantle.DSL.Elab

/-!
# The `environment` command

Declares a Mantle environment, a few lines per declaration, and generates the `Env` value, its
references and the proofs that it is well formed.  A module that declares an environment
imports this one, `public import StrataMantle.Env` and `import StrataMantle.Env.WF`; a module
that only uses one imports neither this module nor `Env.WF`.

```lean
/-- A demo language. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- A demo value. -/
  type Value
  type Map (k) (+v)
  data Box (+a) where
    | /-- A full box. -/ box (contents : a)
    | empty
  mutual
    data Even where
      | zero
      | succE (pred : Odd)
    data Odd where
      | succO (pred : Even)
  end
  abbrev raising (a) := Except Value a
  insn add (lhs rhs : Value) (^err (exc : Value)) : Value
  insn not_ as "not" (operand : Value) : Value
  insn unbox [a] (b : Box a) : raising a
  insn mkTuple (*elems : Value) : Value
  insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  insn «try» [a] (&body : raising a) (&handler (exc : Value) : a) : a
  terminal insn br (cond : Bool) (^yes ^no)
  terminal insn raise (exc : Value) (^err (exc : Value))
  end demo
```

## Declarations

* `[public | private] environment E [extends P] where`: the environment `E.env`, in Lean
  namespace `E` under the current one.  Without a modifier it follows the scope, as a `def`
  does; outside a `module` it is public.
* `namespace n` … `end n`: the environment namespace of the declarations between; `end` names
  the namespace it closes, and one still open closes at the end of the block.  It does not
  enter Lean names: `demo.add` is `Demo.add`.
* `open n₁ n₂`: short names in these namespaces resolve, until the enclosing `end`.
* `type T (+a) (b)`: a primitive type.  `(+a)` is a positive parameter, `(b)` a non-positive
  one.
* `data T (+a) where | c (x : τ) …`: a datatype.  A constructor takes only arguments, whose
  names may not reuse the datatype's parameters.  `mutual … end` groups mutually recursive
  datatypes, and holds only `data`.
* `abbrev n (a b) := τ`: a type abbreviation, expanded where it is used.  It declares nothing
  in the environment.
* `insn o [a b] binders : τ`: an instruction with type parameters `a b`, returning `τ`.
* `terminal insn o [a b] binders`: an instruction that ends its block.  It has no result
  type, and neither has its signature.
* `def` is reserved for defined instructions, and rejected.

An `insn`'s binders come in order: arguments `(x y : τ)`, at most one variadic `(*xs : τ)`,
regions `(&r (p : τ) : σ)` entered with `p` and left with a `σ`, then successors
`(^k (y : τ))`.  `(^k)` passes nothing, and `(&a &b …)` or `(^a ^b …)` declares several
alike.  A successor's payload names are documentation; only their types are kept.

A declared name has one component.  `as "s"` gives the environment name when it differs from
the Lean name: `insn not_ as "not"` is `demo.not` and `Demo.not_`.  A Lean keyword in
guillemets stands for its string: `«then»` is the region `then`.  Every keyword but
`environment` is non-reserved, so `type`, `insn` and `terminal` stay usable as identifiers.

A name in a type is a type parameter; else, inside `namespace a.b`, `a.b.x`, `a.x` or `x`,
innermost first; else `o.x` for each `open o` in scope, where two matches are an error.  It
resolves to a type or abbreviation of this block, declared earlier or in the same group, or
of an ancestor.  Instructions cannot mention instructions.

## What it generates

In namespace `E`, every reference is generic over `{e} [env ⊑ e]`, so it holds in `E.env`
and in every refinement of it:

* `env : Env Unit`, carrying the command's docstring: `P.env` (or the empty environment) and
  every declaration of the block, in order.
* `names : List Name`, every environment name `env` declares, the parent's included, latest
  first.
* `@[simp] mem_env : n ∈ env ↔ n ∈ [ℓ₁, ℓ₂, …]`, the same names in the same order, each a
  `Name` literal such as `.str (.str .base "base") "Unit"`, so `simp` decides membership in
  `env` without unfolding anything.
* `toP`, the instance `P.env ⊑ e` (`Demo.toBase`).
* For a `type` or `data` `T` with `n` parameters: `T.name`, its environment name; `T.ref`, a
  `TypeRef e n`; `T.ty`, a `TypeExpr e s` taking `n` arguments; and the `@[simp]` theorems
  `T.name_ref` and `T.decl_ref`, its name and declaration, which a child's proofs use for
  the types it inherits.
* For a `data` `T (a …)` with constructors `c₁ (x : τ) …`: the terminal instruction
  `T.case [a …] (scrutinee : T a …) (^c₁ (x : τ)) …`, environment name `T`'s followed by
  `case` (`demo.Box.case`), with one successor per constructor, in declaration order,
  receiving its fields.  It is an instruction like any other: `T.case.name`, `T.case.sig` and
  `T.case`.  `Env.addData` declares it with the group, after the group's constructors, and
  `T.case` is the reference `InsnRef.ofAddDataCase` gives.
* For a constructor `c` of `T`: `T.c.name`; `T.c.sig : InsnSig e`, with `T`'s parameters as
  type parameters, the fields as arguments and `T a …` as the result; and
  `T.c : InsnRef e T.c.sig`.
* For an `abbrev` `n`: `n.ty`, taking its parameters.
* For an `insn` `o`: `o.name`, `o.sig : InsnSig e` and `o : InsnRef e o.sig`.

A declaration's docstring goes on `T.ref`, `T.c`, `n.ty` or `o`.  The interface's own
implicit binders are named `e`, the refinement, and `s`, the scope of `T.ty` and `n.ty`, so a
caller can pin them: `(Demo.unbox.sig (e := Demo.env))`.  A parameter of `T.ty` or `n.ty`
named `e` or `s` is renamed to a fresh name, primed past the other parameters
(`Base.Except.ty e' a`; `type T (e) (e')` gives `T.ty e'' e'`).  The `RefinedBy` instance
binder is anonymous.

The interface has the command's visibility.  Everything else, the stages that build `env`
and their lemmas, is `private`, in `E.Internal`.  In a public environment in a `module`:

* the names (`abbrev`s), `names`, `T.ty`, `n.ty`, `o.sig`, `T.c.sig` and `T.case.sig` are
  `@[expose]`, so `rfl`, `decide` and `decide +kernel` unfold them downstream, and `#v[…]`
  checks against `o.sig.typeArgc`;
* `env`, `T.ref`, `T.c`, `T.case`, `o` and the theorems are not.  `T.name_ref` and
  `T.decl_ref` stand in for unfolding `T.ref`.  A `decide +kernel` that evaluates `env`
  itself, such as `Func.WF`, needs `import all` of the declaring module and of Mantle's
  modules it reduces through.

The emitted proofs are by `decide`, `decide +kernel` and `simp`, never `native_decide`, so the
kernel checks every environment.

## Checks

Every mistake is reported at its syntax, all of them in one pass, and nothing is emitted if
there is one.  The checks:

* names: an environment name declared twice, here or in an ancestor; a dotted declared name;
  two declarations with one Lean name, or one taking a name another generates (a type `T`
  and an instruction `T` would both define `T.name`); the reserved Lean names `env`, `names`,
  `mem_env`, `Internal` and `toP`, and the constructor names `ref`, `ty`, `name`, `name_ref`,
  `decl_ref` and `case`; a case instruction's environment name declared otherwise; a
  constructor named as its datatype's parameter or `scrutinee`, which its case instruction
  binds.  A clash is fixed by a new Lean name and `as` for the old environment name.
* scope: an unknown or ambiguous type, an unknown `open`ed namespace, an unmatched `end`,
  anything but `data` in `mutual`;
* types: an arity mismatch, a type parameter applied to arguments, and positivity: a member
  of the group, or a `+` parameter, under a non-positive parameter;
* binders: a duplicate parameter name (type parameters, arguments, the variadic, regions and
  successors share one namespace), binders out of order, two variadics, a variadic binding
  several names, a constructor with anything but arguments, a terminal instruction with a
  result type or another without one;
* the block: no type, datatype or instruction; a missing `Env` or `Env.WF` import.

If the generated code fails to elaborate anyway, that is an elaborator bug, reported as an
internal error at `environment`.

## Extending

`extends P` builds on `P.env`, which must be declared with `environment`.  `t ⊑ s`
(`RefinedBy`, scoped in `Strata.Mantle`) reads "`s` refines `t`"; today it is `t ⊆ s`, a
prefix.  Each environment generates one upward rule, `toP`, so under `[E.env ⊑ e]` every
ancestor's references resolve: `Base.refNew : InsnRef e Base.refNew.sig` in any refinement
of `Demo`.  An environment has one parent.

A child reads its parent from the record every `environment` command leaves, which crosses
module boundaries, not by evaluating `P.env`; the record lists the names, which `mem_env`
spells out.  It also uses the parent's `names` and `mem_env`, and its types' `ref`, `ty`,
`name`, `name_ref` and `decl_ref`, so the parent must be at least as visible as the child: a
public child cannot extend a private environment, and in a `module` its file `public import`s
`P`'s module.  A private child needs only `import`.  Each mistake is reported at the `extends` argument.

## Modules

* `DSL/Syntax.lean`: the grammar.
* `DSL/Model.lean`: the record an environment leaves for its children.
* `DSL/Check.lean`: collecting and resolving the block, and every check.
* `DSL/Elab.lean`: emitting the declarations, and the command.
-/
