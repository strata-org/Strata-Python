/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.DSL.Syntax
public import StrataMantle.DSL.Elab

/-!
# The `environment` command

Declares a Mantle environment, a few lines per declaration, and generates the `Env` value, its
references and the proofs that it is well formed.  A module that declares an environment
imports this one, `public import StrataMantle.Env.Handle` and `import StrataMantle.Env.WF`;
a module that only uses one imports neither this module nor `Env.WF`.

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
  one.  `(xs : list)` ranges over lists of types, and its argument is a literal `[τ, …]`:
  `type Fn (args : list) (+r)` and `Fn [Int, Bool] Int`.
* `data T (+a) where | c (x : τ) …`: a datatype.  Its parameters are a `type`'s, list
  parameters included: `data Closure (as : list) (+r) where | mk (f : Fn as r) (env : Value)`.
  A constructor takes only arguments, whose names may not reuse the datatype's parameters.
  Each field is one value: a spread `(*xs : as)` is not a field.
  `mutual … end` groups mutually recursive datatypes, and holds only `data`.
* `abbrev n (a (cs : list)) := τ`: a type abbreviation, expanded where it is used: a type
  parameter `a` and a list parameter `cs`, as an `insn` takes them.  Expanding splices a list
  argument where the body splices `cs`: `abbrev withInt ((cs : list) r) := Fn [*cs, Int] r`
  makes `withInt [Bool] Int` the type `Fn [Bool, Int] Int`.  It declares nothing in the
  environment.
* `insn o [a (cs : list)] binders : τ`: an instruction with type parameters `a`, which ranges
  over types, and `cs`, which ranges over lists of types, returning `τ`.  They share one scope,
  in the order written.  A list parameter is the argument of a list parameter, `Fn cs r`, or
  is spliced into a literal, at most one in each, anywhere: `Fn [*cs, Value] r`,
  `Fn [Int, *cs, Bool] r`.  `[*cs]` is `cs`.  Whether a type expression is a type or a list is its kind by
  `TypeExpr.Raw.kind`, once it is resolved.
* `terminal insn o [a b] binders`: an instruction that ends its block.  It has no result
  type, and neither has its signature.
* `def` is reserved for defined instructions, and rejected.

An `insn`'s binders come in order: arguments `(x y : τ)`, at most one variadic `(*xs : τ)`
(any number of operands of type `τ`) or `(*xs : cs)` (one operand per element of the list
`cs`, such as a list parameter or a literal), as the annotation's kind says, regions
`(&r (p : τ) : σ)` entered with `p` and left with a `σ`, then successors `(^k (y : τ))`.  A
successor's payload may spread a list too, `(^k (*ys : cs))`, one value per element of `cs`;
a region's parameters and a constructor's fields are one value each.
`(^k)` passes nothing, and `(&a &b …)` or `(^a ^b …)` declares several alike.  A successor's
payload names are documentation; only their types are kept.

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
* `nameSet : NameSet`, the same names as a literal 2-3 tree, with `nameSet_ordered` and
  `mem_nameSet : n ∈ env ↔ n ∈ nameSet`.  Each stage's freshness check adds that stage's
  names to the set before it, from the parent's `nameSet`, so the kernel adds each name once,
  in the stage that declares it.
* `toP`, the instance `P.env ⊑ e` (`Demo.toBase`).
* For a `type` or `data` `T` with `n` parameters: `T.name`, its environment name; `T.ref`, a
  `TypeRef e n`; and the `@[simp]` theorems `T.name_ref` and `T.decl_ref`, its name and
  declaration.  What its handle applies, `Internal.T.ty`, a `TypeExpr e s` taking `n`
  arguments, a `TypeList e s` for a list parameter and a `TypeExpr e s` for any other, and its
  raw form `Internal.T.toRaw_ty`, are public, since generated signatures, children and handles
  are written with them, but are not for users.  A child's proofs use the theorems for the
  types it inherits.
* For a `data` `T (a …)` with constructors `c₁ (x : τ) …`: the terminal instruction
  `T.case [a …] (scrutinee : T a …) (^c₁ (x : τ)) …`, environment name `T`'s followed by
  `case` (`demo.Box.case`), with one successor per constructor, in declaration order,
  receiving its fields.  It is an instruction like any other: `T.case.name`, `T.case.sig` and
  `T.case`.  `Env.addData` declares it with the group, after the group's constructors, and
  `T.case` is the reference `InsnRef.ofAddDataCase` gives.
* For a constructor `c` of `T`: `T.c.name`; `T.c.sig : InsnSig e`, with `T`'s parameters as
  type parameters, the fields as arguments and `T a …` as the result; and
  `T.c : InsnRef e T.c.sig`.
* Handles, after everything else (`StrataMantle.Env.Handle`), the one way to write a type: for
  a type `T` without parameters, `T : TypeExpr e s`, its type expression in every `e` that
  refines its environment, and `T.con : TypeCon []`, its declaration; for one whose parameters
  have kinds `ks`, `T : TypeCon ks`, which applies to type expressions, a `List (TypeExpr e s)`
  or a `TypeList e s` for a list parameter; for an `abbrev` `n`, the same, applying its body's
  handles.  So `Base.Except Base.Int Py.Value` is a `TypeExpr e` in every `e` that refines
  `Py.env`.
* For an `insn` `o`: `o.name`, `o.sig : InsnSig e` and `o : InsnRef e o.sig`.  A list
  parameter is a `TypeList.var` in `o.sig`, and a list-typed variadic a `Variadic.spread`.

A declaration's docstring goes on `T.ref` and `T`'s handle, `T.c`, `n`'s handle or `o`.  The
interface's own implicit binders are named `e`, the refinement, and `s`, the scope of
`Internal.T.ty`, so a caller can pin them: `(Demo.unbox.sig (e := Demo.env))`.  A parameter of
`Internal.T.ty` named `e` or `s` is renamed to a fresh name, primed past the other parameters
(`Base.Internal.Except.ty e' a`; `type T (e) (e')` gives `Internal.T.ty e'' e'`).  The
`RefinedBy` instance binder is anonymous.

The interface has the command's visibility.  Everything else, the stages that build `env`
and their lemmas, is `private`, in `E.Internal`, beside the public `Internal.T.ty` and
`Internal.T.toRaw_ty`.  In a public environment in a `module`:

* the names (`abbrev`s), `names`, `nameSet`, `Internal.T.ty`, `o.sig`, `T.c.sig`,
  `T.case.sig` and the handles are `@[expose]`, so `rfl`, `decide` and `decide +kernel`
  unfold them downstream, and `#v[…]` checks against `o.sig.typeArgc`;
* `env`, `T.ref`, `T.c`, `T.case`, `o` and the theorems are not.  `T.name_ref` and
  `T.decl_ref` stand in for unfolding `T.ref`.  A `decide +kernel` that evaluates `env`
  itself, such as `Func.WF`, needs `import all` of the declaring module and of Mantle's
  modules it reduces through.

The emitted proofs are by `decide`, `decide +kernel`, `simp`, lemma applications and
`mantle_kernel_rfl`, an `Eq.refl` that only the kernel checks, never `native_decide`, so the
kernel checks every environment.  A reference's cast to its interface signature is a term
with one lemma application per node of each type (`InsnSig.carry_eq_of_toRaw`), so a type
nested forty deep elaborates as a flat one does.

## Checks

The environment the command builds is well formed, in the sense of "What well-formedness
requires" in `Env/WF.lean`: every name is declared once, types are declared before they are
used, applications have their parameters' arity and kinds, binders have distinct names, and
datatypes recurse positively.  The command checks these conditions before it emits anything,
so that each mistake is reported at its syntax, with a message that names the declaration and
the parameter involved.  It reports every mistake in one pass, and emits nothing if there is
one.

A block also satisfies conditions of its own, which come from its syntax and from the Lean
names it generates:

* Lean names are distinct.  A declared name has one component.  No two declarations have one
  Lean name, and none takes a name another generates: a type `T` and an instruction `T` would
  both define `T.name`.  No declaration is named `env`, `names`, `mem_env`, `nameSet`,
  `nameSet_ordered`, `mem_nameSet`, `Internal` or `toP`, which the environment defines.  No
  constructor of `T` is named `ref`, `name`, `name_ref`, `decl_ref`, `case` or, if `T` has no
  parameters, `con`, which `T` defines, or as a field of `T`'s handle:
  `decl`, `kinds`, `env` or `apply`.  A new Lean name, with `as` to keep the environment name,
  resolves a clash.
* Names resolve.  Every name in a type resolves, by the rules above, to one type or
  abbreviation, every `open`ed namespace exists, and every `end` closes the innermost
  namespace, by name.  `mutual` holds only `data`.
* Types are written as Mantle represents them.  A type parameter takes no arguments.  A splice
  `*cs` occurs only inside a literal, and a literal holds at most one, so that matching an
  instruction's result type finds its type arguments (`OneSplice`, in
  `Env/TypeExprMatch.lean`).  An abbreviation's parameters have distinct names, and its body
  satisfies the conditions on type expressions, though it declares nothing.
* Binders fit their declaration.  An `insn`'s binders come in order: arguments, the variadic,
  regions, then successors.  It has at most one variadic, binding one name.  A spread in a
  successor's payload ranges over a list and binds one name, and the payload's names are
  distinct.  A constructor takes only arguments, and neither a field nor a region parameter
  is a spread.  An instruction has a result type exactly when it is not `terminal`.
* The block declares at least one type, datatype or instruction, and its module imports
  `StrataMantle.Env.Handle` publicly and `StrataMantle.Env.WF`.
* Lean names are free.  No Lean name the block generates, `E.env` and the environment's
  other names included, is already declared, publicly or privately.  The error is at the
  declaration that generates the name, and a child of the block reports that it failed.

If the generated code fails to elaborate anyway, that is an elaborator bug, reported as an
internal error at `environment`.

## Extending

`extends P` builds on `P.env`, which must be declared with `environment`.  `t ⊑ s`
(`RefinedBy`, scoped in `Strata.Mantle`) reads "`s` refines `t`" and carries a proof of
`t ≤ s`.  A child's stages extend its parent's environment, so the child proves
`P.env ≤ E.env` by `Env.le_of_subset`.  Each environment generates one upward rule, `toP`, so
under `[E.env ⊑ e]` every ancestor's references resolve: `Base.refNew : InsnRef e
Base.refNew.sig` in any refinement of `Demo`.  An environment has one parent.

A child reads its parent from the record every `environment` command leaves, which crosses
module boundaries, not by evaluating `P.env`; the record lists the names, which `mem_env`
spells out.  It also uses the parent's `names`, `mem_env`, `nameSet`, `nameSet_ordered` and
`mem_nameSet`, and its types' `ref`, `name`, `name_ref`, `decl_ref`, `Internal.T.ty` and
`Internal.T.toRaw_ty`, so the parent must be at least as visible as the child: a public child
cannot extend a private environment, and in a `module` its file `public import`s `P`'s module.
A private child needs only `import`.  Each mistake is reported at the `extends` argument.

## Modules

* `DSL/Syntax.lean`: the grammar.
* `DSL/Model.lean`: the record an environment leaves for its children.  A resolved type is a
  `TypeExpr.Raw`, of the core's kinds.
* `DSL/Check.lean`: collecting and resolving the block, and every check.
* `DSL/Elab.lean`: emitting the declarations, and the command.
-/
