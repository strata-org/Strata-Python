/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env.Refine
-- For compiling the handles, as every module that builds environments does.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Type constructors

Dyn's types are type expressions, `TypeExpr e s` (`StrataDyn/Env.lean`): a type whose
names resolve in the environment `e`, over the type variables of the scope `s`.  A list of types
is a `TypeList e s`, which may also splice the scope's list variables.

This module defines `TypeCon ks`, a type constructor: a declared type, or an abbreviation, whose
parameters have the kinds `ks`, applied to type expressions to give a type expression.  The
`environment` command defines one for each type and abbreviation with parameters, under its own
name.  A type or abbreviation without parameters is defined as a type expression itself, and its
`TypeCon []` is `T.con`:

```lean
Base.Int : TypeExpr e s                              -- under [Base.env ≼ e]
Base.Int.con : TypeCon []                            -- its type constructor
Base.Except : TypeCon [.type, .type]
Base.Fn : TypeCon [.list, .type]                     -- a list parameter takes a list
(Base.Except Base.Int Base.Bool : TypeExpr e)        -- applied, under [Base.env ≼ e]
(Base.Fn [Base.Int, Base.Ref Base.Int] Base.Bool : TypeExpr e)
(Base.Fn (TypeList.var 0 h) Base.Bool : TypeExpr e #[.list])   -- a list variable
```

A type expression that names a declared type `T` exists in `e` only if `e` refines the
environment that declares `T`: each use of `T` requires `[T.env ≼ e]`, which instance search
proves from the `extends` chain.  So in a child environment a type can name both the child's
types and its parent's, and a child's type in its parent fails with
`failed to synthesize Hd.env ≼ Base.env`.

Lean takes `e` from the expected type: the builder's environment for an operand or a result,
the declared type of a definition, or, for an argument, the application it is passed to.
Without one, as in `let t := Base.Ref Base.Int`, Lean cannot choose `e`.

A list parameter takes a `List (TypeExpr e s)` or a `TypeList e s`, and the argument's type
chooses which; `TypeCon.ListArg` explains how, and what it costs.

Generic code takes type expressions:
`{e} [Base.env ≼ e] (t : TypeExpr e s) : TypeExpr e s := Base.Ref t`.

An applied type constructor is its type's `Internal.T.ty` by `rfl`, a list of type expressions
as the literal of its types, `TypeList.lit #[.ty t₁, …]`, and a `TypeList` as itself.
`Internal.T.ty` is what generated signatures and proofs are written with; users write type
constructors.  An abbreviation applies its body's type constructors, so it unifies with the
constructor its body applies, and an abbreviation that splices a list parameter among other
elements builds one literal from a list of type expressions, and appends a `TypeList`.

Lean elaborates a list literal of more than 32 elements as nested `let`s, at a cost superlinear
in its length.  For long type lists, build them as a list value, such as `List.replicate n
Base.Int`.

* `TypeCon ks`: a type constructor: its declaration, its environment and its application.
* `TypeCon.Fn e s ks`: the function a type constructor applies as.
* `TypeCon.ListArg`: the two forms of a list parameter's argument.
* `TypeCon.name`, `TypeCon.applyArgs?`: its name, and its type expression at arguments given
  as data.
-/

namespace Strata.Dyn

@[expose] public section

/-- Refinement composes. -/
theorem RefinedBy.trans {a b c : Env Unit} (h₁ : a ≼ b) (h₂ : b ≼ c) : a ≼ c :=
  ⟨Env.Le.trans h₁.le h₂.le⟩

/-- The form of a list parameter's argument.  A handle's list parameter accepts a plain
`List (TypeExpr e s)` or a `TypeList e s`, which can splice the scope's list variables.
`ListArg` names which one: `types` for a list, `list` for a `TypeList`.  Users never write it.

```lean
Base.Fn [Base.Int, Base.Bool] Base.Int                         -- a literal
Base.Fn (ks.map K.ty) Base.Int                                 -- a computed list
Base.Fn (TypeList.lit #[.splice 0 h, .ty Base.Int]) Base.Int   -- a `TypeList` with a splice
```

The parameter's type is `ListArg.Ty e s a`, for an implicit `a`.  Two unification hints, below
`ListArg.splice`, tell Lean that a plain list means `.types` and a `TypeList` means `.list`.
`Ty` is irreducible, so the unifier meets `ListArg.Ty e s ?a` as written, rather than a `match`
it cannot reduce, and the hints fire.  The `.types` hint also unifies a list literal's type
with `List (TypeExpr e s)`, which gives its elements the environment and scope of the
application: Lean elaborates the elements before it knows either.

Rough edges:

* A `TypeList` argument needs its constructor written in full, `TypeList.var 0 h` rather than
  `.var 0 h`: the expected type is `ListArg.Ty e s ?a`, so dot notation finds no namespace.
* A handle needs an expected environment, from the expected type or the application around it.
* A list literal of handles costs about 4% more to elaborate than at a parameter that takes
  only a `List (TypeExpr e s)`.

`HandleTest` fails if either hint stops firing. -/
inductive TypeCon.ListArg where
  | types
  | list

/-- The argument of a list parameter given as `a`, in `e` and scope `s`. -/
def TypeCon.ListArg.Ty (e : Env Unit) (s : Array Kind) : TypeCon.ListArg → Type
  | .types => List (TypeExpr e s)
  | .list => TypeList e s

/-- The argument, as a `TypeList`: a list of type expressions as the literal of its types, which
is the literal a generated signature writes, by `rfl`. -/
@[reducible] def TypeCon.ListArg.toTypeList {e : Env Unit} {s : Array Kind} :
    (a : TypeCon.ListArg) → a.Ty e s → TypeList e s
  | .types, l => .lit (List.map TypeList.Elem.ty l).toArray
  | .list, l => l

/-- The literal of `pre`, the argument's elements and `post`, as an abbreviation splices a
list parameter: for a list of type expressions, the literal of one list, which `rfl` sees. -/
@[reducible] def TypeCon.ListArg.splice {e : Env Unit} {s : Array Kind} :
    (a : TypeCon.ListArg) → List (TypeExpr e s) → a.Ty e s → List (TypeExpr e s) →
      TypeList e s
  | .types, pre, l, post =>
    .lit (List.map TypeList.Elem.ty (List.append (List.append pre l) post)).toArray
  | .list, pre, l, post =>
    TypeExpr.append (TypeExpr.append (TypeList.ofTypes pre.toArray) l)
      (TypeList.ofTypes post.toArray)

-- The two hints `TypeCon.ListArg` describes: a plain list means `.types`, a `TypeList`
-- means `.list`.  `Ty` is irreducible from here on, so that they fire.
unif_hint (e : Env Unit) (s : Array Kind) (a : TypeCon.ListArg) where
  a =?= TypeCon.ListArg.types
  ⊢ TypeCon.ListArg.Ty e s a =?= List (TypeExpr e s)

unif_hint (e : Env Unit) (s : Array Kind) (a : TypeCon.ListArg) where
  a =?= TypeCon.ListArg.list
  ⊢ TypeCon.ListArg.Ty e s a =?= TypeExpr e s .list

attribute [irreducible] TypeCon.ListArg.Ty

/-- A function taking one argument per kind of `ks`, a type expression for a type and, for a
list, a list of them or a `TypeList`, to a type expression, in `e` and scope `s`. -/
@[reducible] def TypeCon.Fn (e : Env Unit) (s : Array Kind) : List Kind → Type
  | [] => TypeExpr e s
  | .type :: ks => TypeExpr e s → TypeCon.Fn e s ks
  | .list :: ks => {a : TypeCon.ListArg} → a.Ty e s → TypeCon.Fn e s ks

/-- A declared type, or an abbreviation, whose parameters have the kinds `ks`. -/
structure TypeCon (ks : List Kind) where
  /-- Its declaration: its name, and each parameter's name, polarity and kind. -/
  decl : TypeDecl Unit
  /-- The declaration's kinds are `ks`. -/
  kinds : decl.params.toList.map (·.type.kind) = ks
  /-- The environment it is defined in: the one that declares it, or, for an abbreviation,
  the most refined environment that declares a name of its body. -/
  env : Env Unit
  /-- It, applied, in every refinement of `env`. -/
  apply : {e : Env Unit} → [env ≼ e] → {s : Array Kind} → TypeCon.Fn e s ks

instance {ks : List Kind} :
    CoeFun (TypeCon ks) (fun T => {e : Env Unit} → [T.env ≼ e] → {s : Array Kind} →
      TypeCon.Fn e s ks) :=
  ⟨TypeCon.apply⟩
attribute [coe] TypeCon.apply

set_option synthInstance.checkSynthOrder false in
instance {T : TypeCon []} {e : Env Unit} [T.env ≼ e] {s : Array Kind} :
    CoeDep (TypeCon []) T (TypeExpr e s) := ⟨T.apply⟩

set_option synthInstance.checkSynthOrder false in
instance {T : TypeCon []} {e : Env Unit} [T.env ≼ e] {s : Array Kind} :
    CoeDep (TypeCon []) T (TypeArg e s) := ⟨.ty T.apply⟩

/-- Type expressions, as a list. -/
@[coe, reducible] def TypeCon.toTypeList {e : Env Unit} {s : Array Kind} (l : List (TypeExpr e s)) :
    TypeList e s :=
  .ofTypes l.toArray

instance {e : Env Unit} {s : Array Kind} : Coe (List (TypeExpr e s)) (TypeList e s) :=
  ⟨TypeCon.toTypeList⟩

instance {e : Env Unit} {s : Array Kind} : Coe (List (TypeExpr e s)) (TypeArg e s) :=
  ⟨fun l => .list (TypeCon.toTypeList l)⟩

namespace TypeCon

/-- Its name. -/
@[reducible] def name {ks : List Kind} (T : TypeCon ks) : Name := T.decl.name

/-- An argument at `E`, as data: a type expression for a type, a list of them for a list. -/
inductive Arg (E : Env Unit) (s : Array Kind) where
  | ty (t : TypeExpr E s)
  | list (ts : List (TypeExpr E s))

/-- A function of type expressions applied to `args`, if they have its kinds. -/
def applyFn? {E : Env Unit} {s : Array Kind} :
    {ks : List Kind} → TypeCon.Fn E s ks → List (Arg E s) → Option (TypeExpr E s)
  | [], t, [] => some t
  | .type :: _, f, .ty t :: as => applyFn? (f t) as
  | .list :: _, f, .list ts :: as => applyFn? (f ts) as
  | _, _, _ => none

/-- `T` applied to `args` in `E`, if they have its kinds: its type expression, built from
data, the one `T` applied to them directly gives. -/
def applyArgs? {ks : List Kind} (T : TypeCon ks) (E : Env Unit) [T.env ≼ E] {s : Array Kind}
    (args : List (Arg E s)) : Option (TypeExpr E s) :=
  applyFn? (@T.apply E _ s) args

end TypeCon

end

end Strata.Dyn
