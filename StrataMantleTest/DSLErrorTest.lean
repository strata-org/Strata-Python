/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantleTest.DSLTest
import StrataMantle.Env.WF
import StrataMantle.DSL

set_option autoImplicit false

/-!
# The `environment` command: across modules, and its errors

`Base` comes from `Mantle/Base.lean` and `Demo` from `DSLTest`, so the first block checks
that a parent's record crosses module boundaries.  Each error test then shows one check's
message, at its syntax.  Nothing is emitted for a block with an error.
-/

namespace Strata.Mantle.DSLErrorTest

open Strata.Mantle.DSLTest

/-! ## A grandchild, in another module -/

/-- A third level: a datatype whose payloads are an ancestor's types. -/
public environment Grand extends Demo where
  namespace grand
  open base demo
  data Cell where
    | cell (ref : Ref Value) (box : Box Int)
  insn peek (c : Cell) : raising Value

example : base ⊑ Grand.env := inferInstance
example : Demo.env ⊑ Grand.env := inferInstance
example : TypeRef Grand.env 1 := Demo.Box.ref
example : InsnRef Grand.env Base.refNew.sig := Base.refNew
example : (Grand.peek.sig (e := Grand.env)).typeArgc = 0 := rfl
example : Vector (TypeExpr Grand.env) (Demo.unbox.sig (e := Grand.env)).typeArgc :=
  #v[Grand.Cell.ty]

/-! ## A grandchild's names

`Demo` is a child of `Base`, so a child of `Demo` starts its freshness checks from
`Demo.nameSet`, which holds `Base`'s names too.  `Twin` declares one fresh type; `ErrTwin`,
the same block in `Base`'s namespace, names a type of its grandparent. -/

/-- A grandchild of `Base` with one type. -/
public environment Twin extends Demo where
  namespace twin
  type Int

/-- `Twin`'s set is its parent's with `Twin`'s one name added, which was not there. -/
example : Demo.nameSet.insertAll? #[Twin.Int.name] = some Twin.nameSet := by mantle_kernel_rfl

-- It holds its own name and its grandparent's.
#guard Twin.nameSet.contains Twin.Int.name &&
  Twin.nameSet.contains (.str (.str .base "base") "Int")

/-- error: `base.Int` is already declared
-/
#guard_msgs in
public environment ErrTwin extends Demo where
  namespace base
  type Int

/-! ## What crosses the module boundary

The interface does; the stages are private to `DSLTest`. -/

example : (Demo.unbox.sig (e := Demo.env)).typeArgc = 1 := rfl
example : Vector (TypeExpr Demo.env) (Base.refNew.sig (e := Demo.env)).typeArgc :=
  #v[Demo.Value.ty]

/-- error: Unknown identifier `Demo.Internal.s1` -/
#guard_msgs in
example := Demo.Internal.s1

/-- error: Unknown identifier `Demo.Internal.add.sig₀` -/
#guard_msgs in
example := Demo.Internal.add.sig₀

/-- error: Unknown identifier `Demo.Internal.Value.ref₀` -/
#guard_msgs in
example := Demo.Internal.Value.ref₀

/-- error: Unknown identifier `Demo.Internal.hsub0` -/
#guard_msgs in
example := Demo.Internal.hsub0

/-! ## Errors -/

/-- error: `base.Int` is already declared
-/
#guard_msgs in
public environment ErrDup extends Base where
  namespace base
  type Int

/-- error: `ErrLean.A` is already generated for `x.A`; rename one with `as`
-/
#guard_msgs in
public environment ErrLean extends Base where
  namespace x
  type A
  insn A as "a" (y : A) : A

/-- error: unknown type `Valu`
---
error: unknown type `Valu`
-/
#guard_msgs in
public environment ErrUnknown extends Base where
  namespace x
  insn f (y : Valu) : Valu

/-- error: `Ref` is ambiguous: `base.Ref`, `x.Ref`
-/
#guard_msgs in
public environment ErrAmb extends Base where
  namespace x
  type Ref (+a)
  end x
  namespace y
  open base x
  insn f (r : Ref Int) : Int

/-- error: unknown namespace `bse`
-/
#guard_msgs in
public environment ErrNs extends Base where
  open bse
  type A

/-- error: `end y` closes namespace `x`
-/
#guard_msgs in
public environment ErrEnd extends Base where
  namespace x
  type A
  end y

/-- error: only `data` may appear in `mutual`
-/
#guard_msgs in
public environment ErrMutual extends Base where
  mutual
    type A
    data B where
      | b
  end

/-- error: type `Except` expects 2 arguments, got 1
-/
#guard_msgs in
public environment ErrArity extends Base where
  open base
  insn f (x : Except Int) : Int

/-- error: type parameter `a` takes no arguments
-/
#guard_msgs in
public environment ErrTyParam extends Base where
  open base
  insn f [a] (x : a Int) : Int

/-- error: duplicate parameter `a`
---
error: duplicate parameter `x`
-/
#guard_msgs in
public environment ErrDupParam extends Base where
  open base
  insn f [a] (a : Int) (x x : Int) : Int

-- The variadic shares the namespace of the type parameters, arguments, regions and
-- successors.
/-- error: duplicate parameter `a`
---
error: duplicate parameter `x`
---
error: duplicate parameter `xs`
---
error: duplicate parameter `xs`
-/
#guard_msgs in
public environment ErrDupVariadic extends Base where
  open base
  insn f [a] (*a : Int) : Int
  insn g (x : Int) (*x : Int) : Int
  insn h (*xs : Int) (&xs : Int) : Int
  insn i (*xs : Int) (^xs) : Int

-- A datatype's parameters are named distinctly, and a constructor's fields may not reuse
-- them: its instruction binds both.
/-- error: duplicate parameter `a`
---
error: duplicate parameter `b`
-/
#guard_msgs in
public environment ErrDupDataParam extends Base where
  data Pair (+a) (+a) where
    | pair
  data Box (+b) where
    | box (b : b)

/-- error: arguments must come before the variadic, the regions and the successors
---
error: arguments must come before the variadic, the regions and the successors
---
error: the variadic must come before the regions and the successors
---
error: at most one variadic
---
error: a variadic binds one name
-/
#guard_msgs in
public environment ErrOrder extends Base where
  open base
  insn f (*xs : Int) (y : Int) : Int
  insn g (&r : Int) (y : Int) : Int
  insn h (&r : Int) (*xs : Int) : Int
  insn i (*xs : Int) (*ys : Int) : Int
  insn j (*xs ys : Int) : Int

/-- error: arguments must come before the variadic, the regions and the successors
---
error: the variadic must come before the regions and the successors
---
error: regions must come before the successors
---
error: duplicate parameter `k`
---
error: duplicate parameter `x`
-/
#guard_msgs in
public environment ErrSuccOrder extends Base where
  open base
  insn f (^k) (y : Int) : Int
  insn g (^k) (*xs : Int) : Int
  terminal insn h (^k (x : Int)) (&r : Int)
  insn i (^k ^k) : Int
  insn j (x : Int) (^x) : Int

/-- error: unknown type `Valu`
-/
#guard_msgs in
public environment ErrSuccTy extends Base where
  insn f (^k (x : Valu)) : base.Int

/-- error: `Expr` recurses through non-positive parameter 1 of `Map`
---
error: positive parameter `a` occurs under non-positive parameter 1 of `Map`
-/
#guard_msgs in
public environment ErrPos extends Base where
  open base
  type Map (k) (+v)
  data Expr where
    | leaf
    | node (kids : Map Expr Int)
  data Wrap (+a) where
    | wrap (m : Map a Int)

/-- error: argument 1 of `F` is a type, but its parameter takes a list of types
---
error: argument 2 of `F` is a list of types, but its parameter takes a type
---
error: a list of types may not hold a list
---
error: a list of types may not hold a list
---
error: a list of types where a type is expected
-/
#guard_msgs in
public environment ErrKind extends Base where
  open base
  type F (args : list) (+r)
  insn f (x : F Int Int) : Int
  insn g (x : F [Int] [Int]) : Int
  insn h (x : F [[Int]] Int) : Int
  insn j (x : F [([Int])] Int) : Int
  insn i (x : [Int]) : Int

/-- error: list parameter `cs` where a type is expected; splice it into a list with `*cs`
---
error: argument 1 of `F` is a type, but its parameter takes a list of types
---
error: a splice `*cs` is allowed only inside `[…]`
---
error: `a` is not a list parameter: only a list parameter may be spliced
---
error: a list may splice at most one list parameter
-/
#guard_msgs in
public environment ErrListParam extends Base where
  open base
  type F (args : list) (+r)
  insn asType [(cs : list)] (x : cs) : Int
  insn typeAsList [a] (f : F a Int) : Int
  insn bareSplice [(cs : list)] (x : *cs) : Int
  insn spliceType [a] (f : F [*a] Int) : Int
  insn twoSplices [(cs ds : list)] (f : F [*cs, *ds] Int) : Int

/-- The same instructions, each with its mistake fixed, are accepted. -/
public environment OkListParam extends Base where
  open base
  type F (args : list) (+r)
  insn asType [(cs : list)] (x : F cs Int) : Int
  insn typeAsList [a] (f : F [a] Int) : Int
  insn bareSplice [(cs : list)] (x : F [*cs] Int) : Int
  insn spliceType [(a : list)] (f : F [*a] Int) : Int
  insn twoSplices [(cs ds : list)] (f : F [*cs, Int] Int) (g : F [Int, *ds] Int) : Int

/-- error: a list of types where a type is expected -/
#guard_msgs in
public environment ErrSplicedAsType extends Base where
  open base
  type F (args : list) (+r)
  insn asType [(cs : list)] (x : [*cs]) : Int

/-- The same instruction, with the list passed to a type, is accepted. -/
public environment OkSplicedAsType extends Base where
  open base
  type F (args : list) (+r)
  insn asType [(cs : list)] (x : F [*cs] Int) : Int

/-- error: a splice `*cs` is allowed only inside `[…]`
---
error: a list of types may not hold a list
---
error: `a` is not a list parameter: only a list parameter may be spliced
---
error: list parameter `cs` where a type is expected; splice it into a list with `*cs`
-/
#guard_msgs in
public environment ErrVariadic extends Base where
  open base
  insn bareSplice [(cs : list)] (*xs : *cs) : Int
  insn nested (*xs : [[Int]]) : Int
  insn spliceType [a] (*xs : [*a]) : Int
  insn unspliced [(cs : list)] (*xs : [cs, Int]) : Int

/-- The same variadics, each with its mistake fixed, are accepted: each annotation is a list,
so each variadic is a spread. -/
public environment OkVariadic extends Base where
  open base
  insn bareSplice [(cs : list)] (*xs : [*cs]) : Int
  insn nested (*xs : [Int]) : Int
  insn spliceType [(a : list)] (*xs : [*a]) : Int
  insn unspliced [(cs : list)] (*xs : [*cs, Int]) : Int

/-- error: a constructor takes no spread `(*xs : τ)`: each field is one value
---
error: list parameter `as` where a type is expected; splice it into a list with `*as`
---
error: a region parameter cannot be a spread `(*xs : τ)`: each is one value
---
error: a spread `(*xs : τ)` in a successor's payload takes a list of types: one value per element
-/
#guard_msgs in
public environment ErrListSpread extends Base where
  open base
  type F (args : list) (+r)
  data D (as : list) where
    | spread (*xs : as)
    | whole (x : as)
  insn lambda [(as : list) r] (&body (*ps : as) : r) : F as r
  terminal insn untuple [t] (^k (*xs : t))

/-- The same declarations, each field and region parameter taking one value, and the spread
over a list, are accepted: a spread belongs in an instruction's variadic or a successor's
payload. -/
public environment OkListSpread extends Base where
  open base
  type F (args : list) (+r)
  data D (as : list) where
    | spread (x : F as Int)
    | whole (x : F as Int)
  insn lambda [(as : list) r] (&body (p : F as r) : r) : F as r
  terminal insn untuple [(t : list)] (^k (*xs : t))
  insn apply [(as : list) r] (f : F as r) (*xs : as) : r

/-- error: positive parameter `as` occurs under non-positive parameter 1 of `F`
---
error: positive parameter `as` occurs under non-positive parameter 1 of `F`
---
error: argument 1 of `D` is a type, but its parameter takes a list of types
-/
#guard_msgs in
public environment ErrListData extends Base where
  open base
  type F (args : list) (+r)
  data P (+as : list) where
    | mkP (f : F as Int)
  data Q (+as : list) where
    | mkQ (f : F [*as, Int] Int)
  data D (as : list) where
    | mkD (f : F as Int)
  insn useD (d : D Int) : Int

/-- The same datatypes, each with its mistake fixed, are accepted. -/
public environment OkListData extends Base where
  open base
  type F (args : list) (+r)
  data P (as : list) where
    | mkP (f : F as Int)
  data Q (as : list) where
    | mkQ (f : F [*as, Int] Int)
  data D (as : list) where
    | mkD (f : F as Int)
  insn useD (d : D [Int]) : Int

/-- error: `Bad` recurses through non-positive parameter 1 of `F`
---
error: positive parameter `a` occurs under non-positive parameter 1 of `F`
-/
#guard_msgs in
public environment ErrListPos extends Base where
  open base
  type F (args : list) (+r)
  data Bad where
    | mk (f : F [Bad] Int)
  data U (+a) where
    | mkU (f : F [a] Int)

/-- Through a `+` list, a datatype may recurse; and `U` is accepted once `a` is declared
non-positive. -/
public environment OkListPos extends Base where
  open base
  type F (args : list) (+r)
  type Tup (+ts : list)
  data T where
    | mk (t : Tup [T])
  data U (a) where
    | mkU (f : F [a] Int)

/-- error: argument 1 of `Fn` is a type, but its parameter takes a list of types
-/
#guard_msgs in
public environment ErrNestedKind extends DSLTest.Fns where
  open fns base
  insn d (f : Fn [Fn [Fn Int Int] Int] Int) : Int

/-- The same instruction, the innermost `Fn` given a list, is accepted: an inherited type nests
in its own argument. -/
public environment OkNestedKind extends DSLTest.Fns where
  open fns base
  insn d (f : Fn [Fn [Fn [Int] Int] Int] Int) : Int

/-- error: argument 1 of `fnOf` is a type, but its parameter takes a list of types
---
error: argument 1 of `wrap` is a list of types, but its parameter takes a type
-/
#guard_msgs in
public environment ErrAbbrevKind extends DSLTest.Fns where
  open fns base
  abbrev fnOf ((as : list) r) := Fn as r
  abbrev wrap (a) := Fn [a] a
  insn f (g : fnOf Int Int) : Int
  insn h (g : wrap [Int]) : Int

/-- The same abbreviations, each at arguments of its parameters' kinds, are accepted. -/
public environment OkAbbrevKind extends DSLTest.Fns where
  open fns base
  abbrev fnOf ((as : list) r) := Fn as r
  abbrev wrap (a) := Fn [a] a
  insn f (g : fnOf [Int] Int) : Int
  insn h (g : wrap Int) : Int

/-- error: defined instructions are not supported yet
-/
#guard_msgs in
public environment ErrDef extends Base where
  open base
  def f (x : Int) : Int := x
  insn g (x : Int) : Int

private environment PrivEnv extends Base where
  type A

/-- error: public environment `ErrVis` cannot extend private environment `PrivEnv`
-/
#guard_msgs in
public environment ErrVis extends PrivEnv where
  type B

/-- error: unknown environment `Nope`
-/
#guard_msgs in
public environment ErrParent extends Nope where
  type B

/-- error: `ErrReserved.env` is reserved for the environment; rename one with `as`
---
error: `ErrReserved.names` is reserved for the environment; rename one with `as`
-/
#guard_msgs in
public environment ErrReserved extends Base where
  type env
  insn names (x : env) : env

/-! ## Case instructions and terminal instructions -/

-- `T.case` is `T`'s case instruction, so no constructor may be named `case`, and `x.U.case`
-- is declared by `U`.
/-- error: `ErrCase.T.case` is already generated for `x.T`; rename one with `as`
---
error: `ErrCase.T.ref` is already generated for `x.T`; rename one with `as`
---
error: `ErrCase.T.toRaw_ty` is already generated for `x.T`; rename one with `as`
---
error: `x.U.case` is already declared
-/
#guard_msgs in
public environment ErrCase extends Base where
  namespace x
  data T where
    | «case»
    | ref
    | toRaw_ty
  data U where
    | u
  end x
  namespace x.U
  insn «case» : base.Int

-- A successor of `T.case` is named by its constructor, and shares a namespace with the type
-- parameters and the scrutinee.
/-- error: constructor `a` clashes with a parameter of `x.T.case`; rename one with `as`
---
error: constructor `scrutinee` clashes with the scrutinee of `x.T.case`; rename one with `as`
-/
#guard_msgs in
public environment ErrCaseSucc extends Base where
  namespace x
  data T (+a) where
    | a
    | scrutinee

/-- error: a terminal instruction has no result type
---
error: `g` needs a result type `: τ`
-/
#guard_msgs in
public environment ErrResult extends Base where
  terminal insn f : base.Unit
  insn g

/-- A constructor may be named `dataSig` or `dataRef`. -/
public environment OkCtorNames extends Base where
  namespace x
  data T where
    | dataSig
    | dataRef

example : OkCtorNames.T.dataSig.name = .str (.str .base "x") "dataSig" := rfl
example : (OkCtorNames.T.case.sig (e := OkCtorNames.env)).succs.size = 2 := rfl

end Strata.Mantle.DSLErrorTest
