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
example : Vector (TypeExpr Grand.env 0) (Demo.unbox.sig (e := Grand.env)).typeArgc :=
  #v[Grand.Cell.ty]

/-! ## What crosses the module boundary

The interface does; the stages are private to `DSLTest`. -/

example : (Demo.unbox.sig (e := Demo.env)).typeArgc = 1 := rfl
example : Vector (TypeExpr Demo.env 0) (Base.refNew.sig (e := Demo.env)).typeArgc :=
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
error: `x.U.case` is already declared
-/
#guard_msgs in
public environment ErrCase extends Base where
  namespace x
  data T where
    | «case»
    | ref
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
