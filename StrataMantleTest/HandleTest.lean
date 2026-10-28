/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Base
public import StrataMantle.Build
public import StrataMantle.DDM
import StrataMantle.Env.WF
import StrataMantle.DSL
-- The builder and the printer run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.DDM
meta import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Type handles

The `environment` command gives each type and abbreviation `T` a handle `T : TypeCon ks` under
its own name, the one way to write it.  Applied to type expressions, a handle is a type
expression, and a list parameter takes a list of them or a `TypeList`.  A type without
parameters is a type expression itself, with its handle at `T.con`.  Each place is tested here
against `Internal.T.ty`, what the handle applies, and each rejection beside its accepted twin.
-/

namespace Strata.Mantle.HandleTest

/-- A child of `Base`: two primitive types, a datatype over the parent's types, and
abbreviations, one with a list parameter. -/
public environment Hd extends Base where
  namespace hd
  open base
  type IntList
  type Flow
  data Pair (+a) where
    | pair (x : a) (y : Int)
  abbrev IntRef := Ref Int
  abbrev withInt ((cs : list) r) := Fn [*cs, Int] r
  abbrev PairRef (a) := Ref (Pair a)
  /-- A cell of an `Except`. -/
  insn excNew (v : Int) : Ref (Except Int Bool)
  end hd

/-- A child of `Hd`. -/
public environment HdKid extends Hd where
  namespace kid
  open base hd
  type Leaf
  end kid

abbrev W := Hd.env

/-! ## Names

A handle is the constant `Base.Int`.  The namespace's constants keep their names and meaning. -/

/--
info: Strata.Mantle.Base.Int {e : Env Unit} [Base.env ⊑ e] {s : Array Kind} : TypeExpr e s
-/
#guard_msgs in #check Base.Int
/-- info: Strata.Mantle.Base.Except : TypeCon [Kind.type, Kind.type] -/
#guard_msgs in #check Base.Except
/-- info: Strata.Mantle.Base.Fn : TypeCon [Kind.list, Kind.type] -/
#guard_msgs in #check Base.Fn
/--
info: Strata.Mantle.HandleTest.Hd.IntRef {e : Env Unit} [Base.env ⊑ e] {s : Array Kind} : TypeExpr e s
-/
#guard_msgs in #check Hd.IntRef
-- An abbreviation with parameters is a handle like a type's: no binders beyond its kinds.
/-- info: Strata.Mantle.HandleTest.Hd.withInt : TypeCon [Kind.list, Kind.type] -/
#guard_msgs in #check Hd.withInt

-- `Base.Internal.Int.ty`, at `[Base.env ⊑ e]`, is what the handle applies.
/--
info: @Base.Internal.Int.ty : {e : Env Unit} → [Base.env ⊑ e] → {s : Array Kind} → TypeExpr e s
-/
#guard_msgs in #check @Base.Internal.Int.ty
example : Base.Int.con.apply (e := W) (s := #[]) = Base.Internal.Int.ty := rfl
example : (Base.Int : TypeExpr W) = Base.Internal.Int.ty := rfl
-- `Base.Fn` takes a list of type expressions or a `TypeList` for its list parameter.
/--
info: @Base.Internal.Fn.ty : {e : Env Unit} → [Base.env ⊑ e] → {s : Array Kind} → TypeList e s → TypeExpr e s → TypeExpr e s
-/
#guard_msgs in #check @Base.Internal.Fn.ty
example : Base.Except.name = (Base.Except).name := rfl
-- `decl` is not a namespace constant, so `Base.Except.decl` is the field.
example : Base.Except.decl.params.size = 2 := rfl
example : Base.Int.con.decl.name = Base.Int.name := rfl
-- The constructor's namespace still holds its instructions.
/-- info: Base.Except.ok : InsnRef Base.env Base.Except.ok.sig -/
#guard_msgs in #check (Base.Except.ok : InsnRef Base.env _)

/-! ## Generic code over type constructors

A constructor's declaration is data: its name, and its parameters' names, polarities and
kinds. -/

/-- A constructor's name and its parameters, `+` for a positive one and `*` for a list. -/
def describe {ks : List Kind} (T : TypeCon ks) : String :=
  s!"{ToDDM.nameText T.name}(" ++ ", ".intercalate (T.decl.params.toList.map fun p =>
    (if p.type.polarity == .pos then "+" else "") ++ p.name ++
      (if p.type.kind == .list then " : list" else "")) ++ ")"

#guard describe Base.Fn == "base.Fn(as : list, +r)"
#guard describe Base.Except == "base.Except(+e, +a)"
#guard describe Base.Int.con == "base.Int()"
#guard describe Hd.Pair == "hd.Pair(+a)"
-- An abbreviation's declaration has its parameters' names and kinds, and no polarities.
#guard describe Hd.withInt == "hd.withInt(cs : list, r)"

-- A type expression built from data is the one written directly, in the environment of the
-- names and in a refinement alike; arguments of the wrong kinds give none.
example : Base.Except.applyArgs? Base.env (s := #[]) [.ty Base.Int, .ty Base.Bool] =
    some (Base.Except Base.Int Base.Bool) := rfl
example : Base.Except.applyArgs? W (s := #[]) [.ty Base.Int, .ty Hd.IntList] =
    some (Base.Except Base.Int Hd.IntList) := rfl
example : Base.Fn.applyArgs? W (s := #[]) [.list [Base.Int], .ty Base.Bool] =
    some (Base.Fn [Base.Int] Base.Bool) := rfl
#guard (Base.Fn.applyArgs? Base.env (s := #[]) [.ty Base.Int, .ty Base.Bool]).isNone
#guard (Base.Except.applyArgs? Base.env (s := #[]) [.ty Base.Int]).isNone

-- A constructor variable applies as a function, in an environment that refines its own.
@[reducible] def twice (T : TypeCon [.type]) {e : Env Unit} [T.env ⊑ e] (t : TypeExpr e) :
    TypeExpr e :=
  T (T t)
example : (twice Base.Ref Base.Int : TypeExpr W) =
    Base.Internal.Ref.ty (Base.Internal.Ref.ty Base.Int) := rfl

/-! ## Type expressions

The list literals here fail if the `.types` hint in `TypeCon.ListArg` stops firing. -/

example : (Base.Int : TypeExpr W) = Base.Internal.Int.ty := rfl
example : (Base.Except Base.Int Base.Bool : TypeExpr W) =
    Base.Internal.Except.ty Base.Int Base.Bool := rfl
-- A parent's handle and a child's mix, in either order.
example : (Base.Except Base.Int Hd.IntList : TypeExpr W) =
    Base.Internal.Except.ty Base.Int Hd.IntList := rfl
example : (Base.Except Hd.IntList Base.Int : TypeExpr W) =
    Base.Internal.Except.ty Hd.IntList Base.Int := rfl
example : (Base.Fn [Base.Int, Hd.IntList] Hd.Flow : TypeExpr W) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Hd.IntList]) Hd.Flow := rfl
example : (Hd.Pair (Base.Ref Base.Int) : TypeExpr W) =
    Hd.Internal.Pair.ty (Base.Internal.Ref.ty Base.Int) := rfl
-- A grandparent's, a parent's and a child's.
example : (Base.Except (Hd.Pair HdKid.Leaf) Base.Bool : TypeExpr HdKid.env) =
    Base.Internal.Except.ty (Hd.Internal.Pair.ty HdKid.Leaf) Base.Bool := rfl
example : (Base.Except (Base.Fn [Base.Int, Hd.IntList] Base.Bool) (Base.Ref HdKid.Leaf) :
      TypeExpr HdKid.env) =
    Base.Internal.Except.ty (Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Hd.IntList]) Base.Bool)
      (Base.Internal.Ref.ty HdKid.Leaf) := rfl
-- A list mixes types without parameters and applied constructors, in either order.
example : (Base.Fn [Base.Int, Base.Ref Base.Int] Base.Bool : TypeExpr W) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty (Base.Internal.Ref.ty Base.Int)]) Base.Bool := rfl
example : (Base.Fn [Base.Ref Base.Int, Base.Int] Base.Bool : TypeExpr W) =
    Base.Internal.Fn.ty (.lit #[.ty (Base.Internal.Ref.ty Base.Int), .ty Base.Int]) Base.Bool := rfl
-- Three deep, with 18 names.
example : TypeExpr HdKid.env :=
  Base.Ref (Base.Except
    (Base.Fn [Base.Ref (Base.Except (Base.Fn [Base.Int, Hd.Flow] Hd.IntList) HdKid.Leaf),
      Hd.IntList, Base.Bool] HdKid.Leaf)
    (Base.Ref (Base.Except (Base.Fn [HdKid.Leaf, Base.Int] Hd.Flow) Hd.IntList)))
-- A literal of 40 types, which is the list `List.replicate` builds.  Lean elaborates a literal
-- of more than 32 elements as nested `let`s, at a cost superlinear in its length, so a long list
-- is better built as a list value.
example : (Base.Fn [Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int,
    Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int,
    Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int,
    Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int, Base.Int,
    Base.Int, Base.Int, Base.Int, Base.Int, Base.Int] Hd.IntList : TypeExpr HdKid.env) =
    Base.Fn (List.replicate 40 Base.Int) Hd.IntList := rfl

-- An abbreviation's handle applies its body's handles.
example : (Hd.IntRef : TypeExpr W) = Base.Ref Base.Int := rfl
example : (Hd.IntRef : TypeExpr W) = Base.Internal.Ref.ty Base.Int := rfl
example : (Hd.withInt [Base.Bool] Base.Int : TypeExpr W) =
    Base.Fn [Base.Bool, Base.Int] Base.Int := rfl
example : (Hd.withInt [Base.Bool] Base.Int : TypeExpr W) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Bool, .ty Base.Int]) Base.Int := rfl
-- An abbreviation's environment is the most refined of its names': `withInt`'s is `Base`'s,
-- though `Hd` declares it, and `PairRef`'s is `Hd`'s.
example : Hd.withInt.env = Base.env := rfl
example : Hd.PairRef.env = Hd.env := rfl
example : (Hd.PairRef Base.Int : TypeExpr W) =
    Base.Internal.Ref.ty (Hd.Internal.Pair.ty Base.Int) := rfl
example : (Hd.PairRef Base.Int : TypeExpr W) = Base.Ref (Hd.Pair Base.Int) := rfl
example : (Hd.PairRef HdKid.Leaf : TypeExpr HdKid.env) =
    Base.Internal.Ref.ty (Hd.Internal.Pair.ty HdKid.Leaf) := rfl

/-- A value of type `t`, as a typed emitter's operand would be. -/
private structure Typed {e : Env Unit} (t : TypeExpr e) where
  id : Nat

/-- What an emitter taking a `Base.Ref a` operand does with `a`: it is solved by
unification. -/
private def deref {e : Env Unit} [Base.env ⊑ e] {a : TypeExpr e} (v : Typed (Base.Ref a)) :
    Typed a :=
  ⟨v.id⟩

-- An abbreviation applies its body's handles, so `Hd.PairRef Base.Bool` unifies with
-- `Base.Ref ?a`, solving `?a` as the constructor its body applies.
example (v : Typed (e := W) (Hd.PairRef Base.Bool)) : Typed (e := W) (Hd.Pair Base.Bool) :=
  deref v

/-- What an emitter calling a `Base.Fn as r` operand does with `as` and `r`. -/
private def callee {e : Env Unit} [Base.env ⊑ e] {as : List (TypeExpr e)} {r : TypeExpr e}
    (v : Typed (Base.Fn as r)) : Typed r :=
  ⟨v.id⟩

-- An abbreviation with a list parameter unifies with `Base.Fn ?as ?r` too: `withInt [Bool] Int`
-- solves `?as` as the list its body builds.
example (v : Typed (e := W) (Hd.withInt [Base.Bool] Base.Int)) : Typed (e := W) Base.Int :=
  callee v
example (v : Typed (e := W) (Base.Fn [Base.Bool, Base.Int] Base.Int)) : Typed (e := W) Base.Int :=
  callee v

/-- Abbreviations that apply a constructor to a closed type beside a parameter. -/
public environment HdAb extends Base where
  namespace hdab
  open base
  type Leaf
  abbrev ex1 (a) := Except (Ref Int) a
  abbrev ex2 (a) := Fn [Ref Int] a
  abbrev ex3 (a) := Ref (Except a (Ref a))
  abbrev ex4 (a b) := Except (Ref a) b
  -- A list parameter spliced after closed elements, in the middle and last.
  abbrev ex5 ((cs : list) r) := Fn [Int, *cs, Bool] r
  abbrev ex6 ((cs : list) r) := Fn [Int, *cs] r
  abbrev ex7 ((cs : list) r) := Fn [Int, Bool, *cs] r
  -- The environment's own type beside its parent's, each applied to the parameter.
  type Box (+a)
  abbrev ex8 (a) := Except (Box a) (Ref a)
  end hdab

/-- info: Strata.Mantle.HandleTest.HdAb.ex1 : TypeCon [Kind.type] -/
#guard_msgs in #check HdAb.ex1
example : (HdAb.ex1 Base.Bool : TypeExpr HdAb.env) =
    Base.Internal.Except.ty (Base.Internal.Ref.ty Base.Int) Base.Bool := rfl
example : (HdAb.ex2 Base.Bool : TypeExpr HdAb.env) =
    Base.Internal.Fn.ty (.lit #[.ty (Base.Internal.Ref.ty Base.Int)]) Base.Bool := rfl
example : (HdAb.ex3 Base.Bool : TypeExpr HdAb.env) =
    Base.Internal.Ref.ty (Base.Internal.Except.ty Base.Bool (Base.Internal.Ref.ty Base.Bool)) := rfl
example : (HdAb.ex3 HdAb.Leaf : TypeExpr HdAb.env) =
    Base.Internal.Ref.ty (Base.Internal.Except.ty HdAb.Leaf (Base.Internal.Ref.ty HdAb.Leaf)) := rfl
example (v : Typed (e := HdAb.env) (HdAb.ex3 Base.Bool)) :
    Typed (e := HdAb.env) (Base.Except Base.Bool (Base.Ref Base.Bool)) :=
  deref v
example : (HdAb.ex4 Base.Int HdAb.Leaf : TypeExpr HdAb.env) =
    Base.Except (Base.Ref Base.Int) HdAb.Leaf := rfl
-- A splice after closed elements, in the middle and last.
example : (HdAb.ex5 [Base.Unit] Base.Int : TypeExpr HdAb.env) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Base.Unit, .ty Base.Bool]) Base.Int := rfl
example : (HdAb.ex6 [Base.Unit, HdAb.Leaf] Base.Int : TypeExpr HdAb.env) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Base.Unit, .ty HdAb.Leaf]) Base.Int := rfl
example : (HdAb.ex7 [] HdAb.Leaf : TypeExpr HdAb.env) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Base.Bool]) HdAb.Leaf := rfl
-- `ex8` names the environment's own type, so it is defined in `HdAb.env`, with no binders.
/-- info: Strata.Mantle.HandleTest.HdAb.ex8 : TypeCon [Kind.type] -/
#guard_msgs in #check HdAb.ex8
example : HdAb.ex8.env = HdAb.env := rfl
example : (HdAb.ex8 Base.Int : TypeExpr HdAb.env) =
    Base.Internal.Except.ty (HdAb.Internal.Box.ty Base.Int) (Base.Internal.Ref.ty Base.Int) := rfl
example : (HdAb.ex8 HdAb.Leaf : TypeExpr HdAb.env) =
    Base.Except (HdAb.Box HdAb.Leaf) (Base.Ref HdAb.Leaf) := rfl

-- In any scope, and generic in the environment.
example : (Base.Int : TypeExpr W #[.type, .list]) = Base.Int := rfl
example {e : Env Unit} [W ⊑ e] : (Base.Except Base.Int Hd.IntList : TypeExpr e) =
    Base.Internal.Except.ty Base.Int Hd.IntList := rfl
-- Generic code takes type expressions.
example {e : Env Unit} [Base.env ⊑ e] {s : Array Kind} (t : TypeExpr e s) : TypeExpr e s :=
  Base.Ref t
example {e : Env Unit} [Hd.env ⊑ e] {s : Array Kind} (t : TypeExpr e s) : TypeExpr e s :=
  Hd.PairRef t

/-! ## Rejections

A type is defined only where every name it mentions is: instance search proves `[T.env ⊑ e]` at
each handle, and fails at the first that `e` does not refine. -/

-- A child's type, in the parent: rejected, since `Base.env` does not refine `Hd.env`.
/--
error: failed to synthesize instance of type class
  Hd.env ⊑ Base.env

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : TypeExpr Base.env := Base.Except Base.Int Hd.IntList
example : TypeExpr Base.env := Base.Except Base.Int Base.Bool
-- A child's constructor, in the parent.
/--
error: failed to synthesize instance of type class
  Hd.Pair.env ⊑ Base.env

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : TypeExpr Base.env := Hd.Pair Base.Int
example : TypeExpr W := Hd.Pair Base.Int
-- An abbreviation, in the parent: rejected only if a name of its body is the child's.
/--
error: failed to synthesize instance of type class
  Hd.PairRef.env ⊑ Base.env

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : TypeExpr Base.env := Hd.PairRef Base.Int
example : TypeExpr Base.env := Hd.withInt [Base.Bool] Base.Int

/-- A sibling of `Hd`. -/
public environment HdSib extends Base where
  namespace sib
  type S
  type B (+a)
  end sib

-- Siblings' handles do not mix: neither environment refines the other.
/--
error: failed to synthesize instance of type class
  HdSib.env ⊑ W

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : TypeExpr W := Base.Except HdSib.S Hd.IntList
example : TypeExpr HdSib.env := Base.Except HdSib.S Base.Int
/--
error: failed to synthesize instance of type class
  HdSib.B.env ⊑ W

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : TypeExpr W := HdSib.B Hd.IntList
example : TypeExpr HdSib.env := HdSib.B Base.Int
/--
error: failed to synthesize instance of type class
  HdSib.env ⊑ W

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  HdKid.env ⊑ W

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  HdSib.env ⊑ W

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example : TypeExpr W := Base.Fn [HdSib.S, Hd.IntList, HdKid.Leaf, HdSib.S] Base.Int
example : TypeExpr HdKid.env := Base.Fn [Base.Int, Hd.IntList, HdKid.Leaf, Base.Int] Base.Int
-- Without an expected type, the environment is not known.
/--
error: typeclass instance problem is stuck
  Base.env ⊑ ?m.11

Note: Lean will not try to resolve this typeclass instance problem because the third type argument to `RefinedBy` is a metavariable. This argument must be fully determined before Lean will try to resolve the typeclass.

Hint: Adding type annotations and supplying implicit arguments to functions can give Lean more information for typeclass resolution. For example, if you have a variable `x` that you intend to be a `Nat`, but Lean reports it as having an unresolved type like `?m`, replacing `x` with `(x : Nat)` can get typeclass resolution un-stuck.
-/
#guard_msgs in
example := Base.Ref Base.Int
example : TypeExpr Base.env := Base.Ref Base.Int

/-! ## Proofs

An applied handle is its type's `Internal.T.ty` by `rfl`, so `simp` and `change` see through it;
`rw` does not, as its pattern is keyed on `Internal.T.ty`.  An abbreviation that splices a list
parameter builds one literal from a list of type expressions, by `rfl`; from a `TypeList` it
appends, which is not exposed, so `simp` proves that equation. -/

example (t : TypeExpr W) (h : Base.Internal.Int.ty = t) : (Base.Int : TypeExpr W) = t := by
  simp only [h]
example (t : TypeExpr W) (h : Base.Internal.Int.ty = t) : (Base.Int : TypeExpr W) = t := by
  change Base.Internal.Int.ty = t
  rw [h]
/--
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  Base.Internal.Int.ty
in the target expression
  Base.Int = t

t : TypeExpr W
h : Base.Internal.Int.ty = t
⊢ Base.Int = t
-/
#guard_msgs in
example (t : TypeExpr W) (h : Base.Internal.Int.ty = t) : (Base.Int : TypeExpr W) = t := by
  rw [h]
-- `withInt [*cs, Int]` at a list of type expressions is one literal, by `rfl`.
example : (Hd.withInt [Base.Bool] Base.Int : TypeExpr Hd.env) =
    Base.Fn [Base.Bool, Base.Int] Base.Int := rfl
-- At a `TypeList`, it appends `[Int]`, so `simp` proves the literal.
example : (Hd.withInt (TypeList.ofTypes #[Base.Bool]) Base.Int : TypeExpr Hd.env) =
    Base.Fn [Base.Bool, Base.Int] Base.Int := by
  simp [TypeList.ofTypes, TypeCon.ListArg.toTypeList]
/--
but is expected to have type
  ↑Hd.withInt (TypeList.ofTypes #[Base.Bool]) Base.Int = ↑Base.Fn [Base.Bool, Base.Int] Base.Int
-/
#guard_msgs (substring := true) in
example : (Hd.withInt (TypeList.ofTypes #[Base.Bool]) Base.Int : TypeExpr Hd.env) =
    Base.Fn [Base.Bool, Base.Int] Base.Int := rfl

/-! ## List parameters

A list parameter takes a list of type expressions, a literal or computed, or a `TypeList`, which
may splice a list variable of the scope.  The argument's type chooses which, by the unification
hints `TypeCon.ListArg` describes.  The cases here that pass a `TypeList` fail if the `.list`
hint stops firing, and the literals of handles if the `.types` hint does. -/

-- A list variable, alone and spliced into a literal.
example (h : (#[.list] : Array Kind)[0]? = some .list) :
    (Base.Fn (TypeList.var 0 h) Base.Bool : TypeExpr W #[.list]) =
      Base.Internal.Fn.ty (TypeList.var 0 h) Base.Bool := rfl
example : TypeExpr W #[.list] := Base.Fn (TypeList.lit #[.splice 0 rfl, .ty Base.Int]) Base.Bool
example : (Base.Fn (TypeList.lit #[.splice 0 rfl, .ty Hd.IntList]) Base.Bool :
      TypeExpr W #[.list]) =
    Base.Internal.Fn.ty (.lit #[.splice 0 rfl, .ty Hd.IntList]) Base.Bool := rfl
-- A literal of handles is the literal of its types, as a generated signature writes it.
example : (Base.Fn [Base.Int, Hd.IntList] Base.Bool : TypeExpr W) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Hd.IntList]) Base.Bool := rfl
example : (Base.Fn [] Base.Bool : TypeExpr W) = Base.Internal.Fn.ty (.lit #[]) Base.Bool := rfl
-- A `TypeList` built from an array is itself.
example : (Base.Fn (TypeList.ofTypes #[Base.Int]) Base.Bool : TypeExpr W) =
    Base.Internal.Fn.ty (.ofTypes #[Base.Int]) Base.Bool := rfl
-- In generic code, at a `TypeList`; at a list, below.
example {e : Env Unit} [Base.env ⊑ e] {s : Array Kind} (l : TypeList e s) (r : TypeExpr e s) :
    TypeExpr e s :=
  Base.Fn l r
-- An abbreviation's list parameter takes either too, and splices a list variable.
example : TypeExpr W #[.list] := Hd.withInt (TypeList.var 0 rfl) Base.Bool

/-! ## Type arguments and lists -/

-- A type without parameters is a type expression, so it is not coerced to a `TypeArg`: its
-- environment and scope are unknown when the coercion is needed.
/--
error: Type mismatch
  Base.Int
has type
  TypeExpr ?m.2 ?m.4
but is expected to have type
  TypeArg W
-/
#guard_msgs in
example : TypeArg W := Base.Int
example : (.ty Base.Int : TypeArg W) = .ty Base.Internal.Int.ty := rfl
example : (([Base.Int, Hd.IntList] : List (TypeExpr W)) : TypeList W) =
    .ofTypes #[Base.Int, Hd.IntList] := rfl
example : (([Base.Int, Hd.IntList] : List (TypeExpr W)) : TypeArg W) =
    .list (.ofTypes #[Base.Int, Hd.IntList]) := rfl
-- A literal of types without parameters, where a `TypeList` is expected, is a list of handles,
-- which does not coerce.
/--
error: Type mismatch
  [Base.Int, Hd.IntList]
has type
  List (TypeExpr ?m.7 ?m.9)
but is expected to have type
  TypeList W
-/
#guard_msgs in
example : TypeList W := [Base.Int, Hd.IntList]
example : TypeList W := ([Base.Int, Hd.IntList] : List (TypeExpr W))
example : TypeArgs W #[.type] := ⟨#[.ty Base.Int], rfl⟩

-- No type expression in a `TypeArg` slot is coerced: its environment and scope are unknown
-- when the coercion is needed.
/--
error: Application type mismatch: The argument
  Base.Int
has type
  TypeExpr ?m.4 ?m.6
but is expected to have type
  TypeArg W
in the application
  List.cons Base.Int
-/
#guard_msgs in
example : Array (TypeArg W) := #[Base.Int]
example : Array (TypeArg W) := #[.ty Base.Int]
-- Nor is an applied handle.
/--
error: Application type mismatch: The argument
  ↑Base.Ref Base.Int
has type
  TypeCon.Fn ?m.8 ?m.10 []
but is expected to have type
  TypeArg W
in the application
  List.cons (↑Base.Ref Base.Int)
-/
#guard_msgs in
example : Array (TypeArg W) := #[Base.Ref Base.Int]
example : Array (TypeArg W) := #[.ty (Base.Ref Base.Int)]

/-! ## The builder -/

open Strata.Mantle.Build (freshVal freshLabel startBlockWith startFreshBlock emitConst
  emitApply finishBlock terminate goto build FailedFunc)

/-- What `build` gives. -/
private abbrev Built := Except (FailedFunc W Unit Unit) {fn : Func W Unit // fn.WF}

/-- The module `m` of `f`, printed, or why it was not built. -/
private def showMod (f : Built) : String :=
  match f with
  | .error e => toString e
  | .ok f => match Module.ofChecked (.str .base "m") #[f] () with
    | .ok m => toString m
    | .error _ => "the module is not well formed"

/-- `f()`: a cell, written and read, and an `Except` built and taken apart, all at handles. -/
private def f : Built :=
  build (.str .base "f") Base.Int () do
    let okL ← freshLabel "ok"
    let errL ← freshLabel "err"
    let _ ← startFreshBlock (base := "entry")
    let zero ← emitConst (.str .base "k") (.int 0)
    let cell ← emitApply (.str .base "cell") (Base.Ref Base.Int) Base.refNew #[zero]
    let _ ← emitApply (.str .base "u") Base.Unit Base.refSet (typeArgs := ta[Base.Int])
      #[cell, zero]
    let r ← emitApply (.str .base "r") Base.Int Base.refGet #[cell]
    let x ← emitApply (.str .base "x") (Base.Except Hd.IntList Base.Int) Base.Except.ok #[r]
    terminate Base.Except.case (typeArgs := ta[Hd.IntList, Base.Int]) #[x]
      #[goto okL, goto errL]
    let _ ← startBlockWith errL (.str .base "e") Hd.IntList
    finishBlock (.ret () zero)
    finishBlock (.ret () (← startBlockWith okL (.str .base "v") Base.Int))

/-- info: module m {
  func @f() -> base.Int {
    entry.0():
      %cell.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = base.refSet[base.Int](%cell.0, 0)
      %r.0 : base.Int = base.refGet[base.Int](%cell.0)
      %x.0 : base.Except(hd.IntList, base.Int) = base.ok[hd.IntList, base.Int](%r.0)
      base.Except.case[hd.IntList, base.Int](%x.0) ^ok.0() ^err.0()
    err.0(%e.0 : hd.IntList):
      ret(0)
    ok.0(%v.0 : base.Int):
      ret(%v.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod f)

/-- `g(%fn : Fn [Int, Bool] Int)`: `callCode` with its list argument written as handles. -/
private def g : Built :=
  build (.str .base "g") Base.Int () do
    let fv ← freshVal (.str .base "fn") (Base.Fn [Base.Int, Base.Bool] Base.Int)
    let _ ← startFreshBlock #[fv] "entry"
    let a ← emitConst (.str .base "a") (.int 1)
    let b ← emitConst (.str .base "b") (.bool true)
    let r ← emitApply (.str .base "r") Base.Int Base.callCode
      (typeArgs := ta[[Base.Int, Base.Bool], Base.Int]) #[fv.id, a, b]
    finishBlock (.ret () r)

/-- info: module m {
  func @g(%fn.0 : base.Fn([base.Int, base.Bool], base.Int)) -> base.Int {
    entry.0(%fn.0 : base.Fn([base.Int, base.Bool], base.Int)):
      %r.0 : base.Int = base.callCode[[base.Int, base.Bool], base.Int](%fn.0, 1, true)
      ret(%r.0)
  }
} -/
#guard_msgs in
#eval IO.println (showMod g)

/-- A new cell holding `v`, in any refinement of `Base`. -/
def newIntCell {e : Env Unit} [Base.env ⊑ e] (v : ValId) : BuildM e Unit ValId :=
  emitApply (.str .base "cell") (Base.Ref Base.Int) Base.refNew #[v]

/-- An `Except` of a `Hd` list, in any refinement of `Hd`. -/
def okList {e : Env Unit} [W ⊑ e] (v : ValId) : BuildM e Unit ValId :=
  emitApply (.str .base "x") (Base.Except Base.Int Hd.IntList) Base.Except.ok #[v]

/-! ## Computed types

A front end computes its types as type expressions, in its environment, writing handles in the
cases; the type is then defined where the expressions are, with nothing to state. -/

/-- A front end's types. -/
inductive K where
  | int
  | list

/-- `K`'s types. -/
def K.ty : K → TypeExpr W
  | .int => Base.Int
  | .list => Hd.IntList

example (k : K) : TypeExpr W := Base.Ref k.ty
example (ks : List K) : TypeExpr W := Base.Fn (ks.map K.ty) Base.Int

/-! ## Type expressions from handles

Type expressions built from handles: a spliced list parameter between types without
parameters, an environment's own type beside its parent's under applied constructors, parameter
lists that Lean computes, in concrete and generic code, and `Typed` operands built by a generic
function.  The computed lists fail if the `.types` hint in `TypeCon.ListArg` stops firing. -/

-- A list parameter spliced between closed elements.
example : (HdAb.ex5 [HdAb.Leaf] Base.Int : TypeExpr HdAb.env) =
    Base.Fn [Base.Int, HdAb.Leaf, Base.Bool] Base.Int := rfl
-- The environment's own type beside its parent's, each applied to the parameter.
example : (HdAb.ex8 HdAb.Leaf : TypeExpr HdAb.env) =
    Base.Except (HdAb.Box HdAb.Leaf) (Base.Ref HdAb.Leaf) := rfl
-- Computed lists.  `++` elaborates its operands before the expected type is known; their
-- environment is unified afterwards.
example : TypeExpr Base.env := Base.Fn ([Base.Int] ++ [Base.Bool]) Base.Int
example : (Base.Fn (List.append [Base.Int] [Base.Bool]) Base.Int : TypeExpr Base.env) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Base.Bool]) Base.Int := rfl

/-- Two parameter types, as a definition. -/
def args2 : List (TypeExpr Base.env) := [Base.Int, Base.Bool]

example : (Base.Fn args2 Base.Int : TypeExpr Base.env) =
    Base.Internal.Fn.ty (.lit #[.ty Base.Int, .ty Base.Bool]) Base.Int := rfl
example (n : Nat) : TypeExpr Base.env := Base.Fn (List.replicate n Base.Int) Base.Int
example {e : Env Unit} [Base.env ⊑ e] (ts : List (TypeExpr e)) (r : TypeExpr e) :
    TypeExpr e :=
  Base.Fn ts r
-- `Typed`, at a type expression, and a generic `mkRef`: there is one type expression per
-- type, so a typed value built in generic code has the type written directly.
/-- A typed operand of `Base.Ref t`, in any refinement of `Base`. -/
private def mkRef {e : Env Unit} [Base.env ⊑ e] (t : TypeExpr e) (n : Nat) :
    Typed (Base.Ref t) := ⟨n⟩
example : Typed (e := W) (Base.Ref Base.Int) := mkRef (e := W) Base.Int 0
example : Typed (e := W) (Base.Ref Hd.IntList) := mkRef (e := W) Hd.IntList 0
-- Without `e`: the environment is unified from the expected type.
example : Typed (e := W) (Base.Ref Base.Int) := mkRef Base.Int 0
example : Typed (e := W) (Base.Ref (Base.Ref Base.Int)) := mkRef (Base.Ref Base.Int) 0
example : Typed (e := W) (Base.Ref (Base.Ref Base.Int)) := mkRef (e := W) (Base.Ref Base.Int) 0

/-! ## Reserved names

A constructor `c` of `T` is `T.c`.  So a type may not have a constructor `decl`, `kinds`,
`env` or `apply`, its handle's fields, nor `con` if it has no parameters.  Each is fixed by
another Lean name, keeping the environment name with `as`. -/

/--
error: `ResCon.T.decl` is already generated for `x.T`; rename one with `as`
---
error: `ResCon.T.env` is already generated for `x.T`; rename one with `as`
---
error: `ResCon.T.apply` is already generated for `x.T`; rename one with `as`
---
error: `ResCon.T.con` is already generated for `x.T`; rename one with `as`
-/
#guard_msgs in
public environment ResCon extends Base where
  namespace x
  data T where
    | decl
    | env
    | apply
    | con
  end x

public environment ResConOk extends Base where
  namespace x
  data T where
    | decl_ as "decl"
    | env_ as "env"
    | apply_ as "apply"
    | con_ as "con"
  end x

#guard ResConOk.T.decl_.name == .str (.str .base "x") "decl"
#guard describe ResConOk.T.con == "x.T()"

/--
error: `ResApply.T.apply` is already generated for `x.T`; rename one with `as`
---
error: `ResApply.T.kinds` is already generated for `x.T`; rename one with `as`
-/
#guard_msgs in
public environment ResApply extends Base where
  namespace x
  data T (+a) where
    | apply (v : a)
    | kinds
  end x

public environment ResApplyOk extends Base where
  namespace x
  data T (+a) where
    | apply_ as "apply" (v : a)
    | kinds_ as "kinds"
  end x

#guard describe ResApplyOk.T == "x.T(+a)"
example : (ResApplyOk.T Base.Int : TypeExpr ResApplyOk.env) =
    ResApplyOk.Internal.T.ty Base.Int := rfl
-- `lift` is not a reserved constructor name.
public environment ResFree extends Base where
  namespace x
  data T where
    | lift
  end x

#guard ResFree.T.lift.name == .str (.str .base "x") "lift"

end Strata.Mantle.HandleTest
