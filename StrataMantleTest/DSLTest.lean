/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
import StrataMantle.Env.WF
import StrataMantle.DSL
-- The reference test reads the environment's declarations directly.
import all StrataMantle.Env
import all StrataMantle.Base
-- The `#guard`s below run as compiled code.
meta import StrataMantle.Env.WF
-- `decide +kernel` unfolds the checker, the environment and core's array operations.
import all StrataMantle.WF
import all StrataMantle.Build
import all StrataMantle.Env.Raw
import all StrataMantle.Env.Data
import all StrataMantle.Util.IndexMap
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq

set_option autoImplicit false

/-!
# The `environment` command

* `Base`, the block in `Mantle/Base.lean`: membership and generated names.
* `Demo`, a child of `Base` with a type, datatypes, abbreviations, an instruction with
  type parameters, a variadic one, ones with regions, ones with successors and terminal
  ones, and a function built against it.
* The checks, each with the error it reports.
-/

namespace Strata.Mantle.DSLTest

/-! ## `Base` -/

/-- The aliases are the generated names. -/
example {n : Name} : n ∈ base ↔ n ∈ Base.env := Iff.rfl

/-- `simp` decides membership in `Base.env` from `mem_env` alone. -/
example : bn "Unit" ∈ base := by simp
example : .str (.str .base "base") "Except" ∈ Base.env := by simp
example : .str (bn "Except") "case" ∈ Base.env := by simp
example : bn "Nope" ∉ base := by simp
example : .str .base "Unit" ∉ Base.env := by simp
example : base ⊑ Base.env := inferInstance

example : (Base.Int.ref (e := Base.env)).name = bn "Int" := rfl
example : Base.Except.ok.name = bn "ok" := rfl
example : (Base.Except.error (e := base)).name = bn "error" := rfl

/-- `#v[…]` type-checks against a generated signature's `typeArgc`. -/
example : Vector (TypeExpr Base.env) (Base.refNew.sig (e := Base.env)).typeArgc :=
  #v[Base.Int.ty]

/-! ## A child -/

/-- A small language over the base. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- A demo value. -/
  type Value
  /-- A box that may be empty. -/
  data Box (+a) where
    | /-- A full box. -/ box (contents : a)
    | empty
  /-- A rose tree: it recurses through `Sequence`, whose parameter is positive. -/
  data Tree (+a) where
    | leaf (label : a)
    | node (kids : Sequence (Tree a))
  mutual
    data Even where
      | zero
      | succE (pred : Odd)
    data Odd where
      | succO (pred : Even)
  end
  /-- An operation that raises a `Value` or produces an `a`. -/
  abbrev raising (a) := Except Value a
  abbrev failing := raising Value
  /-- `lhs + rhs`, or the exception to `err`. -/
  insn add (lhs rhs : Value) (^err (exc : Value)) : Value
  /-- `not operand`. -/
  insn not_ as "not" (operand : Value) (^err (exc : Value)) : Value
  /-- The contents of a full box, or the failure as a value: no successor. -/
  insn unbox [a] (b : Box a) : raising a
  /-- A tuple of `elems`. -/
  insn mkTuple (*elems : Value) : Value
  /-- A closure over `code` and the captured `cells`. -/
  insn mkClosure (code : Code) (*cells : Ref Value) : Value
  /-- Run `then` if `cond` holds, else `else`. -/
  insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  /-- Run `body`; if it raises, run `handler` on the exception. -/
  insn «try» [a] (&body : raising a) (&handler (exc : Value) : a) : a
  /-- Raise `exc`: always to `err`. -/
  terminal insn raise (exc : Value) (^err (exc : Value))
  /-- To `yes` if `cond` holds, else to `no`; neither receives anything. -/
  terminal insn br (cond : Bool) (^yes ^no)
  /-- Run `body` from `init` until it returns `false`, then leave to `exit` with the last
  value. -/
  terminal insn loop [a] (init : a) (&body (x : a) : Bool) (^exit (x : a))
  /-- Two successors receiving the same two values. -/
  insn fork (^left ^right (x y : Value)) : Unit
  end demo

/-! ### What it generates -/

example : Demo.Value.name = .str (.str .base "demo") "Value" := rfl
example : Demo.not_.name = .str (.str .base "demo") "not" := rfl
example : Demo.Box.box.name = .str (.str .base "demo") "box" := rfl
example : (Demo.unbox.sig (e := Demo.env)).typeArgc = 1 := rfl
example : (Demo.mkTuple.sig (e := Demo.env)).variadic.isSome = true := rfl
#guard (Demo.mkTuple.sig (e := Demo.env)).variadic.map (·.name) == some "elems"
#guard (Demo.mkClosure.sig (e := Demo.env)).variadic.map (·.name) == some "cells"
#guard (Demo.mkClosure.sig (e := Demo.env)).argTypes.map (·.name) == #["code"]
#guard (Demo.not_.sig (e := Demo.env)).variadic.isNone
#guard (Demo.«if».sig (e := Demo.env)).regions.map (·.name) == #["then", "else"]
#guard (Demo.«try».sig (e := Demo.env)).regions.map (·.name) == #["body", "handler"]
#guard ((Demo.«try».sig (e := Demo.env)).regions.map (·.type.params.map (·.name))) ==
  #[#[], #["exc"]]
#guard (Demo.add.sig (e := Demo.env)).succs.map (·.name) == #["err"]
#guard (Demo.add.sig (e := Demo.env)).succs.map (·.type.size) == #[1]
#guard !(Demo.add.sig (e := Demo.env)).terminal
#guard (Demo.unbox.sig (e := Demo.env)).succs.isEmpty
#guard (Demo.raise.sig (e := Demo.env)).terminal
#guard (Demo.br.sig (e := Demo.env)).succs.map (fun p => (p.name, p.type.size)) ==
  #[("yes", 0), ("no", 0)]
#guard (Demo.loop.sig (e := Demo.env)).regions.size == 1 &&
  (Demo.loop.sig (e := Demo.env)).succs.map (·.name) == #["exit"]
#guard (Demo.fork.sig (e := Demo.env)).succs.map (fun p => (p.name, p.type.size)) ==
  #[("left", 2), ("right", 2)]
example {n : Name} : n ∈ Demo.env ↔ n ∈ Demo.names := Demo.mem_env
/-- `simp` decides membership in a child, its own names and its ancestors'. -/
example : .str (.str .base "demo") "add" ∈ Demo.env := by simp
example : .str (.str (.str .base "demo") "Box") "case" ∈ Demo.env := by simp
example : bn "refNew" ∈ Demo.env := by simp
example : .str (.str .base "demo") "nope" ∉ Demo.env := by simp

/-- The parent's references resolve in the child, and in every refinement of it. -/
example : TypeRef Demo.env 1 := Base.Ref.ref
example : Base.env ⊑ Demo.env := inferInstance
example : base ⊑ Demo.env := inferInstance

section
variable {e : Env _root_.Unit} [Demo.env ⊑ e]
example : TypeExpr e := Base.Ref.ty Demo.Value.ty
example : TypeExpr e := Demo.raising.ty Base.Int.ty
example : InsnRef e Base.refNew.sig := Base.refNew
example : InsnRef e Demo.add.sig := Demo.add
example : InsnRef e Demo.Box.box.sig := Demo.Box.box
example : InsnRef e Base.Except.ok.sig := Base.Except.ok
end

/-! ### Parameters named as the generated binders

`T.ty` and `n.ty` bind `e`, `s` and `l` themselves, so a parameter with one of those names is
renamed: primed past every other parameter.  Each argument still reaches its own parameter, in
order.  Any other parameter keeps its name, `h` included: the instance binder is hygienic. -/

/-- Types whose parameters are named as `T.ty`'s binders and their primes. -/
public environment Clash extends Base where
  namespace clash
  type T (e) (e')
  data D (e) (e') where
    | mk (x : e) (y : e')
  abbrev A (e e') := T e e'
  type S (s) (s') (h)
  end clash

section
variable {e : Env _root_.Unit} [Clash.env ⊑ e] {s : Array Kind} (x y z : TypeExpr e s)
example : Clash.T.ty x y =
    .app Clash.T.ref #v[x, y] (by rw [TypeRef.kinds, Clash.T.decl_ref]; rfl) := rfl
example : Clash.D.ty x y =
    .app Clash.D.ref #v[x, y] (by rw [TypeRef.kinds, Clash.D.decl_ref]; rfl) := rfl
example : Clash.A.ty x y = Clash.T.ty x y := rfl
example : Clash.S.ty x y z =
    .app Clash.S.ref #v[x, y, z] (by rw [TypeRef.kinds, Clash.S.decl_ref]; rfl) := rfl
-- The binders' names: `e` and `s` are renamed past the other parameters, and the rest keep
-- theirs.
example : Clash.T.ty (e'' := x) (e' := y) = Clash.T.ty x y := rfl
example : Clash.D.ty (e'' := x) (e' := y) = Clash.D.ty x y := rfl
example : Clash.A.ty (e'' := x) (e' := y) = Clash.A.ty x y := rfl
example : Clash.S.ty (s'' := x) (s' := y) (h := z) = Clash.S.ty x y z := rfl
-- The generated `e` and `s` keep their names beside the renamed parameters.
example : Clash.T.ty (e := e) (s := s) x y = Clash.T.ty x y := rfl
example : Clash.S.ty (e := e) (s := s) x y z = Clash.S.ty x y z := rfl
end
example : Clash.T.ty (e := Clash.env) (s := #[]) Base.Int.ty Base.Bool.ty =
    .app Clash.T.ref #v[Base.Int.ty, Base.Bool.ty] (by rw [TypeRef.kinds, Clash.T.decl_ref]; rfl) :=
  rfl

section
variable {e : Env _root_.Unit} [Demo.env ⊑ e] {s : Array Kind} (x y : TypeExpr e s)
-- A parameter that clashes with no other is primed once, and one that clashes with nothing
-- keeps its name.
example : Base.Except.ty (e' := x) (a := y) = Base.Except.ty x y := rfl
example : Demo.Box.ty (a := x) = Demo.Box.ty x := rfl
example : Demo.raising.ty (a := x) = Demo.raising.ty x := rfl
end

/-! ### List parameters

`type Fn (args : list) (+r)` takes a list of types, then a type.  A list parameter's argument
is a literal `[τ, …]` or a list parameter, which `Fn.ty` takes as a `TypeList`.  `Fn` is a
test-only stand-in for `Code`.  An instruction's `(as : list)` parameter is one too, spliced
into a literal as `*as`, and a variadic typed by a list takes one operand per element. -/

/-- A test-only type of functions, a datatype that recurses through its result, and
instructions and an abbreviation over it. -/
public environment Fns extends Base where
  namespace fns
  open base
  /-- A function from `args` to `r`. -/
  type Fn (args : list) (+r)
  /-- An infinite stream: its tail is a thunk. -/
  data Stream where
    | cons (head : Int) (tail : Fn [] Stream)
  abbrev unary (a) := Fn [a] a
  insn apply (f : Fn [Int, Bool] Int) (x : Int) (y : Bool) : Int
  /-- Apply `f` to one operand per element of `as`. -/
  insn callFn [(as : list) r] (f : Fn as r) (*args : as) : r
  /-- `callFn`, with the spread's list in parentheses. -/
  insn callFnParen [(as : list) r] (f : Fn as r) (*args : (as)) : r
  /-- Apply `f`, which takes an `Int` after `as`: the spread's list splices `as` in. -/
  insn callLast [(as : list) r] (f : Fn [*as, Int] r) (*args : [*as, Int]) : r
  /-- Apply `f` to two operands, typed by a literal spread. -/
  insn applyLit (f : Fn [Int, Bool] Int) (*args : [Int, Bool]) : Int
  /-- Any number of `Int`s: a parenthesized type makes an `each` variadic. -/
  insn sumParen (*xs : (Int)) : Int
  /-- Fix `f`'s first argument, leaving a function of `as`. -/
  insn bindFirst [a (as : list) r] (f : Fn [a, *as] r) (x : a) : Fn as r
  end fns

/-- A child applying the inherited `Fn`, whose kinds proof goes through `Fn.decl_ref`. -/
public environment FnsChild extends Fns where
  open fns base
  insn call (f : Fn [Int] Int) (x : Int) : Int
  data Lazy where
    | mk (thunk : Fn [] Lazy)

#guard (Fns.Fn.ref (e := Fns.env)).kinds == #[.list, .type]

section
variable {e : Env _root_.Unit} [Fns.env ⊑ e] {s : Array Kind} (x : TypeExpr e s)
example : Fns.unary.ty x = Fns.Fn.ty (.lit #[.ty x]) x := rfl
end

/-- A list parameter is a variable of kind `list`, passed to `Fn` as a `TypeList.var` and typing
a `spread` variadic. -/
example : Fns.callFn.sig (e := Fns.env) =
    { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"f", Fns.Fn.ty (.var 0 (by decide)) (.var 1 (by decide))⟩],
      variadic := some ⟨"args", .spread (.var 0 (by decide))⟩,
      returnType := some (.var 1 (by decide)), distinct := by decide } := rfl

/-- A parenthesized list parameter types a spread too. -/
example : Fns.callFnParen.sig (e := Fns.env) =
    { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"f", Fns.Fn.ty (.var 0 (by decide)) (.var 1 (by decide))⟩],
      variadic := some ⟨"args", .spread (.var 0 (by decide))⟩,
      returnType := some (.var 1 (by decide)), distinct := by decide } := rfl

/-- `*as` is a splice, in an argument's literal and in the spread's. -/
example : Fns.callLast.sig (e := Fns.env) =
    { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"f", Fns.Fn.ty (.lit #[.splice 0 (by decide), .ty Base.Int.ty])
        (.var 1 (by decide))⟩],
      variadic := some ⟨"args", .spread (.lit #[.splice 0 (by decide), .ty Base.Int.ty])⟩,
      returnType := some (.var 1 (by decide)), distinct := by decide } := rfl

/-- A literal types a spread too. -/
example : Fns.applyLit.sig (e := Fns.env) =
    { ann := (), typeParams := #[],
      argTypes := #[⟨"f", Fns.Fn.ty (.lit #[.ty Base.Int.ty, .ty Base.Bool.ty]) Base.Int.ty⟩],
      variadic := some ⟨"args", .spread (.lit #[.ty Base.Int.ty, .ty Base.Bool.ty])⟩,
      returnType := some Base.Int.ty, distinct := by decide } := rfl

/-- A type, in parentheses, types an `each` variadic. -/
example : Fns.sumParen.sig (e := Fns.env) =
    { ann := (), typeParams := #[], argTypes := #[],
      variadic := some ⟨"xs", .each Base.Int.ty⟩,
      returnType := some Base.Int.ty, distinct := by decide } := rfl

/-- Type and list parameters share one scope, in the order written. -/
example : (Fns.bindFirst.sig (e := Fns.env)).scope = #[.type, .list, .type] := rfl

/-! ### Abbreviations with list parameters

An abbreviation's parameter may be a list, `(as : list)`, as an instruction's may.  Expanding
it splices its argument where the body splices the parameter, so `withInt [*cs] r` is
`Fn [*cs, Int] r`.  Its `n.ty` takes a `TypeList`, and appends it. -/

/-- Abbreviations over lists of types, and instructions using them. -/
public environment FnAbbrevs extends Fns where
  namespace fnab
  open fns base
  /-- A function of `as` returning `r`. -/
  abbrev fnOf ((as : list) r) := Fn as r
  /-- A function taking an `Int` after `as`. -/
  abbrev withInt ((as : list) r) := Fn [*as, Int] r
  /-- Apply `f` to one operand per element of `as`, through `fnOf`. -/
  insn callOf [(as : list) r] (f : fnOf as r) (*args : as) : r
  /-- `callLast`, through `withInt`: `as` is spliced into the expansion. -/
  insn callWith [(cs : list) r] (f : withInt [*cs] r) (*args : [*cs, Int]) : r
  /-- `withInt` at a literal. -/
  insn applyWith (f : withInt [Bool] Int) (x : Bool) (y : Int) : Int
  /-- A function whose arguments splice `as` in the middle. -/
  insn wrap [(as : list)] (x : Int) : Fn [Int, *as, Bool] Int
  /-- `withInt` at a literal splicing `cs` first, which expands to a splice in the middle. -/
  insn applyMid [(cs : list)] (f : withInt [Bool, *cs] Int) : Int
  end fnab

/-- Through an abbreviation, the signatures are those written out. -/
example : FnAbbrevs.callOf.sig (e := FnAbbrevs.env) =
    { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"f", Fns.Fn.ty (.var 0 (by decide)) (.var 1 (by decide))⟩],
      variadic := some ⟨"args", .spread (.var 0 (by decide))⟩,
      returnType := some (.var 1 (by decide)), distinct := by decide } := rfl
example : FnAbbrevs.callWith.sig (e := FnAbbrevs.env) =
    { ann := (), typeParams := #[⟨"cs", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"f", Fns.Fn.ty (.lit #[.splice 0 (by decide), .ty Base.Int.ty])
        (.var 1 (by decide))⟩],
      variadic := some ⟨"args", .spread (.lit #[.splice 0 (by decide), .ty Base.Int.ty])⟩,
      returnType := some (.var 1 (by decide)), distinct := by decide } := rfl
example : FnAbbrevs.applyWith.sig (e := FnAbbrevs.env) =
    { ann := (), typeParams := #[],
      argTypes := #[⟨"f", Fns.Fn.ty (.lit #[.ty Base.Bool.ty, .ty Base.Int.ty]) Base.Int.ty⟩,
        ⟨"x", Base.Bool.ty⟩, ⟨"y", Base.Int.ty⟩],
      returnType := some Base.Int.ty, distinct := by decide } := rfl

/-- A splice may stand anywhere in a literal, as written and as an abbreviation expands. -/
example : (FnAbbrevs.wrap.sig (e := FnAbbrevs.env)).returnType =
    some (Fns.Fn.ty (.lit #[.ty Base.Int.ty, .splice 0 (by decide), .ty Base.Bool.ty])
      Base.Int.ty) := rfl
example : FnAbbrevs.applyMid.sig (e := FnAbbrevs.env) =
    { ann := (), typeParams := #[⟨"cs", .list⟩],
      argTypes := #[⟨"f", Fns.Fn.ty
        (.lit #[.ty Base.Bool.ty, .splice 0 (by decide), .ty Base.Int.ty]) Base.Int.ty⟩],
      returnType := some Base.Int.ty, distinct := by decide } := rfl

section
variable {e : Env _root_.Unit} [FnAbbrevs.env ⊑ e] {s : Array Kind} (l : TypeList e s)
  (r : TypeExpr e s)
example : FnAbbrevs.fnOf.ty l r = Fns.Fn.ty l r := rfl
example : FnAbbrevs.withInt.ty l r = Fns.Fn.ty (l ++ TypeList.lit #[.ty Base.Int.ty]) r := rfl
-- At a literal, the expansion is the literal the DSL's expansion writes.
example (x : TypeExpr e s) :
    FnAbbrevs.withInt.ty (.lit #[.ty x]) r = Fns.Fn.ty (.lit #[.ty x, .ty Base.Int.ty]) r := by
  simp [FnAbbrevs.withInt.ty]
end

#guard (FnAbbrevs.withInt.ty (e := FnAbbrevs.env) (s := #[]) (.ofTypes #[Base.Bool.ty])
    Base.Int.ty).toRaw ==
  (Fns.Fn.ty (e := FnAbbrevs.env) (s := #[]) (.ofTypes #[Base.Bool.ty, Base.Int.ty])
    Base.Int.ty).toRaw

/-! ### Datatypes with list parameters

A datatype's parameter may be a list, `(as : list)`, as a primitive type's may.  A field uses it
wherever a list belongs: as a list argument, or spliced into a literal.  Its constructors and
case instruction bind it as a list parameter. -/

/-- Datatypes over lists of types. -/
public environment Clos extends Fns where
  namespace clos
  open fns base
  /-- A function of `as` returning `r`, with the environment it closes over. -/
  data Closure (as : list) (+r) where
    | mk (f : Fn as r) (env : Int)
  /-- A function taking an `Int` before `as`. -/
  data Curried (as : list) (+r) where
    | curry (f : Fn [Int, *as] r)
  /-- A tuple of `ts`, which recurses through its positive list. -/
  type Tup (+ts : list)
  data Nest (+ts : list) where
    | leaf
    | node (kids : Tup [*ts, Nest ts])
  end clos

#guard (Clos.Closure.ref (e := Clos.env)).kinds == #[.list, .type]
example : Clos.Closure.mk.sig (e := Clos.env) =
    { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"f", Fns.Fn.ty (.var 0 (by decide)) (.var 1 (by decide))⟩,
        ⟨"env", Base.Int.ty⟩],
      returnType := some (Clos.Closure.ty (.var 0 (by decide)) (.var 1 (by decide))),
      distinct := by decide } := rfl
example : Clos.Curried.curry.sig (e := Clos.env) =
    { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"f", Fns.Fn.ty (.lit #[.ty Base.Int.ty, .splice 0 (by decide)])
        (.var 1 (by decide))⟩],
      returnType := some (Clos.Curried.ty (.var 0 (by decide)) (.var 1 (by decide))),
      distinct := by decide } := rfl
example : Clos.Closure.case.sig (e := Clos.env) =
    { ann := (), typeParams := #[⟨"as", .list⟩, ⟨"r", .type⟩],
      argTypes := #[⟨"scrutinee", Clos.Closure.ty (.var 0 (by decide)) (.var 1 (by decide))⟩],
      returnType := none,
      succs := #[⟨"mk", #[Fns.Fn.ty (.var 0 (by decide)) (.var 1 (by decide)), Base.Int.ty]⟩],
      distinct := by decide } := rfl
#guard (Clos.Nest.node.sig (e := Clos.env)).typeParams == #[⟨"ts", .list⟩]

/-! ### Signatures that name no type

Each signature below mentions only type variables, so its reference's cast names no type's
lemmas. -/

/-- Instructions and a constructor over type variables only. -/
public environment TyVars extends Base where
  namespace tyvars
  insn id [a] (x : a) : a
  insn pick [a b] (x : a) (y : b) : a
  insn pass [a] (x : a) (^k (y : a)) : a
  insn first [a] (*xs : a) : a
  insn run [a] (&body (x : a) : a) : a
  data Pair (+a) (+b) where
    | mk (x : a) (y : b)
  end tyvars

example : TyVars.id.sig (e := TyVars.env) =
    { ann := (), typeParams := #[⟨"a", .type⟩], argTypes := #[⟨"x", .var 0 (by decide)⟩],
      returnType := some (.var 0 (by decide)), distinct := by decide } := rfl
example : TyVars.pick.sig (e := TyVars.env) =
    { ann := (), typeParams := #[⟨"a", .type⟩, ⟨"b", .type⟩],
      argTypes := #[⟨"x", .var 0 (by decide)⟩, ⟨"y", .var 1 (by decide)⟩],
      returnType := some (.var 0 (by decide)), distinct := by decide } := rfl
example : TyVars.pass.sig (e := TyVars.env) =
    { ann := (), typeParams := #[⟨"a", .type⟩], argTypes := #[⟨"x", .var 0 (by decide)⟩],
      returnType := some (.var 0 (by decide)), succs := #[⟨"k", #[.var 0 (by decide)]⟩],
      distinct := by decide } := rfl
example : TyVars.first.sig (e := TyVars.env) =
    { ann := (), typeParams := #[⟨"a", .type⟩], argTypes := #[],
      variadic := some ⟨"xs", .each (.var 0 (by decide))⟩, returnType := some (.var 0 (by decide)),
      distinct := by decide } := rfl
example : TyVars.run.sig (e := TyVars.env) =
    { ann := (), typeParams := #[⟨"a", .type⟩], argTypes := #[],
      regions := #[⟨"body", RegionSig.of #[⟨"x", .var 0 (by decide)⟩] (.var 0 (by decide))
        (by decide)⟩],
      returnType := some (.var 0 (by decide)), distinct := by decide } := rfl
example : TyVars.Pair.mk.sig (e := TyVars.env) =
    { ann := (), typeParams := #[⟨"a", .type⟩, ⟨"b", .type⟩],
      argTypes := #[⟨"x", .var 0 (by decide)⟩, ⟨"y", .var 1 (by decide)⟩],
      returnType := some (TyVars.Pair.ty (.var 0 (by decide)) (.var 1 (by decide))),
      distinct := by decide } := rfl

section
variable {e : Env _root_.Unit} [TyVars.env ⊑ e]
example : InsnRef e TyVars.id.sig := TyVars.id
example : InsnRef e TyVars.Pair.mk.sig := TyVars.Pair.mk
end

/-! ### Constructors are instructions

Each constructor is an instruction whose signature `addData` derived: the datatype's type
parameters, by name; the payload as its arguments; the datatype at its parameters as its
result. -/

example : (Demo.Box.box.sig (e := Demo.env)).typeArgc = 1 := rfl
example : (Demo.Box.empty.sig (e := Demo.env)).typeArgc = 1 := rfl
example : (Demo.Even.zero.sig (e := Demo.env)).typeArgc = 0 := rfl
example : (Base.Except.ok.sig (e := Base.env)).typeArgc = 2 := rfl
#guard (Demo.Box.box.sig (e := Demo.env)).typeParams == #[⟨"a", .type⟩]
#guard (Demo.Box.box.sig (e := Demo.env)).argTypes.map (·.name) == #["contents"]
#guard (Demo.Box.empty.sig (e := Demo.env)).argTypes.isEmpty
#guard (Demo.Tree.node.sig (e := Demo.env)).argTypes.map (·.name) == #["kids"]
#guard (Base.Except.error.sig (e := Base.env)).typeParams == #[⟨"e", .type⟩, ⟨"a", .type⟩]
#guard !(Demo.Box.box.sig (e := Demo.env)).terminal
#guard (Demo.Box.box.sig (e := Demo.env)).succs.isEmpty &&
  (Demo.Box.box.sig (e := Demo.env)).regions.isEmpty &&
  (Demo.Box.box.sig (e := Demo.env)).variadic.isNone
-- A constructor's reference is marked with where it sits: `Odd`'s only constructor is the
-- first of its group's second member.
#guard (Demo.Odd.succO (e := Demo.env)).ctorAddr?.map (fun a => (a.dataIdx, a.idx)) ==
  some (1, 0)
#guard (Demo.Box.empty (e := Demo.env)).ctorAddr?.map (fun a => (a.dataIdx, a.idx)) ==
  some (0, 1)
#guard (Demo.add (e := Demo.env)).ctorAddr?.isNone

/-! ### Case instructions

Each datatype `T` has a terminal instruction `T.case`: `T`'s parameters as type parameters,
the scrutinee as its argument, and one successor per constructor, in declaration order,
receiving its fields.  A group's are declared after the whole group. -/

example : Demo.Box.case.name = .str (.str (.str .base "demo") "Box") "case" := rfl
example : Base.Except.case.name = .str (bn "Except") "case" := rfl
example : (Demo.Box.case.sig (e := Demo.env)).typeArgc = 1 := rfl
example : (Demo.Box.case.sig (e := Demo.env)).terminal = true := rfl
#guard (Demo.Box.case.sig (e := Demo.env)).argTypes.map (·.name) == #["scrutinee"]
#guard (Demo.Box.case.sig (e := Demo.env)).succs.map (fun p => (p.name, p.type.size)) ==
  #[("box", 1), ("empty", 0)]
#guard (Demo.Even.case.sig (e := Demo.env)).succs.map (fun p => (p.name, p.type.size)) ==
  #[("zero", 0), ("succE", 1)]
#guard (Demo.Odd.case.sig (e := Demo.env)).succs.map (·.name) == #["succO"]
#guard (Demo.Box.case (e := Demo.env)).ctorAddr?.isNone
example : (Demo.Box.case.sig (e := Demo.env)).succs.map (·.type) =
    #[#[TypeExpr.var 0 (by decide)], #[]] := by simp [Demo.Box.case.sig]
example : (Demo.Box.case.sig (e := Demo.env)).argTypes.map (·.type) =
    #[Demo.Box.ty (TypeExpr.var 0 (by decide))] := by simp [Demo.Box.case.sig]

/-! ### A function over it -/

/-- A builder generic over every refinement of `Demo`. -/
private def body {e : Env _root_.Unit} [Demo.env ⊑ e] : BuildM e _root_.Unit _root_.Unit := do
  let x ← Build.freshVal (.str .base "x") Demo.Value.ty
  let _ ← Build.startFreshBlock #[x]
  let t ← Build.emitApply (.str .base "t") Demo.Value.ty Demo.mkTuple #[x.id, x.id, x.id]
  let b ← Build.emitApply (.str .base "b") (Demo.Box.ty Demo.Value.ty) Demo.Box.box
      #[t]
  let cell ← Build.emitApply (.str .base "cell") (Base.Ref.ty (Demo.Box.ty Demo.Value.ty))
      Base.refNew
    #[b]
  let got ← Build.emitApply (.str .base "got") (Demo.Box.ty Demo.Value.ty) Base.refGet
    #[cell]
  let v ← Build.emitApply (.str .base "v") (Demo.raising.ty Demo.Value.ty) Demo.unbox
      #[got]
  let h ← Build.freshLabel "handler"
  let _ ← Build.emitApply (.str .base "s") Demo.Value.ty Demo.add #[t, x.id] #[Build.goto h]
  Build.finishBlock (.ret () v)
  let exc ← Build.freshVal (.str .base "exc") Demo.Value.ty
  Build.startBlock h #[exc]
  let r ← Build.emitApply (.str .base "r") (Demo.raising.ty Demo.Value.ty) Base.Except.error
    #[exc.id]
  Build.finishBlock (.ret () r)

private def f : Except Build.Errors (Func Demo.env _root_.Unit) :=
  Build.build (.str .base "f") (Demo.raising.ty Demo.Value.ty) () body

example : Build.Holds (Func.WF ∅) f := by decide +kernel

/-! ### Keywords

The declaration keywords are non-reserved: outside a block they are identifiers. -/

private def insn : Nat := 1
private def terminal : Nat := 2
example : insn + terminal = 3 := rfl
example : Nat := let insn := 1; let terminal := 2; insn + terminal

end Strata.Mantle.DSLTest
