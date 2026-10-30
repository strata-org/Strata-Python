/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Demo
import StrataDyn.Env.WF
import StrataDyn.DSL
meta import StrataDynTest.Exec.Demo

set_option autoImplicit false

/-!
# Coverage and the table

`#dyn_coverage` on `Demo` and `DemoChild`; `#dyn_sem_table` for `DemoChild`, whose
wrappers reduce on symbolic operands; and the trace of a small table.
-/

namespace Strata.Dyn.ExecTest

open Strata.Dyn.Exec

/-! ## Coverage -/

/--
info: type demo.Int ↦ Int
type demo.Bool ↦ Bool
type demo.Seq ↦ Array
type demo.Box ↦ Demo.Box.Val (generated)
type demo.IntList ↦ Demo.IntList.Val (generated)
op demo.box: derived constructor of demo.Box
op demo.empty: derived constructor of demo.Box
op demo.Box.case: derived case of demo.Box
op demo.nil: derived constructor of demo.IntList
op demo.cons: derived constructor of demo.IntList
op demo.IntList.case: derived case of demo.IntList
op demo.add ↦ Rules.add (pure)
op demo.div ↦ Rules.div
op demo.divBig ↦ Rules.divBig
op demo.pick ↦ Rules.pick (pure)
op demo.unbox ↦ Rules.unbox
op demo.sum ↦ Rules.sum (pure)
op demo.pow ↦ Rules.pow
op demo.isqrt: missing
op demo.loop ↦ Rules.loop
op demo.branch ↦ Rules.branch
1 missing, and 0 in ancestors
-/
#guard_msgs in
#dyn_coverage Demo

/--
info: op child.neg ↦ Rules.neg (pure)
op child.abs: missing
1 missing, and 1 in ancestors
-/
#guard_msgs in
#dyn_coverage DemoChild

/-! ## The table -/

/-- info: DemoSem: no rule for demo.isqrt, child.abs -/
#guard_msgs in
#dyn_sem_table DemoSem for DemoChild

namespace DemoSem

variable (σ : Type) [Store σ]

/-- The interpretation reduces on codes with variables, at any token. -/
example : interp σ T.demo.Int = Int := rfl
example (a : Ty) : interp σ (T.demo.Box a) = DBox (interp σ a) := rfl
example (a : Ty) : interp σ (T.demo.Seq (T.demo.Box a)) = Array (DBox (interp σ a)) := rfl

-- The codes are distinct.
#guard T.demo.Seq T.demo.Int ≠ T.demo.Seq T.demo.Bool

/-- Each wrapper reduces on symbolic operands. -/
example (a b : Int) : rule.demo.add σ a b = a + b := rfl
example (a : Int) :
    rule.demo.div σ a (0 : Int) = .stop (.jump (.exit (.here (.cons (1 : Int) .nil)))) := rfl
example : rule.demo.divBig σ (200 : Int) (3 : Int) =
    .stop (.jump (.exit (.there (.here (.cons (66 : Int) (.cons (2 : Int) .nil)))))) := rfl
example (t : Ty) (x y : interp σ t) : rule.demo.pick σ t true x y = x := rfl
example (t : Ty) (x : interp σ t) : rule.demo.unbox σ t (.box x) = .ret x := rfl
example (t : Ty) : rule.demo.unbox σ t .empty = .stop (.jump (.exit (.here .nil))) := rfl
example (x y : Int) : rule.demo.sum σ #[x, y] = 0 + x + y := rfl
example (a b : Int) : rule.demo.pow σ a b = .stop (.fault (.gap "demo.pow")) := rfl
example : rule.demo.branch σ false = .stop (.jump (.exit (.there (.here .nil)))) := rfl
example (a : Int) : rule.child.neg σ a = -a := rfl

/-- A region's wrapper asks the machine to run region `0` on the rule's argument. -/
example (t : Ty) :
    rule.demo.loop σ t = .vis (.region ⟨0, Nat.zero_lt_one⟩ (.cons (0 : Int) .nil)) .ret :=
  rfl

/-- Derived constructors and case instructions. -/
example (t : Ty) (x : interp σ t) : rule.demo.box σ t x = .box x := rfl
example (h : Int) (tl : DList) : rule.demo.cons σ h tl = .cons h tl := rfl
example (t : Ty) (x : interp σ t) : rule.demo.Box.case σ t (.box x) = .here (.cons x .nil) := rfl
example (h : Int) (tl : DList) :
    rule.demo.IntList.case σ (.cons h tl) = .there (.here (.cons h (.cons tl .nil))) := rfl

/-- `simp` unfolds a wrapper into its rule. -/
example (a b : Int) (hb : b ≠ 0) : rule.demo.div σ a b = .ret (a / b) := by
  simp [rule.demo.div, Rules.div, hb]

-- A wrapper, as the goal shows it.
/--
info: private def Strata.Dyn.ExecTest.DemoSem.rule.demo.div : (σ : Type) →
  [inst : Store σ] →
    Fn (interp σ) (Tree (interp σ) σ (W σ) [] [[T.demo.Int]] Empty (interp σ T.demo.Int)) [T.demo.Int, T.demo.Int] :=
fun σ [Store σ] a0 a1 => Rules.div a0 a1 { exit := fun p0 => Out.exit (Exit.here (Args.cons p0 Args.nil)) }
-/
#guard_msgs in
#print rule.demo.div

-- The table lists every implemented instruction, with its shape.
#guard ops.toList.map (·.1) = [Demo.Box.box.name, Demo.Box.empty.name, Demo.Box.case.name,
    Demo.IntList.nil.name, Demo.IntList.cons.name, Demo.IntList.case.name, Demo.add.name,
    Demo.div.name, Demo.divBig.name, Demo.pick.name, Demo.unbox.name, Demo.sum.name,
    Demo.pow.name, Demo.loop.name, Demo.branch.name, DemoChild.neg.name]
#guard (ops.toList.find? (·.1 == Demo.unbox.name)).bind (fun (_, o) =>
      if h : o.typeArgc = 1 then some (o.shape (h ▸ #v[T.demo.Int])) else none) =
    some { args := [T.demo.Box T.demo.Int], ret := some T.demo.Int, succs := [[]] }

end DemoSem

/-! ## The trace -/

public section

/-- One type and one raising instruction. -/
environment Tiny where
  namespace tiny
  type Nat
  insn pred (n : Nat) (^zero) : Nat
  end tiny

attribute [dyn_type Tiny.Nat] Nat

/-- `n - 1`, or `^zero` if `n` is `0`. -/
@[expose] public def tinyPred {ε : Eff} {E : Type} (n : Nat) (zero : Target E []) : Sem ε E Nat :=
  if n = 0 then jump zero () else pure (n - 1)

attribute [dyn_sem Tiny.pred] tinyPred

/--
info: @[expose]
public def typeNames : Array Strata.Dyn.Name :=
  #[Strata.Dyn.Name.str (Strata.Dyn.Name.str Strata.Dyn.Name.base "base") "Ref",
    Strata.Dyn.Name.str (Strata.Dyn.Name.str Strata.Dyn.Name.base "base") "Fn",
    Strata.Dyn.Name.str (Strata.Dyn.Name.str Strata.Dyn.Name.base "tiny") "Nat"]
---
info: @[expose, reducible]
public def H : (σ : Type) → [Store σ] → Nat → List Type → Type := fun (σ : Type) [Store σ] h as =>
  match h, as with
  | 2, [] => Nat
  | _, _ => Empty
---
info: @[expose, reducible]
public def interp : Interp := fun (σ : Type) [Store σ] => Ty.decode σ (H σ)
---
info: @[expose, reducible]
public def W : World := fun (σ : Type) [Store σ] => Unit
---
info: @[expose, reducible]
public def T.tiny.Nat : Ty :=
  Ty.app 2 []
---
info: @[expose]
public def decode : Interp :=
  interp
---
info: @[expose]
public instance tagOf.ref : ∀ (σ : Type) [Store σ], @TagCon σ _ (Decode.mk (decode σ)) (Ref σ) :=
  fun (σ : Type) [Store σ] =>
  letI : Decode σ := Decode.mk (decode σ);
  ⟨fun tA => ⟨Ty.app 0 [tA.tag], congrArg (Ref σ) tA.ok⟩⟩
---
info: @[expose]
public instance tagOf.fn :
    ∀ (σ : Type) [Store σ] {as : List Type} {r : Type} [@SigOf σ _ (Decode.mk (decode σ)) as r],
      @TagOf σ _ (Decode.mk (decode σ)) (FnRef σ as r) :=
  fun (σ : Type) [Store σ] {as r} [s : _] =>
  letI : Decode σ := Decode.mk (decode σ);
  ⟨Ty.app 1 [Ty.list s.sig.1, s.sig.2], (Ty.decode_fn σ (H σ) _ _).trans (congr (congrArg (FnRef σ) s.ok.1) s.ok.2)⟩
---
info: @[expose]
public instance tagOf.h2 : ∀ (σ : Type) [Store σ], @TagOf σ _ (Decode.mk (decode σ)) Nat := fun (σ : Type) [Store σ] =>
  letI : Decode σ := Decode.mk (decode σ);
  ⟨Ty.app 2 [], rfl⟩
---
info: @[expose]
public def rule.tiny.pred :
    ∀ (σ : Type) [Store σ], Fn (interp σ) (Tree (interp σ) σ (W σ) [] [[]] Empty (interp σ T.tiny.Nat)) [T.tiny.Nat] :=
  fun (σ : Type) [Store σ] a0 =>
  @tinyPred (MEff (interp σ) σ (W σ) []) (Out (interp σ) [[]] Empty) a0
    (Target.mk fun _ => Out.exit (Exit.here Args.nil))
---
info: @[expose]
public def impl.tiny.pred : OpImpl interp W :=
  { typeArgc := 0, shape := fun _ => Shape.mk [T.tiny.Nat] none (some T.tiny.Nat) [[]] [],
    fn := fun (σ : Type) [Store σ] _ => Impl.sem (rule.tiny.pred σ) }
---
info: @[expose]
public def ops : Array (Strata.Dyn.Name × OpImpl interp W) :=
  #[(Strata.Dyn.Name.str (Strata.Dyn.Name.str Strata.Dyn.Name.base "tiny") "pred", impl.tiny.pred)]
---
info: @[expose]
public def w0 : (σ : Type) → [Store σ] → W σ := fun (σ : Type) [Store σ] => default
---
info: @[expose, reducible]
public def table : Table :=
  { typeNames := typeNames, interp := interp, W := W, w0 := w0, ops := ops }
-/
#guard_msgs in
#dyn_sem_table TinySem for Tiny (trace := true)

end

end Strata.Dyn.ExecTest
