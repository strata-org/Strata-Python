/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Build
public import StrataDyn.Exec
public import StrataDyn.Exec.Base
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
import StrataDyn.DSL
meta import StrataDyn.Build
meta import StrataDyn.Env.WF
meta import StrataDyn.Exec.Base
meta import StrataDyn.Exec.Run

set_option autoImplicit false

/-!
# Tags at the access

A rule names refs and closures at Lean types, and takes the tags of the types it reaches cells
and calls at.  Dyn types that share a Lean type share its tag.  The functions are written
with the builder's type handles.
-/

namespace Strata.Dyn.TagTest

open Strata.Dyn.Exec
open Strata.Dyn.Build (startFreshBlock emitConst emitApply finishBlock build FailedFunc)

/-! ## Shared tags

`Meters` and `Feet` share `Int`'s Lean type, so they share its tag: a cell made under one is
read under another, and a closure whose function takes `Meters` is called at
`Int`. -/

/-- An environment of cells of compound types, and of two types that share a Lean type. -/
public environment Tg extends Base where
  namespace tg
  open base
  insn excNew (v : Int) : Ref (Except Int Bool)
  insn excGet (c : Ref (Except Int Bool)) : Except Int Bool
  insn fnNew (f : Fn [Int, Bool] Int) : Ref (Fn [Int, Bool] Int)
  /-- Two types that share a Lean type. -/
  type Meters
  type Feet
  /-- `x` in feet. -/
  insn scale (x : Meters) : Feet
  /-- A new cell holding `x`, which a rule makes at `Int`. -/
  insn meterRef (x : Meters) : Ref Meters
  /-- Call `f`, from `Meters` to `Feet`. -/
  insn toFeet (f : Fn [Meters] Feet) (x : Meters) : Feet
  end tg

attribute [dyn_type Tg.Meters] Int
attribute [dyn_type Tg.Feet] Int

#dyn_types Tg

namespace TgRules

@[expose] public section

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasHeap σ ε]

@[dyn_sem Tg.excNew]
def excNew [TagOf σ (Except Int Bool)] (v : Int) : Sem ε E (Ref σ (Except Int Bool)) :=
  newRef (.error v)

@[dyn_sem Tg.excGet]
def excGet [TagOf σ (Except Int Bool)] (c : Ref σ (Except Int Bool)) :
    Sem ε E (Except Int Bool) :=
  readRef c

@[dyn_sem Tg.fnNew]
def fnNew [TagOf σ (FnRef σ [Int, Bool] Int)] (f : FnRef σ [Int, Bool] Int) :
    Sem ε E (Ref σ (FnRef σ [Int, Bool] Int)) :=
  newRef f

@[dyn_sem Tg.meterRef]
def meterRef [TagOf σ Int] (x : Int) : Sem ε E (Ref σ Int) := newRef x

end

@[dyn_sem Tg.scale, expose] public def scale (x : Int) : Int := 3 * x

-- `Int` interprets both: the call is checked at `Int`'s tag, which both have.
@[dyn_sem Tg.toFeet, expose]
public def toFeet {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasCall σ ε]
    [TagOf σ Int] (f : FnRef σ [Int] Int) (x : Int) : Sem ε E Int :=
  callFn f x

end TgRules

public section
#dyn_sem_table TgSem for Tg
end

-- One tag for the three Dyn types of `Int`, and for refs to them.
example : TgSem.T.tg.Meters = TgSem.T.base.Int := rfl
example : TgSem.T.tg.Feet = TgSem.T.base.Int := rfl
example : TgSem.T.base.Ref TgSem.T.tg.Meters = TgSem.T.base.Ref TgSem.T.tg.Feet := rfl
-- And a closure from `Meters` to `Feet` is one from `Int` to `Int`.
example : TgSem.interp Run
    (TgSem.T.base.Fn (.list [TgSem.T.tg.Meters]) TgSem.T.tg.Feet) = FnRef Run [Int] Int := rfl

/-- `useExc()`: a cell of an `Except` that a rule makes, read by a rule. -/
private def useExc : Except (FailedFunc Tg.env Unit Unit) {fn : Func Tg.env Unit // fn.WF} :=
  build (.str .base "useExc") (Base.Except Base.Int Base.Bool) () do
    let _ ← startFreshBlock (base := "entry")
    let k ← emitConst (.str .base "k") (.int 7)
    let c ← emitApply (.str .base "c") (Base.Ref (Base.Except Base.Int Base.Bool)) Tg.excNew.ref
      #[k]
    let v ← emitApply (.str .base "v") (Base.Except Base.Int Base.Bool) Tg.excGet.ref #[c]
    finishBlock (.ret () v)

/-- The run of `useExc`, its result read back as an `Except Int Bool`. -/
private def runExc : Option (Except Int Bool) := do
  let f ← useExc.toOption
  let m ← (Module.Raw.check ⟨.str .base "m", #[f.1], ()⟩).toOption
  (runModule TgSem.model m (.str .base "useExc") #[] 100).read? (Except Int Bool)

#guard match runExc with | some (.error 7) => true | _ => false

section
private abbrev TE := Tg.env
private def tv (n : Nat) (t : TypeExpr TE) : ValDecl TE := ⟨⟨n⟩, t⟩
private def tn (s : String) : Name := .str .base s

/-- A function of one block. -/
private def tfn (name : String) (ret : TypeExpr TE) (params : Array (ValDecl TE))
    (instrs : Array (Instruction TE Unit)) (out : Nat) : Func TE Unit :=
  let f : Func TE Unit :=
    ⟨tn name, ret, #[⟨⟨tn "entry"⟩, params, instrs, .ret () ⟨out⟩, ()⟩], #[], ()⟩
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- `m2f(x : Meters) : Feet`. -/
private def m2f : Func TE Unit :=
  tfn "m2f" Tg.Feet #[tv 0 Tg.Meters]
    #[.apply () (tv 1 Tg.Feet) Tg.scale.ref ⟨#[], rfl⟩ #[⟨0⟩] #[] #[]] 1

/-- `useMeters(x : Meters) : Feet`: a cell a rule makes at `Int`, read by the machine at
`Meters`, and `m2f` called on it through a closure at `Int`. -/
private def useMeters : Func TE Unit :=
  tfn "useMeters" Tg.Feet #[tv 0 Tg.Meters] #[
    .apply () (tv 1 (Base.Ref Tg.Meters)) Tg.meterRef.ref ⟨#[], rfl⟩ #[⟨0⟩] #[] #[],
    .apply () (tv 2 Tg.Meters) Base.refGet.ref ⟨#[.ty Tg.Meters], rfl⟩ #[⟨1⟩] #[] #[],
    .const () (tv 3 (Base.Fn [Tg.Meters] Tg.Feet)) (.func (tn "m2f")),
    .apply () (tv 4 Tg.Feet) Tg.toFeet.ref ⟨#[], rfl⟩ #[⟨3⟩, ⟨2⟩] #[] #[]] 4

/-- `useMeters 4`, on `engine`: an `Int` argument at `Meters`, whose tag is `Int`'s, and a
`Feet` result read as an `Int`. -/
private def runMeters (engine : Engine) : Option Int := do
  let m ← (Module.Raw.check ⟨tn "m", #[m2f, useMeters], ()⟩).toOption
  (runModule TgSem.model m (tn "useMeters") #[TgSem.model.arg (4 : Int)] 100
    (engine := engine)).read? Int

#guard runMeters .fused = some 12
#guard runMeters .frames = some 12

end

end Strata.Dyn.TagTest
