/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Sem

set_option autoImplicit false

/-!
# Helpers that the check sees from another module

`RuleErrorTest` and `TableCheckTest` give rules over these.  A `module` file
sees another module's unexposed definitions as axioms, so the check can see nothing behind
`hiddenLie`, and rejects it.  `shownDouble` is exposed, so the check sees through it.  Some
helpers here are deliberate test inputs that the check must reject: they use `sorry` or a false
swap lemma.
-/

namespace Strata.Dyn.ExecTest.Helpers

/-- The running code of `lieRef`: one more than its definition. -/
public def lieImpl (x : Int) : Int := x + 1

/-- `x` in the logic, and `x + 1` when it runs. -/
@[implemented_by lieImpl] public def lieRef (x : Int) : Int := x

/-- A helper whose body this module does not expose, over code that runs differently. -/
public def hiddenLie (x : Int) : Int := lieRef x

/-- A helper whose body this module exposes. -/
@[expose] public def shownDouble (x : Int) : Int := 2 * x

/-- The compiled code of `myRevH`: it drops everything. -/
@[expose] public def lieRevH (_xs : Array Int) : Array Int := #[]
/-- `xs` reversed, run as `lieRevH`. -/
@[implemented_by lieRevH, expose] public def myRevH (xs : Array Int) : Array Int := xs.reverse
/-- `xs` reversed. -/
@[expose] public def revH (xs : Array Int) : Array Int := xs.reverse
/-- `revH` is `myRevH`: a lemma that a swap in this module may use. -/
public theorem revH_eq_myRevH : @revH = @myRevH := by funext xs; rfl

section
attribute [local csimp] revH_eq_myRevH
/-- `xs` reversed, compiled here with the local swap of `revH` for `myRevH`, so it runs
`lieRevH`.  The lemma is public, so a module that imports this one follows the swap. -/
@[expose] public def swappedHere (xs : Array Int) : Array Int := revH xs
end

/-- The compiled code of `myRevB`: it drops everything. -/
@[expose] public def lieRevB (_xs : Array Int) : Array Int := #[]
/-- `xs` reversed, run as `lieRevB`. -/
@[implemented_by lieRevB, expose] public def myRevB (xs : Array Int) : Array Int := xs.reverse
/-- `xs` reversed. -/
@[expose] public def revB (xs : Array Int) : Array Int := xs.reverse
/-- `revB` is `myRevB`, privately: a module that imports this one can't see the lemma. -/
private theorem revB_eq_myRevB : @revB = @myRevB := by funext xs; rfl

/-- The code that runs for `myQ`: `x + 1000`; its unused parameter gives it a reduced-arity
version, `lieQ._redArg`. -/
@[expose] public def lieQ (x : Int) (_n : Nat) : Int := x + 1000
/-- `x` in the logic, run as `lieQ`. -/
@[implemented_by lieQ, expose] public def myQ (x : Int) (n : Nat) : Int := x + 0 * n
/-- `x`. -/
@[expose] public def pQ (x : Int) (n : Nat) : Int := x + 0 * n
/-- `pQ` is `myQ`, privately. -/
private theorem pQ_eq_myQ : @pQ = @myQ := rfl

section
attribute [local csimp] revB_eq_myRevB pQ_eq_myQ
/-- `xs` reversed, compiled here as `lieRevB xs`: a rule that inlines it shows the swap in its own
compiled code. -/
@[expose] public def swappedB (xs : Array Int) : Array Int := revB xs
/-- `x`, compiled here as a call of `lieQ._redArg`. -/
@[expose] public def swappedQ (x : Int) : Int := pQ x 0
end

/-- The code that runs for `myRd`: `x + 1000`. -/
@[expose] public def lieRd (x : Int) (_n : Nat) : Int := x + 1000
/-- `x` in the logic, run as `lieRd`; its unused parameter gives it a reduced-arity version. -/
@[implemented_by lieRd, expose] public def myRd (x : Int) (n : Nat) : Int := x + 0 * n
/-- `x`. -/
@[expose] public def pRd (x : Int) (n : Nat) : Int := x + 0 * n
/-- `pRd` is `myRd`. -/
public theorem pRd_eq_myRd : @pRd = @myRd := rfl

section
attribute [local csimp] pRd_eq_myRd
/-- `x` in the logic, compiled here as a call of `lieRd`'s reduced-arity version. -/
@[expose] public def swappedRd (x : Int) : Int := pRd x 0
end

/-- The compiled code of `myRevP`: it drops everything. -/
@[expose] public def lieRevP (_xs : Array Int) : Array Int := #[]
/-- `xs` reversed, run as `lieRevP`. -/
@[implemented_by lieRevP, expose] public def myRevP (xs : Array Int) : Array Int := xs.reverse
/-- `xs` reversed. -/
@[expose] public def revP (xs : Array Int) : Array Int := xs.reverse
/-- `revP` is `myRevP`, privately: a module that imports this one can't see the lemma. -/
private theorem revP_eq_myRevP : @revP = @myRevP := by funext xs; rfl

section
attribute [local csimp] revP_eq_myRevP
/-- `xs` reversed, compiled here with the private swap of `revP` for `myRevP`, so it runs
`lieRevP`; a caller doesn't inline it, so a module that imports this one sees neither the
lemma nor the compiled code. -/
@[expose, noinline] public def swappedHereNI (xs : Array Int) : Array Int := revP xs
end

/-- The identity. -/
@[expose] public def fPv (x : Int) : Int := x
/-- `x + 100`. -/
@[expose] public def gPv (x : Int) : Int := x + 100
set_option warn.sorry false in
/-- A false equation, private to this module, so a module that imports this one can't see it. -/
private theorem fPv_eq_gPv : @fPv = @gPv := sorry

section
attribute [local csimp] fPv_eq_gPv
/-- `fPv x + gPv 0 - 100`, compiled here as `gPv x + gPv 0 - 100` by the private swap. -/
@[expose] public def privSwapped (x : Int) : Int := fPv x + gPv 0 - 100
end

section
open Strata.Dyn.Exec
variable {ε : Eff} {E : Type}

/-- `semanticGap`. -/
@[expose] public def gapP (x : Int) : Sem ε E Int := semanticGap s!"{x}"
/-- `semanticGap` too, but its code names `Fault.badCell` on a branch that never runs. -/
@[expose] public def gapOrBadCellP (x : Int) : Sem ε E Int :=
  if x = x then semanticGap s!"{x}" else .stop (.fault (.badCell 0))
/-- `gapP` is `gapOrBadCellP`, privately: a module that imports this one can't see the lemma. -/
private theorem gapP_eq_gapOrBadCellP : @gapP = @gapOrBadCellP := by
  funext ε E x
  simp [gapP, gapOrBadCellP]

attribute [local csimp] gapP_eq_gapOrBadCellP
/-- `semanticGap`, compiled here as `gapOrBadCellP` by the private swap; a caller doesn't inline
it, so a module that imports this one sees neither the lemma nor the compiled code. -/
@[expose, noinline] public def faultSwappedNI (x : Int) : Sem ε E Int := gapP x
end

/-- A type whose derived `BEq` this module does not expose. -/
public inductive Shade where
  | light | dark
  deriving BEq

@[expose] public section
/-- A type whose derived `BEq` this module exposes. -/
inductive Tone where
  | low | high
  deriving BEq
end

/-- `n` counted down to `0`: a recursive helper this module does not expose. -/
public def countDown : Nat → Nat
  | 0 => 0
  | n + 1 => countDown n

/-- A helper that stops with a fault that only the machine reports. -/
@[expose] public def stopBadCell {ε : Strata.Dyn.Exec.Eff} {E : Type} : Strata.Dyn.Exec.Sem ε E Int :=
  .stop (.fault (.badCell 0))

end Strata.Dyn.ExecTest.Helpers
