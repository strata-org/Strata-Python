/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
public import StrataDyn.Exec
public import StrataDyn.Exec.Base
import StrataDyn.Env.WF
import StrataDyn.DSL
meta import StrataDyn.Exec.Rules

set_option autoImplicit false

/-!
# A swap of a library loop that the check trusts

The check trusts the library loops of `endingPartials` without entering them, so a `@[csimp]`
swap of one would run code that the walk never sees; the check rejects it, as for every name it
trusts.  So does a swap of a ref's field, which the trusted heap capability's code uses.  The swap here is a deliberate test input, in a module of its own, so that it reaches no
other table.
-/

namespace Strata.Dyn.ExecTest.TrustSwapLib

open Strata.Dyn.Exec

@[expose] public section

universe u in
/-- A fold that returns its initial value, whatever the slice. -/
@[inline] unsafe def lieFoldl {α : Type u} (_f : α → Char → α) (init : α) (_s : String.Slice) : α :=
  init

universe u in
/-- `String.Slice.foldl` in proofs, and `lieFoldl` when it runs. -/
@[implemented_by lieFoldl]
def myFoldl {α : Type u} (f : α → Char → α) (init : α) (s : String.Slice) : α :=
  String.Slice.foldl f init s

/-- A true swap of a trusted library loop for code that runs differently. -/
@[csimp] theorem swapFoldl : @String.Slice.foldl = @myFoldl := rfl

end

/-- One instruction, with a rule that counts a number's characters. -/
environment TsFold extends Base where
  namespace tsFold
  open base
  insn f (x : Int) : Int
  end tsFold

#dyn_types TsFold

/-- The number of characters of `x`. -/
@[dyn_sem TsFold.f] def countChars (x : Int) : Int :=
  (toString x).toSlice.foldl (fun n _ => n + 1) 0

/-- error: the table FoldSem: rule countChars for tsFold.f reaches String.Slice.foldl (FoldSem.ops → FoldSem.impl.tsFold.f → FoldSem.rule.tsFold.f → countChars → String.Slice.foldl), which the check trusts, but the @[csimp] lemma swapFoldl swaps in myFoldl, which a run would execute instead -/
#guard_msgs in
#dyn_sem_table FoldSem for TsFold

/-! A swap of a ref's field, which the heap capability's code uses, is rejected too.  It comes
last, since it reaches every later check in this module. -/

@[expose] public section

/-- A ref's raw cell in proofs, and the same when it runs, through a swap. -/
@[implemented_by Ref.raw]
def otherRaw {σ : Type} [Store σ] {α : Type} (r : Ref σ α) : Ref.Raw σ := r.raw

/-- A true swap of a ref's field. -/
@[csimp] theorem swapRaw : @Ref.raw = @otherRaw := rfl

end

/-- One instruction, with a rule that reads a cell. -/
environment TsRaw extends Base where
  namespace tsRaw
  open base
  insn f (x : Int) : Int
  end tsRaw

#dyn_types TsRaw

/-- Makes a cell holding `x`, and reads it. -/
@[dyn_sem TsRaw.f]
def readBackRaw {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasHeap σ ε] [TagOf σ Int]
    (x : Int) : Sem ε E Int := do
  let a ← newRef (σ := σ) x
  readRef a

/-- error: the table RawSem: rule readBackRaw for tsRaw.f reaches MReq.Out (RawSem.ops → RawSem.impl.tsRaw.f → RawSem.rule.tsRaw.f → MEff → MReq.Out), which the check trusts, and swapRaw equates Ref.raw, which the trusted names' code uses, with otherRaw: no swap of it is allowed, so that code compiled later that names it runs it as defined -/
#guard_msgs in
#dyn_sem_table RawSem for TsRaw

/-! A table reaches `MReq.Out` through the base rules, so every table here now fails; the check
on a rule alone shows that a trusted library loop doesn't concern the swap of a ref's field. -/

open Lean Meta in
/-- What the check finds on `d`, as a message. -/
meta def checkDecl (d : Lean.Name) : MetaM Unit := do
  match ← notAsProved d m!"{.ofConstName d}" with
  | some m => logInfo m
  | none => logInfo "no finding"

/-- `1` if `x` is a natural number, through `String.Slice.isNat`, which the check trusts. -/
@[expose] public def natFlag (x : Int) : Int := if (toString x).toSlice.isNat then 1 else 0

/-- info: no finding -/
#guard_msgs in
#eval checkDecl ``natFlag

end Strata.Dyn.ExecTest.TrustSwapLib
