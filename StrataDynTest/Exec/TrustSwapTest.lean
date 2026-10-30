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
# A swap on a name that the check trusts

The check doesn't walk into the machine's capabilities, which the table's wrappers use, nor into
equality of refs.  A `@[csimp]` swap of one of them would run other code that the walk never
sees, so the check rejects a table that reaches a trusted name with a swap.  The swaps here are
deliberate test inputs, in a module of their own, so that they reach no other table.
-/

namespace Strata.Dyn.ExecTest.TrustSwap

open Strata.Dyn.Exec

@[expose] public section

/-- The heap capability, but a read asks for the next cell. -/
@[inline, reducible] def evilImpl {σ : Type} [Store σ] {I : Ty → Type} {W : Type} {rs : List (List Ty × Ty)} :
    @HasHeap σ _ ⟨I⟩ (MEff I σ W rs) :=
  @HasHeap.mk σ _ ⟨I⟩ (MEff I σ W rs)
    (fun t v => .new t.tag (cast t.ok.symm v))
    (fun t _ c => cast (congrArg (Ref σ) t.ok) c)
    (fun t c => .get t.tag (c.loc + 1))
    (fun t _ v => cast t.ok v)
    (fun t c v => .set t.tag c.loc (cast t.ok.symm v))
    (fun t c f => .modify t.tag c.loc fun v => cast t.ok.symm (f (cast t.ok v)))

/-- The heap capability in proofs, and `evilImpl` when it runs. -/
@[implemented_by evilImpl, reducible]
def evilMreq {σ : Type} [Store σ] {I : Ty → Type} {W : Type} {rs : List (List Ty × Ty)} :
    @HasHeap σ _ ⟨I⟩ (MEff I σ W rs) := HasHeap.mreq

/-- A true swap of the heap capability for code that runs differently. -/
@[csimp] theorem swapMreq : @HasHeap.mreq = @evilMreq := rfl

end

/-- One instruction, with a rule that reads a cell. -/
environment TsHeap extends Base where
  namespace tsHeap
  open base
  insn f (x : Int) : Int
  end tsHeap

#dyn_types TsHeap

/-- Makes a cell holding `x`, and reads it. -/
@[dyn_sem TsHeap.f]
def readBack {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasHeap σ ε] [TagOf σ Int]
    (x : Int) : Sem ε E Int := do
  let a ← newRef (σ := σ) x
  readRef a

/-- error: the table HeapSem: rule readBack for tsHeap.f reaches HasHeap.mreq (HeapSem.ops → HeapSem.impl.tsHeap.f → HeapSem.rule.tsHeap.f → HasHeap.mreq), which the check trusts, but the @[csimp] lemma swapMreq swaps in evilMreq, which a run would execute instead -/
#guard_msgs in
#dyn_sem_table HeapSem for TsHeap

@[expose] public section

/-- Equality of refs in proofs, and the same equality when it runs, through a swap. -/
@[implemented_by instDecidableEqRef]
def otherEq {σ : Type} [Store σ] {α : Type} : DecidableEq (Ref σ α) := instDecidableEqRef

/-- A true swap of equality of refs. -/
@[csimp] theorem swapEq : @instDecidableEqRef = @otherEq := rfl

end

/-- One instruction, with a rule that compares two refs. -/
environment TsEq extends Base where
  namespace tsEq
  open base
  insn f (a b : Ref Int) : Bool
  end tsEq

#dyn_types TsEq

/-- Whether two refs are equal. -/
@[dyn_sem TsEq.f] def compare {σ : Type} [Store σ] (a b : Ref σ Int) : Bool := a = b

/-- error: the table EqSem: rule compare for tsEq.f reaches instDecidableEqRef (EqSem.ops → EqSem.impl.tsEq.f → EqSem.rule.tsEq.f → compare → instDecidableEqRef), which the check trusts, but the @[csimp] lemma swapEq swaps in otherEq, which a run would execute instead -/
#guard_msgs in
#dyn_sem_table EqSem for TsEq

/-! The check trusts Lean's library by its modules' names, so a directory of the search path,
other than Lean's own, that holds a module named `Init`, `Std` or `Lean` is reported. -/

/-- `strayLibraryDirs` on paths given as strings, with `present` the files that exist. -/
meta def stray (paths present : List String) : List String :=
  (strayLibraryDirs "/lean/lib" (paths.map .mk) fun f => present.contains f.toString).map (·.toString)

#guard stray ["/lean/lib", "/pkg/lib", "/evil/lib"]
    ["/lean/lib/Init", "/lean/lib/Lean.olean", "/evil/lib/Std.olean"] = ["/evil/lib"]
#guard stray ["/lean/lib", "/pkg/lib"] ["/lean/lib/Init", "/pkg/lib/Strata"] = []
#guard stray ["/evil/lib"] ["/evil/lib/Init"] = ["/evil/lib"]

/-! The check on a declaration alone, for code that only a table's own declarations may hold. -/

open Lean Meta in
/-- What the check finds on `d`, as a message. -/
meta def checkDecl (d : Lean.Name) : MetaM Unit := do
  match ← notAsProved d m!"{.ofConstName d}" with
  | some m => logInfo m
  | none => logInfo "no finding"

/-- Region 0 of an operation, as a handle built outside a table's wrappers. -/
@[expose] public def slotOutside {σ : Type} [Store σ] {I : Ty → Type} {W : Type} :
    Region (MEff I σ W [([], Ty.app 9 [])]) [] (I (Ty.app 9 [])) :=
  Region.slot ⟨0, by decide⟩ (fun _ => Args.nil)

/-- info: slotOutside reaches Region.slot (slotOutside → Region.slot), the machine's own capability, which only the declarations a table command emits may build: its requests name cells, closures or regions that only the machine may choose -/
#guard_msgs in
#eval checkDecl ``slotOutside

/-- The location a read request names, through the matcher of `MReq.Out`, which the check trusts
only as `MReq.Out`. -/
@[expose] public def viaOutMatch {I : Ty → Type} {rs : List (List Ty × Ty)} (q : MReq I rs) : Nat :=
  MReq.Out.match_1 (motive := fun _ => Nat) q
    (fun _ _ => 0) (fun _ _ _ _ => 0) (fun _ _ => 0) (fun _ l => l) (fun _ _ _ => 0)
    (fun _ _ _ => 0) (fun _ _ _ _ _ => 0)

/-- info: viaOutMatch reaches MReq.bind (viaOutMatch → MReq.Out.match_1 → MReq.bind), which builds or takes apart a machine request: a request holds locations, so only the handles that a table passes to a rule may build one, and only the machine reads it -/
#guard_msgs in
#eval checkDecl ``viaOutMatch

@[expose] public section

/-- Equality of closures, the same as the trusted one. -/
def otherFnEq {σ : Type} [Store σ] {as : List Type} {r : Type} : DecidableEq (FnRef σ as r) :=
  instDecidableEqFnRef

/-- A true equation of the trusted equality of closures with `otherFnEq`, without `@[csimp]`: a
`local` swap may have used it. -/
theorem swapFnEq : @instDecidableEqFnRef = @otherFnEq := rfl

/-- Whether two closures are equal. -/
def cmpFn {σ : Type} [Store σ] (f g : FnRef σ [Int] Int) : Bool := f = g

end

/-- info: cmpFn reaches instDecidableEqFnRef (cmpFn → instDecidableEqFnRef), which the check trusts, but swapFnEq equates it with otherFnEq, so a @[csimp] swap may run otherFnEq instead -/
#guard_msgs in
#eval checkDecl ``cmpFn

/-! The request ban covers every constructor of `MReq`, read from the environment. -/

open Lean in
/-- info: [Strata.Dyn.Exec.MReq.region,
 Strata.Dyn.Exec.MReq.call,
 Strata.Dyn.Exec.MReq.new,
 Strata.Dyn.Exec.MReq.get,
 Strata.Dyn.Exec.MReq.set,
 Strata.Dyn.Exec.MReq.modify,
 Strata.Dyn.Exec.MReq.bind,
 Strata.Dyn.Exec.MReq.rec,
 Strata.Dyn.Exec.MReq.casesOn,
 Strata.Dyn.Exec.MReq.recOn] -/
#guard_msgs in
#eval show CoreM Unit from do logInfo m!"{requestConsts (← getEnv)}"

/-! A swap of a request's constructor, which the trusted names' code uses, is rejected too.  It
comes last, since it reaches every later check in this module. -/

@[expose] public section

/-- The code that runs for a read request: a read of the next cell. -/
@[inline] def nextGet {I : Ty → Type} {rs : List (List Ty × Ty)} (t : Ty) (l : Nat) : MReq I rs :=
  MReq.get t (l + 1)

/-- A read request in proofs, and `nextGet` when it runs. -/
@[implemented_by nextGet]
def otherGet {I : Ty → Type} {rs : List (List Ty × Ty)} (t : Ty) (l : Nat) : MReq I rs :=
  MReq.get t l

/-- A true swap of a request's constructor, which the trusted heap capability's code uses. -/
@[csimp] theorem swapGet : @MReq.get = @otherGet := rfl

end

/-- One instruction, with a rule that reads a cell. -/
environment TsGet extends Base where
  namespace tsGet
  open base
  insn f (x : Int) : Int
  end tsGet

#dyn_types TsGet

/-- Makes a cell holding `x`, and reads it. -/
@[dyn_sem TsGet.f]
def readBackGet {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasHeap σ ε] [TagOf σ Int]
    (x : Int) : Sem ε E Int := do
  let a ← newRef (σ := σ) x
  readRef a

/-- error: the table GetSem: rule readBackGet for tsGet.f reaches MReq.Out (GetSem.ops → GetSem.impl.tsGet.f → GetSem.rule.tsGet.f → MEff → MReq.Out), which the check trusts, and swapGet equates MReq.get, which the trusted names' code uses, with otherGet: no swap of it is allowed, so that code compiled later that names it runs it as defined -/
#guard_msgs in
#dyn_sem_table GetSem for TsGet

end Strata.Dyn.ExecTest.TrustSwap
