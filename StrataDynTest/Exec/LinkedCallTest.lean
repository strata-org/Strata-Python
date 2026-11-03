/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Call
public import StrataDyn.Exec.CertLink
public import StrataDyn.Exec.Safety
public import StrataDyn.Examples.While.Elab
public import StrataDyn.Examples.While.Lower
public import StrataDynTest.Exec.FrameTest
import StrataDyn.Env.WF
-- `#guard` runs the lowering, the linker, the checks and the engine as compiled code.
meta import StrataDyn.Exec.Call
meta import StrataDyn.Exec.CertLink
meta import StrataDyn.Examples.While.Lower
meta import StrataDynTest.Exec.FrameTest
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The frame theorem for a call, along every run of functions that `link` makes

`caller()`, a While function, makes a `Cell` `a` holding `1` and a `ListRef` `l`, a cell holding
the empty `IntList`, then calls `store(a, 7)`, which writes `7` into `a` and returns what `a`
holds.  The caller holds `l` and does not pass it.  Both functions go through `lower` and `link`
against While's table, whose rules are certified.

Run from the engine's start, an empty heap and the initial world, on no arguments, every run of
`caller` keeps every cell that holds an `IntList` at a pending call whose callee's store holds
only units, `Int`s and refs of `Int`s (`IntOnly`), along the callee's run until the caller resumes
(`call_keeps_unpassed`).  Every hypothesis of the frame theorem for a call is discharged from the
caller's start: the run invariant holds there (`inv_startCore_of`, from `Snapshot.ok_initial`)
and at the call (`frame_call_of_run`), which makes the callee's roots well tagged and its frame
one of the run.  A cell that holds an `IntList` at the call is in the heap there, and it is not
reached from the callee's roots, which name only cells that hold an `Int` in the typing of the
heap at the call (`unpassed_unreached`).  `l` holds an `IntList` so that this follows from the
tags of the callee's store, without running the code.

The run does reach such a call: after eight steps it is at the pending call of `store`, the tags
of the callee's store pass `IntOnly`, and cell `1`, the one `l` names, is the only cell that holds
an `IntList` there; the run is at no other call (`#guard` below).  The heap at the start is empty,
so the frame theorem from the caller's start says nothing of cell `1`: the run allocates it.  The
run changes cell `0` and keeps cell `1` (`#guard` below).

The axioms of the main theorems are pinned.
-/

namespace Strata.Dyn.ExecTest.LinkedCallTest

open Strata.Dyn.Exec
open Strata.Dyn.ExecTest.FrameTest (M A acct_int)

@[expose] public section

/-- `store(c, v)` writes `v` into the cell `c` and returns what `c` holds; `caller()` makes the
cells `a` and `l`, calls `store(a, 7)` and does not pass `l`. -/
def prog : While.Ast.Program := #while
  fun store(c : Cell, v : Int) : Int {
    *c := v;
    return *c;
  }
  fun caller() : Int {
    var a : Cell := wcell(1);
    var l : ListRef := ref nil;
    return store(a, 7);
  }
#end

/-- `lm` is what `link` makes, against While's table, of the module that `prog` lowers to. -/
def Linked (lm : LModule M) : Prop :=
  ∃ m, While.lower prog = .ok m ∧ link WhileSem.model m = .ok lm

/-- `IntList`'s tag. -/
abbrev listT : Ty := .app 10 []

/-- The cells of `T` that hold an `Int`. -/
def intCells (T : Typing) : Typing where
  cell l := if T.cell l = some M.int then some M.int else none

/-- A value of tag `Int` holds no ref. -/
private theorem acct_of_int {d : Dyn M.interp} (h : d.1 = M.int) : A.acct d.1 d.2 = [] := by
  obtain ⟨t, x⟩ := d
  dsimp only at h
  subst h
  exact acct_int x

/-- Whether `t` is `Int`, a ref of an `Int` or the unit.  A value of such a tag names no cell, or
one cell that holds an `Int`. -/
def IntOnly (t : Ty) : Bool := t == M.int || t == Ty.ref M.int || t == M.unit

/-- **The callee's roots do not reach a cell that holds an `IntList`.**  At a pending call whose
callee's store holds only values whose tags pass `IntOnly`, where the run invariant holds at a
typing `T₁`, the callee's store and the world name only cells that hold an `Int` in `T₁`, and so
reach only those.  `T₁` types the heap, so a cell that holds an `IntList` there is not one of
them. -/
theorem unpassed_unreached {Q : Nat → Prop} {heap₀ : Heap M} {T₁ : Typing} {c : Core M}
    {g : Frame M} {w : Wait M} {drawn : Nat} (htags : ∀ d ∈ g.env, IntOnly d.1)
    (hi : A.Inv Q heap₀ T₁ ⟨c, .call g w, drawn, ()⟩) {l : Nat} {xs : M.interp listT}
    (hl : c.heap.cells[l]? = some ⟨listT, xs⟩) :
    ¬ ReachesCell A c.heap (frameRoots A g c.world) l := by
  have hH : A.HeapOK T₁ c.heap := hi.1.heap
  have hg := hi.2.1
  have hS : A.HeapOK (intCells T₁) c.heap := {
    cell := fun l t ht => by
      simp only [intCells] at ht
      split at ht
      · next hint =>
        cases ht
        obtain ⟨hl₁, ht₁, -⟩ := hH.cell l _ hint
        refine ⟨hl₁, ht₁, ?_⟩
        rw [Accounts.DynOK, Accounts.ValOK, acct_of_int ht₁]
        exact Typing.allValid_nil _
      · cases ht
    caps := fun _ _ h => nomatch h }
  have hroots : (intCells T₁).AllValid (frameRoots A g c.world) := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨d, hd, hp⟩ := List.mem_flatMap.mp hp
      have hd := Array.mem_toList_iff.mp hd
      have h₁ := hg.env d hd p hp
      have ht := htags d hd
      obtain ⟨t, x⟩ := d
      simp only [IntOnly, Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with (rfl | rfl) | rfl
      · rw [acct_int] at hp
        exact nomatch hp
      · rw [A.ref] at hp
        obtain rfl := List.mem_singleton.mp hp
        show (if T₁.cell _ = some M.int then some M.int else none) = some M.int
        simp only [show T₁.cell _ = some M.int from h₁, ↓reduceIte]
      · exact nomatch hp
    · exact nomatch hp
  have hnone : (intCells T₁).cell l = none := by
    show (if T₁.cell l = some M.int then some M.int else none) = none
    split
    · next hint =>
      obtain ⟨hl₁, ht₁, -⟩ := hH.cell l _ hint
      obtain ⟨_, he⟩ := Array.getElem?_eq_some_iff.mp hl
      rw [he] at ht₁
      exact nomatch ht₁
    · rfl
  rintro ⟨t, hr⟩
  have hv : (intCells T₁).cell l = some t := hS.valid_of_reachable hroots hr
  rw [hnone] at hv
  exact nomatch hv

/-- **The cells that hold an `IntList` at a call that does not pass them are kept by the call,
along every run from the engine's start.**  Run from an empty heap and the initial world, on no
arguments, every run of the linked `caller` that is at a pending call after `n` steps, whose
callee's store holds only values whose tags pass `IntOnly`, has a callee's run along which it
keeps every cell that holds an `IntList` in the heap at the call (`CallKeeps`): as it was at the
call, at every configuration until the callee returns, at the end if the run ends there, and when
the caller resumes.  Those cells are allocated by the run, after its start.  The proof does not
look at the code of `caller` or `store`. -/
theorem call_keeps_unpassed {lm : LModule M} (hl : Linked lm) (hwf : WF lm) {B : Ty}
    {c : Core M} {hc : CoreOK lm B c} (hst : startCore hwf 1 [] = .ok ⟨B, c, hc⟩)
    (r : RunFrom hwf ⟨c, .exec, 0, ()⟩ hc) {n : Nat} {c₁ : Core M} {g : Frame M} {w : Wait M}
    {drawn : Nat} {h : StateOK lm B ⟨c₁, .call g w, drawn, ()⟩} (hn : r.cfg n = .running ⟨_, h⟩)
    (htags : ∀ d ∈ g.env, IntOnly d.1) :
    ∃ r₀, CalleeRun (r.drop n hn) r₀ ∧
      CallKeeps (fun l => ∃ xs : M.interp listT, c₁.heap.cells[l]? = some ⟨listT, xs⟩)
        (r.drop n hn) r₀ := by
  obtain ⟨_, -, hl⟩ := hl
  have hR := link_rulesOK WhileCert.certified hl
  obtain ⟨_, hH, hw⟩ := Snapshot.ok_initial (A := A) rfl
  exact frame_call_of_run hR (Q := fun _ => False) (fun _ h => h.elim)
    (inv_startCore_of hR hst hH (fun _ h => h.elim) hw fun _ hd => absurd hd List.not_mem_nil)
    r hn (fun _ _ hi _ ⟨_, hl⟩ =>
      ⟨(Array.getElem?_eq_some_iff.mp hl).1, unpassed_unreached htags hi hl⟩)

/-- The linked module of `prog`, if it lowers and links. -/
def linked : Option (LModule M) := do
  let m ← (While.lower prog).toOption
  (link WhileSem.model m).toOption

-- `store` is function `0`, on a `Cell` and an `Int`, and `caller` is function `1`, on nothing.
#guard (linked.map fun lm => lm.funcs.toList.map fun g => (nameStr g.name, g.params)) ==
  some [("store", [Ty.ref M.int, M.int]), ("caller", [])]

/-- The locations of the cells of `heap` that hold an `IntList`. -/
def listCells (heap : Heap M) : List Nat :=
  (List.range heap.cells.size).filter fun l => (heap.cells[l]?.map (·.1)) == some listT

/-- The linked `caller`'s run from the engine's start on no arguments, under the oracle that
always chooses `0`, after `k` steps, if it is at a pending call: the callee's name, whether every
tag of the callee's store passes `IntOnly`, and the locations of the cells that hold an `IntList`
in the heap at the call. -/
def callAt (k : Nat) : Option (String × Bool × List Nat) :=
  match linked with
  | none => none
  | some lm =>
    match hw : checkModule lm with
    | .error _ => none
    | .ok () =>
      match startCore (m := lm) hw 1 [] with
      | .error _ => none
      | .ok ⟨_, c, hc⟩ =>
        match trace hw (fun _ => 0) ⟨c, .exec, 0, ()⟩ hc k with
        | .running ⟨⟨c₁, .call g _, _, ()⟩, _⟩ =>
          some (nameStr g.func.name, g.env.toList.all (fun d => IntOnly d.1), listCells c₁.heap)
        | _ => none

-- In its first `20` steps, the run is at a pending call once: after `8` steps, of `store`, whose
-- store's tags pass `IntOnly`, where cell `1` is the only cell that holds an `IntList`.
#guard (List.range 20).filterMap (fun k => (callAt k).map (k, ·)) == [(8, ("store", true, [1]))]

/-- What the linked `caller`'s run from the engine's start on no arguments returned, the integer
at location `0` of the heap where it ended, and whether location `1` still holds the empty
list. -/
def outcome : Option (Int × Int × Bool) :=
  match linked with
  | none => none
  | some lm =>
    match hw : checkModule lm with
    | .error _ => none
    | .ok () =>
      match startCore (m := lm) hw 1 [] with
      | .error _ => none
      | .ok ⟨_, c, hc⟩ =>
        match runFused hw (fun _ => 0) 50 ⟨c, .exec, 0, ()⟩ hc with
        | .done (.ok d) sn _ _ => do
          let list? := (sn.heap.cells[1]?).bind fun d =>
            WhileSem.model.read? (.ok d) While.IntList.Val
          return (← WhileSem.model.read? (.ok d) Int,
            ← (sn.heap.cells[0]?).bind fun d => WhileSem.model.read? (.ok d) Int,
            match list? with
            | some .nil => true
            | _ => false)
        | _ => none

-- The passed cell, which `caller` made with `1`, is overwritten with `7`, which `store` returns;
-- the unpassed one still holds the empty list.
#guard outcome == some (7, 7, true)

/--
info: 'Strata.Dyn.Exec.frame_call_of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms frame_call_of_run

/--
info: 'Strata.Dyn.ExecTest.LinkedCallTest.call_keeps_unpassed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms call_keeps_unpassed

end

end Strata.Dyn.ExecTest.LinkedCallTest
