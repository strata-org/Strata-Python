/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.CasesSound.Sound
public import StrataDyn.Exec.Base

set_option autoImplicit false

/-!
# The soundness of case lowering, on a hand-linked example

The theorem applies to a module of two functions, linked by hand, at any run model: the source
and the target validate (`src_wf`, `tgt_wf`) and the certificate relates them (`lowering_ok`), so
the closing example asks nothing of the modules.  The first function ends in a case of a
datatype with two constructors, the second of which carries a field; the second function ends in
a branch whose edges carry arguments.  The targets are written by hand, as `cases` lays its
output out, and not made by it: the theorems hold for any target that `LoweringOK` relates to the
source.

Each instruction has the form linking gives it.  The case is a pure terminal wrapper, as a
datatype's case links, and the tester a pure wrapper.  A jump, a return and a branch are the
base's rules, so they are rule trees (`jumpAlong`, `branchOn`), and so is the selector, whose tree
returns the field on its own constructor and faults on the other (`fieldOf`).  The certificate's
laws are proved of these trees: a jump and the selector need no hypothesis.

A run model does not say how a value of its `Bool` tag reads as a `Bool`, which the base's branch
takes, so the reading is the parameter `toBool`; in a table's model it is the identity.  The one
hypothesis is the tester's law (`htest`): its result reads as true exactly when the case picks the
first constructor.  The axioms of the main theorems are pinned.
-/

namespace Strata.Dyn.CasesSoundTest

open Strata.Dyn.Exec
open Strata.Dyn.CasesSound

public section

variable {M : RunModel} (t a : Ty) (cs : Fn M.interp (Exit M.interp [[], [a]]) [t])
  (isNil : Fn M.interp (M.interp M.bool) [t]) (toBool : M.interp M.bool → Bool)

/-! ## Rules, as linking gives them -/

/-- What an instruction of a rule that does not loop runs on: its operands `args`, of tags `ts`,
and a tree on a state that never runs. -/
abbrev once {rs : List (List Ty × Ty)} {ps : List (List Ty)} {R : Type} (ts : List Ty)
    (args : List Nat) : Rerun M rs ps R :=
  ⟨(0, #[]), ts, args, Fn.const (fun _ => semanticFailure "a rule that does not loop ran again") ts⟩

/-- `base.jump` along `s`: the rule's tree on the target of its one successor. -/
def jumpAlong (s : LSite) : LTerm M :=
  .sem (.str (.str .base "base") "jump") [] [[]] (once [] [])
    (BaseRules.jump ⟨fun _ => .exit (.here .nil)⟩) [] [s]

/-- A jump to block `j` with the arguments `args`. -/
def jumpTo (j : Nat) (args : List Nat) : LTerm M := jumpAlong ⟨.block j, args⟩

/-- A return of `v`: a jump to the body's exit. -/
def retOf (v : Nat) : LTerm M := jumpAlong ⟨.exit, [v]⟩

/-- `base.branch` on `c`, to `st` if it reads as true and to `sf` otherwise: the rule's tree on
the targets of its two successors. -/
def branchOn (c : Nat) (st sf : LSite) : LTerm M :=
  .sem (.str (.str .base "base") "branch") [] [[], []] (once [M.bool] [c])
    (fun x : M.interp M.bool => BaseRules.branch (toBool x) ⟨fun _ => .exit (.here .nil)⟩
      ⟨fun _ => .exit (.there (.here .nil))⟩) [] [st, sf]

/-- The tree of the selector of the second constructor's field: it returns the field of a value
of that constructor, and faults on the first. -/
def fieldOf (x : M.interp t) : Tree M.interp Run M.W [] [] (M.St (0, #[])) (M.interp a) :=
  match cs x with
  | .here _ => semanticFailure "the first constructor has no field"
  | .there (.here (.cons v .nil)) => .ret v

/-- `dst = hd s`, the selector's rule on `s`. -/
def hdOf (dst s : Nat) : LInsn M :=
  .sem (.str .base "hd") dst [] a [] (once [t] [s]) (fieldOf t a cs) [] []

/-! ## The modules -/

/-- The source, linked: the head of a list, or a default, with the values `s d y` at slots
`0`–`2`.
```
entry(s, d): case s ^join(d) ^join
join(y):     ret y
``` -/
def src : LBody M where
  name := .base
  ret := a
  slots := 3
  params := [t, a]
  blocks := #[
    ⟨Label.exit, [(0, t), (1, a)], [], [],
      .case [t] [[], [a]] cs [0] [⟨.block 1, [1]⟩, ⟨.block 1, []⟩]⟩,
    ⟨Label.exit, [(2, a)], [], [], retOf 2⟩]

/-- The target, as case lowering lays it out: a test of the first constructor and a branch, a new
block per arm, the second of which reads the field, and the join after them.  The new values are
the test's result `3` and the field `4`.  A new block's scope is what it reads of the entry
block: the default, or the list.
```
entry(s, d): c = isNil s; branch c ^nil ^cons
nil:         jump ^join(d)
cons:        h = hd s; jump ^join(h)
join(y):     ret y
``` -/
def tgt : LBody M where
  name := .base
  ret := a
  slots := 5
  params := [t, a]
  blocks := #[
    ⟨Label.exit, [(0, t), (1, a)], [], [.pure 3 [t] M.bool isNil [0]],
      branchOn toBool 3 ⟨.block 1, []⟩ ⟨.block 2, []⟩⟩,
    ⟨Label.exit, [], [(1, a)], [], jumpTo 3 [1]⟩,
    ⟨Label.exit, [], [(0, t)], [hdOf t a cs 4 0], jumpTo 3 [4]⟩,
    ⟨Label.exit, [(2, a)], [], [], retOf 2⟩]

/-- A source whose branch passes arguments along both edges, with the values `c x y z` at slots
`0`–`3`.
```
entry(c, x, y): branch c ^out(x) ^out(y)
out(z):         ret z
``` -/
def brSrc : LBody M where
  name := .base
  ret := a
  slots := 4
  params := [M.bool, a, a]
  blocks := #[
    ⟨Label.exit, [(0, M.bool), (1, a), (2, a)], [], [],
      branchOn toBool 0 ⟨.block 1, [1]⟩ ⟨.block 1, [2]⟩⟩,
    ⟨Label.exit, [(3, a)], [], [], retOf 3⟩]

/-- Its target: the branch passes nothing, to new blocks that jump with the arguments, each of
which is the block's scope.
```
entry(c, x, y): branch c ^l ^r
l:              jump ^out(x)
r:              jump ^out(y)
out(z):         ret z
``` -/
def brTgt : LBody M where
  name := .base
  ret := a
  slots := 4
  params := [M.bool, a, a]
  blocks := #[
    ⟨Label.exit, [(0, M.bool), (1, a), (2, a)], [], [],
      branchOn toBool 0 ⟨.block 1, []⟩ ⟨.block 2, []⟩⟩,
    ⟨Label.exit, [], [(1, a)], [], jumpTo 3 [1]⟩,
    ⟨Label.exit, [], [(2, a)], [], jumpTo 3 [2]⟩,
    ⟨Label.exit, [(3, a)], [], [], retOf 3⟩]

/-- The source module. -/
def srcMod : LModule M := ⟨#[src t a cs, brSrc a toBool], #[]⟩

/-- The target module. -/
def tgtMod : LModule M := ⟨#[tgt t a cs isNil toBool, brTgt a toBool], #[]⟩

/-! ## Validation -/

/-- Validation of one of the example's modules, unfolded: each check compares a tag with
itself. -/
local macro "validate" : tactic =>
  `(tactic| simp [WF, checkModule, srcMod, tgtMod, src, tgt, brSrc, brTgt, forAll, checkFunc,
    checkBlock, checkCode, checkTerm, checkSites, checkSite, targetSig, checkArgs, checkVal,
    checkScope, checkFits, checkRegions, insnTy, entryCtx, ctxOf, LBlock.paramTys, List.lookup,
    require, retOf, jumpTo, jumpAlong, branchOn, once, hdOf, LInsn.dst, bind, Except.bind,
    Except.mapError, pure, Except.pure])

/-- **The source module validates.** -/
theorem src_wf : WF (srcMod t a cs toBool) := by validate

/-- **The target module validates.** -/
theorem tgt_wf : WF (tgtMod t a cs isNil toBool) := by validate

/-! ## The certificate -/

/-- The map of blocks, of both functions: the entry stays, and the second block is the fourth. -/
def blockMap : Nat → Nat
  | 0 => 0
  | _ => 3

/-- A jump leaves along its successor, whatever the store: its tree is that exit. -/
private theorem jumps (s : LSite) : Jumps (M := M) (jumpAlong s) s :=
  fun _ => .sem (re := once [] []) trivial rfl

/-- A branch on a value that reads as whether `p` holds leaves along its first successor if `p`
holds, and along its second otherwise. -/
private theorem branch_exits {env : Array (Dyn M.interp)} {c : Nat} (st sf : LSite)
    (h : HasTy env c M.bool) (p : Prop) [Decidable p]
    (hp : toBool (getT env c M.bool h) = decide p) :
    Exits env (branchOn toBool c st sf) [[], []] [st, sf]
      (if p then .here .nil else .there (.here .nil)) := by
  refine .sem (re := once [M.bool] [c]) (And.intro h trivial) ?_
  show BaseRules.branch (toBool (getT env c M.bool h)) _ _ = _
  rw [hp]
  by_cases hp : p <;> simp [BaseRules.branch, jump, Jump.exit, hp]

/-- A return stays a return. -/
private theorem ret_ok (bound : Nat → Nat) (n : Nat) (g₁ : LBody M) (v : Nat) :
    TermOK bound n blockMap g₁ (retOf v) (retOf v) :=
  ⟨_, rfl, .cons (.inl ⟨rfl, rfl⟩) .nil, nofun⟩

/-- A jump to the join with `args` delivers an edge to it that passes them. -/
private theorem jump_tail (n : Nat) (args : List Nat) :
    Tail (M := M) n blockMap ⟨.block 1, args⟩ [] (jumpTo 3 args) :=
  ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil, ⟨.block 3, args⟩, jumps _,
    (List.append_nil _).symm, rfl⟩

/-- A new block that only jumps to the join with `args` lowers an edge to it that passes them. -/
private theorem bridge_ok (n j : Nat) (args : List Nat) (g₁ : LBody M) (b : LBlock M)
    (hb : g₁.blocks[j]? = some b) (hps : b.params = []) (hi : b.insns = [])
    (ht : b.term = jumpTo 3 args) :
    Via g₁ ⟨.block j, []⟩ fun code term =>
      code = [] ∧ Tail n blockMap ⟨.block 1, args⟩ code term :=
  ⟨j, b, rfl, hb, hps, hi, hi ▸ ht ▸ jump_tail n args⟩

/-- The selector returns the field the case passes, when it picks the second constructor. -/
private theorem selects : Selects (M := M) cs [0] 1 [hdOf t a cs 4 0] := by
  intro env h hk
  have hx : applyFn env [t] cs [0] h = cs (getT env 0 t h.1) := rfl
  rw [hx] at hk ⊢
  generalize hcs : cs (getT env 0 t h.1) = e at hk
  match e, hk with
  | .there (.here (.cons v .nil)), _ =>
    exact .cons (.sem h (show fieldOf t a cs _ = _ by simp only [fieldOf, hcs])) .nil
  | .here .nil, hk => exact absurd hk (show ¬ (0 = 0 + 1) by decide)

/-- The branch's function is lowered by its target. -/
private theorem br_ok (bound : Nat → Nat) :
    BodyOK bound 4 blockMap (brTgt a toBool) (brSrc a toBool) := by
  refine ⟨rfl, fun j b hb => ?_⟩
  match j, hb with
  | 0, hb =>
    obtain rfl := Option.some.inj hb
    exact ⟨_, rfl, rfl, .term ⟨_, rfl,
      .cons (.inr ⟨rfl, bridge_ok 4 1 [1] _ _ rfl rfl rfl rfl⟩)
        (.cons (.inr ⟨rfl, bridge_ok 4 2 [2] _ _ rfl rfl rfl rfl⟩) .nil), nofun⟩⟩
  | 1, hb =>
    obtain rfl := Option.some.inj hb
    exact ⟨_, rfl, rfl, .term (ret_ok ..)⟩
  | n + 2, hb => exact absurd hb (by simp [brSrc])

section
variable (htest : ∀ x : M.interp t, toBool (isNil x) = decide (armOf (cs x) = 0))

include htest in
/-- The case's function is lowered by the target, under the tester's law. -/
private theorem src_tgt_ok (bound : Nat → Nat) :
    BodyOK bound 3 blockMap (tgt t a cs isNil toBool) (src t a cs) := by
  refine ⟨rfl, fun j b hb => ?_⟩
  match j, hb with
  | 0, hb =>
    obtain rfl := Option.some.inj hb
    refine ⟨_, rfl, rfl, .case (.test (st := ⟨.block 1, []⟩) (sf := ⟨.block 2, []⟩)
      (Nat.le_refl 3) ?_ ⟨_, rfl, .inr ?_⟩ rfl ⟨_, rfl, .inr ?_⟩)⟩
    · intro env h hd₃ _
      have hty : HasTy (env.setIfInBounds 3 ⟨M.bool, applyFn env [t] isNil [0] h⟩) 3 M.bool :=
        hasTy_set hd₃ _
      exact ⟨_, .pure h, branch_exits toBool _ _ hty _ ((getT_set _ hty).symm ▸ htest _)⟩
    · refine ⟨1, _, rfl, rfl, rfl, jump_tail 3 [1], fun env h hk => ?_⟩
      rw [valsOf_nil _ (by rw [hk]; rfl)]
      exact .nil
    · exact ⟨2, _, rfl, rfl, rfl,
        ⟨List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun i hi => by
            obtain rfl := List.mem_singleton.mp hi
            exact show 3 ≤ 4 by decide,
          ⟨.block 3, [4]⟩, jumps _, rfl, rfl⟩, selects t a cs⟩
  | 1, hb =>
    obtain rfl := Option.some.inj hb
    exact ⟨_, rfl, rfl, .term (ret_ok ..)⟩
  | n + 2, hb => exact absurd hb (by simp [src])

include htest in
/-- **The two-function modules are certified**, under the tester's law. -/
theorem lowering_ok : LoweringOK (srcMod t a cs toBool) (tgtMod t a cs isNil toBool) := by
  refine ⟨fun _ => 0, ⟨rfl, fun i hi hi₁ => ?_⟩, fun i g hg => ?_,
    fun k g hg => absurd hg (by simp [srcMod])⟩
  · match i, hi with
    | 0, _ => exact ⟨rfl, rfl, rfl⟩
    | 1, _ => exact ⟨rfl, rfl, rfl⟩
    | n + 2, hi => exact absurd hi (by simp [srcMod])
  · match i, hg with
    | 0, hg =>
      obtain rfl := Option.some.inj hg
      exact ⟨_, blockMap, rfl, show 3 ≤ 5 by decide, src_tgt_ok t a cs isNil toBool htest _⟩
    | 1, hg =>
      obtain rfl := Option.some.inj hg
      exact ⟨_, blockMap, rfl, Nat.le_refl _, br_ok a toBool _⟩
    | n + 2, hg => exact absurd hg (by simp [srcMod])

include htest in
/-- The theorem applies: a start of either function of the source has a start of the same
function of the target, with the same behaviour under every oracle. -/
example (i : Nat) (args : List (Dyn M.interp)) (snap : Snapshot M) {B : Ty} {c : Core M}
    {h : CoreOK _ B c} (hs : startCore (src_wf t a cs toBool) i args snap = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore (tgt_wf t a cs isNil toBool) i args snap = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.W → O) (oracle : Nat → Nat),
        behW (tgt_wf t a cs isNil toBool) obs
            (oracleRun (tgt_wf t a cs isNil toBool) oracle ⟨c₁, .exec, 0, ()⟩ h₁) =
          behW (src_wf t a cs toBool) obs
            (oracleRun (src_wf t a cs toBool) oracle ⟨c, .exec, 0, ()⟩ h) :=
  lowering_sound _ _ (lowering_ok t a cs isNil toBool htest) i args snap hs

end

end

/--
info: 'Strata.Dyn.CasesSoundTest.src_wf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms src_wf

/--
info: 'Strata.Dyn.CasesSoundTest.tgt_wf' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms tgt_wf

/--
info: 'Strata.Dyn.CasesSoundTest.lowering_ok' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms lowering_ok

/--
info: 'Strata.Dyn.CasesSound.lowering_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lowering_sound

/--
info: 'Strata.Dyn.CasesSound.lowering_sound_runs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms lowering_sound_runs

/--
info: 'Strata.Dyn.CasesSound.step_match' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms step_match

end Strata.Dyn.CasesSoundTest
