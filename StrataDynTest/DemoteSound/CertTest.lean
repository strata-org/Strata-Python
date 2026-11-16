/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.RefToReg
import all StrataDyn.RefToRegSound.Cert
import all StrataDynTest.RefToRegSound.SoundTest

set_option autoImplicit false

/-!
# The linked swap-loop bodies and their promotion certificate

A loop whose head takes two parameters and whose back edge swaps them, linked by hand at any
run model and any branch rule. The original, its padded form and its demoted form validate for
any integer default `k`. The source of the promotion is the function as `demote` leaves it.
The target is the original with the default values and `refNew`s added to its entry block:
promotion keeps each `refNew`, so the certificate needs them on both sides.

The certificate relates the two bodies block by block and edge by edge, which is why `demote`
writes an edge's cells before the edge's jump and adds no block.
-/

namespace Strata.Dyn.DemoteSoundTest

open Strata.Dyn.Exec
open Strata.Dyn.RefToRegSound
open Strata.Dyn.RefToRegSoundTest (jumpTo retOf)

variable {M : RunModel} (br : Fn M.interp (Exit M.interp [[], []]) [M.bool]) (k : M.interp M.int)

/-- The head, swap and return blocks shared by the original and its padded form. -/
def loopTail : Array (LBlock M) := #[
  ⟨Label.exit, [(3, M.int), (4, M.int)], [(0, M.bool)], [],
    .case [M.bool] [[], []] br [0] [⟨.block 2, []⟩, ⟨.block 3, []⟩]⟩,
  ⟨Label.exit, [], [(0, M.bool), (3, M.int), (4, M.int)], [], jumpTo 1 [4, 3]⟩,
  ⟨Label.exit, [], [(3, M.int)], [], retOf 3⟩]

/-- The unpadded loop: its entry jumps to the head, and slots zero through four hold its
parameters and the head's parameters. -/
def original : LBody M where
  name := .base
  ret := M.int
  slots := 5
  params := [M.bool, M.int, M.int]
  blocks := #[⟨Label.exit, [(0, M.bool), (1, M.int), (2, M.int)], [], [],
    jumpTo 1 [1, 2]⟩] ++ loopTail br

/-- The padded original, linked, with the values `c a b x y` at slots `0`–`4`, and with what `demote`
adds to the entry block: the cells `cx` and `cy` at `5` and `6`, and their default values at `7`
and `8`.
```
entry(c, a, b): d = k; cx = refNew d; e = k; cy = refNew e; jump ^head(a, b)
head(x, y):     branch c ^swap ^done
swap:           jump ^head(y, x)
done:           ret x
``` -/
def padded : LBody M where
  name := .base
  ret := M.int
  slots := 13
  params := [M.bool, M.int, M.int]
  blocks := #[
    ⟨Label.exit, [(0, M.bool), (1, M.int), (2, M.int)], [],
      [.const 7 ⟨M.int, k⟩, .refNew 5 M.int 7, .const 8 ⟨M.int, k⟩, .refNew 6 M.int 8],
      jumpTo 1 [1, 2]⟩] ++ loopTail br

/-- The function as `demote` leaves it: each jump to the head writes the head's cells first, and
the head reads them.  The results of the writes are at slots `9`–`12`.
```
entry(c, a, b): d = k; cx = refNew d; e = k; cy = refNew e
                s = refSet cx a; t = refSet cy b; jump ^head
head:           x = refGet cx; y = refGet cy; branch c ^swap ^done
swap:           u = refSet cx y; v = refSet cy x; jump ^head
done:           ret x
``` -/
def demoted : LBody M where
  name := .base
  ret := M.int
  slots := 13
  params := [M.bool, M.int, M.int]
  blocks := #[
    ⟨Label.exit, [(0, M.bool), (1, M.int), (2, M.int)], [],
      [.const 7 ⟨M.int, k⟩, .refNew 5 M.int 7, .const 8 ⟨M.int, k⟩, .refNew 6 M.int 8,
        .refSet 9 M.int 5 1,
        .refSet 10 M.int 6 2], jumpTo 1 []⟩,
    ⟨Label.exit, [], [(0, M.bool), (5, Ty.ref M.int), (6, Ty.ref M.int)],
      [.refGet 3 M.int 5, .refGet 4 M.int 6],
      .case [M.bool] [[], []] br [0] [⟨.block 2, []⟩, ⟨.block 3, []⟩]⟩,
    ⟨Label.exit, [], [(0, M.bool), (3, M.int), (4, M.int), (5, Ty.ref M.int), (6, Ty.ref M.int)],
      [.refSet 11 M.int 5 4, .refSet 12 M.int 6 3], jumpTo 1 []⟩,
    ⟨Label.exit, [], [(3, M.int)], [], retOf 3⟩]

/-- The entry facts: the parameters at the entry; at the head, both cells are promoted, and the
original's parameters hold their contents; in `swap` and `done`, the values that the head read
are the original's parameters. -/
def entryFacts : Nat → List Fact
  | 0 => [.eq 0 0, .eq 1 1, .eq 2 2]
  | 1 => [.prom 5, .prom 6, .cell 3 5, .cell 4 6, .eq 0 0]
  | 2 => [.prom 5, .prom 6, .eq 0 0, .eq 3 3, .eq 4 4]
  | 3 => [.eq 3 3]
  | _ => []

/-! ## Validation -/

/-- Validation reduces to slot bounds and comparisons of each operand's tag with itself. -/
local macro "validate" : tactic =>
  `(tactic| simp [WF, checkModule, original, padded, demoted, loopTail, forAll, checkFunc,
    checkBlock, checkCode, checkTerm, checkSites, checkSite, targetSig, checkArgs, checkVal,
    checkScope, checkFits, checkRegions, insnTy, entryCtx, ctxOf, LBlock.paramTys, List.lookup,
    require, retOf, jumpTo, LInsn.dst, bind, Except.bind, Except.mapError, pure, Except.pure])

/-- The original loop validates without default computations or allocations. -/
theorem original_wf : WF (M := M) ⟨#[original br], #[]⟩ := by validate

/-- The padded original validates for any integer default. -/
theorem padded_wf : WF (M := M) ⟨#[padded br k], #[]⟩ := by validate

/-- The demoted loop validates for any integer default. -/
theorem demoted_wf : WF (M := M) ⟨#[demoted br k], #[]⟩ := by validate

/-! ## Promotion certificate -/

/-- Membership in a list of facts, by evaluation, or a fact about the bodies' shapes, by
unfolding them. -/
local macro "ok" : tactic => `(tactic| first | decide | simp [paramsOf, padded, demoted, loopTail])

/-- The certificate's modules, with no condition on instructions and no regions. -/
abbrev X : CertEnv M :=
  ⟨⟨#[demoted br k], #[]⟩, ⟨#[padded br k], #[]⟩, fun _ => True, fun _ => True, fun _ _ => []⟩

/-- The padded original's body promotes the demoted body's cells. -/
theorem demoted_padded_ok : BodyOK (X br k) (demoted br k) (padded br k) entryFacts := by
  intro j hj
  match j, hj with
  | 0, _ =>
    refine ⟨by ok, .const trivial <| .newProm (u := 7) (by ok) (by ok) <| .const trivial <|
      .newProm (u := 8) (by ok) (by ok) <| .setProm (u := 1) (by ok) (by ok) (by ok) <|
      .setProm (u := 2) (by ok) (by ok) (by ok) <|
      .term (.case trivial .nil (.cons ⟨rfl, by ok, by ok, ?_⟩ .nil))⟩
    intro φ hφ
    simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by ok, by ok⟩
    · exact ⟨by ok, by ok⟩
    · exact ⟨by ok, 1, Or.inr ⟨0, by ok, rfl, Or.inl ⟨by ok, rfl⟩⟩, by ok⟩
    · exact ⟨by ok, 2, Or.inr ⟨1, by ok, rfl, Or.inl ⟨by ok, rfl⟩⟩, by ok⟩
    · exact ⟨.inl 0, .inl 0, Or.inl ⟨by ok, rfl⟩, Or.inl ⟨by ok, rfl⟩, by ok⟩
  | 1, _ =>
    refine ⟨by ok, .getProm (u := 3) (by ok) <| .getProm (u := 4) (by ok) <|
      .term (.case trivial (.cons (by ok) .nil)
        (.cons ⟨rfl, by ok, by ok, ?_⟩ (.cons ⟨rfl, by ok, by ok, ?_⟩ .nil)))⟩
    · intro φ hφ
      simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
      rcases hφ with rfl | rfl | rfl | rfl | rfl
      · exact ⟨by ok, by ok⟩
      · exact ⟨by ok, by ok⟩
      · exact ⟨.inl 0, .inl 0, Or.inl ⟨by ok, rfl⟩, Or.inl ⟨by ok, rfl⟩, by ok⟩
      · exact ⟨.inl 3, .inl 3, Or.inl ⟨by ok, rfl⟩, Or.inl ⟨by ok, rfl⟩, by ok⟩
      · exact ⟨.inl 4, .inl 4, Or.inl ⟨by ok, rfl⟩, Or.inl ⟨by ok, rfl⟩, by ok⟩
    · intro φ hφ
      simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
      subst hφ
      exact ⟨.inl 3, .inl 3, Or.inl ⟨by ok, rfl⟩, Or.inl ⟨by ok, rfl⟩, by ok⟩
  | 2, _ =>
    refine ⟨by ok, .setProm (u := 4) (by ok) (by ok) (by ok) <|
      .setProm (u := 3) (by ok) (by ok) (by ok) <|
      .term (.case trivial .nil (.cons ⟨rfl, by ok, by ok, ?_⟩ .nil))⟩
    intro φ hφ
    simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
    rcases hφ with rfl | rfl | rfl | rfl | rfl
    · exact ⟨by ok, by ok⟩
    · exact ⟨by ok, by ok⟩
    · exact ⟨by ok, 4, Or.inr ⟨0, by ok, rfl, Or.inl ⟨by ok, rfl⟩⟩, by ok⟩
    · exact ⟨by ok, 3, Or.inr ⟨1, by ok, rfl, Or.inl ⟨by ok, rfl⟩⟩, by ok⟩
    · exact ⟨.inl 0, .inl 0, Or.inl ⟨by ok, rfl⟩, Or.inl ⟨by ok, rfl⟩, by ok⟩
  | 3, _ =>
    exact ⟨by ok, .term (.case trivial .nil (.cons ⟨rfl, .cons (by ok) .nil⟩ .nil))⟩
  | n + 4, hj => exact absurd hj (by ok)

/-- **The demoted function is a source whose cells the padded original promotes.** -/
theorem promotion_ok : PromotionOK (M := M) ⟨#[demoted br k], #[]⟩ ⟨#[padded br k], #[]⟩ := by
  refine ⟨fun _ _ => [], rfl, rfl, fun i hi => ?_, fun j hj => absurd hj (by ok)⟩
  match i, hi with
  | 0, _ =>
    refine ⟨by ok, entryFacts, demoted_padded_ok br k, ⟨rfl, by ok, by ok, ?_⟩, rfl, rfl, rfl⟩
    intro φ hφ
    simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact ⟨0, by ok, by ok, rfl⟩
    · exact ⟨1, by ok, by ok, rfl⟩
    · exact ⟨2, by ok, by ok, rfl⟩
  | n + 1, hi => exact absurd hi (by ok)

-- The theorem is private to this module, so its name prints in full.
/--
info: '_private.StrataDynTest.DemoteSound.CertTest.0.Strata.Dyn.DemoteSoundTest.promotion_ok' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms promotion_ok

end Strata.Dyn.DemoteSoundTest
