/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.RefToReg
public import StrataDyn.Examples.While.RefToRegSound
import all StrataDyn.RefToRegSound.Cert

set_option autoImplicit false

/-!
# Ref-to-reg's soundness, on its own example

The promotion certificate is satisfiable for ref-to-reg's own example (`docs/Dyn.md`, §3), linked
by hand, at any run model and any branch rule: a cell set on one arm of a branch and read at the
join becomes a parameter of the join (`promotion_ok`).  It is also satisfiable for functions
that read and write a cell they did not allocate, such as a parameter or a closure's captured
cell: such a cell is kept, beside a local cell that is promoted (`param_cell_ok`), and a function
that only reads its cell parameter is certified against itself, with nothing promoted
(`get_param_ok`).  The targets are written by
hand, not made by `refToReg`: the theorems hold for any target that `PromotionOK` relates to the
source.  The axioms of the main theorems are pinned.
-/

namespace Strata.Dyn.RefToRegSoundTest

open Strata.Dyn.Exec
open Strata.Dyn.RefToRegSound

variable {M : RunModel} (br : Fn M.interp (Exit M.interp [[], []]) [M.bool])

/-- A jump to block `j` with the arguments `args`. -/
def jumpTo (j : Nat) (args : List Nat) : LTerm M := .case [] [[]] (Exit.here .nil) [] [⟨.block j, args⟩]

/-- A return of `v`. -/
def retOf (v : Nat) : LTerm M := .case [] [[]] (Exit.here .nil) [] [⟨.exit, [v]⟩]

/-- The source, linked: `x := ref a; if c then *x := b; return *x`, with the values `c a b x u r` at
slots `0`–`5`.
```
entry(c, a, b): x = refNew a; branch c ^yes ^join
yes:            u = refSet x b; jump ^join
join:           r = refGet x; ret r
``` -/
def src : LBody M where
  name := .base
  ret := M.int
  slots := 6
  params := [M.bool, M.int, M.int]
  blocks := #[
    ⟨Label.exit, [(0, M.bool), (1, M.int), (2, M.int)], [], [.refNew 3 M.int 1],
      .case [M.bool] [[], []] br [0] [⟨.block 1, []⟩, ⟨.block 2, []⟩]⟩,
    ⟨Label.exit, [], [(2, M.int), (3, Ty.ref M.int)], [.refSet 4 M.int 3 2], jumpTo 2 []⟩,
    ⟨Label.exit, [], [(3, Ty.ref M.int)], [.refGet 5 M.int 3], retOf 5⟩]

/-- The target, as ref-to-reg rewrites it: the `refNew` stays, the write and the read go, and the
join takes the content as the new parameter `6`.
```
entry(c, a, b): x = refNew a; branch c ^yes ^join(a)
yes:            jump ^join(b)
join(a₁):       ret a₁
``` -/
def tgt : LBody M where
  name := .base
  ret := M.int
  slots := 7
  params := [M.bool, M.int, M.int]
  blocks := #[
    ⟨Label.exit, [(0, M.bool), (1, M.int), (2, M.int)], [], [.refNew 3 M.int 1],
      .case [M.bool] [[], []] br [0] [⟨.block 1, []⟩, ⟨.block 2, [1]⟩]⟩,
    ⟨Label.exit, [], [(2, M.int)], [], jumpTo 2 [2]⟩,
    ⟨Label.exit, [(6, M.int)], [], [], retOf 6⟩]

/-- The entry facts: the parameters at the entry; in `yes`, `x` is promoted with content `a`, and
`b` is itself; at the join, the content is the new parameter. -/
def entryFacts : Nat → List Fact
  | 0 => [.eq 0 0, .eq 1 1, .eq 2 2]
  | 1 => [.prom 3, .cell 1 3, .eq 2 2]
  | 2 => [.prom 3, .cell 6 3]
  | _ => []

/-- Membership in a list of facts, by evaluation, or a fact about the bodies' shapes, by
unfolding them. -/
local macro "ok" : tactic => `(tactic| first | decide | simp [paramsOf, src, tgt])

/-- The certificate's modules, with no condition on instructions and no regions. -/
abbrev X : CertEnv M :=
  ⟨⟨#[src br], #[]⟩, ⟨#[tgt br], #[]⟩, fun _ => True, fun _ => True, fun _ _ => []⟩

/-- The source's body is promoted by the target's. -/
theorem src_tgt_ok : BodyOK (X br) (src br) (tgt br) entryFacts := by
  intro j hj
  match j, hj with
  | 0, _ =>
    refine ⟨by ok, .newProm (u := 1) (by ok) (by ok) (.term (.case trivial (.cons (by ok) .nil)
      (.cons ⟨rfl, by ok, by ok, ?_⟩ (.cons ⟨rfl, by ok, by ok, ?_⟩ .nil))))⟩
    · intro φ hφ
      simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
      rcases hφ with rfl | rfl | rfl
      · exact ⟨by ok, by ok⟩
      · exact ⟨by ok, 1, Or.inl ⟨by ok, rfl⟩, by ok⟩
      · exact ⟨.inl 2, .inl 2, Or.inl ⟨by ok, rfl⟩, Or.inl ⟨by ok, rfl⟩, by ok⟩
    · intro φ hφ
      simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact ⟨by ok, by ok⟩
      · exact ⟨by ok, 1, Or.inr ⟨0, by ok, rfl, Or.inl ⟨by ok, rfl⟩⟩, by ok⟩
  | 1, _ =>
    refine ⟨by ok, .setProm (u := 2) (by ok) (by ok) (by ok)
      (.term (.case trivial .nil (.cons ⟨rfl, by ok, by ok, ?_⟩ .nil)))⟩
    intro φ hφ
    simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
    rcases hφ with rfl | rfl
    · exact ⟨by ok, by ok⟩
    · exact ⟨by ok, 2, Or.inr ⟨0, by ok, rfl, Or.inl ⟨by ok, rfl⟩⟩, by ok⟩
  | 2, _ =>
    exact ⟨by ok, .getProm (u := 6) (by ok)
      (.term (.case trivial .nil (.cons ⟨rfl, .cons (by ok) .nil⟩ .nil)))⟩
  | n + 3, hj => exact absurd hj (by ok)

/-- The one-function modules are certified. -/
theorem promotion_ok : PromotionOK (M := M) ⟨#[src br], #[]⟩ ⟨#[tgt br], #[]⟩ := by
  refine ⟨fun _ _ => [], rfl, rfl, fun i hi => ?_, fun k hk => absurd hk (by ok)⟩
  match i, hi with
  | 0, _ =>
    refine ⟨by ok, entryFacts, src_tgt_ok br, ⟨rfl, by ok, by ok, ?_⟩, rfl, rfl, rfl⟩
    intro φ hφ
    simp only [entryFacts, List.mem_cons, List.mem_nil_iff, or_false] at hφ
    rcases hφ with rfl | rfl | rfl
    · exact ⟨0, by ok, by ok, rfl⟩
    · exact ⟨1, by ok, by ok, rfl⟩
    · exact ⟨2, by ok, by ok, rfl⟩
  | n + 1, hi => exact absurd hi (by ok)

/-- A terminator with no payload exits validly, whatever its exit. -/
theorem exitOK_empty (A : Accounts M) (S : Typing) : ∀ e : Exit M.interp [[], []], A.ExitOK S e
  | .here .nil => trivial
  | .there (.here .nil) => trivial

/-- So, for any accounts under which both modules validate, every start of the source's function
on arguments that hold no ref has a target start whose run, under every oracle, improves on the
source's run under the same oracle. -/
example (A : Accounts M) (hwf : WF (M := M) ⟨#[src br], #[]⟩)
    (hwf₁ : WF (M := M) ⟨#[tgt br], #[]⟩) (args : List (Dyn M.interp)) (snap : Snapshot M)
    (hsnap : SnapOK A snap) (hargs : ∀ d ∈ args, A.DynOK (typOff snap.heap []) d) {B : Ty}
    {c : Core M} {h : CoreOK _ B c} (hs : startCore hwf 0 args snap = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hwf₁ 0 args snap = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.W → O),
        Exec.OracleRefines hwf hwf₁ obs Result.Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩
          ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ := by
  obtain ⟨ER, hok⟩ := promotion_ok br
  have hblocks : ∀ g ∈ (⟨#[src br], #[]⟩ : LModule M).funcs, g.All A.InsnOK A.TermOK := by
    intro g hg b hb
    simp only [List.mem_toArray, List.mem_singleton] at hg
    subst hg
    simp only [src, List.mem_toArray, List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact ⟨fun i hi => by simp only [List.mem_singleton] at hi; subst hi; trivial,
        fun S x _ => exitOK_empty A S _⟩
    · exact ⟨fun i hi => by simp only [List.mem_singleton] at hi; subst hi; trivial,
        fun _ => trivial⟩
    · exact ⟨fun i hi => by simp only [List.mem_singleton] at hi; subst hi; trivial,
        fun _ => trivial⟩
  exact promote_sound A _ hwf hwf₁ (hok.withRules A.InsnOK A.TermOK hblocks
    (fun g hg => by simp at hg)) (fun _ h => h) (fun _ h => h) 0 args snap hsnap hargs hs

/-! ## Cells the function did not allocate -/

public section

/-- The source, linked: a function of a cell `x` and an int `a` that writes `a` into `x`, reads
it back, and passes it through a new cell `y`, with the values `x a y u r w s` at slots `0`–`6`.
```
f(x, a): y = refNew a; u = refSet x a; r = refGet x; w = refSet y r; s = refGet y; ret s
``` -/
def paramSrc : LBody M where
  name := .base
  ret := M.int
  slots := 7
  params := [Ty.ref M.int, M.int]
  blocks := #[
    ⟨Label.exit, [(0, Ty.ref M.int), (1, M.int)], [],
      [.refNew 2 M.int 1, .refSet 3 M.int 0 1, .refGet 4 M.int 0, .refSet 5 M.int 2 4,
        .refGet 6 M.int 2], retOf 6⟩]

/-- The target: the parameter `x` is kept, so its write and its read stay; the new cell `y` is
promoted, so its write and its read go, and `r` stands for its content.
```
f(x, a): y = refNew a; u = refSet x a; r = refGet x; ret r
``` -/
def paramTgt : LBody M where
  name := .base
  ret := M.int
  slots := 7
  params := [Ty.ref M.int, M.int]
  blocks := #[
    ⟨Label.exit, [(0, Ty.ref M.int), (1, M.int)], [],
      [.refNew 2 M.int 1, .refSet 3 M.int 0 1, .refGet 4 M.int 0], retOf 4⟩]

/-- A function that reads the cell it is given, as a closure reads a captured cell, with the
values `x r` at slots `0` and `1`.
```
g(x): r = refGet x; ret r
``` -/
def getParam : LBody M where
  name := .base
  ret := M.int
  slots := 2
  params := [Ty.ref M.int]
  blocks := #[⟨Label.exit, [(0, Ty.ref M.int)], [], [.refGet 1 M.int 0], retOf 1⟩]

/-- Membership in a list of facts, by evaluation, or a fact about these bodies' shapes, by
unfolding them. -/
local macro "ok'" : tactic =>
  `(tactic| first | decide | simp [paramsOf, paramSrc, paramTgt, getParam])

/-- The function that writes and reads its cell parameter, with its local cell promoted, is
certified: the kept accesses of `x` need only that the target's `x` is the source's. -/
theorem param_cell_ok : PromotionOK (M := M) ⟨#[paramSrc], #[]⟩ ⟨#[paramTgt], #[]⟩ := by
  refine ⟨fun _ _ => [], rfl, rfl, fun i hi => ?_, fun k hk => absurd hk (by ok')⟩
  match i, hi with
  | 0, _ =>
    refine ⟨by ok', fun _ => [.eq 0 0, .eq 1 1], fun j hj => ?_, ⟨rfl, by ok', by ok', ?_⟩, rfl,
      rfl, rfl⟩
    · match j, hj with
      | 0, _ =>
        exact ⟨by ok', .newProm (u := 1) (by ok') (by ok') <| .setKept (by ok') (by ok') <|
          .getKept (by ok') <| .setProm (u := 4) (by ok') (by ok') (by ok') <|
          .getProm (u := 4) (by ok') <|
          .term (.case trivial .nil (.cons ⟨rfl, .cons (by ok') .nil⟩ .nil))⟩
      | n + 1, hj => exact absurd hj (by ok')
    · intro φ hφ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact ⟨0, by ok', by ok', rfl⟩
      · exact ⟨1, by ok', by ok', rfl⟩
  | n + 1, hi => exact absurd hi (by ok')

/-- The function that reads its cell parameter is certified against itself, with nothing
promoted. -/
theorem get_param_ok : PromotionOK (M := M) ⟨#[getParam], #[]⟩ ⟨#[getParam], #[]⟩ := by
  refine ⟨fun _ _ => [], rfl, rfl, fun i hi => ?_, fun k hk => absurd hk (by ok')⟩
  match i, hi with
  | 0, _ =>
    refine ⟨by ok', fun _ => [.eq 0 0], fun j hj => ?_, ⟨rfl, by ok', by ok', ?_⟩, rfl, rfl, rfl⟩
    · match j, hj with
      | 0, _ =>
        exact ⟨by ok', .getKept (by ok')
          (.term (.case trivial .nil (.cons ⟨rfl, .cons (by ok') .nil⟩ .nil)))⟩
      | n + 1, hj => exact absurd hj (by ok')
    · intro φ hφ
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hφ
      rcases hφ with rfl
      exact ⟨0, by ok', by ok', rfl⟩
  | n + 1, hi => exact absurd hi (by ok')

/-- So, for any accounts under which both modules validate, every start of the function that
writes and reads its cell parameter, on arguments valid in the snapshot's heap, has a target
start whose run, under every oracle, improves on the source's run up to a bad cell. -/
example (A : Accounts M) (hwf : WF (M := M) ⟨#[paramSrc], #[]⟩)
    (hwf₁ : WF (M := M) ⟨#[paramTgt], #[]⟩) (args : List (Dyn M.interp)) (snap : Snapshot M)
    (hsnap : SnapOK A snap) (hargs : ∀ d ∈ args, A.DynOK (typOff snap.heap []) d) {B : Ty}
    {c : Core M} {h : CoreOK _ B c} (hs : startCore hwf 0 args snap = .ok ⟨B, c, h⟩) :
    ∃ B₁ c₁ h₁, startCore hwf₁ 0 args snap = .ok ⟨B₁, c₁, h₁⟩ ∧
      ∀ {O : Type} [DecidableEq O] (obs : M.W → O),
        Exec.OracleRefines hwf hwf₁ obs Wrong ⟨⟨c, .exec, 0, ()⟩, h⟩ ⟨⟨c₁, .exec, 0, ()⟩, h₁⟩ := by
  obtain ⟨ER, hok⟩ := param_cell_ok (M := M)
  have hblocks : ∀ g ∈ (⟨#[paramSrc], #[]⟩ : LModule M).funcs, g.All A.InsnOK A.TermOK := by
    intro g hg b hb
    simp only [List.mem_toArray, List.mem_singleton] at hg
    subst hg
    simp only [paramSrc, List.mem_toArray, List.mem_singleton] at hb
    subst hb
    refine ⟨fun i hi => ?_, fun _ => trivial⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> trivial
  exact promote_sound_cell A _ hwf hwf₁ (hok.withRules A.InsnOK A.TermOK hblocks
    (fun g hg => by simp at hg)) (fun _ h => h) (fun _ h => h) 0 args snap hsnap hargs hs

end

/--
info: 'Strata.Dyn.RefToRegSoundTest.param_cell_ok' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms param_cell_ok

/--
info: 'Strata.Dyn.RefToRegSoundTest.get_param_ok' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms get_param_ok

/--
info: 'Strata.Dyn.RefToRegSound.refToReg_sound_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refToReg_sound_cell

/--
info: 'Strata.Dyn.RefToRegSound.refToReg_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refToReg_sound

/--
info: 'Strata.Dyn.RefToRegSound.refToReg_sound_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refToReg_sound_eq

/--
info: 'Strata.Dyn.RefToRegSound.refToReg_sound_runs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms refToReg_sound_runs

/--
info: 'Strata.Dyn.WhileCert.refToReg_sound_while' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WhileCert.refToReg_sound_while

/--
info: 'Strata.Dyn.RefToRegSound.promote_sound_cell' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms promote_sound_cell

/--
info: 'Strata.Dyn.RefToRegSound.promote_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms promote_sound

/--
info: 'Strata.Dyn.RefToRegSound.step_good' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms step_good

end Strata.Dyn.RefToRegSoundTest
