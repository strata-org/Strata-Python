/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonicalize
import all StrataDyn.Canonicalize
import all StrataDyn.Canonical
import all StrataDyn.EveryBody

set_option autoImplicit false

/-!
# Putting a function in canonical form, proved

## Main theorems

* `Canonicalize.canonicalize_of_check`: a function that `Func.checkCanonicalCFG` accepts comes back
  unchanged, so running the pass again changes nothing;
* `Canonicalize.canonicalize_of_canonical`: the same, for a well-formed canonical function;
* `Canonicalize.runModule_funcs`: when `runModule` succeeds, function `i` of its module is
  function `i` of the input, put in canonical form;
* `Canonicalize.check_ok_val`, `Canonicalize.checkModule_module`: `check` and `checkModule` never
  change what they are given;
* `Canonicalize.runModule_ghosts`: `runModule` keeps the module's ghosts as they are.

## To prove

`Canonicalize.run` checks its result at run time.  These statements are still to prove:

* `canonicalize_wf`: the result of a well-formed function is well formed;
* `canonicalize_canonical`: the result of a well-formed function is canonical, if every loop has
  one entry (`Func.Reducible`) and no loop inside a region leaves its region;
* that `canonicalize` keeps `Func.Reducible`.  With these three, `run` would need to check only
  its input;
* that `reducibleB` accepts every body whose loops have one entry and whose blocks are all
  reachable, so that `run` never rejects such a function;
* when Dyn has a semantics, that `canonicalize` keeps a function's outcomes: every run of the
  result is a run of the original, one `jump` longer at each forwarding block, and the converse.
  Its proof is a stuttering simulation that uses only the meaning of `jump`.
-/

namespace Strata.Dyn

namespace Canonicalize

variable {env : Env Unit} {α : Type}

/-- `loopsInnerFirst` pairs heads of the body's loops with the labels of their loops. -/
theorem mem_loopsInnerFirst {bs : List (Block env α)} {h : Label} {L : List Label}
    (hh : (h, L) ∈ loopsInnerFirst (Body.backEdges bs) bs) :
    h ∈ Body.heads bs ∧ L = Body.loopOf bs h := by
  simp only [loopsInnerFirst, Body.tableOf_loopsOf, List.map_map, List.mem_map,
    List.mem_mergeSort] at hh
  obtain ⟨_, ⟨h', hh', rfl⟩, he⟩ := hh
  simp only [Function.comp, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hh', rfl⟩

/-- On a body whose loops all have dedicated exits, no exit target of a loop needs a block. -/
theorem exitsToFix_of_exitsB {bs : List (Block env α)} {h : Label}
    (he : Body.exitsB bs (Body.loopOf bs h) = true) :
    exitsToFix (Body.transfers bs) (Body.loopOf bs h) = [] := by
  unfold exitsToFix
  rw [List.filter_eq_nil_iff]
  intro x hx
  simp only [List.mem_eraseDups] at hx
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', not_exists,
    not_and, Bool.eq_false_iff, ne_eq]
  rintro ⟨w, l⟩ hw rfl hwL
  simp only [Body.exitsB, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at he
  rcases he.1 (w, l) hw with hne | hin
  · exact hne (List.contains_iff_mem.mpr hx)
  · exact hwL hin

/-- If no loop of `loops` needs an exit block, given the transfers `tr₀`, then `addExits`, started
with nothing added, nothing fixed and no loop fixed, fixes nothing. -/
theorem addExits_none [base ≼ env] {hs : List Label} {tr₀ : List (Point × Label)} :
    ∀ (loops : List (Label × List Label)) (bs : List (Block env α)) (st : Fresh),
      (∀ x ∈ loops, exitsToFix tr₀ x.2 = []) →
      (addExits hs tr₀ loops (bs, st, [], false, [])).2.2.2.1 = false
  | [], _, _, _ => rfl
  | (_, L) :: loops, bs, st, hx => by
    have hL : exitsToFix tr₀ L = [] := hx _ List.mem_cons_self
    have hov : (L.any ([] : List Label).contains) = false := by simp
    simp only [addExits, hov, Bool.false_eq_true, ite_false, hL, List.isEmpty_nil, Bool.true_or,
      ite_true]
    exact addExits_none loops bs st (fun x hm => hx x (List.mem_cons_of_mem _ hm))

/-- On a body whose loops all have a preheader, a latch and dedicated exits, `fixRound` finds
nothing to fix. -/
theorem fixRound_of_loopsSimplifiedB [base ≼ env] {bs : List (Block env α)}
    (h : Body.loopsSimplifiedB bs = true) (st : Fresh) : fixRound st bs = none := by
  have hall : ∀ x ∈ loopsInnerFirst (Body.backEdges bs) bs,
      x.2 = Body.loopOf bs x.1 ∧ Body.preheaderB bs (Body.loopOf bs x.1) x.1 = true ∧
        Body.latchB bs x.1 = true ∧ Body.exitsB bs (Body.loopOf bs x.1) = true := by
    rintro ⟨hd, L⟩ hmem
    obtain ⟨hhd, rfl⟩ := mem_loopsInnerFirst hmem
    have h' := h
    simp only [Body.loopsSimplifiedB, List.all_eq_true, Bool.and_eq_true] at h'
    obtain ⟨⟨hp, hl⟩, he⟩ := h' hd hhd
    exact ⟨rfl, hp, hl, he⟩
  have hex : ∀ x ∈ loopsInnerFirst (Body.backEdges bs) bs,
      exitsToFix (Body.transfers bs) x.2 = [] := fun x hx => by
    rw [(hall x hx).1]
    exact exitsToFix_of_exitsB (hall x hx).2.2.2
  unfold fixRound
  dsimp only
  have hlatch : (List.filter (fun x => !Body.theOneB
      (((Body.backEdges bs).filter (·.2 == x.1)).map (·.1)) (Body.endsAtB bs · x.1))
      (loopsInnerFirst (Body.backEdges bs) bs)).isEmpty = true := by
    rw [List.isEmpty_iff, List.filter_eq_nil_iff]
    intro x hx
    simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Classical.not_not]
    exact (hall x hx).2.2.1
  have hpre : (List.filter (fun x => !Body.theOneB (((Body.transfers bs).filter fun (u, l) =>
      l == x.1 && !x.2.contains u.label).map (·.1)) (Body.endsAtB bs · x.1))
      (loopsInnerFirst (Body.backEdges bs) bs)).isEmpty = true := by
    rw [List.isEmpty_iff, List.filter_eq_nil_iff]
    intro x hx
    simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq, Classical.not_not]
    rw [(hall x hx).1]
    exact (hall x hx).2.1
  simp only [hlatch, hpre, Bool.not_true, Bool.false_eq_true, ite_false]
  have hany := addExits_none (hs := (loopsInnerFirst (Body.backEdges bs) bs).map (·.1))
    (loopsInnerFirst (Body.backEdges bs) bs) bs st hex
  have hnone : ((loopsInnerFirst (Body.backEdges bs) bs).all fun x =>
      (exitsToFix (Body.transfers bs) x.2).isEmpty) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [hex x hx]
    rfl
  generalize addExits ((loopsInnerFirst (Body.backEdges bs) bs).map (·.1)) (Body.transfers bs)
    (loopsInnerFirst (Body.backEdges bs) bs) (bs, st, [], false, []) = r at hany ⊢
  obtain ⟨bs', st', ad, any, tk⟩ := r
  simp only at hany
  simp only [hany, Bool.false_eq_true, ite_false, hnone, ite_true]

/-- On a body whose loops all have a preheader, a latch and dedicated exits, step 2 changes
nothing. -/
theorem simplifyBody_of_loopsSimplifiedB [base ≼ env] {bs : List (Block env α)}
    (h : Body.loopsSimplifiedB bs = true) (st : Fresh) : simplifyBody st bs = (bs, st) := by
  unfold simplifyBody
  generalize 3 * (Body.transfers bs).length + 3 = n
  cases n with
  | zero => rfl
  | succ n => simp only [simplifyLoops, fixRound_of_loopsSimplifiedB h st]

variable {f : Fresh → List (Block env α) → List (Block env α) × Fresh}
  {p : List (Block env α) → Bool}

mutual

/-- If `f` changes nothing on a body where `p` holds, and `p` holds of every body nested in the
instruction, then `Instruction.mapBodies f` changes nothing. -/
theorem Instruction.mapBodies_of_everyB (hf : ∀ st bs, p bs = true → f st bs = (bs, st)) :
    ∀ (i : Instruction env α) (st : Fresh), i.everyB p = true →
      Instruction.mapBodies f st i = (i, st)
  | .const .., _, _ => rfl
  | .apply _ _ _ _ _ _ ⟨regions⟩, st, h => by
    simp only [Instruction.mapBodies, Region.mapBodiesList_of_everyB hf regions st h]

/-- If `f` changes nothing on a body where `p` holds, and `p` holds of every body nested in the
instructions, then `Instruction.mapBodiesList f` changes nothing. -/
theorem Instruction.mapBodiesList_of_everyB (hf : ∀ st bs, p bs = true → f st bs = (bs, st)) :
    ∀ (is : List (Instruction env α)) (st : Fresh), Instruction.everyListB p is = true →
      Instruction.mapBodiesList f st is = (is, st)
  | [], _, _ => rfl
  | i :: is, st, h => by
    rw [Instruction.everyListB, Bool.and_eq_true] at h
    simp only [Instruction.mapBodiesList, Instruction.mapBodies_of_everyB hf i st h.1,
      Instruction.mapBodiesList_of_everyB hf is st h.2]

/-- If `f` changes nothing on a body where `p` holds, and `p` holds of every body nested in the
terminator, then `Terminator.mapBodies f` changes nothing. -/
theorem Terminator.mapBodies_of_everyB (hf : ∀ st bs, p bs = true → f st bs = (bs, st)) :
    ∀ (t : Terminator env α) (st : Fresh), t.everyB p = true → Terminator.mapBodies f st t = (t, st)
  | .apply _ _ _ _ _ ⟨regions⟩, st, h => by
    simp only [Terminator.mapBodies, Region.mapBodiesList_of_everyB hf regions st h]

/-- If `f` changes nothing on a body where `p` holds, and `p` holds of every body nested in the
blocks, then `Block.mapBodiesList f` changes nothing. -/
theorem Block.mapBodiesList_of_everyB (hf : ∀ st bs, p bs = true → f st bs = (bs, st)) :
    ∀ (bs : List (Block env α)) (st : Fresh), Block.everyListB p bs = true →
      Block.mapBodiesList f st bs = (bs, st)
  | [], _, _ => rfl
  | ⟨l, ps, ⟨is⟩, t, info⟩ :: bs, st, h => by
    rw [Block.everyListB, Bool.and_eq_true, Bool.and_eq_true] at h
    simp only [Block.mapBodiesList, Instruction.mapBodiesList_of_everyB hf is st h.1.1,
      Terminator.mapBodies_of_everyB hf t st h.1.2, Block.mapBodiesList_of_everyB hf bs st h.2]

/-- If `f` changes nothing on a body where `p` holds, and `p` holds of the region and of every
body nested in it, then `Region.mapBodies f` changes nothing. -/
theorem Region.mapBodies_of_everyB (hf : ∀ st bs, p bs = true → f st bs = (bs, st)) :
    ∀ (r : Region env α) (st : Fresh), r.everyB p = true → Region.mapBodies f st r = (r, st)
  | ⟨⟨bs⟩⟩, st, h => by
    rw [Region.everyB, Bool.and_eq_true] at h
    simp only [Region.mapBodies, Block.mapBodiesList_of_everyB hf bs st h.2, hf st bs h.1]

/-- If `f` changes nothing on a body where `p` holds, and `p` holds of each region and of every
body nested in them, then `Region.mapBodiesList f` changes nothing. -/
theorem Region.mapBodiesList_of_everyB (hf : ∀ st bs, p bs = true → f st bs = (bs, st)) :
    ∀ (rs : List (Region env α)) (st : Fresh), Region.everyListB p rs = true →
      Region.mapBodiesList f st rs = (rs, st)
  | [], _, _ => rfl
  | r :: rs, st, h => by
    rw [Region.everyListB, Bool.and_eq_true] at h
    simp only [Region.mapBodiesList, Region.mapBodies_of_everyB hf r st h.1,
      Region.mapBodiesList_of_everyB hf rs st h.2]

end

/-- A body whose loops all have dedicated exits leaves through no point of a loop, so step 1
needs only `oneExitB`. -/
theorem exitDone_of {bs : List (Block env α)} (hl : Body.loopsSimplifiedB bs = true)
    (ho : Body.oneExitB bs = true) : exitDone bs = true := by
  simp only [exitDone, ho, Bool.true_and, Body.tableOf_loopsOf, List.all_eq_true]
  intro u hu
  rw [Bool.not_eq_true', Bool.eq_false_iff]
  intro hc
  obtain ⟨_, hx, hmem⟩ := List.mem_flatMap.mp (List.contains_iff_mem.mp hc)
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
  simp only [Body.loopsSimplifiedB, List.all_eq_true, Bool.and_eq_true] at hl
  have he := (hl h hh).2
  simp only [Body.exitsB, Bool.and_eq_true, List.all_eq_true] at he
  have hn := he.2 u hu
  rw [List.contains_iff_mem.mpr hmem] at hn
  exact absurd hn (by decide)

/-- A function that `Func.checkCanonicalCFG` accepts comes back from `canonicalize` unchanged. -/
public theorem canonicalize_of_check [base ≼ env] {fn : Func env α}
    (h : fn.checkCanonicalCFG = true) :
    canonicalize fn = fn := by
  rw [Func.checkCanonicalCFG, Bool.and_eq_true] at h
  have htop : Body.loopsSimplifiedB fn.blocks.toList = true := by
    have h1 := h.1
    simp only [Body.everyB, Region.everyB, Bool.and_eq_true] at h1
    exact h1.1
  unfold canonicalize oneExit
  simp only [exitDone_of htop h.2, ite_true]
  have hr := Region.mapBodies_of_everyB (p := Body.loopsSimplifiedB)
    (fun st bs hb => simplifyBody_of_loopsSimplifiedB hb st) ⟨fn.blocks.toList.toArray⟩
    ⟨fn.labels, fn.names⟩ h.1
  simp only [hr, Array.toArray_toList]

/-- A well-formed canonical function comes back from `canonicalize` unchanged. -/
public theorem canonicalize_of_canonical [base ≼ env] {fn : Func env α} (hw : fn.WF)
    (hc : fn.CanonicalCFG) :
    canonicalize fn = fn :=
  canonicalize_of_check ((fn.checkCanonicalCFG_iff hw.distinct).mpr hc)

/-- When `check` succeeds, its result is the function it was given. -/
public theorem check_ok_val [base ≼ env] {fn : {f : Func env α // f.WF}}
    {g : {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible}} (h : check fn = .ok g) :
    g.val = fn.val := by
  unfold check at h
  split at h
  · cases h
    rfl
  · split at h <;> cases h

/-- When `run` succeeds, its result is the function put in canonical form by `canonicalize`. -/
theorem run_ok_val [base ≼ env] {fn : {f : Func env α // f.WF}}
    {g : {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible}} (h : run fn = .ok g) :
    g.val = canonicalize fn.val := by
  unfold run at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · exact check_ok_val h
  · cases h

/-- If `R` gives no error on any element of `xs`, and every result `g` of `R x` has
`val g = F x`, then the `val`s of the results are `xs.map F`, in order. -/
theorem resultsOf_map {X β γ δ : Type} (R : X → Except β γ) (val : γ → δ) (F : X → δ)
    (hR : ∀ x g, R x = .ok g → val g = F x) :
    ∀ xs : List X, errorsOf (xs.map R) = [] → (resultsOf (xs.map R)).map val = xs.map F
  | [], _ => rfl
  | x :: xs, he => by
    cases hx : R x with
    | error e => simp [errorsOf, hx] at he
    | ok g =>
      simp only [errorsOf, List.map_cons, hx, List.filterMap_cons] at he
      simp only [resultsOf, List.map_cons, hx, List.filterMap_cons, List.map_cons]
      rw [hR x g hx]
      exact congrArg _ (resultsOf_map R val F hR xs he)

/-- When `moduleWith step` succeeds, and every result of `step` is `F` of the function it was
given, function `i` of its module is `F` of function `i` of the input. -/
theorem moduleWith_funcs [base ≼ env]
    {step : {f : Func env α // f.WF} →
      Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible}}
    {F : Func env α → Func env α} (hF : ∀ fn g, step fn = .ok g → g.val = F fn.val)
    {m : Module env α} {cm : CanonicalModule env α} (h : moduleWith step m = .ok cm) :
    cm.module.raw.funcs = m.raw.funcs.map F := by
  unfold moduleWith at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hne
    split at h
    · rename_i m' hm
      cases h
      rw [Module.ofChecked_funcs hm]
      have he : errorsOf (m.raw.funcs.toList.attach.map fun x =>
          step ⟨x.1, m.wf.funcs x.1 (Array.mem_toList_iff.mp x.2)⟩) = [] := by
        simpa using hne
      have hr := resultsOf_map (fun x : {f // f ∈ m.raw.funcs.toList} =>
          step ⟨x.1, m.wf.funcs x.1 (Array.mem_toList_iff.mp x.2)⟩) Subtype.val
        (fun x => F x.1) (fun x g hx => hF _ g hx) _ he
      apply Array.ext'
      simp only [List.map_toArray, List.map_map, Array.toList_map]
      refine Eq.trans ?_ (hr.trans ?_)
      · rfl
      · simp
    · cases h

/-- When `moduleWith step` succeeds, its module is the input with its functions replaced: the same
name, ghosts and annotation. -/
theorem moduleWith_raw [base ≼ env]
    {step : {f : Func env α // f.WF} →
      Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible}}
    {m : Module env α} {cm : CanonicalModule env α} (h : moduleWith step m = .ok cm) :
    cm.module.raw = { m.raw with funcs := cm.module.raw.funcs } := by
  unfold moduleWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · rename_i m' hm
      cases h
      rw [Module.ofChecked_raw hm]
      congr 1
      apply Array.ext'
      simp
    · cases h

/-- When `runModule` succeeds, its module has the ghosts of the input, unchanged. -/
public theorem runModule_ghosts [base ≼ env] {m : Module env α}
    {cm : CanonicalModule env α} (h : runModule m = .ok cm) :
    cm.module.raw.ghosts = m.raw.ghosts := by
  rw [moduleWith_raw h]

/-- When `runModule` succeeds, function `i` of its module is function `i` of the input, put in
canonical form by `canonicalize`. -/
public theorem runModule_funcs [base ≼ env] {m : Module env α} {cm : CanonicalModule env α}
    (h : runModule m = .ok cm) : cm.module.raw.funcs = m.raw.funcs.map canonicalize :=
  moduleWith_funcs (fun _ _ hx => run_ok_val hx) h

/-- When `checkModule` succeeds, its module has the functions of the input, unchanged. -/
public theorem checkModule_funcs [base ≼ env] {m : Module env α} {cm : CanonicalModule env α}
    (h : checkModule m = .ok cm) : cm.module.raw.funcs = m.raw.funcs := by
  rw [moduleWith_funcs (F := id) (fun _ _ hx => check_ok_val hx) h, Array.map_id]

/-- When `checkModule` succeeds, its module is the module it was given. -/
public theorem checkModule_module [base ≼ env] {m : Module env α}
    {cm : CanonicalModule env α} (h : checkModule m = .ok cm) : cm.module = m := by
  have hr : cm.module.raw = m.raw := by
    rw [moduleWith_raw h, checkModule_funcs h]
  revert hr
  cases cm.module
  cases m
  intro hr
  cases hr
  rfl

end Canonicalize

end Strata.Dyn
