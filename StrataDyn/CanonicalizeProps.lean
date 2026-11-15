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
  function `i` of the input, put in canonical form.  With no loop records, the pass is
  `canonicalize` (`canonicalizeWith_nil`);
* `Canonicalize.check_ok_val`, `Canonicalize.checkModule_module`: `check` and `checkModule` never
  change what they are given;
* `Canonicalize.runModule_ghosts`: `runModule` keeps the module's ghosts as they are.

## To prove

`Canonicalize.run` checks its result at run time.  These statements are still to prove, about
the pass as it is written, which reads each body through hash maps:

* `canonicalize_wf`: the result of a well-formed function is well formed;
* `canonicalize_canonical`: the result of a well-formed function is canonical, if every loop has
  one entry (`Func.Reducible`) and no loop inside a region leaves its region;
* that `canonicalize` keeps `Func.Reducible`.  With these three, `run` would need to check only
  its input for the loop and return blocks; what a front end's `CanonicalSpec` asks is checked on
  the result in any case;
* that `reducibleB` accepts every body whose loops have one entry and whose blocks are all
  reachable, so that `run` never rejects such a function;
* when Dyn has a semantics, that `canonicalize` keeps a function's outcomes: every run of the
  result is a run of the original, one `jump` longer at each forwarding block, and the converse.
  Its proof is a stuttering simulation that uses only the meaning of `jump`.
-/

namespace Strata.Dyn

namespace Canonicalize

variable {env : Env Unit} {α : Type}

/-- A function that `Func.checkCanonicalCFG` accepts comes back from `canonicalize` unchanged. -/
public theorem canonicalize_of_check [base ≼ env] {fn : Func env α}
    (h : fn.checkCanonicalCFG = true) :
    canonicalize fn = fn := by
  unfold canonicalize
  simp only [h, ite_true]

/-- A well-formed canonical function comes back from `canonicalize` unchanged. -/
public theorem canonicalize_of_canonical [base ≼ env] {fn : Func env α} (hw : fn.WF)
    (hc : fn.CanonicalCFG) :
    canonicalize fn = fn :=
  canonicalize_of_check ((fn.checkCanonicalCFG_iff hw.distinct).mpr hc)

/-- With no record heads, `canonicalizeWith` is `canonicalize`. -/
theorem canonicalizeWith_nil [base ≼ env] (fn : Func env α) :
    canonicalizeWith [] fn = canonicalize fn := rfl

/-- When `check` succeeds, its result is the function it was given. -/
public theorem check_ok_val [base ≼ env] {fn : {f : Func env α // f.WF}}
    {spec : CanonicalSpec env α}
    {g : {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible ∧ spec.Holds g}}
    (h : check fn spec = .ok g) : g.val = fn.val := by
  unfold check at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · split at h <;> cases h

/-- When `run` succeeds, its function is the canonicalized input. -/
theorem run_ok_val [base ≼ env] {fn : {f : Func env α // f.WF}} {spec : CanonicalSpec env α}
    {g : {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible ∧ spec.Holds g}}
    (h : run fn spec = .ok g) :
    g.val = canonicalizeWith (recordHeads spec fn.val) fn.val := by
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
theorem moduleWith_funcs [base ≼ env] {spec : CanonicalSpec env α}
    {step : {f : Func env α // f.WF} →
      Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible ∧ spec.Holds g}}
    {F : Func env α → Func env α} (hF : ∀ fn g, step fn = .ok g → g.val = F fn.val)
    {m : Module env α} {cm : CanonicalModule env α spec} (h : moduleWith step m = .ok cm) :
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
theorem moduleWith_raw [base ≼ env] {spec : CanonicalSpec env α}
    {step : {f : Func env α // f.WF} →
      Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible ∧ spec.Holds g}}
    {m : Module env α} {cm : CanonicalModule env α spec} (h : moduleWith step m = .ok cm) :
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
public theorem runModule_ghosts [base ≼ env] {m : Module env α} {spec : CanonicalSpec env α}
    {cm : CanonicalModule env α spec} (h : runModule m spec = .ok cm) :
    cm.module.raw.ghosts = m.raw.ghosts := by
  rw [moduleWith_raw h]

/-- When `runModule` succeeds, function `i` of its module is function `i` of the input, put in
canonical form by `canonicalizeWith`, with the heads of its loop records. -/
public theorem runModule_funcs [base ≼ env] {m : Module env α} {spec : CanonicalSpec env α}
    {cm : CanonicalModule env α spec} (h : runModule m spec = .ok cm) :
    cm.module.raw.funcs = m.raw.funcs.map fun f => canonicalizeWith (recordHeads spec f) f :=
  moduleWith_funcs (fun _ _ hx => run_ok_val hx) h

/-- When `checkModule` succeeds, its module has the functions of the input, unchanged. -/
public theorem checkModule_funcs [base ≼ env] {m : Module env α} {spec : CanonicalSpec env α}
    {cm : CanonicalModule env α spec} (h : checkModule m spec = .ok cm) :
    cm.module.raw.funcs = m.raw.funcs := by
  rw [moduleWith_funcs (F := id) (fun _ _ hx => check_ok_val hx) h, Array.map_id]

/-- When `checkModule` succeeds, its module is the module it was given. -/
public theorem checkModule_module [base ≼ env] {m : Module env α} {spec : CanonicalSpec env α}
    {cm : CanonicalModule env α spec} (h : checkModule m spec = .ok cm) : cm.module = m := by
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
