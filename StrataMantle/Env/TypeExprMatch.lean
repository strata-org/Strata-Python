/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.TypeExprRaw

set_option autoImplicit false

/-!
# Matching a type pattern against a type

`match? ks p t σ` finds arguments for the variables of a pattern `p`, whose kinds are `ks`,
that make it the target `t`: one-sided, first-order matching.  `σ` holds the arguments found so
far, and `matchAll` threads it through several pairs in order, so that what one pair binds fixes
what a later one may.

A literal is matched element by element, left to right.  An element covers as many of the
target's elements as the arguments found so far fix: one for a type or a type variable, and its
argument's elements for a list variable already bound.  A list variable not yet bound is
spliced in where the rest of the literal is fixed: it takes what the rest leaves.  Two such
variables in what remains of a literal make it ambiguous, `MatchError.ambiguous`, rather than a
mismatch: the target might be split more than one way, and the caller must give the arguments.

* `match?_sound` (`matchAll_sound`): what matching finds makes each pattern its target, under
  any arguments that agree with it.
* `match?_complete` (`matchAll_complete`): if some well-kinded arguments make the pattern its
  target, matching finds a substitution that agrees with them, unless it reports an ambiguity.
  Since every solution agrees with it, the solution is unique on the variables it binds.

Targets are not instantiated, so a target's variables are atoms, never bound.
-/

namespace Strata.Mantle

public section

namespace TypeExpr.Raw

/-- The arguments found so far: one slot per variable of the pattern's scope. -/
abbrev Subst := Array (Option Raw)

/-- Why matching stops. -/
inductive MatchError where
  /-- No arguments make the pattern the target. -/
  | mismatch
  /-- What remains of a literal splices the list variables `vars`, two or more, whose lengths
  nothing fixes yet. -/
  | ambiguous (vars : List Nat)
deriving DecidableEq, Repr

/-- `σ` with variable `i` bound to `t`: unchanged if it is bound to `t` already, a mismatch if
it is bound to something else or is out of scope. -/
@[expose] def bindVar (σ : Subst) (i : Nat) (t : Raw) : Except MatchError Subst :=
  if h : i < σ.size then
    match σ[i] with
    | some u => if u = t then .ok σ else .error .mismatch
    | none => .ok (σ.set i (some t) h)
  else .error .mismatch

/-- How many of a target literal's elements the pattern element `e` covers, if `σ` fixes it: a
bound variable its argument's elements (`spliced`), a type variable or any other element one.
An unbound list variable is not fixed. -/
@[expose] def elemLen? (ks : Array Kind) (σ : Subst) : Raw → Option Nat
  | .var i =>
    match σ[i]? with
    | some (some u) => some u.spliced.length
    | _ => if ks[i]? = some .list then none else some 1
  | _ => some 1

/-- How many target elements `es` cover, if `σ` fixes each. -/
@[expose] def fixedLen? (ks : Array Kind) (σ : Subst) : List Raw → Option Nat
  | [] => some 0
  | e :: es => do
    let n ← elemLen? ks σ e
    let m ← fixedLen? ks σ es
    pure (n + m)

/-- The variables of `es` that `σ` does not fix the length of. -/
@[expose] def unfixed (ks : Array Kind) (σ : Subst) (es : List Raw) : List Nat :=
  es.filterMap fun
    | .var i => if elemLen? ks σ (.var i) = none then some i else none
    | _ => none

/-- How many of `n` target elements the element `e`, followed by `es`, covers: what `σ` fixes,
or else what `es` leaves, if `σ` fixes `es`. -/
@[expose] def sliceLen (ks : Array Kind) (σ : Subst) (e : Raw) (es : List Raw) (n : Nat) :
    Except MatchError Nat :=
  match elemLen? ks σ e with
  | some l => .ok l
  | none =>
    match fixedLen? ks σ es with
    | some m => .ok (n - m)
    | none => .error (.ambiguous (unfixed ks σ (e :: es)))

/-- Match the variable `i`, an element of a literal, against the target elements `slice`: a
bound variable's argument must contribute exactly `slice`, an unbound list variable is bound to
the literal of `slice`, and an unbound type variable to `slice`'s one element. -/
@[expose] def elemVar (ks : Array Kind) (σ : Subst) (i : Nat) (slice : List Raw) :
    Except MatchError Subst :=
  match σ[i]? with
  | some (some u) => if u.spliced = slice then .ok σ else .error .mismatch
  | some none =>
    if ks[i]? = some .list then bindVar σ i (.list ⟨slice⟩)
    else
      match slice with
      | [t] => if t.isElem then bindVar σ i t else .error .mismatch
      | _ => .error .mismatch
  | none => .error .mismatch

mutual

/-- Extend `σ` so that the pattern `p` is the target `t`, its variables of kinds `ks`. -/
@[expose] def match? (ks : Array Kind) : Raw → Raw → Subst → Except MatchError Subst
  | .var i, t, σ => bindVar σ i t
  | .app n ⟨ps⟩, .app m ⟨ts⟩, σ => if n = m then matchArgs ks ps ts σ else .error .mismatch
  | .list ⟨ps⟩, .list ⟨ts⟩, σ => matchElems ks ps ts σ
  | _, _, _ => .error .mismatch

/-- `match?`, argument by argument. -/
@[expose] def matchArgs (ks : Array Kind) : List Raw → List Raw → Subst → Except MatchError Subst
  | [], [], σ => .ok σ
  | p :: ps, t :: ts, σ => do matchArgs ks ps ts (← match? ks p t σ)
  | _, _, _ => .error .mismatch

/-- Extend `σ` so that the literal elements `ps` are the target elements `ts`. -/
@[expose] def matchElems (ks : Array Kind) :
    List Raw → List Raw → Subst → Except MatchError Subst
  | [], ts, σ => if ts = [] then .ok σ else .error .mismatch
  | p :: ps, ts, σ => do
    let n ← sliceLen ks σ p ps ts.length
    let σ₁ ← match p with
      | .var i => elemVar ks σ i (ts.take n)
      | _ =>
        match ts.take n with
        | [t] => match? ks p t σ
        | _ => .error .mismatch
    matchElems ks ps (ts.drop n) σ₁

end

/-- `match?` on each pair, in order. -/
@[expose] def matchAll (ks : Array Kind) : List (Raw × Raw) → Subst → Except MatchError Subst
  | [], σ => .ok σ
  | (p, t) :: pts, σ => do matchAll ks pts (← match? ks p t σ)

/-! ## What a substitution says -/

/-- `args` gives each variable `σ` binds its binding. -/
@[expose] def Agrees (σ : Subst) (args : Array Raw) : Prop :=
  ∀ (i : Nat) (x : Raw), σ[i]? = some (some x) → args[i]? = some x

/-- `σ₂` has `σ₁`'s size, and keeps its bindings. -/
@[expose] def Extends (σ₁ σ₂ : Subst) : Prop :=
  σ₁.size = σ₂.size ∧ ∀ (i : Nat) (x : Raw), σ₁[i]? = some (some x) → σ₂[i]? = some (some x)

/-- Arguments of the kinds `ks`: a type variable's is an element of a literal, not a literal,
and a list variable's is a literal. -/
@[expose] def WellKinded (ks : Array Kind) (args : Array Raw) : Prop :=
  args.size = ks.size ∧ ∀ i (h : i < ks.size),
    (ks[i] = .type → ∃ t, args[i]? = some t ∧ t.isElem = true) ∧
    (ks[i] = .list → ∃ xs, args[i]? = some (.list ⟨xs⟩))

mutual

/-- Every variable of the expression is below `n`. -/
@[expose] def VarsLt (n : Nat) : Raw → Prop
  | .var i => i < n
  | .app _ ⟨as⟩ => VarsLtList n as
  | .list ⟨es⟩ => VarsLtList n es

/-- `VarsLt` of each. -/
@[expose] def VarsLtList (n : Nat) : List Raw → Prop
  | [] => True
  | a :: as => VarsLt n a ∧ VarsLtList n as

end

/-! ## Lemmas -/

/-- A bind succeeds when both steps do. -/
private theorem bind_eq_ok {α β : Type} {x : Except MatchError α} {f : α → Except MatchError β}
    {y : β} : (x >>= f) = .ok y ↔ ∃ z, x = .ok z ∧ f z = .ok y := by
  cases x <;> simp [bind, Except.bind]

/-- A substitution extends itself. -/
theorem Extends.refl (σ : Subst) : Extends σ σ := ⟨rfl, fun _ _ h => h⟩

/-- Extending is transitive. -/
theorem Extends.trans {σ₁ σ₂ σ₃ : Subst} (h₁ : Extends σ₁ σ₂) (h₂ : Extends σ₂ σ₃) :
    Extends σ₁ σ₃ :=
  ⟨h₁.1.trans h₂.1, fun i x h => h₂.2 i x (h₁.2 i x h)⟩

/-- Arguments that agree with a substitution agree with what it extends. -/
theorem Agrees.of_extends {σ₁ σ₂ : Subst} {args : Array Raw} (he : Extends σ₁ σ₂)
    (h : Agrees σ₂ args) : Agrees σ₁ args :=
  fun i x hx => h i x (he.2 i x hx)

/-- Binding a variable extends the substitution, with the variable bound. -/
theorem bindVar_ok {σ σ₂ : Subst} {i : Nat} {t : Raw} (h : bindVar σ i t = .ok σ₂) :
    Extends σ σ₂ ∧ σ₂[i]? = some (some t) := by
  unfold bindVar at h
  split at h
  · rename_i hi
    split at h
    · rename_i u hu
      split at h
      · rename_i heq
        cases h
        subst heq
        exact ⟨Extends.refl σ, by simp [hi, hu]⟩
      · cases h
    · rename_i hu
      cases h
      refine ⟨⟨(Array.size_set hi).symm, fun j x hj => ?_⟩, Array.getElem?_set_self hi⟩
      rw [Array.getElem?_set hi]
      split
      · rename_i hij
        subst hij
        simp [hi, hu] at hj
      · exact hj
  · cases h

/-- A bound variable stays bound to its argument in any extension. -/
theorem bindVar_agrees {σ σ₂ : Subst} {i : Nat} {t : Raw} {args : Array Raw}
    (h : bindVar σ i t = .ok σ₂) (ha : Agrees σ₂ args) : args[i]? = some t :=
  ha i t (bindVar_ok h).2

/-- A literal contributes its elements. -/
@[simp] theorem spliced_list (xs : List Raw) : (Raw.list ⟨xs⟩).spliced = xs := rfl

/-- An element of a literal contributes itself. -/
theorem spliced_of_isElem {t : Raw} (h : t.isElem = true) : t.spliced = [t] := by
  cases t with
  | var => rfl
  | app => rfl
  | list => simp [isElem] at h

/-- A variable instantiates to its argument. -/
theorem instantiate_var (args : Array Raw) (i : Nat) :
    (Raw.var i).instantiate args = args[i]?.getD (.var i) := by
  simp [instantiate]

/-- An application instantiates its arguments. -/
private theorem instantiate_app_mk (args : Array Raw) (n : Name) (as : List Raw) :
    (Raw.app n ⟨as⟩).instantiate args = .app n ⟨instantiateList args as⟩ := by
  simp [instantiate]

/-- A literal instantiates its elements, splicing. -/
private theorem instantiate_list_mk (args : Array Raw) (es : List Raw) :
    (Raw.list ⟨es⟩).instantiate args = .list ⟨instantiateElems args es⟩ := by
  simp [instantiate]

/-- A literal's elements instantiate one after another. -/
theorem instantiateElems_cons (args : Array Raw) (e : Raw) (es : List Raw) :
    instantiateElems args (e :: es) = instantiateElem args e ++ instantiateElems args es := by
  cases e <;> simp [instantiateElems, instantiateElem]

/-- An element that is not a variable instantiates to one element. -/
theorem instantiateElem_of_not_var (args : Array Raw) {e : Raw} (h : ∀ i, e ≠ .var i) :
    instantiateElem args e = [e.instantiate args] := by
  cases e with
  | var i => exact absurd rfl (h i)
  | app => rfl
  | list => rfl

/-- A variable element contributes its argument's elements. -/
theorem instantiateElem_var (args : Array Raw) (i : Nat) :
    instantiateElem args (.var i) = (args[i]?.getD (.var i)).spliced := rfl

/-! ## Soundness -/

/-- What `elemVar` finds makes the variable contribute `slice`. -/
theorem elemVar_sound {ks : Array Kind} {σ σ₂ : Subst} {i : Nat} {slice : List Raw}
    (h : elemVar ks σ i slice = .ok σ₂) :
    Extends σ σ₂ ∧ ∀ args, Agrees σ₂ args → instantiateElem args (.var i) = slice := by
  unfold elemVar at h
  split at h
  · rename_i u hu
    split at h
    · rename_i heq
      cases h
      exact ⟨Extends.refl σ, fun args ha => by simp [instantiateElem_var, ha i u hu, heq]⟩
    · cases h
  · split at h
    · exact ⟨(bindVar_ok h).1, fun args ha => by
        simp [instantiateElem_var, bindVar_agrees h ha]⟩
    · split at h
      · rename_i t
        split at h
        · rename_i ht
          exact ⟨(bindVar_ok h).1, fun args ha => by
            simp [instantiateElem_var, bindVar_agrees h ha, spliced_of_isElem ht]⟩
        · cases h
      · cases h
  · cases h

mutual

/-- What `match?` finds makes the pattern the target, under any arguments that agree with
it. -/
theorem match?_sound (ks : Array Kind) :
    ∀ (p t : Raw) (σ σ₂ : Subst), match? ks p t σ = .ok σ₂ →
      Extends σ σ₂ ∧ ∀ args, Agrees σ₂ args → p.instantiate args = t
  | .var i, t, σ, σ₂, h => by
    simp only [match?] at h
    exact ⟨(bindVar_ok h).1, fun args ha => by simp [instantiate_var, bindVar_agrees h ha]⟩
  | .app n ⟨ps⟩, .app m ⟨ts⟩, σ, σ₂, h => by
    simp only [match?] at h
    split at h
    · rename_i hnm
      subst hnm
      obtain ⟨he, hs⟩ := matchArgs_sound ks ps ts σ σ₂ h
      exact ⟨he, fun args ha => by rw [instantiate_app_mk, hs args ha]⟩
    · cases h
  | .app _ ⟨_⟩, .var _, _, _, h | .app _ ⟨_⟩, .list ⟨_⟩, _, _, h => by
    simp [match?] at h
  | .list ⟨ps⟩, .list ⟨ts⟩, σ, σ₂, h => by
    simp only [match?] at h
    obtain ⟨he, hs⟩ := matchElems_sound ks ps ts σ σ₂ h
    exact ⟨he, fun args ha => by rw [instantiate_list_mk, hs args ha]⟩
  | .list ⟨_⟩, .var _, _, _, h | .list ⟨_⟩, .app _ ⟨_⟩, _, _, h => by
    simp [match?] at h

/-- `matchArgs_sound`, argument by argument. -/
theorem matchArgs_sound (ks : Array Kind) :
    ∀ (ps ts : List Raw) (σ σ₂ : Subst), matchArgs ks ps ts σ = .ok σ₂ →
      Extends σ σ₂ ∧ ∀ args, Agrees σ₂ args → instantiateList args ps = ts
  | [], [], σ, σ₂, h => by
    simp only [matchArgs, Except.ok.injEq] at h
    subst h
    exact ⟨Extends.refl σ, fun _ _ => rfl⟩
  | p :: ps, t :: ts, σ, σ₂, h => by
    simp only [matchArgs] at h
    obtain ⟨σ₁, h₁, h₂⟩ := bind_eq_ok.mp h
    obtain ⟨he₁, hs₁⟩ := match?_sound ks p t σ σ₁ h₁
    obtain ⟨he₂, hs₂⟩ := matchArgs_sound ks ps ts σ₁ σ₂ h₂
    exact ⟨he₁.trans he₂, fun args ha => by
      simp [instantiateList, hs₁ args (ha.of_extends he₂), hs₂ args ha]⟩
  | [], _ :: _, _, _, h | _ :: _, [], _, _, h => by simp [matchArgs] at h

/-- What `matchElems` finds makes the literal's elements the target's. -/
theorem matchElems_sound (ks : Array Kind) :
    ∀ (ps ts : List Raw) (σ σ₂ : Subst), matchElems ks ps ts σ = .ok σ₂ →
      Extends σ σ₂ ∧ ∀ args, Agrees σ₂ args → instantiateElems args ps = ts
  | [], ts, σ, σ₂, h => by
    simp only [matchElems] at h
    split at h
    · rename_i hts
      cases h
      exact ⟨Extends.refl σ, fun _ _ => by simp [instantiateElems, hts]⟩
    · cases h
  | .var i :: ps, ts, σ, σ₂, h => by
    simp only [matchElems] at h
    obtain ⟨n, -, h⟩ := bind_eq_ok.mp h
    obtain ⟨σ₁, h₁, h₂⟩ := bind_eq_ok.mp h
    obtain ⟨he₁, hs₁⟩ := elemVar_sound h₁
    obtain ⟨he₂, hs₂⟩ := matchElems_sound ks ps (ts.drop n) σ₁ σ₂ h₂
    exact ⟨he₁.trans he₂, fun args ha => by
      rw [instantiateElems_cons, hs₁ args (ha.of_extends he₂), hs₂ args ha,
        List.take_append_drop]⟩
  | .app m ⟨as⟩ :: ps, ts, σ, σ₂, h => by
    simp only [matchElems] at h
    obtain ⟨n, -, h⟩ := bind_eq_ok.mp h
    split at h
    · rename_i t ht
      obtain ⟨σ₁, h₁, h₂⟩ := bind_eq_ok.mp h
      obtain ⟨he₁, hs₁⟩ := match?_sound ks (.app m ⟨as⟩) t σ σ₁ h₁
      obtain ⟨he₂, hs₂⟩ := matchElems_sound ks ps (ts.drop n) σ₁ σ₂ h₂
      exact ⟨he₁.trans he₂, fun args ha => by
        rw [instantiateElems_cons, instantiateElem_of_not_var args (by simp),
          hs₁ args (ha.of_extends he₂), hs₂ args ha, ← ht, List.take_append_drop]⟩
    · simp [bind, Except.bind] at h
  | .list ⟨es⟩ :: ps, ts, σ, σ₂, h => by
    simp only [matchElems] at h
    obtain ⟨n, -, h⟩ := bind_eq_ok.mp h
    split at h
    · rename_i t ht
      obtain ⟨σ₁, h₁, h₂⟩ := bind_eq_ok.mp h
      obtain ⟨he₁, hs₁⟩ := match?_sound ks (.list ⟨es⟩) t σ σ₁ h₁
      obtain ⟨he₂, hs₂⟩ := matchElems_sound ks ps (ts.drop n) σ₁ σ₂ h₂
      exact ⟨he₁.trans he₂, fun args ha => by
        rw [instantiateElems_cons, instantiateElem_of_not_var args (by simp),
          hs₁ args (ha.of_extends he₂), hs₂ args ha, ← ht, List.take_append_drop]⟩
    · simp [bind, Except.bind] at h

end

/-- What `matchAll` finds makes each pattern its target, under any arguments that agree with
it. -/
theorem matchAll_sound (ks : Array Kind) :
    ∀ (pts : List (Raw × Raw)) (σ σ₂ : Subst), matchAll ks pts σ = .ok σ₂ →
      Extends σ σ₂ ∧ ∀ args, Agrees σ₂ args → ∀ pt ∈ pts, pt.1.instantiate args = pt.2
  | [], σ, σ₂, h => by
    simp only [matchAll, Except.ok.injEq] at h
    subst h
    exact ⟨Extends.refl σ, fun _ _ _ hm => by simp at hm⟩
  | (p, t) :: pts, σ, σ₂, h => by
    simp only [matchAll] at h
    obtain ⟨σ₁, h₁, h₂⟩ := bind_eq_ok.mp h
    obtain ⟨he₁, hs₁⟩ := match?_sound ks p t σ σ₁ h₁
    obtain ⟨he₂, hs₂⟩ := matchAll_sound ks pts σ₁ σ₂ h₂
    refine ⟨he₁.trans he₂, fun args ha pt hm => ?_⟩
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hs₁ args (ha.of_extends he₂)
    · exact hs₂ args ha pt hm

/-! ## Completeness -/

/-- What matching gives when some arguments `τ` solve it: an ambiguity, or an extension of `σ`
that agrees with `τ`. -/
@[expose] def Solved (τ : Array Raw) (σ : Subst) (r : Except MatchError Subst) : Prop :=
  (∃ vs, r = .error (.ambiguous vs)) ∨ ∃ σ₂, r = .ok σ₂ ∧ Extends σ σ₂ ∧ Agrees σ₂ τ

private theorem bind_ok_eq {α β : Type} (x : α) (f : α → Except MatchError β) :
    (Except.ok x >>= f) = f x := rfl

private theorem bind_error_eq {α β : Type} (e : MatchError) (f : α → Except MatchError β) :
    (Except.error e >>= f) = .error e := rfl

/-- A solved first step, then a solved rest, is solved. -/
private theorem Solved.bind {τ : Array Raw} {σ : Subst} {r : Except MatchError Subst}
    {f : Subst → Except MatchError Subst} (h : Solved τ σ r)
    (hf : ∀ σ₁, Extends σ σ₁ → Agrees σ₁ τ → Solved τ σ₁ (f σ₁)) : Solved τ σ (r >>= f) := by
  rcases h with ⟨vs, rfl⟩ | ⟨σ₁, rfl, he₁, ha₁⟩
  · exact .inl ⟨vs, rfl⟩
  · rcases hf σ₁ he₁ ha₁ with ⟨vs, h⟩ | ⟨σ₂, h, he₂, ha₂⟩
    · exact .inl ⟨vs, by rw [bind_ok_eq, h]⟩
    · exact .inr ⟨σ₂, by rw [bind_ok_eq, h], he₁.trans he₂, ha₂⟩

/-- An argument of a well-kinded `τ`, by the variable's kind. -/
private theorem WellKinded.get {ks : Array Kind} {τ : Array Raw} (hτ : WellKinded ks τ) {i : Nat}
    (hi : i < ks.size) :
    (ks[i] = .type → ∃ t, τ[i]? = some t ∧ t.isElem = true) ∧
      (ks[i] = .list → ∃ xs, τ[i]? = some (.list ⟨xs⟩)) :=
  hτ.2 i hi

/-- Binding a variable to its argument in `τ` succeeds, and agrees with `τ`. -/
theorem bindVar_complete {σ : Subst} {τ : Array Raw} {i : Nat} {t : Raw} (hi : i < σ.size)
    (ha : Agrees σ τ) (ht : τ[i]? = some t) :
    ∃ σ₂, bindVar σ i t = .ok σ₂ ∧ Extends σ σ₂ ∧ Agrees σ₂ τ := by
  unfold bindVar
  rw [dif_pos hi]
  cases hu : σ[i] with
  | some u =>
    have hut : u = t := Option.some.inj ((ha i u (by simp [hi, hu])).symm.trans ht)
    exact ⟨σ, by simp [hut], Extends.refl σ, ha⟩
  | none =>
    have hb : bindVar σ i t = .ok (σ.set i (some t) hi) := by simp [bindVar, hi, hu]
    refine ⟨_, rfl, (bindVar_ok hb).1, fun j x hj => ?_⟩
    rw [Array.getElem?_set hi] at hj
    split at hj
    · rename_i hij
      subst hij
      exact ht.trans (Option.some.inj hj ▸ rfl)
    · exact ha j x hj

/-- An element's length, where `σ` fixes it, is its instance's in any `τ` that agrees. -/
theorem elemLen?_eq {ks : Array Kind} {σ : Subst} {τ : Array Raw} (hτ : WellKinded ks τ)
    (ha : Agrees σ τ) {e : Raw} (hv : VarsLt ks.size e) {n : Nat}
    (h : elemLen? ks σ e = some n) : n = (instantiateElem τ e).length := by
  cases e with
  | var i =>
    simp only [VarsLt] at hv
    simp only [elemLen?] at h
    split at h
    · rename_i u hu
      cases h
      simp [instantiateElem_var, ha i u hu]
    · split at h
      · cases h
      · rename_i hk
        cases h
        obtain ⟨t, ht, hte⟩ := (hτ.get hv).1 (by
          cases hks : ks[i] with
          | type => rfl
          | list => exact absurd (by simp [hv, hks]) hk)
        simp [instantiateElem_var, ht, spliced_of_isElem hte]
  | app => simp only [elemLen?, Option.some.injEq] at h; simp [← h, instantiateElem]
  | list => simp only [elemLen?, Option.some.injEq] at h; simp [← h, instantiateElem]

/-- `fixedLen?`, where `σ` fixes every element, is the instances' length. -/
theorem fixedLen?_eq {ks : Array Kind} {σ : Subst} {τ : Array Raw} (hτ : WellKinded ks τ)
    (ha : Agrees σ τ) : ∀ {es : List Raw}, VarsLtList ks.size es → ∀ {m : Nat},
      fixedLen? ks σ es = some m → m = (instantiateElems τ es).length
  | [], _, m, h => by simp only [fixedLen?, Option.some.injEq] at h; simp [← h, instantiateElems]
  | e :: es, hv, m, h => by
    simp only [VarsLtList] at hv
    simp only [fixedLen?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨n, hn, m₁, hm', rfl⟩ := h
    rw [instantiateElems_cons, List.length_append, ← elemLen?_eq hτ ha hv.1 hn,
      ← fixedLen?_eq hτ ha hv.2 hm']

/-- The length `sliceLen` gives the first element is its instance's, unless it reports an
ambiguity. -/
theorem sliceLen_complete {ks : Array Kind} {σ : Subst} {τ : Array Raw} (hτ : WellKinded ks τ)
    (ha : Agrees σ τ) {p : Raw} {ps : List Raw} (hv : VarsLtList ks.size (p :: ps)) :
    (∃ vs, sliceLen ks σ p ps (instantiateElems τ (p :: ps)).length =
        .error (.ambiguous vs)) ∨
      sliceLen ks σ p ps (instantiateElems τ (p :: ps)).length =
        .ok (instantiateElem τ p).length := by
  simp only [VarsLtList] at hv
  unfold sliceLen
  split
  · rename_i l hl
    exact .inr (by rw [elemLen?_eq hτ ha hv.1 hl])
  · split
    · rename_i m hm
      refine .inr ?_
      rw [instantiateElems_cons, List.length_append, ← fixedLen?_eq hτ ha hv.2 hm]
      simp
    · exact .inl ⟨_, rfl⟩

/-- `elemVar` against the variable's instance in `τ` succeeds, and agrees with `τ`. -/
theorem elemVar_complete {ks : Array Kind} {σ : Subst} {τ : Array Raw} (hτ : WellKinded ks τ)
    (hs : σ.size = ks.size) (ha : Agrees σ τ) {i : Nat} (hi : i < ks.size) :
    Solved τ σ (elemVar ks σ i (instantiateElem τ (.var i))) := by
  have hσ : i < σ.size := hs ▸ hi
  unfold elemVar
  rw [Array.getElem?_eq_getElem hσ]
  cases hu : σ[i] with
  | some u =>
    have hτu : τ[i]? = some u := ha i u (by simp [hσ, hu])
    simp only [instantiateElem_var, hτu, Option.getD_some, if_true]
    exact .inr ⟨σ, rfl, Extends.refl σ, ha⟩
  | none =>
    simp only
    cases hk : ks[i] with
    | list =>
      obtain ⟨xs, hxs⟩ := (hτ.get hi).2 hk
      rw [if_pos (by simp [hi, hk]), instantiateElem_var, hxs, Option.getD_some, spliced_list]
      obtain ⟨σ₂, h, he, ha₂⟩ := bindVar_complete hσ ha hxs
      exact .inr ⟨σ₂, h, he, ha₂⟩
    | type =>
      obtain ⟨t, ht, hte⟩ := (hτ.get hi).1 hk
      rw [if_neg (by simp [hi, hk]), instantiateElem_var, ht, Option.getD_some,
        spliced_of_isElem hte]
      simp only [hte, if_true]
      obtain ⟨σ₂, h, he, ha₂⟩ := bindVar_complete hσ ha ht
      exact .inr ⟨σ₂, h, he, ha₂⟩

mutual

/-- Completeness and unitarity: if the well-kinded arguments `τ`, agreeing with `σ`, make the
pattern the target, matching finds an extension of `σ` that agrees with `τ`, unless it reports
an ambiguity. -/
theorem match?_complete (ks : Array Kind) (τ : Array Raw) (hτ : WellKinded ks τ) :
    ∀ (p : Raw) (σ : Subst), σ.size = ks.size → Agrees σ τ → VarsLt ks.size p →
      Solved τ σ (match? ks p (p.instantiate τ) σ)
  | .var i, σ, hs, ha, hv => by
    simp only [VarsLt] at hv
    obtain ⟨t, ht⟩ : ∃ t, τ[i]? = some t :=
      Option.isSome_iff_exists.mp (by simp [hτ.1, hv])
    rw [instantiate_var, ht, Option.getD_some]
    obtain ⟨σ₂, h, he, ha₂⟩ := bindVar_complete (hs ▸ hv) ha ht
    exact .inr ⟨σ₂, h, he, ha₂⟩
  | .app n ⟨ps⟩, σ, hs, ha, hv => by
    simp only [VarsLt] at hv
    rw [instantiate_app_mk]
    simp only [match?, if_true]
    exact matchArgs_complete ks τ hτ ps σ hs ha hv
  | .list ⟨es⟩, σ, hs, ha, hv => by
    simp only [VarsLt] at hv
    rw [instantiate_list_mk]
    simp only [match?]
    exact matchElems_complete ks τ hτ es σ hs ha hv

/-- `match?_complete`, argument by argument. -/
theorem matchArgs_complete (ks : Array Kind) (τ : Array Raw) (hτ : WellKinded ks τ) :
    ∀ (ps : List Raw) (σ : Subst), σ.size = ks.size → Agrees σ τ → VarsLtList ks.size ps →
      Solved τ σ (matchArgs ks ps (instantiateList τ ps) σ)
  | [], σ, _, ha, _ => .inr ⟨σ, rfl, Extends.refl σ, ha⟩
  | p :: ps, σ, hs, ha, hv => by
    simp only [VarsLtList] at hv
    simp only [instantiateList, matchArgs]
    exact (match?_complete ks τ hτ p σ hs ha hv.1).bind fun σ₁ he₁ ha₁ =>
      matchArgs_complete ks τ hτ ps σ₁ (he₁.1 ▸ hs) ha₁ hv.2

/-- `match?_complete`, for a literal's elements. -/
theorem matchElems_complete (ks : Array Kind) (τ : Array Raw) (hτ : WellKinded ks τ) :
    ∀ (ps : List Raw) (σ : Subst), σ.size = ks.size → Agrees σ τ → VarsLtList ks.size ps →
      Solved τ σ (matchElems ks ps (instantiateElems τ ps) σ)
  | [], σ, _, ha, _ => .inr ⟨σ, by simp [matchElems, instantiateElems], Extends.refl σ, ha⟩
  | .var i :: ps, σ, hs, ha, hv => by
    have hv₁ := hv
    simp only [VarsLtList, VarsLt] at hv₁
    simp only [matchElems]
    rcases sliceLen_complete hτ ha hv with ⟨vs, h⟩ | h
    · exact .inl ⟨vs, by rw [h, bind_error_eq]⟩
    rw [h, bind_ok_eq, instantiateElems_cons, List.take_left' rfl, List.drop_left' rfl]
    exact (elemVar_complete hτ hs ha hv₁.1).bind fun σ₁ he₁ ha₁ =>
      matchElems_complete ks τ hτ ps σ₁ (he₁.1 ▸ hs) ha₁ hv₁.2
  | .app m ⟨as⟩ :: ps, σ, hs, ha, hv => by
    have hv₁ := hv
    simp only [VarsLtList] at hv₁
    simp only [matchElems]
    rcases sliceLen_complete hτ ha hv with ⟨vs, h⟩ | h
    · exact .inl ⟨vs, by rw [h, bind_error_eq]⟩
    rw [h, bind_ok_eq]
    rw [instantiateElem_of_not_var τ (by simp)]
    simp only [instantiateElems_cons, instantiateElem_of_not_var τ (e := .app m ⟨as⟩) (by simp),
      List.length_singleton, List.singleton_append, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero]
    exact (match?_complete ks τ hτ (.app m ⟨as⟩) σ hs ha hv₁.1).bind fun σ₁ he₁ ha₁ =>
      matchElems_complete ks τ hτ ps σ₁ (he₁.1 ▸ hs) ha₁ hv₁.2
  | .list ⟨es⟩ :: ps, σ, hs, ha, hv => by
    have hv₁ := hv
    simp only [VarsLtList] at hv₁
    simp only [matchElems]
    rcases sliceLen_complete hτ ha hv with ⟨vs, h⟩ | h
    · exact .inl ⟨vs, by rw [h, bind_error_eq]⟩
    rw [h, bind_ok_eq]
    rw [instantiateElem_of_not_var τ (by simp)]
    simp only [instantiateElems_cons, instantiateElem_of_not_var τ (e := .list ⟨es⟩) (by simp),
      List.length_singleton, List.singleton_append, List.take_succ_cons, List.take_zero,
      List.drop_succ_cons, List.drop_zero]
    exact (match?_complete ks τ hτ (.list ⟨es⟩) σ hs ha hv₁.1).bind fun σ₁ he₁ ha₁ =>
      matchElems_complete ks τ hτ ps σ₁ (he₁.1 ▸ hs) ha₁ hv₁.2

end

/-- Completeness and unitarity of `matchAll`: if the well-kinded arguments `τ`, agreeing with
`σ`, make each pattern its target, `matchAll` finds an extension of `σ` that agrees with `τ`,
unless it reports an ambiguity.  So what it finds is the one solution on the variables it
binds. -/
theorem matchAll_complete (ks : Array Kind) (τ : Array Raw) (hτ : WellKinded ks τ) :
    ∀ (pts : List (Raw × Raw)) (σ : Subst), σ.size = ks.size → Agrees σ τ →
      (∀ pt ∈ pts, VarsLt ks.size pt.1 ∧ pt.1.instantiate τ = pt.2) →
      Solved τ σ (matchAll ks pts σ)
  | [], σ, _, ha, _ => .inr ⟨σ, rfl, Extends.refl σ, ha⟩
  | (p, t) :: pts, σ, hs, ha, h => by
    obtain ⟨hv, ht⟩ := h (p, t) (List.mem_cons_self ..)
    simp only at hv ht
    subst ht
    simp only [matchAll]
    exact (match?_complete ks τ hτ p σ hs ha hv).bind fun σ₁ he₁ ha₁ =>
      matchAll_complete ks τ hτ pts σ₁ (he₁.1 ▸ hs) ha₁ fun pt hm =>
        h pt (List.mem_cons_of_mem _ hm)

end TypeExpr.Raw

end

end Strata.Mantle
