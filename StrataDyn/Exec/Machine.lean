/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Check

set_option autoImplicit false

/-!
# The machine

A deterministic, small-step machine for well-formed linked modules, in the style
of Crucible's simulator: `step` is a first-order function over inspectable states,
and each step reports an `Event`.  It runs at the token `Run`.

The machine's state, `State`, is a `Core` (the running frame, the frames waiting on a body,
the heap and the world), the pending transition `Mode`, how many choices the oracle has made, and
a slot for a path condition.  The oracle, a stream `Nat → Nat`, is a parameter of the run, like
the module.  A frame's code is the program's, and `block` and `pc` locate it.  The one closure
is the continuation of a rule paused at a request.

The modes:

* `exec`: run the top frame's next instruction or terminator;
* `jump`: take an edge, holding the target frame;
* `call`: enter a body, a function or a region, holding its frame and the frame waiting on it;
* `ret`: leave the top frame with a value, to the waiting frame or out of the run;
* `request`: a rule paused at a world request, a choice or an update of the world, or at a
  heap request, a new cell, a read, a write or an update of a cell, or a partial application;
* `again`: a rule that jumped to its `Again`, holding the new state, with which it runs again;
* `done`.

An instruction or terminator that transfers control leaves a pending mode, and the next step
performs it, so a hook sees every edge, entry and request before it happens.  Every control
transfer is an operation of the environment: a terminator's rule exits along a target, and a
transfer to a body's exit leaves the body.  A function returns one value; a language whose
functions raise returns a `base.Except`, which its call rule inspects.

A closure is called in one of two ways.  `base.callCode` is the machine's, and waits as a
`Wait.call` to bind the result.  A rule's call is a request, and the rule waits as a
`Wait.rule`.  Either way the machine checks the call first (`LModule.callee`): the function
exists, and takes what the closure captured and then the call's tags, and returns the call's
tag.  A rule's partial application makes a new captures cell, after the same check.

The state carries an invariant, `StateOK`, and `step` preserves it, so the machine
never checks a tag or a binding of the program's own values.  `StateOK` of a pending mode is
what performing it needs: `CoreOK` of the state it leads to, `LeftOK` for a leaving
frame, `InstOK` for a paused rule.  `CoreOK` is:

* **The store.** A frame's bindings are an array with a slot for each value of its body,
  below `LBody.slots`, so each read and write is in bounds by proof, and `set` updates it in
  place when it is unshared.  They `Agree` with a context `Γ`: each value `Γ` gives tag `t` is
  bound, at tag `t`.  The context is the checker's, and exists only in proofs.  An operand is
  looked up by `getT`, which returns the value at its tag by proof.
* **Waiting frames** expect a value of the tag they wait for: a paused rule's answer, or a
  `callCode`'s result.

Nothing constrains the heap or the world.  **The heap** holds the cells, each a value with its
tag, and the captures cells, each the values a closure captured.  A ref or a closure may be
anywhere a value may: in a datatype, a payload, a function's result, a region's or a callee's
argument.  So every access of a cell checks it, by `Heap.cell`: its location is below the
heap's size and holds a value of the ref's tag, or the run faults with `Fault.badCell`; and
every call of a closure checks it, by `LModule.callee`, or the run faults with
`Fault.badCall`.  `refNew` appends a cell, and `refSet` replaces a value with one of the same
tag; a partial application appends a captures cell, which nothing writes.  **The world** is the
environment's, and the machine only threads it.

What remains are the genuine faults: running out of fuel, a rule's gap or failure, and an
access or a call that its check refutes.

**Hooks** are pure functions `ρ → Event → State → Action`; `runHooked` runs at most some
number of steps and consults one after each.  Every step costs one unit of fuel, whatever its
mode, so `runHooked` on one unit is a debugger's single step.  When the fuel runs out or the
hook stops the run, `runHooked` returns the state, from which the run can resume.
`Exec/Trace.lean` relates a hooked run to the run's trace, and `Exec/Fused.lean` gives the
engine for execution, `runFused`.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-! ## The heap -/

section
variable {M : RunModel}

/-- The heap: the cells, one value per location, with its tag, and the captures cells, each
the values a closure captured, oldest first.  `refNew` appends a cell and `refSet` replaces a
cell's value with one of the same tag; a partial application appends a captures cell, and
nothing writes one, so a closure's captures are fixed when it is made.  A captures cell is the
machine's: no rule is given a ref to one.  The closure whose `captured` is `k + 1` has captured
`caps[k]`, and `0` stands for none. -/
structure Heap (M : RunModel) : Type where
  cells : Array (Dyn M.interp) := #[]
  caps : Array (List (Dyn M.interp)) := #[]

/-- Location `l` of `heap` holds a value of tag `t`. -/
structure Heap.Holds (heap : Heap M) (l : Nat) (t : Ty) : Prop where
  lt : l < heap.cells.size
  code : (heap.cells[l]'lt).1 = t

/-- Decide `heap.Holds l t`.  It is out of line, so that the machine's loop makes one call for
the check. -/
@[noinline] def Heap.holds (heap : Heap M) (l : Nat) (t : Ty) : Decidable (heap.Holds l t) :=
  if hl : l < heap.cells.size then
    if ht : (heap.cells[l]'hl).1 = t then isTrue ⟨hl, ht⟩ else isFalse fun h => ht h.code
  else isFalse fun h => hl h.lt

/-- **The check of a cell**: location `l` of `heap` holds a value of tag `t`, and `ok` takes
the proofs, or else `bad`, which takes `()` so that a fault is built only when the check fails.
Every access of a cell, the machine's and a rule's, goes through it. -/
@[inline] def Heap.cell {R : Type} (heap : Heap M) (l : Nat) (t : Ty)
    (ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → R) (bad : Unit → R) : R :=
  have := heap.holds l t
  if h : heap.Holds l t then ok h.lt h.code else bad ()

/-- When location `l` holds a value of tag `t`, the cell check takes `ok`. -/
theorem Heap.cell_pos {R : Type} {heap : Heap M} {l : Nat} {t : Ty}
    {ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → R} {bad : Unit → R}
    (h : heap.Holds l t) : heap.cell l t ok bad = ok h.lt h.code := by
  rw [Heap.cell, dite_eq_left h]

/-- When location `l` does not hold a value of tag `t`, the cell check takes `bad`. -/
theorem Heap.cell_neg {R : Type} {heap : Heap M} {l : Nat} {t : Ty}
    {ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → R} {bad : Unit → R}
    (h : ¬ heap.Holds l t) : heap.cell l t ok bad = bad () := by
  rw [Heap.cell, dite_eq_right h]

/-- The value at location `l`, at the tag the check found there. -/
@[inline] def Heap.valueAt (heap : Heap M) {l : Nat} {t : Ty} (hl : l < heap.cells.size)
    (ht : (heap.cells[l]'hl).1 = t) : M.interp t :=
  cast (congrArg M.interp ht) (heap.cells[l]'hl).2

/-- What the closure whose captures cell is `captured` captured: nothing if it is `0`. -/
@[inline] def Heap.captures? (heap : Heap M) (captured : Nat) : Option (List (Dyn M.interp)) :=
  if captured = 0 then some [] else heap.caps[captured - 1]?

/-- `heap` with a new cell holding `d`. -/
@[inline] def Heap.push (heap : Heap M) (d : Dyn M.interp) : Heap M :=
  { heap with cells := heap.cells.push d }

/-- `heap` with location `l`'s value replaced by `d`. -/
@[inline] def Heap.set (heap : Heap M) (l : Nat) (d : Dyn M.interp) (hl : l < heap.cells.size) :
    Heap M :=
  { heap with cells := heap.cells.set l d hl }

/-- `heap` with location `l`'s value, of tag `t`, replaced by `f` of it.  `Array.modify` takes the
value out of the array before it applies `f`, so `f` gets it unshared when the heap is. -/
@[inline] def Heap.modify (heap : Heap M) (l : Nat) (t : Ty) (f : M.interp t → M.interp t) :
    Heap M :=
  { heap with cells := heap.cells.modify l fun d =>
      if h : d.1 = t then ⟨t, f (cast (congrArg M.interp h) d.2)⟩ else d }

/-- `heap.modify l t f`, at a location `l` whose bound and tag `t` the cell check has proved, so
the tag is not compared again.  The value is swapped out of the array before `f` is applied, so
`f` gets it unshared when the heap is. -/
@[inline] def Heap.modifyAt (heap : Heap M) (l : Nat) (t : Ty) (f : M.interp t → M.interp t)
    (hl : l < heap.cells.size) (ht : (heap.cells[l]'hl).1 = t) : Heap M :=
  let r := heap.cells.swapAt l ⟨M.unit, M.unitVal⟩ hl
  { heap with cells := r.2.set l ⟨t, f (cast (congrArg M.interp ht) r.1.2)⟩ (by simp [r, hl]) }

/-- The update at a checked cell is the update `Heap.modify`. -/
theorem Heap.modifyAt_eq (heap : Heap M) (l : Nat) (t : Ty) (f : M.interp t → M.interp t)
    (hl : l < heap.cells.size) (ht : (heap.cells[l]'hl).1 = t) :
    heap.modifyAt l t f hl ht = heap.modify l t f := by
  simp only [Heap.modifyAt, Heap.modify, Array.swapAt, Array.set_set]
  congr 1
  refine Array.ext (by simp) fun i h₁ _ => ?_
  by_cases e : l = i
  · subst e; simp [Array.getElem_modify_self, ht]
  · simp only [Array.getElem_modify_of_ne e]
    exact Array.getElem_set_ne hl _ e

/-- `heap` with a new captures cell holding `ds`. -/
@[inline] def Heap.capture (heap : Heap M) (ds : List (Dyn M.interp)) : Heap M :=
  { heap with caps := heap.caps.push ds }

end

/-! ## Stores -/

section
variable {M : RunModel}

variable (M) in
/-- A store of `n` slots, each holding the unit value until it is bound. -/
@[inline] def freshStore (n : Nat) : Array (Dyn M.interp) := Array.replicate n ⟨M.unit, M.unitVal⟩

/-- The store invariant: each value `Γ` gives tag `t` is bound, at tag `t`. -/
def Agree (Γ : Ctx) (env : Array (Dyn M.interp)) : Prop :=
  ∀ v t, Γ.lookup v = some t → ∃ h : v < env.size, (env[v]'h).1 = t

/-- `v` is a slot of the store. -/
abbrev Bound (env : Array (Dyn M.interp)) (v : Nat) : Prop := v < env.size

/-- `v` is bound at tag `t`. -/
def HasTy (env : Array (Dyn M.interp)) (v : Nat) (t : Ty) : Prop :=
  v < env.size ∧ ∀ h : v < env.size, (env[v]'h).1 = t

/-- The value of `v`. -/
@[inline] def getD (env : Array (Dyn M.interp)) (v : Nat) (h : Bound env v) : Dyn M.interp := env[v]

/-- A value bound at a tag is a slot of the store. -/
theorem HasTy.bound {env : Array (Dyn M.interp)} {v : Nat} {t : Ty} (h : HasTy env v t) :
    Bound env v :=
  h.1

/-- The value of `v` at its tag. -/
@[inline] def getT (env : Array (Dyn M.interp)) (v : Nat) (t : Ty) (h : HasTy env v t) :
    M.interp t :=
  cast (congrArg M.interp (h.2 h.1)) (env[v]'h.1).2

/-- Casting a dynamic value's payload to a tag equal to its own gives back the same value. -/
theorem sigma_cast {I : Ty → Type} :
    ∀ (d : Sigma I) {t : Ty} (h : d.1 = t), (⟨t, cast (congrArg I h) d.2⟩ : Sigma I) = d
  | ⟨_, _⟩, _, rfl => rfl

variable {Γ : Ctx} {env : Array (Dyn M.interp)}

/-- Every store agrees with the empty context. -/
theorem Agree.nil : Agree [] env := fun _ _ h => nomatch h

/-- Looking up `v` in a context extended with `w` at `t` gives `t` if `v` is `w`, and otherwise
looks in the rest. -/
theorem lookup_cons {v w : Nat} {t : Ty} {Γ : Ctx} :
    ((w, t) :: Γ).lookup v = if v = w then some t else Γ.lookup v := by
  rw [List.lookup]
  by_cases h : v = w
  · rw [ite_eq_left h, h, beq_self_eq_true]
  · rw [ite_eq_right h, beq_eq_false_iff_ne.mpr h]

/-- Setting slot `v` to a value of tag `t` keeps the store in agreement with the context extended by
`v` at `t`. -/
theorem Agree.insert (hA : Agree Γ env) {v : Nat} {t : Ty} {d : Dyn M.interp}
    (hv : v < env.size) (ht : d.1 = t) : Agree ((v, t) :: Γ) (env.set v d hv) := by
  intro w u hw
  rw [lookup_cons] at hw
  split at hw
  · rename_i hwv
    cases hw
    subst hwv
    refine ⟨(Array.size_set hv).symm.subst hv, ?_⟩
    rw [Array.getElem_set_self]
    exact ht
  · rename_i hwv
    obtain ⟨hl, ht₁⟩ := hA w u hw
    refine ⟨(Array.size_set hv).symm.subst hl, ?_⟩
    rw [Array.getElem_set_ne hv hl (Ne.symm hwv)]
    exact ht₁

/-- In an agreeing store, a value the context gives tag `t` is bound at tag `t`. -/
theorem Agree.hasTy (hA : Agree Γ env) {v : Nat} {t : Ty} (h : Γ.lookup v = some t) :
    HasTy env v t :=
  let ⟨hl, ht⟩ := hA v t h
  ⟨hl, fun _ => ht⟩

/-- In an agreeing store, the value of `v` has the tag the context gives `v`. -/
theorem Agree.getD (hA : Agree Γ env) {v : Nat} {t : Ty} (h : Γ.lookup v = some t)
    (hb : Bound env v) : (getD env v hb).1 = t :=
  (hA v t h).2

/-- A scope checked in `Γ` agrees with the store. -/
theorem Agree.ofScope (hA : Agree Γ env) :
    ∀ {Γ₀ : Ctx} {l : Ctx}, Agree Γ₀ env →
      (∀ p ∈ l, Γ.lookup p.1 = some p.2) → Agree (ctxOf Γ₀ l) env
  | _, [], h₀, _ => h₀
  | Γ₀, (v, t) :: l, h₀, hl => by
    refine hA.ofScope (Γ₀ := (v, t) :: Γ₀) ?_ (fun p hp => hl p (List.mem_cons_of_mem _ hp))
    intro w u hw
    rw [lookup_cons] at hw
    split at hw
    · rename_i hwv
      cases hw
      rw [hwv]
      exact hA v t (hl (v, t) List.mem_cons_self)
    · exact h₀ w u hw

end

/-! ## Operands -/

/-- `R` holds of the elements of two lists, pairwise. -/
inductive All₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → All₂ R as bs → All₂ R (a :: as) (b :: bs)

/-- A pairwise relation implies a weaker one. -/
theorem All₂.imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {as : List α} {bs : List β}, All₂ R as bs → All₂ S as bs
  | _, _, .nil => .nil
  | _, _, .cons hab hs => .cons (h _ _ hab) (hs.imp h)

/-- Pairwise related lists have the same length. -/
theorem All₂.length_eq {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β}, All₂ R as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ hs => congrArg (· + 1) hs.length_eq

section
variable {M : RunModel}

/-- Each of `vs` is bound at its tag in `ts`. -/
def Typed (env : Array (Dyn M.interp)) : List Nat → List Ty → Prop
  | [], [] => True
  | v :: vs, t :: ts => HasTy env v t ∧ Typed env vs ts
  | _, _ => False

/-- `f` applied to the values of `vs`, each at its tag. -/
@[specialize] def applyFn (env : Array (Dyn M.interp)) {R : Type} :
    (ts : List Ty) → Fn M.interp R ts → (vs : List Nat) → Typed env vs ts → R
  | [], f, [], _ => f
  | t₀ :: t₁ :: ts, f, v₀ :: v₁ :: vs, h =>
    applyFn env ts (f (getT env v₀ t₀ h.1) (getT env v₁ t₁ h.2.1)) vs h.2.2
  | t :: ts, f, v :: vs, h => applyFn env ts (f (getT env v t h.1)) vs h.2
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- Each of `vs` is bound. -/
def AllBound (env : Array (Dyn M.interp)) : List Nat → Prop
  | [] => True
  | v :: vs => Bound env v ∧ AllBound env vs

/-- The values of `vs`. -/
@[specialize]
def lookupAll (env : Array (Dyn M.interp)) : (vs : List Nat) → AllBound env vs → List (Dyn M.interp)
  | [], _ => []
  | v :: vs, h => getD env v h.1 :: lookupAll env vs h.2

/-- Setting a slot of the store keeps the remaining parameters' ids within it. -/
theorem fits_set {env : Array (Dyn M.interp)} {p : Nat × Ty} {ps : Ctx}
    (h : ∀ q ∈ p :: ps, q.1 < env.size) (d : Dyn M.interp) :
    ∀ q ∈ ps, q.1 < (env.set p.1 d (h p List.mem_cons_self)).size :=
  fun q hq => (Array.size_set _).symm.subst (h q (List.mem_cons_of_mem _ hq))

/-- Bind `ps`, slots of the store, to `ds`, then the rest of `ps` to `xs`. -/
@[specialize]
def bindSite : (env : Array (Dyn M.interp)) → {ts : List Ty} → (ps : Ctx) → List (Dyn M.interp) →
    Args M.interp ts → (∀ p ∈ ps, p.1 < env.size) → Array (Dyn M.interp)
  | env, _, (p, _) :: ps, d :: ds, xs, h => bindSite (env.set p d _) ps ds xs (fits_set h d)
  | env, _, (p, _) :: ps, [], @Args.cons _ t _ x xs, h =>
    bindSite (env.set p ⟨t, x⟩ _) ps [] xs (fits_set h _)
  | env, _, _, _, _, _ => env

/-- Binding a site's parameters does not change the store's size. -/
theorem size_bindSite :
    ∀ (env : Array (Dyn M.interp)) {ts : List Ty} (ps : Ctx) (ds : List (Dyn M.interp))
      (xs : Args M.interp ts) (h : ∀ p ∈ ps, p.1 < env.size),
      (bindSite env ps ds xs h).size = env.size
  | _, _, [], _, _, _ => rfl
  | _, _, (_, _) :: ps, _ :: ds, xs, h =>
    (size_bindSite _ ps ds xs (fits_set h _)).trans (Array.size_set _)
  | _, _, (_, _) :: ps, [], .cons _ xs, h =>
    (size_bindSite _ ps [] xs (fits_set h _)).trans (Array.size_set _)
  | _, _, (_, _) :: _, [], .nil, _ => rfl

/-- Two slots that hold the same value give it at the same tag. -/
theorem getT_congr {env env₁ : Array (Dyn M.interp)} {v v₁ : Nat} {t : Ty}
    (h : HasTy env v t) (h₁ : HasTy env₁ v₁ t) (he : env₁[v₁]? = env[v]?) :
    getT env₁ v₁ t h₁ = getT env v t h := by
  have hd : env₁[v₁]'h₁.1 = env[v]'h.1 := by
    rw [Array.getElem?_eq_getElem h₁.1, Array.getElem?_eq_getElem h.1] at he
    exact Option.some.inj he
  have key : ∀ (d₁ d : Dyn M.interp) (p₁ : d₁.1 = t) (p : d.1 = t), d₁ = d →
      cast (congrArg M.interp p₁) d₁.2 = cast (congrArg M.interp p) d.2 := by
    intro d₁ d p₁ p e
    subst e
    rfl
  exact key _ _ (h₁.2 h₁.1) (h.2 h.1) hd

/-- `f` applied to the values of `vs`, one at a time. -/
def apply1 (env : Array (Dyn M.interp)) {R : Type} :
    (ts : List Ty) → Fn M.interp R ts → (vs : List Nat) → Typed env vs ts → R
  | [], f, [], _ => f
  | t :: ts, f, v :: vs, h => apply1 env ts (f (getT env v t h.1)) vs h.2
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- `applyFn`, which takes two operands at a time where it can, is `apply1`. -/
private theorem applyFn_eq_apply1 (env : Array (Dyn M.interp)) {R : Type} :
    ∀ (ts : List Ty) (f : Fn M.interp R ts) (vs : List Nat) (h : Typed env vs ts),
      applyFn env ts f vs h = apply1 env ts f vs h
  | [], _, [], _ => rfl
  | [_], _, [_], _ => rfl
  | _ :: _ :: ts, f, _ :: _ :: vs, h => by
    rw [applyFn, applyFn_eq_apply1 env ts _ vs h.2.2]
    rfl
  | [_], _, _ :: _ :: _, h => h.2.elim
  | _ :: _ :: _, _, [_], h => h.2.elim
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- Operands that hold the same values give `f` the same arguments. -/
private theorem apply1_congr {env env₁ : Array (Dyn M.interp)} {R : Type} :
    ∀ {vs₁ vs : List Nat}, All₂ (fun v₁ v => env₁[v₁]? = env[v]?) vs₁ vs →
      ∀ (ts : List Ty) (f : Fn M.interp R ts) (h₁ : Typed env₁ vs₁ ts) (h : Typed env vs ts),
        apply1 env₁ ts f vs₁ h₁ = apply1 env ts f vs h
  | _, _, .nil, [], _, _, _ => rfl
  | _, _, .nil, _ :: _, _, h₁, _ => h₁.elim
  | _, _, .cons _ _, [], _, h₁, _ => h₁.elim
  | _, _, .cons he hs, _ :: ts, f, h₁, h => by
    rw [apply1, apply1, getT_congr h.1 h₁.1 he]
    exact apply1_congr hs ts _ h₁.2 h.2

/-- Operands that hold the same values give `f` the same arguments. -/
theorem applyFn_congr {env env₁ : Array (Dyn M.interp)} {R : Type} {vs₁ vs : List Nat}
    (hs : All₂ (fun v₁ v => env₁[v₁]? = env[v]?) vs₁ vs) (ts : List Ty) (f : Fn M.interp R ts)
    (h₁ : Typed env₁ vs₁ ts) (h : Typed env vs ts) :
    applyFn env₁ ts f vs₁ h₁ = applyFn env ts f vs h := by
  rw [applyFn_eq_apply1, applyFn_eq_apply1]
  exact apply1_congr hs ts f h₁ h

/-- Operands that hold the same values have the same values. -/
theorem lookupAll_congr {env env₁ : Array (Dyn M.interp)} :
    ∀ {vs₁ vs : List Nat}, All₂ (fun v₁ v => env₁[v₁]? = env[v]?) vs₁ vs →
      ∀ (h₁ : AllBound env₁ vs₁) (h : AllBound env vs), lookupAll env₁ vs₁ h₁ = lookupAll env vs h
  | _, _, .nil, _, _ => rfl
  | _, _, .cons he hs, h₁, h => by
    rw [lookupAll, lookupAll, lookupAll_congr hs h₁.2 h.2]
    refine congrArg (· :: _) ?_
    rw [Array.getElem?_eq_getElem h₁.1, Array.getElem?_eq_getElem h.1] at he
    exact Option.some.inj he

/-- The values of `vs`, as their lookups. -/
theorem lookupAll_getElem? {env : Array (Dyn M.interp)} :
    ∀ {vs : List Nat} (h : AllBound env vs) (k : Nat) (hk : k < vs.length),
      (lookupAll env vs h)[k]? = env[vs[k]]?
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | v :: _, h, 0, _ => by
    rw [lookupAll, List.getElem?_cons_zero, List.getElem_cons_zero, Array.getElem?_eq_getElem h.1]
    rfl
  | _ :: vs, h, k + 1, hk => by
    rw [lookupAll, List.getElem?_cons_succ]
    exact lookupAll_getElem? h.2 k (Nat.lt_of_succ_lt_succ hk)

/-- `lookupAll` gives a value per operand. -/
theorem length_lookupAll {env : Array (Dyn M.interp)} :
    ∀ {vs : List Nat} (h : AllBound env vs), (lookupAll env vs h).length = vs.length
  | [], _ => rfl
  | _ :: _, h => congrArg (· + 1) (length_lookupAll h.2)

/-- Binding parameters leaves every other slot as it was. -/
theorem bindSite_other {w : Nat} :
    ∀ (env : Array (Dyn M.interp)) {ts : List Ty} (ps : Ctx) (ds : List (Dyn M.interp))
      (xs : Args M.interp ts) (h : ∀ p ∈ ps, p.1 < env.size), w ∉ ps.map (·.1) →
      (bindSite env ps ds xs h)[w]? = env[w]?
  | env, _, (p, _) :: ps, d :: ds, xs, h, hw => by
    rw [bindSite, bindSite_other _ ps ds xs _ (fun hm => hw (List.mem_cons_of_mem _ hm))]
    exact Array.getElem?_set_ne _ (fun he => hw (he ▸ List.mem_cons_self))
  | env, _, (p, _) :: ps, [], .cons x xs, h, hw => by
    rw [bindSite, bindSite_other _ ps [] xs _ (fun hm => hw (List.mem_cons_of_mem _ hm))]
    exact Array.getElem?_set_ne _ (fun he => hw (he ▸ List.mem_cons_self))
  | _, _, [], _, _, _, _ => rfl
  | _, _, (_, _) :: _, [], .nil, _, _ => rfl

/-- The one value a transfer to a body's exit passes: its arguments and its payload, which
validation makes exactly one value. -/
def single {r : Ty} : (ds : List (Dyn M.interp)) → {ts : List Ty} → Args M.interp ts →
    ds.map (·.1) ++ ts = [r] → Dyn M.interp
  | [d], _, .nil, _ => d
  | [], _, .cons x .nil, _ => ⟨_, x⟩
  | [], _, .nil, h => absurd h (by simp)
  | [], _, .cons _ (.cons _ _), h => absurd h (by simp)
  | [_], _, .cons _ _, h => absurd h (by simp)
  | _ :: _ :: _, _, _, h => absurd h (by simp)

/-- The one value passed to a body's exit has the tag `r` that its arguments and payload have. -/
theorem single_ty {r : Ty} :
    ∀ (ds : List (Dyn M.interp)) {ts : List Ty} (xs : Args M.interp ts)
      (h : ds.map (·.1) ++ ts = [r]), (single ds xs h).1 = r
  | [_], _, .nil, h => List.cons.inj h |>.1
  | [], _, .cons _ .nil, h => List.cons.inj h |>.1
  | [], _, .nil, h => absurd h (by simp)
  | [], _, .cons _ (.cons _ _), h => absurd h (by simp)
  | [_], _, .cons _ _, h => absurd h (by simp)
  | _ :: _ :: _, _, _, h => absurd h (by simp)

variable {Γ : Ctx} {env : Array (Dyn M.interp)}

/-- In an agreeing store, values that check against tags `ts`, with none left over, are bound at
those tags. -/
theorem Agree.typed (hA : Agree Γ env) :
    ∀ {vs : List Nat} {ts : List Ty}, checkArgs M Γ vs ts [] = .ok () → Typed env vs ts
  | [], [], _ => trivial
  | [], _ :: _, h => absurd (checkArgs_nil.mp h) (List.cons_ne_nil _ _)
  | _ :: _, [], h => absurd h checkArgs_cons_nil
  | _ :: _, _ :: _, h =>
    let ⟨h₁, h₂⟩ := checkArgs_cons.mp h
    ⟨hA.hasTy h₁, hA.typed h₂⟩

/-- In an agreeing store, values that check against tags are all bound. -/
theorem Agree.allBound (hA : Agree Γ env) :
    ∀ {vs : List Nat} {ts rest : List Ty}, checkArgs M Γ vs ts rest = .ok () →
      AllBound env vs
  | [], _, _, _ => trivial
  | _ :: _, [], _, h => absurd h checkArgs_cons_nil
  | _ :: _, _ :: _, _, h =>
    let ⟨h₁, h₂⟩ := checkArgs_cons.mp h
    ⟨(hA.hasTy h₁).bound, hA.allBound h₂⟩

/-- In an agreeing store, the tags of values that check against `ts` leaving `rest`, followed by
`rest`, are `ts`. -/
theorem Agree.lookupAll (hA : Agree Γ env) :
    ∀ {vs : List Nat} {ts rest : List Ty}, checkArgs M Γ vs ts rest = .ok () →
      ∀ hb : AllBound env vs, (lookupAll env vs hb).map (·.1) ++ rest = ts
  | [], _, _, h, _ => (checkArgs_nil.mp h).symm
  | _ :: _, [], _, h, _ => absurd h checkArgs_cons_nil
  | _ :: _, _ :: _, _, h, hb =>
    let ⟨h₁, h₂⟩ := checkArgs_cons.mp h
    List.cons_eq_cons.mpr ⟨hA.getD h₁ hb.1, hA.lookupAll h₂ hb.2⟩

/-- Binding parameters `ps` to values whose tags, then the payload's, are the parameters' tags keeps
the store in agreement with the context extended by `ps`. -/
theorem Agree.bindSite :
    ∀ {Γ : Ctx} {env : Array (Dyn M.interp)} {ts : List Ty} (ps : Ctx) (ds : List (Dyn M.interp))
      (xs : Args M.interp ts) (h : ∀ p ∈ ps, p.1 < env.size), Agree Γ env →
      ds.map (·.1) ++ ts = ps.map (·.2) → Agree (ctxOf Γ ps) (bindSite env ps ds xs h)
  | _, _, _, [], _, _, _, hA, _ => hA
  | _, _, _, (_, _) :: ps, d :: ds, xs, h, hA, hty =>
    let ⟨h₁, h₂⟩ := List.cons.inj hty
    Agree.bindSite ps ds xs (fits_set h d) (hA.insert _ h₁) h₂
  | _, _, _, (_, _) :: ps, [], .cons _ xs, h, hA, hty =>
    let ⟨h₁, h₂⟩ := List.cons.inj hty
    Agree.bindSite ps [] xs (fits_set h _) (hA.insert _ h₁) h₂
  | _, _, _, (_, _) :: _, [], .nil, _, _, hty => nomatch hty

end

/-! ## Frames and states -/

section
variable (M : RunModel)

/-- A frame: its body, the rest of its block, and its bindings, with a slot for each of the
body's values.  `block` and `pc` locate the rest of the block, the instruction at `pc` of block
`block`, for tools; the machine runs `code`. -/
structure Frame where
  func : LBody M
  code : List (LInsn M)
  term : LTerm M
  env : Array (Dyn M.interp)
  block : Nat := 0
  pc : Nat := 0
  fits : func.slots ≤ env.size

/-- An operation whose rule is running: its name, its position in its block, and what its
outcome needs: its result's id and tag, if it is an instruction, its successors and regions,
and its operands, its rule's state type and its tree with a state, which a jump to its `Again`
runs. -/
structure Inst where
  op : Name
  pc : Nat
  dst : Nat
  ret : Option Ty
  ps : List (List Ty)
  rs : List (List Ty × Ty)
  regs : List Nat
  succs : List LSite
  rerun : Rerun M rs ps (Res M.interp ret)

variable {M} in
/-- A running rule's state type. -/
abbrev Inst.St (i : Inst M) : Type := M.St i.rerun.key

variable {M} in
/-- A running rule's tree. -/
abbrev Inst.Tree (i : Inst M) : Type :=
  Exec.Tree M.interp Run M.W i.rs i.ps i.St (Res M.interp i.ret)

/-- A jump to the `Again` of operation `inst`'s rule, with the state `st` to run it with. -/
structure Reentry where
  inst : Inst M
  st : inst.St

/-- A rule waiting for the answer to its request `req`, to resume with `k`. -/
structure Pending where
  inst : Inst M
  /-- The request, a region's or a call's. -/
  req : MReq M.interp inst.rs
  /-- The tag of the answer. -/
  ret : Ty
  k : M.interp ret → inst.Tree

/-- A frame below the top, waiting for a body to return: a rule paused at a request, or the
caller of a `callCode`, which binds the value to `dst`, of tag `r`. -/
inductive Wait where
  | rule (frame : Frame M) (pending : Pending M)
  | call (frame : Frame M) (dst : Nat) (r : Ty)

variable {M} in
/-- The waiting frame. -/
def Wait.frame : Wait M → Frame M
  | .rule f _ | .call f _ _ => f

variable {M} in
/-- The tag of the value the frame waits for. -/
def Wait.ret : Wait M → Ty
  | .rule _ p => p.ret
  | .call _ _ r => r

/-- The frames and the data: the running frame, the frames waiting below it, the heap and the
world. -/
structure Core where
  top : Frame M
  conts : List (Wait M)
  heap : Heap M
  /-- The environment's world, which the machine threads but never reads. -/
  world : M.W

/-- A run's heap and world, as a run ends with them and another run starts from them. -/
structure Snapshot where
  heap : Heap M
  world : M.W

variable {M} in
/-- The snapshot a run starts from by default: an empty heap and the initial world. -/
def Snapshot.initial : Snapshot M := ⟨{}, M.w0⟩

end

/-- How a run ended. -/
inductive Result (I : Ty → Type) where
  | ok (v : Dyn I)
  | fault (f : Fault)

/-- `d`'s value, at the tag `t` it has. -/
@[inline] def Dyn.at {I : Ty → Type} (d : Dyn I) {t : Ty} (h : d.1 = t) : I t := h ▸ d.2

section
variable (M : RunModel)

/-- The pending transition: run the top frame's next instruction or terminator, take an edge,
enter a body, leave the top frame, answer a rule's world request, or nothing, the run having
ended.  A hook sees each before the machine performs it. -/
inductive Mode where
  | exec
  /-- Continue in `to`, a block of the top frame's body. -/
  | jump (to : Frame M)
  /-- Run `callee`, a function's entry block or a region's, with `w` waiting on it. -/
  | call (callee : Frame M) (w : Wait M)
  /-- Leave the top frame with `v`. -/
  | ret (v : Dyn M.interp)
  /-- The rule of operation `i`, whose frame is the top one, is at a world request: the head
  of `t`, a choice or an update. -/
  | request (i : Inst M) (t : i.Tree)
  /-- The rule of operation `r.inst`, whose frame is the top one, jumped to its `Again`: run it
  again, on its operands, with the state `r.st`. -/
  | again (r : Reentry M)
  | done (r : Result M.interp)

/-- A state of the machine. -/
structure State where
  core : Core M
  mode : Mode M := .exec
  /-- How many choices the oracle has made: the next one is its answer at this index. -/
  drawn : Nat := 0
  /-- Reserved for a symbolic reading's path condition. -/
  path : Unit := ()

end

/-- Where an instruction is: its body, its block and its position in the block. -/
structure Pos where
  fn : Name
  block : Nat
  pc : Nat
  deriving Repr, DecidableEq

/-- Where the frame is. -/
def Frame.pos {M : RunModel} (f : Frame M) : Pos := ⟨f.func.name, f.block, f.pc⟩

section
variable {M : RunModel}

/-- `f` with `v`, a value of its body, bound to `d`, in place if `f`'s store is unshared. -/
@[inline] def Frame.bind (f : Frame M) (v : Nat) (d : Dyn M.interp) (h : v < f.func.slots) :
    Frame M :=
  { f with env := f.env.set v d (Nat.lt_of_lt_of_le h f.fits),
           fits := Nat.le_trans f.fits (Nat.le_of_eq (Array.size_set _).symm) }

/-- Block `b`'s parameters are values of body `g`. -/
def ParamsFit (g : LBody M) (b : LBlock M) : Prop := ∀ p ∈ b.params, p.1 < g.slots

/-- The frame that runs block `b` of body `g` in the store `env`, its parameters bound to `ds`
and then `xs`. -/
@[inline] def Frame.entry (g : LBody M) (b : LBlock M) (env : Array (Dyn M.interp)) {ts : List Ty}
    (ds : List (Dyn M.interp)) (xs : Args M.interp ts) (hle : g.slots ≤ env.size)
    (hp : ParamsFit g b) : Frame M :=
  { func := g, code := b.insns, term := b.term,
    env := bindSite env b.params ds xs fun p hp₁ => Nat.lt_of_lt_of_le (hp p hp₁) hle,
    fits := Nat.le_trans hle (Nat.le_of_eq (size_bindSite ..).symm) }

end

/-- A rule's cell request. -/
inductive CellOp where
  | new
  | get
  | set
  | modify
  deriving Repr, DecidableEq

/-- A rule's world or cell request, as the machine answered it. -/
inductive Answer where
  /-- A choice: the oracle's answer. -/
  | choose (pick : Nat)
  /-- An update of the world. -/
  | world
  /-- A cell request at location `loc`: a new cell's, or the one read or written. -/
  | cell (op : CellOp) (loc : Nat)
  /-- A partial application, whose new closure's captures cell is `captured`. -/
  | capture (captured : Nat)
  deriving Repr, DecidableEq


/-- What a step did: the label of the machine's transitions, which hooks observe. -/
inductive Event where
  /-- Ran the instruction or terminator at `pos`. -/
  | instr (pos : Pos)
  | edge (src dst : Pos)
  /-- Entered a function or a region. -/
  | enter (fn : Name)
  | leave (fn : Name)
  | answer (a : Answer)
  | fault (f : Fault)
  deriving Repr, DecidableEq

/-! ## The invariant -/

section
variable {M : RunModel} (m : LModule M)

/-- `f` is a function or a region of the module. -/
def InM (f : LBody M) : Prop := f ∈ m.funcs ∨ f ∈ m.regions

/-- `f` runs checked code in an agreeing store. -/
def Runs (f : Frame M) : Prop :=
  InM m f.func ∧ ∃ Γ, Agree Γ f.env ∧ checkCode m f.func Γ f.code f.term = .ok ()

/-- What operation `i`'s rule, running in frame `f` whose code follows `i`, needs in context
`Γ`: its operands have their tags, so that it can run again on them, its result is a value of
the body and continues the frame, and its successors and regions check. -/
structure InstFacts (f : Frame M) (i : Inst M) (Γ : Ctx) : Prop where
  agree : Agree Γ f.env
  args : checkArgs M Γ i.rerun.args i.rerun.ts [] = .ok ()
  next : ∀ r, i.ret = some r → i.dst < f.func.slots ∧
    checkCode m f.func ((i.dst, r) :: Γ) f.code f.term = .ok ()
  sites : checkSites f.func Γ i.succs i.ps = .ok ()
  regions : checkRegions m f.func Γ i.regs i.rs = .ok ()

/-- Operation `i`'s rule runs in frame `f`. -/
def InstOK (f : Frame M) (i : Inst M) : Prop :=
  InM m f.func ∧ ∃ Γ, InstFacts m f i Γ

/-- A waiting frame resumes checked code: a rule's operation runs in it, or the code after a
`callCode` checks with its result, a value of the body, bound. -/
def WaitOK : Wait M → Prop
  | .rule f p => InstOK m f p.inst
  | .call f dst r => InM m f.func ∧ dst < f.func.slots ∧
    ∃ Γ, Agree Γ f.env ∧ checkCode m f.func ((dst, r) :: Γ) f.code f.term = .ok ()

/-- Each waiting frame expects its body's result tag, and the bottom frame returns tag
`B`. -/
def ContsOK (B : Ty) : Ty → List (Wait M) → Prop
  | R, [] => R = B
  | R, w :: cs => (WaitOK m w ∧ w.ret = R) ∧ ContsOK B w.frame.func.ret cs

/-- The invariant of a run whose bottom frame returns tag `B`, for frames about to run. -/
def CoreOK (B : Ty) (s : Core M) : Prop :=
  Runs m s.top ∧ ContsOK m B s.top.func.ret s.conts

/-- The top frame of `s` may leave with `v`. -/
def LeftOK (B : Ty) (s : Core M) (v : Dyn M.interp) : Prop :=
  v.1 = s.top.func.ret ∧ ContsOK m B s.top.func.ret s.conts

/-- The invariant of a state: what performing its pending transition needs.  A pending
edge or entry holds the frame it leads to, which runs checked code; a rule at a request or about
to run again runs in the top frame. -/
def StateOK (B : Ty) (s : State M) : Prop :=
  match s.mode with
  | .exec => CoreOK m B s.core
  | .jump to => CoreOK m B { s.core with top := to }
  | .call callee w => CoreOK m B { s.core with top := callee, conts := w :: s.core.conts }
  | .ret v => LeftOK m B s.core v
  | .request i _ => InstOK m s.core.top i ∧ ContsOK m B s.core.top.func.ret s.core.conts
  | .again r => InstOK m s.core.top r.inst ∧ ContsOK m B s.core.top.func.ret s.core.conts
  | .done _ => True

variable {m}

/-- In a well-formed module, every block of every function and region checks in its entry context.
-/
theorem WF.blocks (hwf : WF m) {f : LBody M} (hf : InM m f) :
    ∀ b ∈ f.blocks, checkCode m f (entryCtx b) b.insns b.term = .ok () :=
  hf.elim (fun h => (hwf.func h).2) (fun h => hwf.region h)

/-- In a well-formed module, every function has an entry block. -/
theorem WF.entry (hwf : WF m) {g : LBody M} (hg : g ∈ m.funcs) : 0 < g.blocks.size :=
  let ⟨⟨_, hb, _⟩, _⟩ := hwf.func hg
  (Array.getElem?_eq_some_iff.mp hb).1

/-- A function's entry block's parameters are values of the function. -/
theorem WF.entryFits (hwf : WF m) {g : LBody M} (hg : g ∈ m.funcs) (h0 : 0 < g.blocks.size) :
    ParamsFit g (g.blocks[0]'h0) := by
  obtain ⟨⟨b, hb, -, -, hfit⟩, -⟩ := hwf.func hg
  rw [Option.some.inj ((Array.getElem?_eq_getElem h0).symm.trans hb)]
  exact hfit

/-- A fresh store has a slot for each of `g`'s values. -/
theorem fresh_fits (g : LBody M) : g.slots ≤ (freshStore M g.slots).size :=
  Nat.le_of_eq Array.size_replicate.symm

variable (hwf : WF m) in
/-- The frame that runs function `i` of `m`, on `ds` and then `xs`, in a fresh store.
Validation gives the function its entry block. -/
@[inline] def callFrame (i : Nat) (hi : i < m.funcs.size) (ds : List (Dyn M.interp))
    {ts : List Ty} (xs : Args M.interp ts) : Frame M :=
  let g := m.funcs[i]'hi
  let h0 := hwf.entry (Array.getElem_mem hi)
  Frame.entry g (g.blocks[0]'h0) (freshStore M g.slots) ds xs (fresh_fits g)
    (hwf.entryFits (Array.getElem_mem hi) h0)

/-- A function's entry block, run on values of its parameters' tags, runs checked code. -/
theorem Runs.callFrame (hwf : WF m) {i : Nat} (hi : i < m.funcs.size) {ds : List (Dyn M.interp)}
    {ts : List Ty} (xs : Args M.interp ts)
    (hty : (m.funcs[i]'hi).params = ds.map (·.1) ++ ts) :
    Runs m (callFrame hwf i hi ds xs) := by
  have hg := Array.getElem_mem hi
  have h0 := hwf.entry hg
  obtain ⟨⟨b, hb, hsc, hps, -⟩, hblocks⟩ := hwf.func hg
  obtain rfl : (m.funcs[i]'hi).blocks[0]'h0 = b :=
    Option.some.inj ((Array.getElem?_eq_getElem h0).symm.trans hb)
  refine ⟨Or.inl hg, entryCtx _, ?_, hblocks _ (Array.mem_of_getElem? hb)⟩
  unfold entryCtx
  rw [hsc]
  exact Agree.bindSite _ _ xs _ Agree.nil (hty.symm.trans hps)

end

/-! ## Transfers

A transfer either enters a block of the same body or leaves the body with one value.  `take`
performs one, and `exitTo` the one an operation's exit picks. -/

section
variable {M : RunModel} {m : LModule M}

/-- Where a transfer leads: a frame at a block of the same body, or out of the body with a
value. -/
inductive Next (M : RunModel) where
  | frame (f : Frame M)
  | leave (v : Dyn M.interp)

/-- `f` may take `s`, with a payload of tags `ts`: its arguments are bound, and its target is a
block of the body whose parameters are values of the body, or the body's exit, to which it
passes one value of the body's result tag. -/
def CanTake (f : Frame M) (s : LSite) (ts : List Ty) : Prop :=
  ∃ hb : AllBound f.env s.args, match s.target with
    | .block i => i < f.func.blocks.size ∧
      ∀ hi : i < f.func.blocks.size, ParamsFit f.func f.func.blocks[i]
    | .exit => (lookupAll f.env s.args hb).map (·.1) ++ ts = [f.func.ret]

/-- `f` enters block `i`, binding its parameters to the values of `args` and then `xs`. -/
@[specialize]
def enter (f : Frame M) (i : Nat) (args : List Nat) {ts : List Ty} (xs : Args M.interp ts)
    (hb : AllBound f.env args) (hi : i < f.func.blocks.size)
    (hp : ParamsFit f.func f.func.blocks[i]) : Frame M :=
  let b := f.func.blocks[i]
  ⟨f.func, b.insns, b.term,
    bindSite f.env b.params (lookupAll f.env args hb) xs fun p hp₁ =>
      Nat.lt_of_lt_of_le (hp p hp₁) f.fits,
    i, 0, Nat.le_trans f.fits (Nat.le_of_eq (size_bindSite ..).symm)⟩

/-- `f` takes `s`, with the payload `xs` after the site's arguments. -/
@[specialize]
def take (f : Frame M) : (s : LSite) → {ts : List Ty} → Args M.interp ts → CanTake f s ts →
    Next M
  | ⟨.block i, args⟩, _, xs, h => .frame (enter f i args xs h.1 h.2.1 (h.2.2 h.2.1))
  | ⟨.exit, args⟩, _, xs, h => .leave (single (lookupAll f.env args h.1) xs h.2)

variable (m) in
/-- What a transfer from `f` leads to satisfies: a frame of the same body that runs checked
code, or a value of the body's result tag. -/
def NextOK (f : Frame M) : Next M → Prop
  | .frame g => Runs m g ∧ g.func = f.func
  | .leave v => v.1 = f.func.ret

/-- A frame whose store agrees with `Γ` may take any edge that checks in `Γ`. -/
theorem Agree.canTake {Γ : Ctx} {f : Frame M} {s : LSite} {p : List Ty}
    (hA : Agree Γ f.env) (hs : checkSite f.func Γ s p = .ok ()) : CanTake f s p := by
  obtain ⟨ps, sc, qs, ht, ha, _, hfit⟩ := checkSite_eq_ok.mp hs
  obtain ⟨target, args⟩ := s
  refine ⟨hA.allBound ha, ?_⟩
  cases target with
  | block i =>
    obtain ⟨b, hb, hbe⟩ := Option.map_eq_some_iff.mp ht
    cases hbe
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
    exact ⟨hi, fun _ => hfit⟩
  | exit =>
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj ht).symm
    exact hA.lookupAll ha _

/-- In a well-formed module, taking a checked edge leads to a frame of the same body that runs
checked code, or out with a value of the body's result tag. -/
theorem take_ok (hwf : WF m) {Γ : Ctx} {f : Frame M} {s : LSite} {ts : List Ty}
    {xs : Args M.interp ts} (hm : InM m f.func) (hA : Agree Γ f.env)
    (hs : checkSite f.func Γ s ts = .ok ()) (h : CanTake f s ts) :
    NextOK m f (take f s xs h) := by
  obtain ⟨ps, sc, qs, ht, ha, hsc, -⟩ := checkSite_eq_ok.mp hs
  obtain ⟨target, args⟩ := s
  cases target with
  | block i =>
    obtain ⟨b, hb, hbe⟩ := Option.map_eq_some_iff.mp ht
    cases hbe
    obtain rfl : f.func.blocks[i]'h.2.1 = b := (Array.getElem?_eq_some_iff.mp hb).2
    refine ⟨⟨hm, entryCtx (f.func.blocks[i]'h.2.1), ?_, ?_⟩, rfl⟩
    · exact Agree.bindSite _ _ xs _ (hA.ofScope Agree.nil (checkScope_eq_ok.mp hsc))
        (hA.lookupAll ha h.1)
    · exact hwf.blocks hm _ (Array.getElem_mem h.2.1)
  | exit => exact single_ty _ xs h.2

/-- `ss` are checked sites of `f`, which may be left along any of them. -/
def SitesOK (f : Frame M) (ss : List LSite) (ps : List (List Ty)) : Prop :=
  ∃ Γ : Ctx, Agree Γ f.env ∧ checkSites f.func Γ ss ps = .ok ()

/-- `f` leaves along the site of `ss` that `e` picks, with `e`'s payload. -/
@[specialize]
def exitTo (f : Frame M) : {ps : List (List Ty)} → (ss : List LSite) → Exit M.interp ps →
    SitesOK f ss ps → Next M
  | _, s :: _, .here xs, h => take f s xs (by
      obtain ⟨_, hA, hs⟩ := h
      exact hA.canTake (checkSites_cons.mp hs).1)
  | _, _ :: ss, .there e, h => exitTo f ss e (by
      obtain ⟨Γ, hA, hs⟩ := h
      exact ⟨Γ, hA, (checkSites_cons.mp hs).2⟩)
  | _, [], .here _, h => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)
  | _, [], .there _, h => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)

/-- In a well-formed module, leaving along whichever checked successor an exit picks leads to a
frame of the same body that runs checked code, or out with a value of the body's result tag. -/
theorem exitTo_ok (hwf : WF m) {Γ : Ctx} {f : Frame M} (hm : InM m f.func) (hA : Agree Γ f.env) :
    ∀ {ps : List (List Ty)} (ss : List LSite) (e : Exit M.interp ps) (h : SitesOK f ss ps),
      checkSites f.func Γ ss ps = .ok () → NextOK m f (exitTo f ss e h)
  | _, _ :: _, .here _, _, hs => take_ok hwf hm hA (checkSites_cons.mp hs).1 _
  | _, _ :: ss, .there e, _, hs => exitTo_ok hwf hm hA ss e _ (checkSites_cons.mp hs).2
  | _, [], .here _, _, hs => absurd hs checkSites_nil_cons
  | _, [], .there _, _, hs => absurd hs checkSites_nil_cons

end

/-! ## Instructions

Each instruction's transition, with what it needs at run time (`Ready` or `TermReady`, which
`CoreOK` gives) and the lemma that it preserves the invariant. -/

section
variable {M : RunModel} {m : LModule M}

/-- What instruction `i` needs of the state: its operands bound, at their tags where the
machine uses them at a tag. -/
def Ready (s : Core M) : LInsn M → Prop
  | .const .. => True
  | .pure _ ts _ _ args => Typed s.top.env args ts
  | .sem _ _ _ _ _ re _ _ _ => Typed s.top.env re.args re.ts
  | .refNew _ _ v => Bound s.top.env v
  | .refGet _ t c => HasTy s.top.env c (Ty.ref t)
  | .refSet _ t c v => HasTy s.top.env c (Ty.ref t) ∧ Bound s.top.env v
  | .callCode _ ts r f args => HasTy s.top.env f (Ty.fn ts r) ∧ AllBound s.top.env args

/-- What terminator `t` needs of the state. -/
def TermReady (s : Core M) : LTerm M → Prop
  | .case ts ps _ args succs => Typed s.top.env args ts ∧ SitesOK s.top succs ps
  | .sem _ _ _ re _ _ _ => Typed s.top.env re.args re.ts

/-- Bind `dst`, a value of the top frame's body, to `d` and continue with `code`, over the
heap `heap`. -/
@[specialize] def Core.next (s : Core M) (code : List (LInsn M)) (dst : Nat) (d : Dyn M.interp)
    (heap : Heap M) (hd : dst < s.top.func.slots) : Core M :=
  let f := s.top
  { top := ⟨f.func, code, f.term, f.env.set dst d (Nat.lt_of_lt_of_le hd f.fits), f.block,
      f.pc + 1, Nat.le_trans f.fits (Nat.le_of_eq (Array.size_set _).symm)⟩,
    conts := s.conts, heap, world := s.world }

/-- A new cell holding the value of `v`. -/
@[specialize] def Core.refNew (s : Core M) (code : List (LInsn M)) (dst : Nat) (t : Ty) (v : Nat)
    (h : Bound s.top.env v) (hd : dst < s.top.func.slots) : Core M :=
  -- The heap is updated within `s`, so that the update finds it unshared.
  let x := getD s.top.env v h
  let l := s.heap.cells.size
  let s₁ := { s with heap := s.heap.push x }
  s₁.next code dst ⟨Ty.ref t, M.cellAt t l⟩ s₁.heap hd

/-- The location the cell `c` names. -/
@[inline] def Core.cellLoc (s : Core M) (t : Ty) (c : Nat) (h : HasTy s.top.env c (Ty.ref t)) :
    Nat :=
  M.locOf (getT s.top.env c (Ty.ref t) h)

/-- The contents of location `l`, which the check found holding a value of the cell's
contents' tag. -/
@[specialize] def Core.refGet (s : Core M) (code : List (LInsn M)) (dst : Nat) (l : Nat)
    (hl : l < s.heap.cells.size) (hd : dst < s.top.func.slots) : Core M :=
  s.next code dst (s.heap.cells[l]'hl) s.heap hd

/-- Replace the contents of location `l`, which the check found holding a value of the cell's
contents' tag, with the value of `v`. -/
@[specialize] def Core.refSet (s : Core M) (code : List (LInsn M)) (dst : Nat) (l : Nat)
    (hl : l < s.heap.cells.size) (v : Nat) (hv : Bound s.top.env v) (hd : dst < s.top.func.slots) :
    Core M :=
  let x := getD s.top.env v hv
  let s₁ := { s with heap := s.heap.set l x hl }
  s₁.next code dst ⟨M.unit, M.unitVal⟩ s₁.heap hd

variable {s : Core M} {B : Ty}

/-- Under the run invariant, the next instruction has a tag in a context that the store agrees with.
-/
theorem CoreOK.ctx (h : CoreOK m B s) {i : LInsn M} {code : List (LInsn M)}
    (hc : s.top.code = i :: code) :
    ∃ Γ r, Agree Γ s.top.env ∧ insnTy m s.top.func Γ i = .ok r := by
  obtain ⟨⟨_, Γ, hA, hC⟩, _⟩ := h
  rw [hc] at hC
  obtain ⟨-, r, hr, -⟩ := checkCode_cons.mp hC
  exact ⟨Γ, r, hA, hr⟩

/-- The value the next instruction defines is one of its body's. -/
theorem CoreOK.dst_lt (h : CoreOK m B s) {i : LInsn M} {code : List (LInsn M)}
    (hc : s.top.code = i :: code) : i.dst < s.top.func.slots := by
  obtain ⟨⟨_, _, _, hC⟩, _⟩ := h
  rw [hc] at hC
  exact (checkCode_cons.mp hC).1

/-- Under the run invariant, the state has what the next instruction needs: its operands bound, at
their tags where the machine uses them at a tag. -/
theorem CoreOK.ready (h : CoreOK m B s) {i : LInsn M} {code : List (LInsn M)}
    (hc : s.top.code = i :: code) : Ready s i := by
  obtain ⟨Γ, r, hA, hr⟩ := h.ctx hc
  cases i with
  | const => trivial
  | pure => exact hA.typed (insnTy_pure.mp hr).1
  | sem => exact hA.typed (insnTy_sem.mp hr).1
  | refNew => exact (hA.hasTy (insnTy_refNew.mp hr).1).bound
  | refGet => exact hA.hasTy (insnTy_refGet.mp hr).1
  | refSet =>
    obtain ⟨hcr, hvr, _⟩ := insnTy_refSet.mp hr
    exact ⟨hA.hasTy hcr, (hA.hasTy hvr).bound⟩
  | callCode =>
    obtain ⟨hf, ha, _⟩ := insnTy_callCode.mp hr
    exact ⟨hA.hasTy hf, hA.allBound ha⟩

/-- An instruction that binds its result `d`, of the tag its check gives, preserves the
invariant, over any heap. -/
theorem CoreOK.next (h : CoreOK m B s) {i : LInsn M} {code : List (LInsn M)}
    (hc : s.top.code = i :: code) {heap : Heap M} {d : Dyn M.interp}
    (hd : ∀ Γ r, Agree Γ s.top.env → insnTy m s.top.func Γ i = .ok r → d.1 = r) :
    CoreOK m B (s.next code i.dst d heap (h.dst_lt hc)) := by
  obtain ⟨⟨hm, Γ, hA, hC⟩, hK⟩ := h
  rw [hc] at hC
  obtain ⟨hlt, r, hr, hC₁⟩ := checkCode_cons.mp hC
  exact ⟨⟨hm, (i.dst, r) :: Γ, hA.insert (Nat.lt_of_lt_of_le hlt s.top.fits) (hd Γ r hA hr), hC₁⟩,
    hK⟩

/-- Binding a constant's value preserves the run invariant. -/
theorem CoreOK.const (h : CoreOK m B s) {dst : Nat} {v : Dyn M.interp}
    {code : List (LInsn M)} (hc : s.top.code = .const dst v :: code) :
    CoreOK m B (s.next code dst v s.heap (h.dst_lt hc)) :=
  h.next hc fun _ _ _ hr => insnTy_const.mp hr

/-- Binding a pure instruction's result preserves the run invariant. -/
theorem CoreOK.pure (h : CoreOK m B s) {dst : Nat} {ts : List Ty} {r : Ty}
    {f : Fn M.interp (M.interp r) ts} {args : List Nat} {code : List (LInsn M)}
    (hc : s.top.code = .pure dst ts r f args :: code) (x : M.interp r) :
    CoreOK m B (s.next code dst ⟨r, x⟩ s.heap (h.dst_lt hc)) :=
  h.next hc fun _ _ _ hr => (insnTy_pure.mp hr).2

/-- Allocating a cell for a `refNew` and binding its ref preserves the run invariant. -/
theorem CoreOK.refNew (h : CoreOK m B s) {dst : Nat} {t : Ty} {v : Nat}
    {code : List (LInsn M)} (hc : s.top.code = .refNew dst t v :: code)
    (hb : Bound s.top.env v) : CoreOK m B (s.refNew code dst t v hb (h.dst_lt hc)) :=
  h.next hc fun _ _ _ hr => (insnTy_refNew.mp hr).2

/-- Binding the contents of a cell that holds a value of the tag a `refGet` reads preserves the run
invariant. -/
theorem CoreOK.refGet (h : CoreOK m B s) {dst : Nat} {t : Ty} {c : Nat}
    {code : List (LInsn M)} (hc : s.top.code = .refGet dst t c :: code) {l : Nat}
    (hl : l < s.heap.cells.size) (ht : (s.heap.cells[l]'hl).1 = t) :
    CoreOK m B (s.refGet code dst l hl (h.dst_lt hc)) :=
  h.next hc fun _ _ _ hr => ht.trans (insnTy_refGet.mp hr).2

/-- Replacing a cell's contents for a `refSet` and binding its unit result preserves the run
invariant. -/
theorem CoreOK.refSet (h : CoreOK m B s) {dst : Nat} {t : Ty} {c v : Nat}
    {code : List (LInsn M)} (hc : s.top.code = .refSet dst t c v :: code) {l : Nat}
    (hl : l < s.heap.cells.size) (hv : Bound s.top.env v) :
    CoreOK m B (s.refSet code dst l hl v hv (h.dst_lt hc)) :=
  h.next hc fun _ _ _ hr => (insnTy_refSet.mp hr).2.2

/-- The name of function `i`, for a fault. -/
def LModule.fnName (m : LModule M) (i : Nat) : Name :=
  ((m.funcs[i]?).map (·.name)).getD (.num .base i)

/-- Decide `ps = ds.map (·.1) ++ ts`, a function's parameters against what a closure captured
and a call's tags, without building the right side. -/
def fitsCaps {I : Ty → Type} : (ps : List Ty) → (ds : List (Dyn I)) → (ts : List Ty) →
    Decidable (ps = ds.map (·.1) ++ ts)
  | ps, [], ts => Ty.decEqList ps ts
  | [], _ :: _, _ => isFalse fun h => nomatch h
  | p :: ps, d :: ds, ts =>
    match Ty.decEq p d.1 with
    | isTrue h₁ => match fitsCaps ps ds ts with
      | isTrue h₂ => isTrue (by rw [h₁, h₂]; rfl)
      | isFalse h₂ => isFalse fun h => h₂ (List.cons.inj h).2
    | isFalse h₁ => isFalse fun h => h₁ (List.cons.inj h).1

/-- **The check of a call**: function `idx` of `m` takes what the closure's captures cell
`captured` holds and then arguments of tags `ts`, and returns tag `r`, and `ok` takes the
proofs, or else `bad`.  Every call and every partial application of a closure goes through
it. -/
@[inline] def LModule.callee {R : Type} (m : LModule M) (heap : Heap M) (idx captured : Nat)
    (ts : List Ty) (r : Ty)
    (ok : (hi : idx < m.funcs.size) → (caps : List (Dyn M.interp)) →
      (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts → (m.funcs[idx]'hi).ret = r → R)
    (bad : Unit → R) : R :=
  if hi : idx < m.funcs.size then
    match heap.captures? captured with
    | some caps =>
      match fitsCaps (m.funcs[idx]'hi).params caps ts, Ty.decEq (m.funcs[idx]'hi).ret r with
      | isTrue hp, isTrue hr => ok hi caps hp hr
      | _, _ => bad ()
    | none => bad ()
  else bad ()

/-- The check passes, with the closure's captures `caps`. -/
def LModule.CallOK (m : LModule M) (heap : Heap M) (idx captured : Nat) (ts : List Ty) (r : Ty)
    (caps : List (Dyn M.interp)) : Prop :=
  ∃ hi : idx < m.funcs.size, heap.captures? captured = some caps ∧
    (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts ∧ (m.funcs[idx]'hi).ret = r

/-- When the call check passes with captures `caps`, `callee` takes `ok` with them. -/
theorem LModule.callee_pos {R : Type} {m : LModule M} {heap : Heap M} {idx captured : Nat}
    {ts : List Ty} {r : Ty}
    {ok : (hi : idx < m.funcs.size) → (caps : List (Dyn M.interp)) →
      (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts → (m.funcs[idx]'hi).ret = r → R}
    {bad : Unit → R} {caps : List (Dyn M.interp)} (h : m.CallOK heap idx captured ts r caps) :
    m.callee heap idx captured ts r ok bad = ok h.1 caps h.2.2.1 h.2.2.2 := by
  obtain ⟨hi, hc, hp, hr⟩ := h
  unfold LModule.callee
  rw [dite_eq_left hi]
  split
  · rename_i caps₁ hc₁
    obtain rfl : caps₁ = caps := Option.some.inj (hc₁.symm.trans hc)
    rw [Subsingleton.elim (fitsCaps _ caps₁ ts) (isTrue hp),
      Subsingleton.elim (Ty.decEq _ r) (isTrue hr)]
  · rename_i hc₁
    exact absurd (hc₁.symm.trans hc) (by simp)

/-- When the call check fails whatever the captures, `callee` takes `bad`. -/
theorem LModule.callee_neg {R : Type} {m : LModule M} {heap : Heap M} {idx captured : Nat}
    {ts : List Ty} {r : Ty}
    {ok : (hi : idx < m.funcs.size) → (caps : List (Dyn M.interp)) →
      (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts → (m.funcs[idx]'hi).ret = r → R}
    {bad : Unit → R} (h : ∀ caps, ¬ m.CallOK heap idx captured ts r caps) :
    m.callee heap idx captured ts r ok bad = bad () := by
  unfold LModule.callee
  by_cases hi : idx < m.funcs.size
  · rw [dite_eq_left hi]
    split
    · rename_i caps hc
      cases fitsCaps (m.funcs[idx]'hi).params caps ts with
      | isFalse _ => rfl
      | isTrue hp =>
        cases Ty.decEq (m.funcs[idx]'hi).ret r with
        | isFalse _ => rfl
        | isTrue hr => exact absurd ⟨hi, hc, hp, hr⟩ (h caps)
    · rfl
  · rw [dite_eq_right hi]

/-- What a closure captured, then the arguments of a call: no work when it captured nothing, as
a static code pointer has. -/
@[inline] def appendCaps (caps ds : List (Dyn M.interp)) : List (Dyn M.interp) :=
  match caps with
  | [] => ds
  | _ :: _ => caps ++ ds

/-- `appendCaps` puts the captures before the arguments. -/
theorem appendCaps_eq (caps ds : List (Dyn M.interp)) : appendCaps caps ds = caps ++ ds := by
  cases caps <;> rfl

/-- A `callCode` enters the function its pointer names, on what it captured and the
arguments, with the caller waiting to bind the result. -/
theorem CoreOK.callCode (hwf : WF m) (h : CoreOK m B s) {dst : Nat} {ts : List Ty} {r : Ty}
    {f : Nat} {args : List Nat} {code : List (LInsn M)}
    (hc : s.top.code = .callCode dst ts r f args :: code)
    (hr : Ready s (.callCode dst ts r f args)) {idx : Nat} (hi : idx < m.funcs.size)
    {caps : List (Dyn M.interp)} (hp : (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts)
    (hret : (m.funcs[idx]'hi).ret = r) :
    CoreOK m B { s with
      top := callFrame hwf idx hi (appendCaps caps (lookupAll s.top.env args hr.2)) .nil,
      conts := .call { s.top with code, pc := s.top.pc + 1 } dst r :: s.conts } := by
  obtain ⟨⟨hm, Γ, hA, hC⟩, hK⟩ := h
  rw [hc] at hC
  obtain ⟨hd, _, hr₁, hC₁⟩ := checkCode_cons.mp hC
  obtain ⟨-, ha, rfl⟩ := insnTy_callCode.mp hr₁
  have hty := hA.lookupAll ha hr.2
  rw [List.append_nil] at hty
  refine ⟨Runs.callFrame hwf hi .nil ?_, ⟨⟨hm, hd, Γ, hA, hC₁⟩, hret.symm⟩, hK⟩
  rw [appendCaps_eq, List.map_append, hty, List.append_nil]
  exact hp

/-- Under the run invariant, a frame whose code is done has what its terminator needs. -/
theorem CoreOK.termReady (h : CoreOK m B s) (hc : s.top.code = []) {t : LTerm M}
    (ht : s.top.term = t) : TermReady s t := by
  obtain ⟨⟨_, Γ, hA, hC⟩, _⟩ := h
  rw [hc, ht] at hC
  cases t with
  | case =>
    obtain ⟨h₁, h₂⟩ := checkTerm_case.mp hC
    exact ⟨hA.typed h₁, Γ, hA, h₂⟩
  | sem => exact hA.typed (checkTerm_sem.mp hC).1

/-- In a well-formed module, the successor a `case` terminator picks leads to a frame of the same
body that runs checked code, or out with a value of the body's result tag. -/
theorem CoreOK.caseNext (hwf : WF m) (h : CoreOK m B s) (hc : s.top.code = [])
    {ts : List Ty} {ps : List (List Ty)} {f : Fn M.interp (Exit M.interp ps) ts}
    {args : List Nat} {succs : List LSite} (ht : s.top.term = .case ts ps f args succs)
    (e : Exit M.interp ps) (hs : SitesOK s.top succs ps) :
    NextOK m s.top (exitTo s.top succs e hs) := by
  obtain ⟨⟨hm, Γ, hA, hC⟩, _⟩ := h
  rw [hc, ht] at hC
  exact exitTo_ok hwf hm hA succs e hs (checkTerm_case.mp hC).2

/-- A value left to a waiting rule has its request's answer code. -/
theorem LeftOK.rule {v : Dyn M.interp} (h : LeftOK m B s v) {f : Frame M} {p : Pending M}
    {cs : List (Wait M)} (hk : s.conts = .rule f p :: cs) :
    v.1 = p.ret ∧ InstOK m f p.inst ∧ ContsOK m B f.func.ret cs := by
  obtain ⟨hty, hK⟩ := h
  rw [hk] at hK
  obtain ⟨⟨hi, hr⟩, hK₁⟩ := hK
  exact ⟨hty.trans hr.symm, hi, hK₁⟩

/-- The caller of a `callCode` binds its result to a value of its body. -/
theorem LeftOK.call_dst {v : Dyn M.interp} (h : LeftOK m B s v) {f : Frame M} {dst : Nat}
    {r : Ty} {cs : List (Wait M)} (hk : s.conts = .call f dst r :: cs) : dst < f.func.slots := by
  obtain ⟨-, hK⟩ := h
  rw [hk] at hK
  exact hK.1.1.2.1

/-- A value left to the caller of a `callCode` binds its result, and the caller runs on. -/
theorem LeftOK.call {v : Dyn M.interp} (h : LeftOK m B s v) {f : Frame M} {dst : Nat} {r : Ty}
    {cs : List (Wait M)} (hk : s.conts = .call f dst r :: cs) :
    CoreOK m B { top := f.bind dst v (h.call_dst hk), conts := cs, heap := s.heap,
                  world := s.world } := by
  obtain ⟨hty, hK⟩ := h
  rw [hk] at hK
  obtain ⟨⟨⟨hm, hd, Γ, hA, hC⟩, hr⟩, hK₁⟩ := hK
  exact ⟨⟨hm, (dst, r) :: Γ, hA.insert (Nat.lt_of_lt_of_le hd f.fits) (hty.trans hr.symm), hC⟩,
    hK₁⟩

end

/-! ## Rules, regions and calls

A rule's tree runs in the frame of its operation, whose code is what follows the operation.
`settle` reads the head of the tree: a result binds the instruction's value, a jump is a
pending transfer along a successor, a jump to its `Again` a pending run of the rule with a new
state, `Mode.again`, a body request is a pending entry, and a world or cell request pauses
the rule in `Mode.request`.
`serve` answers it: a choice from the oracle, an update of the world, or a new cell, a read, a
write or an update of one, each checked as the machine's own are (`Heap.cell`).  A
region runs in a frame that sees the enclosing frame's values; a function, in a fresh one.
When the body returns, the rule resumes with its value (`leave`).  Each of these is one
step. -/

section
variable {M : RunModel} {m : LModule M} {B : Ty}

/-- A running rule's operands are bound at their tags. -/
theorem InstOK.typed {f : Frame M} {i : Inst M} (h : InstOK m f i) :
    Typed f.env i.rerun.args i.rerun.ts :=
  let ⟨_, _, hi⟩ := h
  hi.agree.typed hi.args

/-- The tree of operation `i`'s rule, running again on its operands in `env` with the state
`s`. -/
@[inline] def Inst.again (i : Inst M) (env : Array (Dyn M.interp))
    (h : Typed env i.rerun.args i.rerun.ts) (s : i.St) : i.Tree :=
  applyFn env i.rerun.ts i.rerun.tree i.rerun.args h s

/-- The result a rule's tree returned, with its tag: an instruction's. -/
def resDyn : (o : Option Ty) → Res M.interp o → Dyn M.interp
  | some r, v => ⟨r, v⟩
  | none, v => nomatch v

/-- A rule's result is an instruction's, and has that instruction's result tag. -/
theorem resDyn_ty : ∀ (o : Option Ty) (v : Res M.interp o), ∃ r, o = some r ∧ (resDyn o v).1 = r
  | some r, _ => ⟨r, rfl, rfl⟩
  | none, v => nomatch v

/-- Regions that check against signatures are as many as the signatures. -/
theorem checkRegions_length {fn : LBody M} {Γ : Ctx} :
    ∀ {ks : List Nat} {rs : List (List Ty × Ty)}, checkRegions m fn Γ ks rs = .ok () →
      ks.length = rs.length
  | [], [], _ => rfl
  | _ :: _, (_, _) :: _, h => congrArg (· + 1) (checkRegions_length (checkRegions_cons.mp h).2)
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- When regions check against signatures, region `j` checks at signature `j`. -/
theorem checkRegions_get {fn : LBody M} {Γ : Ctx} :
    ∀ {ks : List Nat} {rs : List (List Ty × Ty)} (h : checkRegions m fn Γ ks rs = .ok ())
      (j : Fin rs.length),
      checkRegion m fn Γ (ks[j.1]'(by rw [checkRegions_length h]; exact j.2)) (rs.get j).1
        (rs.get j).2 = .ok ()
  | [], [], _, j => j.elim0
  | _ :: _, (_, _) :: _, h, ⟨0, _⟩ => (checkRegions_cons.mp h).1
  | _ :: _, (_, _) :: _, h, ⟨j + 1, hj⟩ =>
    checkRegions_get (checkRegions_cons.mp h).2 ⟨j, Nat.lt_of_succ_lt_succ hj⟩
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h

/-- A running rule's operation has as many regions as region signatures. -/
theorem InstOK.length {f : Frame M} {i : Inst M} (h : InstOK m f i) :
    i.regs.length = i.rs.length :=
  let ⟨_, _, hi⟩ := h
  checkRegions_length hi.regions

/-- The module index of region `j` of `i`. -/
def Inst.region (i : Inst M) (j : Fin i.rs.length) (h : i.regs.length = i.rs.length) : Nat :=
  i.regs[j.1]'(by rw [h]; exact j.2)

/-- Region `j` of a running rule's operation checks at its signature in a context that the frame's
store agrees with. -/
theorem InstOK.region_ok {f : Frame M} {i : Inst M} (h : InstOK m f i) (j : Fin i.rs.length) :
    ∃ Γ, Agree Γ f.env ∧
      checkRegion m f.func Γ (i.region j h.length) (i.rs.get j).1 (i.rs.get j).2 = .ok () :=
  let ⟨_, Γ, hi⟩ := h
  ⟨Γ, hi.agree, checkRegions_get hi.regions j⟩

/-- Region `j` of a running rule's operation is a region of the module. -/
theorem InstOK.region_lt {f : Frame M} {i : Inst M} (h : InstOK m f i)
    (j : Fin i.rs.length) : i.region j h.length < m.regions.size := by
  obtain ⟨_, _, hc⟩ := h.region_ok j
  obtain ⟨_, _, hf, _⟩ := checkRegion_eq_ok.mp hc
  exact (Array.getElem?_eq_some_iff.mp hf).1

/-- Region `j` of a running rule's operation has an entry block. -/
theorem InstOK.region_entry {f : Frame M} {i : Inst M} (h : InstOK m f i)
    (j : Fin i.rs.length) :
    0 < (m.regions[i.region j h.length]'(h.region_lt j)).blocks.size := by
  obtain ⟨_, _, hc⟩ := h.region_ok j
  obtain ⟨_, _, hf, hb, _⟩ := checkRegion_eq_ok.mp hc
  rw [Option.some.inj ((Array.getElem?_eq_getElem (h.region_lt j)).symm.trans hf)]
  exact (Array.getElem?_eq_some_iff.mp hb).1

/-- Region `j` of `i` fits the slots of the body it runs in, and so do its entry block's
parameters. -/
theorem InstOK.region_fits {f : Frame M} {i : Inst M} (h : InstOK m f i)
    (j : Fin i.rs.length) :
    (m.regions[i.region j h.length]'(h.region_lt j)).slots ≤ f.func.slots ∧
      ParamsFit (m.regions[i.region j h.length]'(h.region_lt j))
        ((m.regions[i.region j h.length]'(h.region_lt j)).blocks[0]'(h.region_entry j)) := by
  obtain ⟨_, _, hc⟩ := h.region_ok j
  obtain ⟨g, b, hg, hb, -, -, -, hsl, hp⟩ := checkRegion_eq_ok.mp hc
  obtain rfl : m.regions[i.region j h.length]'(h.region_lt j) = g :=
    Option.some.inj ((Array.getElem?_eq_getElem (h.region_lt j)).symm.trans hg)
  obtain rfl : (m.regions[i.region j h.length]'(h.region_lt j)).blocks[0]'(h.region_entry j) =
      b := Option.some.inj ((Array.getElem?_eq_getElem (h.region_entry j)).symm.trans hb)
  exact ⟨hsl, hp⟩

variable (m) in
/-- The frame that runs region `k` on `args`: its entry block, seeing frame `f`'s values, in a
copy of its store. -/
@[specialize] def regionStart (f : Frame M) (k : Nat) (hk : k < m.regions.size)
    (hb : 0 < (m.regions[k]'hk).blocks.size) (hs : (m.regions[k]'hk).slots ≤ f.func.slots)
    (hp : ParamsFit (m.regions[k]'hk) ((m.regions[k]'hk).blocks[0]'hb)) {ts : List Ty}
    (args : Args M.interp ts) : Frame M :=
  let g := m.regions[k]'hk
  Frame.entry g (g.blocks[0]'hb) f.env [] args (Nat.le_trans hs f.fits) hp

/-- The entry block of a function of a well-formed module has parameters that fit its
slots. -/
theorem WF.fits_of_getElem? (hwf : WF m) {k : Nat} {g : LBody M} {b : LBlock M}
    (hg : m.funcs[k]? = some g) (hb : g.blocks[0]? = some b) : ParamsFit g b := by
  obtain ⟨hgi, rfl⟩ := Array.getElem?_eq_some_iff.mp hg
  obtain ⟨⟨b₀, hb₀, -, -, hfit⟩, -⟩ := hwf.func (Array.getElem_mem hgi)
  obtain rfl : b₀ = b := Option.some.inj (hb₀.symm.trans hb)
  exact hfit

/-- A frame that runs a body's entry block, `b`, seeing values that agree with its scope, runs
checked code. -/
theorem Runs.entry (hwf : WF m) {f : LBody M} {b : LBlock M} (hf : InM m f) (hb : b ∈ f.blocks)
    {Γ : Ctx} {env : Array (Dyn M.interp)} (hA : Agree Γ env)
    (hsc : ∀ p ∈ b.scope, Γ.lookup p.1 = some p.2) {ts : List Ty} (hps : b.paramTys = ts)
    (args : Args M.interp ts) (hle : f.slots ≤ env.size) (hp : ParamsFit f b) :
    Runs m (Frame.entry f b env [] args hle hp) :=
  ⟨hf, entryCtx b, Agree.bindSite b.params [] args _ (hA.ofScope Agree.nil hsc)
    (by rw [List.map_nil, List.nil_append]; exact hps.symm), hwf.blocks hf b hb⟩

/-- A rule's request for region `j` starts it, with the rule waiting for its result. -/
theorem InstOK.start (hwf : WF m) {c : Core M} {i : Inst M} (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) (j : Fin i.rs.length)
    (args : Args M.interp (i.rs.get j).1)
    (k : M.interp (i.rs.get j).2 → i.Tree) :
    CoreOK m B { c with
      top := regionStart m c.top (i.region j hi.length) (hi.region_lt j) (hi.region_entry j)
        (hi.region_fits j).1 (hi.region_fits j).2 args,
      conts := .rule c.top ⟨i, .region j args, (i.rs.get j).2, k⟩ :: c.conts } := by
  obtain ⟨Γ, hA, hc⟩ := hi.region_ok j
  obtain ⟨g, b, hg, hb, hps, hret, hsc, -, -⟩ := checkRegion_eq_ok.mp hc
  obtain rfl : m.regions[i.region j hi.length]'(hi.region_lt j) = g :=
    Option.some.inj ((Array.getElem?_eq_getElem (hi.region_lt j)).symm.trans hg)
  obtain rfl : (m.regions[i.region j hi.length]'(hi.region_lt j)).blocks[0]'(hi.region_entry j) =
      b := Option.some.inj ((Array.getElem?_eq_getElem (hi.region_entry j)).symm.trans hb)
  exact ⟨Runs.entry hwf (Or.inr (Array.getElem_mem (hi.region_lt j)))
    (Array.getElem_mem (hi.region_entry j)) hA (checkScope_eq_ok.mp hsc) hps args
    (Nat.le_trans (hi.region_fits j).1 c.top.fits) (hi.region_fits j).2, ⟨hi, hret.symm⟩, hK⟩

/-- A rule's call of a closure starts its function, on what the closure captured and the
call's arguments, with the rule waiting for its result. -/
theorem InstOK.call (hwf : WF m) {c : Core M} {i : Inst M} (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) {sig : List Ty × Ty} {idx captured : Nat}
    (hl : idx < m.funcs.size) {caps : List (Dyn M.interp)}
    (hp : (m.funcs[idx]'hl).params = caps.map (·.1) ++ sig.1)
    (hr : (m.funcs[idx]'hl).ret = sig.2) (args : Payload (sig.1.map M.interp))
    (k : M.interp sig.2 → i.Tree) :
    CoreOK m B { c with top := callFrame hwf idx hl caps (Args.ofPayload sig.1 args),
                        conts := .rule c.top ⟨i, .call sig idx captured args, sig.2, k⟩ ::
                          c.conts } :=
  ⟨Runs.callFrame hwf hl _ hp, ⟨hi, hr.symm⟩, hK⟩

/-- A rule's result is bound to a value of its body. -/
theorem InstOK.dst_lt {f : Frame M} {i : Inst M} (hi : InstOK m f i)
    (v : Res M.interp i.ret) : i.dst < f.func.slots :=
  let ⟨_, _, hf⟩ := hi
  let ⟨r, hr, _⟩ := resDyn_ty i.ret v
  (hf.next r hr).1

/-- Binding a running rule's result in its frame satisfies the run invariant, over any heap and
world. -/
theorem InstOK.next {f : Frame M} {i : Inst M} {cs : List (Wait M)} {heap : Heap M}
    {world : M.W} (hi : InstOK m f i) (hK : ContsOK m B f.func.ret cs) (v : Res M.interp i.ret) :
    CoreOK m B { top := f.bind i.dst (resDyn i.ret v) (hi.dst_lt v), conts := cs, heap,
                  world } := by
  obtain ⟨hm, Γ, hf⟩ := hi
  obtain ⟨r, hr, hd⟩ := resDyn_ty i.ret v
  obtain ⟨hlt, hC⟩ := hf.next r hr
  exact ⟨⟨hm, (i.dst, r) :: Γ, hf.agree.insert (Nat.lt_of_lt_of_le hlt f.fits) hd, hC⟩, hK⟩

/-- A running rule's operation's successors are checked sites of its frame. -/
theorem InstOK.sitesOK {f : Frame M} {i : Inst M} (hi : InstOK m f i) :
    SitesOK f i.succs i.ps :=
  let ⟨_, Γ, hf⟩ := hi
  ⟨Γ, hf.agree, hf.sites⟩

/-- In a well-formed module, the successor a rule's exit picks leads to a frame of the same body
that runs checked code, or out with a value of the body's result tag. -/
theorem InstOK.exit (hwf : WF m) {f : Frame M} {i : Inst M} (hi : InstOK m f i)
    (e : Exit M.interp i.ps) : NextOK m f (exitTo f i.succs e hi.sitesOK) := by
  obtain ⟨hm, Γ, hf⟩ := id hi
  exact exitTo_ok hwf hm hf.agree i.succs e _ hf.sites

/-- A `sem` instruction's rule runs in its frame, whose code is what follows it. -/
theorem CoreOK.inst {s : Core M} (h : CoreOK m B s) {op : Name} {dst : Nat}
    {rs : List (List Ty × Ty)} {r : Ty} {ps : List (List Ty)} {re : Rerun M rs ps (M.interp r)}
    {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) (M.interp r)) re.ts}
    {regs : List Nat} {succs : List LSite} {code : List (LInsn M)}
    (hc : s.top.code = .sem op dst rs r ps re f regs succs :: code) :
    InstOK m { s.top with code, pc := s.top.pc + 1 }
      ⟨op, s.top.pc, dst, some r, ps, rs, regs, succs, re⟩ := by
  obtain ⟨⟨hm, Γ, hA, hC⟩, _⟩ := h
  rw [hc] at hC
  obtain ⟨hd, r₁, hr, hC₁⟩ := checkCode_cons.mp hC
  obtain ⟨ha, hreg, hsites, rfl⟩ := insnTy_sem.mp hr
  exact ⟨hm, Γ, ⟨hA, ha, fun _ h => Option.some.inj h ▸ ⟨hd, hC₁⟩, hsites, hreg⟩⟩

/-- A terminal rule runs in its frame, whose code is done. -/
theorem CoreOK.termInst {s : Core M} (h : CoreOK m B s) (hc : s.top.code = []) {op : Name}
    {rs : List (List Ty × Ty)} {ps : List (List Ty)} {re : Rerun M rs ps Empty}
    {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) Empty) re.ts}
    {regs : List Nat} {succs : List LSite}
    (ht : s.top.term = .sem op rs ps re f regs succs) :
    InstOK m s.top ⟨op, s.top.pc, 0, none, ps, rs, regs, succs, re⟩ := by
  obtain ⟨⟨hm, Γ, hA, hC⟩, _⟩ := h
  rw [hc, ht] at hC
  obtain ⟨ha, hreg, hsites⟩ := checkTerm_sem.mp hC
  exact ⟨hm, Γ, ⟨hA, ha, (fun _ h => nomatch h), hsites, hreg⟩⟩

end

/-! ## The step function -/

section
variable {M : RunModel} {m : LModule M} (hwf : WF m) (oracle : Nat → Nat) {B : Ty}

variable (m B) in
/-- A step: its event and the next state, or, from a state whose run has
ended, the outcome, the heap, the world and the number of choices made. -/
inductive StepR where
  | next (e : Event) (s : State M) (h : StateOK m B s)
  | final (r : Result M.interp) (heap : Heap M) (world : M.W) (drawn : Nat)

/-- Stop with the fault `f`: the step reports it, and the next one ends the run. -/
@[inline] def faultStep (c : Core M) (f : Fault) (drawn : Nat) : StepR m B :=
  .next (.fault f) ⟨c, .done (.fault f), drawn, ()⟩ trivial

/-- A transfer, pending: an edge to a block of the body, or leaving it. -/
@[inline] def transfer (c : Core M) (n : Next M) (hn : NextOK m c.top n)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) (ev : Event) : StepR m B :=
  match n, hn with
  | .frame g, hn => .next ev ⟨c, .jump g, drawn, ()⟩ ⟨hn.1, hn.2 ▸ hK⟩
  | .leave v, hn => .next ev ⟨c, .ret v, drawn, ()⟩ ⟨hn, hK⟩

/-- A rule's call of the closure `(idx, captured)` at the signature `sig`, pending: an entry
into its function, if the check passes. -/
@[inline] def visitCall (c : Core M) (i : Inst M) (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) (ev : Event) (sig : List Ty × Ty)
    (idx captured : Nat) (args : Payload (sig.1.map M.interp)) (k : M.interp sig.2 → i.Tree) :
    StepR m B :=
  m.callee c.heap idx captured sig.1 sig.2
    (fun hl caps hp hr => .next ev ⟨c, .call (callFrame hwf idx hl caps (Args.ofPayload sig.1 args))
        (.rule c.top ⟨i, .call sig idx captured args, sig.2, k⟩), drawn, ()⟩
      (hi.call hwf hK hl hp hr args k))
    (fun _ => faultStep c (.badCall (m.fnName idx)) drawn)

/-- A rule's request for region `j`, pending: an entry into it. -/
@[inline] def visitRegion (c : Core M) (i : Inst M) (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) (ev : Event) (j : Fin i.rs.length)
    (args : Args M.interp (i.rs.get j).1) (k : M.interp (i.rs.get j).2 → i.Tree) : StepR m B :=
  .next ev ⟨c, .call (regionStart m c.top (i.region j hi.length) (hi.region_lt j)
      (hi.region_entry j) (hi.region_fits j).1 (hi.region_fits j).2 args)
      (.rule c.top ⟨i, .region j args, (i.rs.get j).2, k⟩), drawn, ()⟩
    (hi.start hwf hK j args k)

/-- Continue the rule of operation `i`, whose tree is now `t`, in `c`'s top frame: bind its
result, take an edge along a successor, run `i` again with a new state, enter a body, stop, or
pause at a world request.  `ev` is the step's event. -/
@[inline] def settle (c : Core M) (i : Inst M) (hi : InstOK m c.top i)
    (hK : ContsOK m B c.top.func.ret c.conts) (drawn : Nat) (ev : Event) : i.Tree → StepR m B
  | .ret v => .next ev
      ⟨{ c with top := c.top.bind i.dst (resDyn i.ret v) (hi.dst_lt v) }, .exec, drawn, ()⟩
      (hi.next hK v)
  | .stop (.jump (.exit e)) =>
    transfer c (exitTo c.top i.succs e hi.sitesOK) (hi.exit hwf e) hK drawn ev
  | .stop (.jump (.again st)) => .next ev ⟨c, .again ⟨i, st⟩, drawn, ()⟩ ⟨hi, hK⟩
  | .stop (.fault f) => faultStep c f drawn
  | .vis (.region j args) k => visitRegion hwf c i hi hK drawn ev j args k
  | .vis (.call sig idx captured args) k => visitCall hwf c i hi hK drawn ev sig idx captured args k
  | t => .next ev ⟨c, .request i t, drawn, ()⟩ ⟨hi, hK⟩

/-- Answer the world request at the head of `t`, from the rule of operation `i`. -/
@[inline] def serve (c : Core M) (i : Inst M) (t : i.Tree)
    (h : InstOK m c.top i ∧ ContsOK m B c.top.func.ret c.conts) (drawn : Nat) : StepR m B :=
  match t with
  | .choose k =>
    let pick := oracle drawn
    settle hwf c i h.1 h.2 (drawn + 1) (.answer (.choose pick)) (k pick)
  | .update f =>
    -- Taking the state apart first leaves `f` the only holder of the world.
    match c, h with
    | ⟨top, conts, heap, w⟩, h =>
      let p := f w
      settle hwf ⟨top, conts, heap, p.1⟩ i h.1 h.2 drawn (.answer .world) p.2
  | .vis (.new t v) k =>
    -- The new location is read before the push, so that the push finds the heap unshared.
    let l := c.heap.cells.size
    settle hwf { c with heap := c.heap.push ⟨t, v⟩ } i h.1 h.2 drawn (.answer (.cell .new l))
      (k ⟨⟨l, trivial⟩⟩)
  | .vis (.get t l) k =>
    c.heap.cell l t
      (fun hl ht => settle hwf c i h.1 h.2 drawn (.answer (.cell .get l)) (k (c.heap.valueAt hl ht)))
      (fun _ => faultStep c (.badCell l) drawn)
  | .vis (.set t l v) k =>
    c.heap.cell l t
      (fun hl _ => settle hwf { c with heap := c.heap.set l ⟨t, v⟩ hl } i h.1 h.2 drawn
        (.answer (.cell .set l)) (k ()))
      (fun _ => faultStep c (.badCell l) drawn)
  | .vis (.modify t l g) k =>
    c.heap.cell l t
      (fun hl ht => settle hwf { c with heap := c.heap.modifyAt l t g hl ht } i h.1 h.2 drawn
        (.answer (.cell .modify l)) (k ()))
      (fun _ => faultStep c (.badCell l) drawn)
  | .vis (.bind t v sig idx captured) k =>
    let l := c.heap.caps.size + 1
    m.callee c.heap idx captured (t :: sig.1) sig.2
      (fun _ caps _ _ => settle hwf { c with heap := c.heap.capture (caps ++ [⟨t, v⟩]) } i h.1 h.2
        drawn (.answer (.capture l)) (k ⟨⟨idx, l, trivial⟩⟩))
      (fun _ => faultStep c (.badCall (m.fnName idx)) drawn)
  | t => settle hwf c i h.1 h.2 drawn (.instr c.top.pos) t

/-- Run the terminator of the top frame, `t`, whose code is done. -/
@[inline] def execTerm (c : Core M) (h : CoreOK m B c) (hc : c.top.code = []) (drawn : Nat) :
    (t : LTerm M) → c.top.term = t → StepR m B
  | .case ts ps f args succs, ht =>
    have hr : TermReady c (.case ts ps f args succs) := h.termReady hc ht
    let e := applyFn c.top.env ts f args hr.1
    transfer c (exitTo c.top succs e hr.2) (h.caseNext hwf hc ht e hr.2) h.2 drawn
      (.instr c.top.pos)
  | .sem op rs ps re f regs succs, ht =>
    have hr : TermReady c (.sem op rs ps re f regs succs) := h.termReady hc ht
    settle hwf c ⟨op, c.top.pc, 0, none, ps, rs, regs, succs, re⟩ (h.termInst hc ht) h.2 drawn
      (.instr c.top.pos) (applyFn c.top.env re.ts f re.args hr)

/-- Run the top frame's next instruction, the head of `code`, or its terminator. -/
@[inline] def execCode (c : Core M) (h : CoreOK m B c) (drawn : Nat) :
    (code : List (LInsn M)) → c.top.code = code → StepR m B
  | [], hc => execTerm hwf c h hc drawn c.top.term rfl
  | .const dst v :: code, hc =>
    .next (.instr c.top.pos) ⟨c.next code dst v c.heap (h.dst_lt hc), .exec, drawn, ()⟩
      (h.const hc)
  | .pure dst ts r f args :: code, hc =>
    .next (.instr c.top.pos)
      ⟨c.next code dst ⟨r, applyFn c.top.env ts f args (h.ready hc)⟩ c.heap (h.dst_lt hc), .exec,
        drawn, ()⟩
      (h.pure hc _)
  | .sem op dst rs r ps re f regs succs :: code, hc =>
    settle hwf { c with top := { c.top with code, pc := c.top.pc + 1 } }
      ⟨op, c.top.pc, dst, some r, ps, rs, regs, succs, re⟩
      (h.inst hc) h.2 drawn (.instr c.top.pos) (applyFn c.top.env re.ts f re.args (h.ready hc))
  | .refNew dst t v :: code, hc =>
    .next (.instr c.top.pos) ⟨c.refNew code dst t v (h.ready hc) (h.dst_lt hc), .exec, drawn, ()⟩
      (h.refNew hc (h.ready hc))
  | .refGet dst t x :: code, hc =>
    let l := c.cellLoc t x (h.ready hc)
    c.heap.cell l t
      (fun hl ht => .next (.instr c.top.pos) ⟨c.refGet code dst l hl (h.dst_lt hc), .exec, drawn, ()⟩
        (h.refGet hc hl ht))
      (fun _ => faultStep c (.badCell l) drawn)
  | .refSet dst t x v :: code, hc =>
    have hr : HasTy c.top.env x (Ty.ref t) ∧ Bound c.top.env v := h.ready hc
    let l := c.cellLoc t x hr.1
    c.heap.cell l t
      (fun hl _ => .next (.instr c.top.pos)
        ⟨c.refSet code dst l hl v hr.2 (h.dst_lt hc), .exec, drawn, ()⟩ (h.refSet hc hl hr.2))
      (fun _ => faultStep c (.badCell l) drawn)
  | .callCode dst ts r f args :: code, hc =>
    have hr : Ready c (.callCode dst ts r f args) := h.ready hc
    let g := M.fnOf (getT c.top.env f (Ty.fn ts r) hr.1)
    m.callee c.heap g.idx g.captured ts r
      (fun hl caps hp hret =>
        .next (.instr c.top.pos)
          ⟨c, .call (callFrame hwf g.idx hl (appendCaps caps (lookupAll c.top.env args hr.2)) .nil)
            (.call { c.top with code, pc := c.top.pc + 1 } dst r), drawn, ()⟩
          (h.callCode hwf hc hr hl hp hret))
      (fun _ => faultStep c (.badCall (m.fnName g.idx)) drawn)

/-- Run the top frame's next instruction, or its terminator. -/
@[inline] def exec (c : Core M) (h : CoreOK m B c) (drawn : Nat) : StepR m B :=
  execCode hwf c h drawn c.top.code rfl

/-- Leave the top frame with `v`, the rules `cs` waiting: end the run, or resume the rule
waiting on the body. -/
@[inline] def leaveTo (c : Core M) (v : Dyn M.interp) (h : LeftOK m B c v) (drawn : Nat) :
    (cs : List (Wait M)) → c.conts = cs → StepR m B
  | [], _ => .next (.leave c.top.func.name) ⟨c, .done (.ok v), drawn, ()⟩ trivial
  | .rule f p :: cs, hk =>
    have hw := h.rule hk
    settle hwf { top := f, conts := cs, heap := c.heap, world := c.world } p.inst hw.2.1 hw.2.2
      drawn (.leave c.top.func.name) (p.k (v.at hw.1))
  | .call f dst _ :: cs, hk =>
    .next (.leave c.top.func.name)
      ⟨{ top := f.bind dst v (h.call_dst hk), conts := cs, heap := c.heap, world := c.world },
        .exec, drawn, ()⟩ (h.call hk)

/-- Leave the top frame with `v`: end the run, or resume the rule waiting on the body. -/
@[inline] def leave (c : Core M) (v : Dyn M.interp) (h : LeftOK m B c v) (drawn : Nat) :
    StepR m B :=
  leaveTo hwf c v h drawn c.conts rfl

/-- One step: perform the pending transition. -/
@[inline] def step : (s : State M) → StateOK m B s → StepR m B
  | ⟨c, .exec, drawn, _⟩, h => exec hwf c h drawn
  | ⟨c, .jump to, drawn, _⟩, h =>
    .next (.edge c.top.pos to.pos) ⟨{ c with top := to }, .exec, drawn, ()⟩ h
  | ⟨c, .call callee w, drawn, _⟩, h =>
    .next (.enter callee.func.name)
      ⟨{ c with top := callee, conts := w :: c.conts }, .exec, drawn, ()⟩ h
  | ⟨c, .ret v, drawn, _⟩, h => leave hwf c v h drawn
  | ⟨c, .request i t, drawn, _⟩, h => serve hwf oracle c i t h drawn
  | ⟨c, .again r, drawn, _⟩, h =>
    settle hwf c r.inst h.1 h.2 drawn (.instr ⟨c.top.func.name, c.top.block, r.inst.pc⟩)
      (r.inst.again c.top.env h.1.typed r.st)
  | ⟨c, .done r, drawn, _⟩, _ => .final r c.heap c.world drawn

variable (m B) in
/-- How a run of at most some fuel ended: an outcome, the snapshot of its heap and world, the
number of choices made and the fuel left, or the state where the fuel ran out, from
which the run can resume. -/
inductive RunEnd where
  | done (r : Result M.interp) (snap : Snapshot M) (drawn left : Nat)
  | timeout (s : State M) (h : StateOK m B s)

/-! ## Hooks

A hook is a pure function of its own state, a step's event and the machine state the step led
to.  It continues, continues from another well-formed state, or stops the run, which
returns the state so that a driver can resume it.  `runFused` is a loop of its own, so a
run without a hook pays nothing for hooks.

`Action.modify` must supply the state's `StateOK`, so a generic hook can modify only
to a state whose invariant it can prove outright, such as a fault.  That is a
deliberate limit: a hook is not given the invariant of the state it sees. -/

variable (m B) in
/-- What a hook asks for after a step. -/
inductive Action (ρ : Type) where
  | continue (st : ρ)
  /-- Continue from `s` instead: a well-formed state. -/
  | modify (st : ρ) (s : State M) (h : StateOK m B s)
  | stop (st : ρ)

variable (m B) in
/-- A hook with state `ρ`. -/
abbrev Hook (ρ : Type) : Type := ρ → Event → State M → Action m B ρ

variable (m B) in
/-- How a hooked run ended: as a run does, or stopped by the hook at a state, with
the fuel left. -/
inductive HookEnd where
  | done (r : Result M.interp) (snap : Snapshot M) (drawn left : Nat)
  | timeout (s : State M) (h : StateOK m B s)
  | stopped (s : State M) (h : StateOK m B s) (left : Nat)

/-- The run's end, unless the hook stopped it. -/
def HookEnd.toRunEnd : HookEnd m B → Option (RunEnd m B)
  | .done r sn d n => some (.done r sn d n)
  | .timeout s h => some (.timeout s h)
  | .stopped .. => none

/-- Run at most `fuel` steps, consulting `hook` after each. -/
@[specialize]
def runHooked {ρ : Type} (hook : Hook m B ρ) : Nat → ρ → (s : State M) → StateOK m B s →
    HookEnd m B × ρ
  | 0, st, s, h => (.timeout s h, st)
  | n + 1, st, s, h => match step hwf oracle s h with
    | .final r hp w d => (.done r ⟨hp, w⟩ d n, st)
    | .next ev s₁ h₁ => match hook st ev s₁ with
      | .continue st₁ => runHooked hook n st₁ s₁ h₁
      | .modify st₁ s₂ h₂ => runHooked hook n st₁ s₂ h₂
      | .stop st₁ => (.stopped s₁ h₁ n, st₁)

end

end

end Strata.Dyn.Exec
