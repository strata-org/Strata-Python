/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Effects

set_option autoImplicit false

/-!
# Properties of the effects of rules

Key theorems: `Within.lift` (a lower level implies a higher one) and `Within.bind`, which make
`Within` compose as a rule's computation does; `pure_reads_alike`: two readings of a `pure` tree
from the same heap and from worlds that `immEq` relates end alike.  Each recursive theorem
follows the mutual recursion of its definition through an update.

The definitions are in `Exec/Effects.lean`: the levels (`Level`), what a language says about its
world (`WorldSpec`), `Within`, `FnAll` and `VarAll`, and the readings (`Reading.read`, `EnvImm`).
-/

namespace Strata.Dyn.Exec.Effects

@[expose] public section

section
variable {I : Ty → Type} {σ : Type} [Store σ] {W St : Type} {rs : List (List Ty × Ty)}
  {ps : List (List Ty)} {S R : Type}

/-- `Within.after` of a pair is `Within` of the pair's tree. -/
theorem Within.after_eq (sp : WorldSpec W St) (s : St) (e : Level) (post : Cells → R → Prop)
    (N : Cells) (p : W × Tree I σ W rs ps S R) :
    Within.after sp s e post N p = Within sp s e post N p.2 := by
  cases p; rfl

/-- A level at most `pure` is `pure`. -/
theorem Level.eq_pure {e : Level} (h : e.le .pure) : e = .pure := by
  cases e <;> simp_all [Level.le, Level.rank]

/-- `≤` on levels is transitive. -/
theorem Level.le_trans {a b c : Level} (h₁ : a.le b) (h₂ : b.le c) : a.le c :=
  Nat.le_trans h₁ h₂

/-- Above a level other than `pure`, the level isn't `pure`. -/
theorem Level.ne_pure_up {e e' : Level} (h : e.le e') (he : e ≠ .pure) : e' ≠ .pure := by
  cases e <;> cases e' <;> simp_all [Level.le, Level.rank]

/-- Below a level that isn't `writes`, the level isn't `writes`. -/
private theorem Level.ne_writes {e e' : Level} (h : e.le e') (h' : e' ≠ .writes) : e ≠ .writes := by
  cases e <;> cases e' <;> simp_all [Level.le, Level.rank]

/-- Above `calls` or `writes`, the level is `calls` or `writes`. -/
theorem Level.calls_up {e e' : Level} (h : e.le e') (h' : e = .calls ∨ e = .writes) :
    e' = .calls ∨ e' = .writes := by
  cases e <;> cases e' <;> simp_all [Level.le, Level.rank]

/-- Above `writes`, the level is `writes`. -/
theorem Level.writes_up {e e' : Level} (h : e.le e') (h' : e = .writes) : e' = .writes := by
  cases e <;> cases e' <;> simp_all [Level.le, Level.rank]

mutual
/-- `Within` lifts to a higher level. -/
theorem Within.lift {sp : WorldSpec W St} {s : St} {e e' : Level} {post : Cells → R → Prop}
    (he : e.le e') :
    ∀ (t : Tree I σ W rs ps S R) {N : Cells}, Within sp s e post N t → Within sp s e' post N t
  | .ret _, _, h => h
  | .stop _, _, _ => trivial
  | .choose k, _, h =>
      ⟨fun h' => h.1 (Level.eq_pure (h' ▸ he)), fun i => Within.lift he (k i) (h.2 i)⟩
  | .update f, _, h => ⟨fun h' => h.1 (Level.ne_writes he h'),
      fun h' => h.2.1 (Level.eq_pure (h' ▸ he)), fun w => Within.after_lift he (f w) (h.2.2 w)⟩
  | .vis (.region _ _) k, _, h => fun o => Within.lift he (k o) (h o)
  | .vis (.call _ _ _ _) k, _, h => ⟨Level.calls_up he h.1, fun o => Within.lift he (k o) (h.2 o)⟩
  | .vis (.new _ _) k, _, h => fun r => Within.lift he (k r) (h r)
  | .vis (.get _ _) k, _, h =>
      ⟨fun h' => h.1 (Level.eq_pure (h' ▸ he)), fun v => Within.lift he (k v) (h.2 v)⟩
  | .vis (.set _ _ _) k, _, h =>
      ⟨h.1.imp (Level.writes_up he) id, fun u => Within.lift he (k u) (h.2 u)⟩
  | .vis (.modify _ _ _) k, _, h =>
      ⟨h.1.imp (Level.writes_up he) id, fun u => Within.lift he (k u) (h.2 u)⟩
  | .vis (.bind _ _ _ _ _) k, _, h => fun g => Within.lift he (k g) (h g)

/-- `Within.after` lifts to a higher level, as `Within` does. -/
theorem Within.after_lift {sp : WorldSpec W St} {s : St} {e e' : Level} {post : Cells → R → Prop}
    (he : e.le e') :
    ∀ (p : W × Tree I σ W rs ps S R) {N : Cells}, Within.after sp s e post N p →
      Within.after sp s e' post N p
  | (_, t), _, h => Within.lift he t h
end

/-- An update's new world is not changed by what follows it. -/
private theorem bindAfter_fst {R' : Type} (p : W × Tree I σ W rs ps S R)
    (f : R → Tree I σ W rs ps S R') : (Sem.bindAfter p f).1 = p.1 := by
  cases p; rfl

/-- An update's continuation, followed by `f`. -/
private theorem bindAfter_snd {R' : Type} (p : W × Tree I σ W rs ps S R)
    (f : R → Tree I σ W rs ps S R') : (Sem.bindAfter p f).2 = p.2.bind f := by
  cases p; rfl

mutual
/-- `Within` is closed under `bind`: if `x` stays within `e` with the post-condition `mid`, and
`f` of each result stays within `e` with `post` from the new cells that `mid` holds of, so does
the sequence, with `post`.  `mid` carries the cells that `x` made to `f`. -/
theorem Within.bind {sp : WorldSpec W St} {s : St} {e : Level} {R' : Type}
    {mid : Cells → R → Prop} {post : Cells → R' → Prop}
    {f : R → Tree I σ W rs ps S R'} (hf : ∀ N a, mid N a → Within sp s e post N (f a)) :
    ∀ (x : Tree I σ W rs ps S R) {N : Cells}, Within sp s e mid N x →
      Within sp s e post N (x.bind f)
  | .ret a, _, h => hf _ a h
  | .stop _, _, _ => trivial
  | .choose k, _, h => ⟨h.1, fun i => Within.bind hf (k i) (h.2 i)⟩
  | .update u, _, h => ⟨fun he w => by
        simpa only [bindAfter_fst] using h.1 he w,
      fun he w₁ w₂ hw => by
        obtain ⟨h1, h2⟩ := h.2.1 he w₁ w₂ hw
        refine ⟨by simpa only [bindAfter_fst] using h1, ?_⟩
        simp only [bindAfter_snd]; rw [h2],
      fun w => Within.after_bind hf (u w) (h.2.2 w)⟩
  | .vis (.region _ _) k, _, h => fun o => Within.bind hf (k o) (h o)
  | .vis (.call _ _ _ _) k, _, h => ⟨h.1, fun o => Within.bind hf (k o) (h.2 o)⟩
  | .vis (.new _ _) k, _, h => fun r => Within.bind hf (k r) (h r)
  | .vis (.get _ _) k, _, h => ⟨h.1, fun v => Within.bind hf (k v) (h.2 v)⟩
  | .vis (.set _ _ _) k, _, h => ⟨h.1, fun u => Within.bind hf (k u) (h.2 u)⟩
  | .vis (.modify _ _ _) k, _, h => ⟨h.1, fun u => Within.bind hf (k u) (h.2 u)⟩
  | .vis (.bind _ _ _ _ _) k, _, h => fun g => Within.bind hf (k g) (h g)

/-- `Within.after` is closed under `bind`, as `Within` is. -/
theorem Within.after_bind {sp : WorldSpec W St} {s : St} {e : Level} {R' : Type}
    {mid : Cells → R → Prop} {post : Cells → R' → Prop}
    {f : R → Tree I σ W rs ps S R'} (hf : ∀ N a, mid N a → Within sp s e post N (f a)) :
    ∀ (p : W × Tree I σ W rs ps S R) {N : Cells}, Within.after sp s e mid N p →
      Within.after sp s e post N (Sem.bindAfter p f)
  | (_, t), _, h => Within.bind hf t h
end

end

/-! ## Every operand -/

/-- `FnAll` of a function made from a payload (`Fn.ofPayload`): `P` holds of `k` of every
payload. -/
theorem FnAll_ofPayload {I : Ty → Type} {X : Type} (P : X → Prop) :
    ∀ (ts : List Ty) (k : Payload (ts.map I) → X), (∀ vs, P (k vs)) →
      FnAll (I := I) P ts (Fn.ofPayload ts k)
  | [], _, h => h ()
  | [_], _, h => fun x => h x
  | _ :: t' :: ts, k, h => fun x => FnAll_ofPayload P (t' :: ts) (fun p => k (x, p)) fun p => h (x, p)

/-- `FnAll` is kept by a weaker property. -/
theorem FnAll.imp {I : Ty → Type} {X : Type} {P P' : X → Prop} (h : ∀ x, P x → P' x) :
    ∀ {ts : List Ty} {f : Fn I X ts}, FnAll P ts f → FnAll P' ts f
  | [], _, hf => h _ hf
  | _ :: _, _, hf => fun a => FnAll.imp h (hf a)

/-- `VarAll` is kept by a weaker property. -/
theorem VarAll.imp {I : Ty → Type} {X : Type} {P P' : X → Prop} (h : ∀ x, P x → P' x) :
    ∀ {v : Option Ty} {f : VarFn I v X}, VarAll P v f → VarAll P' v f
  | none, _, hf => h _ hf
  | some _, _, hf => fun xs => h _ (hf xs)

/-! ## Readings of a `pure` tree -/

section
variable {I : Ty → Type} {W St : Type} {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S R : Type}

mutual
/-- **A `pure` tree's result depends only on what `immEq` keeps**: two readings of a tree within
`pure`, from the same heap and two worlds that `immEq` relates, with an environment that can't
tell such worlds apart, end with the same outcome, heap and number of choices, and with related
worlds.  By induction on the tree. -/
theorem pure_reads_alike {sp : WorldSpec W St} {s : St} {post : Cells → R → Prop}
    {env : Reading.Env I W rs} (hE : EnvImm sp s env) (oracle : Nat → Nat) :
    ∀ (t : Tree I Run W rs ps S R) (N : Cells) (d : Nat) (h : Reading.RHeap I) (w₁ w₂ : W),
      Within sp s .pure post N t → sp.immEq s w₁ w₂ →
      (Reading.read env oracle t d h w₁).out = (Reading.read env oracle t d h w₂).out ∧
      (Reading.read env oracle t d h w₁).heap = (Reading.read env oracle t d h w₂).heap ∧
      (Reading.read env oracle t d h w₁).drawn = (Reading.read env oracle t d h w₂).drawn ∧
      sp.immEq s (Reading.read env oracle t d h w₁).world (Reading.read env oracle t d h w₂).world
  | .ret _, _, _, _, _, _, _, hw => ⟨rfl, rfl, rfl, hw⟩
  | .stop _, _, _, _, _, _, _, hw => ⟨rfl, rfl, rfl, hw⟩
  | .choose k, N, d, h, w₁, w₂, hW, hw =>
      pure_reads_alike hE oracle (k (oracle d)) N (d + 1) h w₁ w₂ (hW.2 _) hw
  | .update f, N, d, h, w₁, w₂, hW, hw => by
      simp only [Reading.read]
      obtain ⟨hw', ht⟩ := hW.2.1 rfl w₁ w₂ hw
      exact pure_reads_alike.after hE oracle (f w₁) (f w₂) N d h ht (hW.2.2 w₁) hw'
  | .vis (.new t v) k, N, d, h, w₁, w₂, hW, hw =>
      pure_reads_alike hE oracle (k ⟨h.cells.size, trivial⟩) _ d _ w₁ w₂ (hW _) hw
  | .vis (.get t l) k, N, d, h, w₁, w₂, hW, hw => by
      simp only [Reading.read]
      split
      · rename_i v _
        exact pure_reads_alike hE oracle (k v) N d h w₁ w₂ (hW.2 v) hw
      · exact ⟨rfl, rfl, rfl, hw⟩
  | .vis (.set t l v) k, N, d, h, w₁, w₂, hW, hw => by
      simp only [Reading.read]
      split
      · exact pure_reads_alike hE oracle (k ()) N d _ w₁ w₂ (hW.2 ()) hw
      · exact ⟨rfl, rfl, rfl, hw⟩
  | .vis (.modify t l g) k, N, d, h, w₁, w₂, hW, hw => by
      simp only [Reading.read]
      split
      · exact pure_reads_alike hE oracle (k ()) N d _ w₁ w₂ (hW.2 ()) hw
      · exact ⟨rfl, rfl, rfl, hw⟩
  | .vis (.bind t v sig idx cap) k, N, d, h, w₁, w₂, hW, hw => by
      simp only [Reading.read]
      split
      · exact ⟨rfl, rfl, rfl, hw⟩
      · exact pure_reads_alike hE oracle _ N d _ w₁ w₂ (hW _) hw
  | .vis (.region slot args) k, N, d, h, w₁, w₂, hW, hw => by
      have hq := hE (.region slot args) h w₁ w₂ hw
      simp only [Reading.read]
      revert hq
      cases env.answer (.region slot args) h w₁ <;> cases env.answer (.region slot args) h w₂
      · intro hq; exact ⟨by rw [hq], rfl, rfl, hw⟩
      · intro hq; exact hq.elim
      · intro hq; exact hq.elim
      · rename_i a b
        obtain ⟨o₁, h₁, w₁'⟩ := a
        obtain ⟨o₂, h₂, w₂'⟩ := b
        rintro ⟨rfl, rfl, hw'⟩
        exact pure_reads_alike hE oracle (k o₁) N d h₁ w₁' w₂' (hW o₁) hw'
  | .vis (.call sig idx cap args) _, _, _, _, _, _, hW, _ => by
      rcases hW.1 with h | h <;> cases h

/-- `pure_reads_alike` after an update: two updates with the same continuation and related new
worlds read alike. -/
theorem pure_reads_alike.after {sp : WorldSpec W St} {s : St} {post : Cells → R → Prop}
    {env : Reading.Env I W rs} (hE : EnvImm sp s env) (oracle : Nat → Nat) :
    ∀ (p₁ p₂ : W × Tree I Run W rs ps S R) (N : Cells) (d : Nat) (h : Reading.RHeap I),
      p₁.2 = p₂.2 → Within.after sp s .pure post N p₁ → sp.immEq s p₁.1 p₂.1 →
      (Reading.read.after env oracle p₁ d h).out = (Reading.read.after env oracle p₂ d h).out ∧
      (Reading.read.after env oracle p₁ d h).heap = (Reading.read.after env oracle p₂ d h).heap ∧
      (Reading.read.after env oracle p₁ d h).drawn =
        (Reading.read.after env oracle p₂ d h).drawn ∧
      sp.immEq s (Reading.read.after env oracle p₁ d h).world
        (Reading.read.after env oracle p₂ d h).world
  | (w₁, t), (w₂, _), N, d, h, rfl, hW, hw => by
      simp only [Reading.read.after]
      exact pure_reads_alike hE oracle t N d h w₁ w₂ hW hw
end
end

end

end Strata.Dyn.Exec.Effects
