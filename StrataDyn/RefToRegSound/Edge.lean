/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.Cert

set_option autoImplicit false

/-!
# Edges keep the facts

An edge that `SiteOK` certifies, taken by a source frame and a
target frame whose facts hold, leads to block entries whose entry facts hold (`FrameOK`), or out
of both bodies with the same value (`NextRel`, `exitTo_rel`).
-/

namespace Strata.Dyn.RefToRegSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

variable (A : Accounts M) (X : CertEnv M)

/-- The locations of the promoted cells that the facts `F` of a frame with store `env` may
write. -/
def promLocs (env : Array (Dyn M.interp)) (F : List Fact) (l : Nat) : Prop :=
  ∃ c, Fact.prom c ∈ F ∧ RefAt env c l

/-- The locations of the promoted cells whose contents the facts `F` of a frame with store `env`
hold. -/
def cellLocs (env : Array (Dyn M.interp)) (F : List Fact) (l : Nat) : Prop :=
  ∃ u c, Fact.cell u c ∈ F ∧ RefAt env c l

/-- The source frame `f` and the target frame `f₁` run a certified body pair, with facts `F`
that hold at the rest of their code: promoted locations `P`, the source's heap `heap`. -/
def FrameOK (P : List Nat) (heap : Heap M) (F : List Fact) (f f₁ : Frame M) : Prop :=
  ∃ E, BodyOK X f.func f₁.func E ∧ CodeOK X E f.func f₁.func F f.code f.term f₁.code f₁.term ∧
    Sound A P F f.env f₁.env heap

/-- Where a source transfer and a target transfer lead, from a frame with store `env` and facts
`F`: frames that `FrameOK` relates, with facts that promote no other cell than `F` does, or out
with the same valid value. -/
def NextRel (P : List Nat) (heap : Heap M) (env : Array (Dyn M.interp)) (F : List Fact) :
    Next M → Next M → Prop
  | .frame g, .frame g₁ => ∃ F₁, FrameOK A X P heap F₁ g g₁ ∧
      ∀ l, promLocs g.env F₁ l → promLocs env F l
  | .leave v, .leave v₁ => v₁ = v ∧ A.DynOK (typOff heap P) v
  | _, _ => False

/-- Values checked against `ts` leaving `rest` are as many as `ts` without `rest`. -/
private theorem checkArgs_length {Γ : Exec.Ctx} :
    ∀ {vs : List Nat} {ts rest : List Ty}, checkArgs M Γ vs ts rest = .ok () →
      vs.length + rest.length = ts.length
  | [], _, _, h => by rw [checkArgs_nil.mp h, List.length_nil, Nat.zero_add]
  | _ :: _, [], _, h => absurd h checkArgs_cons_nil
  | _ :: vs, _ :: _, _, h => by
    have := checkArgs_length (checkArgs_cons.mp h).2
    simp only [List.length_cons]
    omega

/-- A checked edge to block `j` passes as many values as the block's parameters, with its
payload. -/
private theorem checkSite_length {fn : LBody M} {Γ : Exec.Ctx} {j : Nat} {args : List Nat}
    {ts : List Ty} (h : checkSite fn Γ ⟨.block j, args⟩ ts = .ok ()) :
    args.length + ts.length = (paramsOf fn j).length := by
  obtain ⟨ps, sc, qs, ht, ha, -, -⟩ := checkSite_eq_ok.mp h
  have hl := checkArgs_length ha
  simp only [targetSig] at ht
  obtain ⟨b, hb, he⟩ := Option.map_eq_some_iff.mp ht
  obtain ⟨rfl, -⟩ := Prod.mk.inj he
  rw [paramsOf, hb, Option.map_some, Option.getD_some]
  simpa [LBlock.paramTys] using hl

/-- What a parameter is bound to, as a value of the source store or of the payload. -/
def valOf (env : Array (Dyn M.interp)) {ts : List Ty} (xs : Args M.interp ts) :
    Nat ⊕ Nat → Option (Dyn M.interp)
  | .inl a => env[a]?
  | .inr i => (Args.toList xs)[i]?

/-- Binding distinct parameters to the arguments' values and the payload binds each value as
`BoundTo` says. -/
private theorem BoundTo.get {ps : Exec.Ctx} {args : List Nat} {w : Nat} {s : Nat ⊕ Nat}
    (hb : BoundTo ps args w s) (env : Array (Dyn M.interp)) {ts : List Ty} (xs : Args M.interp ts)
    (ha : AllBound env args) (h : ∀ p ∈ ps, p.1 < env.size) (hn : (ps.map (·.1)).Nodup)
    (hl : args.length + ts.length = ps.length) :
    (bindSite env ps (lookupAll env args ha) xs h)[w]? = valOf env xs s := by
  rcases hb with ⟨hw, rfl⟩ | ⟨k, hk, rfl, hs⟩
  · exact bindSite_other env ps _ xs h hw
  · rw [bindSite_param env ps _ xs h hn (by rw [length_lookupAll]; exact hl) k hk]
    rcases hs with ⟨hk₁, rfl⟩ | ⟨hk₁, rfl⟩
    · rw [List.getElem?_append_left (by rw [length_lookupAll]; exact hk₁),
        lookupAll_getElem? ha k hk₁]
      rfl
    · rw [List.getElem?_append_right (by rw [length_lookupAll]; exact hk₁), length_lookupAll]
      rfl

/-- A payload position that `BoundTo` names has a value. -/
private theorem BoundTo.pay_lt {ps : Exec.Ctx} {args : List Nat} {w i : Nat}
    (hb : BoundTo ps args w (.inr i)) {ts : List Ty} (hl : args.length + ts.length = ps.length) :
    i < ts.length := by
  rcases hb with ⟨-, h⟩ | ⟨k, hk, -, ⟨_, h⟩ | ⟨hk₁, h⟩⟩
  · exact nomatch h
  · exact nomatch h
  · cases h
    omega

/-- A payload has a value at each position below its length. -/
private theorem Args.getElem?_toList_isSome {I : Ty → Type} {ts : List Ty} (xs : Args I ts)
    {i : Nat} (hi : i < ts.length) : ∃ d, (Args.toList xs)[i]? = some d :=
  ⟨_, List.getElem?_eq_getElem (by rw [Args.length_toList]; exact hi)⟩

/-- An edge that `Established` certifies, taken by frames whose facts hold, binds the entry
facts. -/
theorem established_sound {P : List Nat} {F : List Fact} {E0 : List Fact}
    {env env₁ : Array (Dyn M.interp)} {heap : Heap M} (hS : Sound A P F env env₁ heap)
    {ps ps₁ : Exec.Ctx} {args args₁ : List Nat} {ts : List Ty} (xs : Args M.interp ts)
    (hxs : ∀ d ∈ Args.toList xs, A.DynOK (typOff heap P) d)
    (ha : AllBound env args) (ha₁ : AllBound env₁ args₁)
    (h : ∀ p ∈ ps, p.1 < env.size) (h₁ : ∀ p ∈ ps₁, p.1 < env₁.size)
    (hn : (ps.map (·.1)).Nodup) (hn₁ : (ps₁.map (·.1)).Nodup)
    (hl : args.length + ts.length = ps.length) (hl₁ : args₁.length + ts.length = ps₁.length)
    (hE : ∀ φ ∈ E0, Established F ps ps₁ args args₁ φ) :
    Sound A P E0 (bindSite env ps (lookupAll env args ha) xs h)
      (bindSite env₁ ps₁ (lookupAll env₁ args₁ ha₁) xs h₁) heap ∧
    ∀ l, promLocs (bindSite env ps (lookupAll env args ha) xs h) E0 l → promLocs env F l := by
  have g := fun {w s} (hb : BoundTo ps args w s) => hb.get env xs ha h hn hl
  have g₁ := fun {w s} (hb : BoundTo ps₁ args₁ w s) => hb.get env₁ xs ha₁ h₁ hn₁ hl₁
  have keep : ∀ c, c ∉ ps.map (·.1) →
      (bindSite env ps (lookupAll env args ha) xs h)[c]? = env[c]? :=
    fun c hc => bindSite_other env ps _ xs h hc
  have refKeep : ∀ c l, c ∉ ps.map (·.1) →
      (RefAt (bindSite env ps (lookupAll env args ha) xs h) c l ↔ RefAt env c l) := by
    intro c l hc
    unfold RefAt
    rw [keep c hc]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro φ hφ
    have he := hE φ hφ
    cases φ with
    | eq u v =>
      obtain ⟨s₁, s, hb₁, hb, hm⟩ := he
      show ∃ d, _ = some d ∧ _ = some d ∧ _
      rw [g hb, g₁ hb₁]
      cases s₁ with
      | inl a₁ =>
        cases s with
        | inl a => exact hS.holds _ hm
        | inr _ => exact hm.elim
      | inr i₁ =>
        cases s with
        | inl _ => exact hm.elim
        | inr i =>
          cases hm
          obtain ⟨d, hd⟩ := Args.getElem?_toList_isSome xs (hb.pay_lt hl)
          exact ⟨d, hd, hd, hxs d (List.mem_of_getElem? hd)⟩
    | cell u c =>
      obtain ⟨hc, a₁, hb₁, hm⟩ := he
      obtain ⟨l, d, hr, hP, hh, hu⟩ := hS.holds _ hm
      exact ⟨l, d, (refKeep c l hc).mpr hr, hP, hh, (g₁ hb₁).trans hu⟩
    | prom c =>
      obtain ⟨hc, hm⟩ := he
      obtain ⟨l, hr, hP, hlt⟩ := hS.holds _ hm
      exact ⟨l, (refKeep c l hc).mpr hr, hP, hlt⟩
  · -- Each promoted cell of the entry facts is a promoted cell of `F`, at the same slot.
    have src : ∀ φ ∈ E0, ∀ c, φ.prom? = some c →
        c ∉ ps.map (·.1) ∧ ∃ ψ ∈ F, ψ.prom? = some c := by
      intro φ hφ c hc
      have he := hE φ hφ
      cases φ with
      | cell u c₁ =>
        cases hc
        obtain ⟨hc, a₁, -, hm⟩ := he
        exact ⟨hc, _, hm, rfl⟩
      | prom c₁ =>
        cases hc
        obtain ⟨hc, hm⟩ := he
        exact ⟨hc, _, hm, rfl⟩
      | eq _ _ => exact nomatch hc
    intro φ hφ ψ hψ c c₁ l h₀ h₁ hne hl₀ hl₁
    obtain ⟨hc, φ₁, hφ₁, e₀⟩ := src φ hφ c h₀
    obtain ⟨hc₁, ψ₁, hψ₁, e₁⟩ := src ψ hψ c₁ h₁
    exact hS.distinct φ₁ hφ₁ ψ₁ hψ₁ c c₁ l e₀ e₁ hne ((refKeep c l hc).mp hl₀)
      ((refKeep c₁ l hc₁).mp hl₁)
  · intro l ⟨c, hc, hr⟩
    obtain ⟨hcp, hm⟩ := hE _ hc
    exact ⟨c, hm, (refKeep c l hcp).mp hr⟩

/-- Exits that pass the same values pass the same one value. -/
private theorem single_congr {r r₁ : Ty} {ts : List Ty} {xs : Args M.interp ts}
    {ds₁ ds : List (Dyn M.interp)} (hd : ds₁ = ds) (h₁ : ds₁.map (·.1) ++ ts = [r₁])
    (h : ds.map (·.1) ++ ts = [r]) : single ds₁ xs h₁ = single ds xs h := by
  subst hd
  have e := (single_spec ds₁ xs h₁).symm.trans (single_spec ds₁ xs h)
  exact List.head_eq_of_cons_eq e

/-- The source values of operands that `eq` facts name are valid. -/
theorem Sound.lookupAll_ok {P : List Nat} {F : List Fact} {env env₁ : Array (Dyn M.interp)}
    {heap : Heap M} (hS : Sound A P F env env₁ heap) :
    ∀ {args₁ args : List Nat}, All₂ (fun a₁ a => Fact.eq a₁ a ∈ F) args₁ args →
      ∀ (h : AllBound env args), ∀ d ∈ lookupAll env args h, A.DynOK (typOff heap P) d
  | _, _, .nil, _, _, hd => nomatch hd
  | _, a :: _, .cons hm hs, h, d, hd => by
    rw [lookupAll] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · obtain ⟨d₀, h₂, -, h₄⟩ := hS.holds _ hm
      rw [Array.getElem?_eq_getElem h.1] at h₂
      cases h₂
      exact h₄
    · exact Sound.lookupAll_ok hS hs h.2 d hd

/-- A certified edge, taken by frames of a certified body pair whose facts hold, with a valid
payload, leads where `NextRel` relates. -/
theorem take_rel {P : List Nat} {heap : Heap M} {E : Nat → List Fact} {F : List Fact}
    {f f₁ : Frame M} (hB : BodyOK X f.func f₁.func E) (hS : Sound A P F f.env f₁.env heap)
    {s s₁ : LSite} (hs : SiteOK E f.func f₁.func F s s₁) {ts : List Ty} (xs : Args M.interp ts)
    (hxs : ∀ d ∈ Args.toList xs, A.DynOK (typOff heap P) d)
    {Γ Γ₁ : Exec.Ctx} (hc : checkSite f.func Γ s ts = .ok ())
    (hc₁ : checkSite f₁.func Γ₁ s₁ ts = .ok ()) (h : CanTake f s ts) (h₁ : CanTake f₁ s₁ ts) :
    NextRel A X P heap f.env F (take f s xs h) (take f₁ s₁ xs h₁) := by
  obtain ⟨target, args⟩ := s
  obtain ⟨target₁, args₁⟩ := s₁
  obtain ⟨ht, hs⟩ := hs
  simp only at ht
  subst ht
  cases target₁ with
  | exit =>
    simp only [take, NextRel]
    have hd := lookupAll_congr (hs.imp fun a₁ a hm => by
      obtain ⟨d, h₂, h₃, -⟩ := hS.holds _ hm
      exact h₃.trans h₂.symm) h₁.1 h.1
    refine ⟨single_congr hd _ _, ?_⟩
    have hsp := single_spec (lookupAll f.env args h.1) xs h.2
    have hmem : single (lookupAll f.env args h.1) xs h.2 ∈
        lookupAll f.env args h.1 ++ Args.toList xs := by
      rw [hsp]; exact List.mem_singleton_self _
    rcases List.mem_append.mp hmem with hm | hm
    · exact Sound.lookupAll_ok A hS hs h.1 _ hm
    · exact hxs _ hm
  | block j =>
    simp only [take, NextRel]
    obtain ⟨hn, hn₁, hE⟩ := hs
    obtain ⟨hj₁, hcode⟩ := hB j h.2.1
    have hp : paramsOf f.func j = (f.func.blocks[j]'h.2.1).params := by
      rw [paramsOf, Array.getElem?_eq_getElem h.2.1, Option.map_some, Option.getD_some]
    have hp₁ : paramsOf f₁.func j = (f₁.func.blocks[j]'h₁.2.1).params := by
      rw [paramsOf, Array.getElem?_eq_getElem h₁.2.1, Option.map_some, Option.getD_some]
    have hl := checkSite_length hc
    have hl₁ := checkSite_length hc₁
    rw [hp] at hn hE hl
    rw [hp₁] at hn₁ hE hl₁
    obtain ⟨hS₁, hsub⟩ := established_sound A hS xs hxs h.1 h₁.1 _ _ hn hn₁ hl hl₁ hE
    exact ⟨E j, ⟨E, hB, hcode, hS₁⟩, hsub⟩

/-- Certified edges, taken by the same exit with a valid payload, lead where `NextRel`
relates. -/
theorem exitTo_rel {P : List Nat} {heap : Heap M} {E : Nat → List Fact} {F : List Fact}
    {f f₁ : Frame M} (hB : BodyOK X f.func f₁.func E) (hS : Sound A P F f.env f₁.env heap) :
    ∀ {ps : List (List Ty)} {ss ss₁ : List LSite} (e : Exit M.interp ps),
      A.ExitOK (typOff heap P) e → (h : SitesOK f ss ps) → (h₁ : SitesOK f₁ ss₁ ps) →
      All₂ (SiteOK E f.func f₁.func F) ss ss₁ →
      NextRel A X P heap f.env F (exitTo f ss e h) (exitTo f₁ ss₁ e h₁)
  | _, _ :: _, _ :: _, .here xs, he, h, h₁, .cons hs _ => by
    simp only [exitTo]
    obtain ⟨Γ, -, hc⟩ := h
    obtain ⟨Γ₁, -, hc₁⟩ := h₁
    exact take_rel A X hB hS hs xs (Accounts.argsOK_toList he) (checkSites_cons.mp hc).1
      (checkSites_cons.mp hc₁).1 _ _
  | _, _ :: _, _ :: _, .there e, he, h, h₁, .cons _ hss => by
    simp only [exitTo]
    exact exitTo_rel hB hS e he _ _ hss
  | _, [], [], .here _, _, h, _, .nil => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)
  | _, [], [], .there _, _, h, _, .nil => False.elim (by
      obtain ⟨_, _, hs⟩ := h
      exact checkSites_nil_cons hs)

end

end Strata.Dyn.RefToRegSound
