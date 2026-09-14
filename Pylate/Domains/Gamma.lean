/-
Concretization (LEAN_SPEC.md section 4) and T1. Constants enter gamma by
tag alone, so payloads are omitted without loss; a reference value needs
its tag and a location witness; `tany` concretizes to everything. With
T2 (reductive) and T3 (monotone) in Domain.lean, T1 completes the
reduced product's theorem set: reduction drops no meaning and adds none.
-/
import Pylate.Domains.Value

namespace Pylate

inductive CVal
  | cnone | cbool | cint | cfloat | cstr
  | addr (a : Nat)
  | func (f : String)
  | cls (c : String)

def CVal.constTag : CVal → Option Tag
  | .cnone => some .tnone
  | .cbool => some .tbool
  | .cint => some .tint
  | .cfloat => some .tfloat
  | .cstr => some .tstr
  | _ => none

def gammaV (pi : Nat → Loc) (v : AbsVal) : CVal → Prop
  | .addr a => Tag.tany ∈ v.tags ∨ ((pi a).cls.tag ∈ v.tags ∧ pi a ∈ v.locs)
  | .func f => Tag.tany ∈ v.tags ∨ (Tag.tfunc ∈ v.tags ∧ f ∈ v.funcs)
  | .cls c => Tag.tany ∈ v.tags ∨ (Tag.ttype ∈ v.tags ∧ c ∈ v.classes)
  | k => Tag.tany ∈ v.tags ∨ ∃ t, k.constTag = some t ∧ t ∈ v.tags

theorem gammaV_mono {v w : AbsVal} (h : v.Le w) (pi : Nat → Loc)
    (c : CVal) : gammaV pi v c → gammaV pi w c := by
  cases c <;> simp only [gammaV] <;>
    rintro (hany | hc) <;> first
      | exact Or.inl (h.tags _ hany)
      | skip
  case addr => exact Or.inr ⟨h.tags _ hc.1, h.locs _ hc.2⟩
  case func => exact Or.inr ⟨h.tags _ hc.1, h.funcs _ hc.2⟩
  case cls => exact Or.inr ⟨h.tags _ hc.1, h.classes _ hc.2⟩
  all_goals
    obtain ⟨t, ht, hm⟩ := hc
    exact Or.inr ⟨t, ht, h.tags _ hm⟩

private theorem tag_isRef_of_locCls (lc : LocCls) : lc.tag.isRef = true := by
  cases lc <;> rfl

private theorem reduce_tags_any {v : AbsVal} (h : Tag.tany ∈ v.tags) :
    (v.reduce).tags = v.tags := by
  unfold AbsVal.reduce
  rw [if_pos h]

private theorem mem_reduce_locs {v : AbsVal} {l : Loc}
    (hl : l ∈ v.locs) (ht : l.cls.tag ∈ v.tags) : l ∈ (v.reduce).locs := by
  unfold AbsVal.reduce
  by_cases hany : Tag.tany ∈ v.tags
  · rw [if_pos hany]
    exact List.mem_filter.mpr ⟨hl, decide_eq_true ht⟩
  · rw [if_neg hany]
    exact List.mem_filter.mpr ⟨hl, decide_eq_true ht⟩

/-- A tag with its kind's witness survives the tag filter (no-`tany`
    branch): a reference tag needs a filtered location of its class, a
    function or type tag needs a name, other tags pass unconditionally. -/
private theorem mem_reduce_tags {v : AbsVal} {t : Tag}
    (hany : Tag.tany ∉ v.tags) (hmem : t ∈ v.tags)
    (href : t.isRef = true →
      ∃ l ∈ v.locs, l.cls.tag ∈ v.tags ∧ l.cls.tag = t)
    (hfun : t = Tag.tfunc → v.funcs ≠ [])
    (htyp : t = Tag.ttype → v.classes ≠ []) :
    t ∈ (v.reduce).tags := by
  unfold AbsVal.reduce
  rw [if_neg hany]
  refine List.mem_filter.mpr ⟨hmem, ?_⟩
  by_cases hr : t.isRef = true
  · rw [if_pos hr]
    obtain ⟨l, hl, hlive, heq⟩ := href hr
    refine decide_eq_true (List.mem_map.mpr ⟨l, ?_, heq⟩)
    exact List.mem_filter.mpr ⟨hl, decide_eq_true hlive⟩
  · rw [if_neg hr]
    cases t <;> simp_all [Tag.isRef]

private theorem reduce_funcs_of_mem {v : AbsVal}
    (h : Tag.tfunc ∈ (v.reduce).tags) : (v.reduce).funcs = v.funcs := by
  unfold AbsVal.reduce at *
  by_cases hany : Tag.tany ∈ v.tags
  · rw [if_pos hany]
  · rw [if_neg hany] at h ⊢
    simp only [if_pos h]

private theorem reduce_classes_of_mem {v : AbsVal}
    (h : Tag.ttype ∈ (v.reduce).tags) : (v.reduce).classes = v.classes := by
  unfold AbsVal.reduce at *
  by_cases hany : Tag.tany ∈ v.tags
  · rw [if_pos hany]
  · rw [if_neg hany] at h ⊢
    simp only [if_pos h]

private theorem locTag_ne_tfunc {lc : LocCls} : lc.tag ≠ Tag.tfunc := by
  cases lc <;> intro h <;> cases h

private theorem locTag_ne_ttype {lc : LocCls} : lc.tag ≠ Tag.ttype := by
  cases lc <;> intro h <;> cases h

/-- T1 (gamma-preservation): `gamma (reduce v) = gamma v`. Forward is
    monotonicity along T2; backward, each surviving concretization
    supplies exactly the witness the filters demand. -/
theorem reduce_gamma (pi : Nat → Loc) (v : AbsVal) (c : CVal) :
    gammaV pi (v.reduce) c ↔ gammaV pi v c := by
  constructor
  · exact gammaV_mono (AbsVal.reduce_le v) pi c
  · intro h
    by_cases hany : Tag.tany ∈ v.tags
    · have htop : Tag.tany ∈ (v.reduce).tags := by
        rw [reduce_tags_any hany]; exact hany
      cases c <;> exact Or.inl htop
    · cases c with
      | addr a =>
        rcases h with h | ⟨ht, hl⟩
        · exact absurd h hany
        · exact Or.inr ⟨mem_reduce_tags hany ht
            (fun _ => ⟨pi a, hl, ht, rfl⟩)
            (fun h' => absurd h' locTag_ne_tfunc)
            (fun h' => absurd h' locTag_ne_ttype),
            mem_reduce_locs hl ht⟩
      | func f =>
        rcases h with h | ⟨ht, hf⟩
        · exact absurd h hany
        · have hne : v.funcs ≠ [] := fun hnil => by
            rw [hnil] at hf; cases hf
          have hkept : Tag.tfunc ∈ (v.reduce).tags :=
            mem_reduce_tags hany ht (fun hr => nomatch hr)
              (fun _ => hne) (fun h' => nomatch h')
          exact Or.inr ⟨hkept, by rw [reduce_funcs_of_mem hkept]; exact hf⟩
      | cls cn =>
        rcases h with h | ⟨ht, hf⟩
        · exact absurd h hany
        · have hne : v.classes ≠ [] := fun hnil => by
            rw [hnil] at hf; cases hf
          have hkept : Tag.ttype ∈ (v.reduce).tags :=
            mem_reduce_tags hany ht (fun hr => nomatch hr)
              (fun h' => nomatch h') (fun _ => hne)
          exact Or.inr ⟨hkept,
            by rw [reduce_classes_of_mem hkept]; exact hf⟩
      | cnone =>
        rcases h with h | ⟨t, hct, hmem⟩
        · exact absurd h hany
        · cases hct
          exact Or.inr ⟨_, rfl, mem_reduce_tags hany hmem
            (fun hr => nomatch hr) (fun h' => nomatch h')
            (fun h' => nomatch h')⟩
      | cbool =>
        rcases h with h | ⟨t, hct, hmem⟩
        · exact absurd h hany
        · cases hct
          exact Or.inr ⟨_, rfl, mem_reduce_tags hany hmem
            (fun hr => nomatch hr) (fun h' => nomatch h')
            (fun h' => nomatch h')⟩
      | cint =>
        rcases h with h | ⟨t, hct, hmem⟩
        · exact absurd h hany
        · cases hct
          exact Or.inr ⟨_, rfl, mem_reduce_tags hany hmem
            (fun hr => nomatch hr) (fun h' => nomatch h')
            (fun h' => nomatch h')⟩
      | cfloat =>
        rcases h with h | ⟨t, hct, hmem⟩
        · exact absurd h hany
        · cases hct
          exact Or.inr ⟨_, rfl, mem_reduce_tags hany hmem
            (fun hr => nomatch hr) (fun h' => nomatch h')
            (fun h' => nomatch h')⟩
      | cstr =>
        rcases h with h | ⟨t, hct, hmem⟩
        · exact absurd h hany
        · cases hct
          exact Or.inr ⟨_, rfl, mem_reduce_tags hany hmem
            (fun hr => nomatch hr) (fun h' => nomatch h')
            (fun h' => nomatch h')⟩

end Pylate
