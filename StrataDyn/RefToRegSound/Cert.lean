/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToRegSound.Facts

set_option autoImplicit false

/-!
# A certificate that a linked target promotes a linked source's cells

`CodeOK` relates the rest of a source block to the rest of the target block, with the facts `F`
that hold where they start.  It is the shape of what ref-to-reg does to a block:

* a `refGet` of a promoted cell is removed, and the value that holds the cell's content stands for
  its result (`getProm`); a `refSet` of a promoted cell is removed, and its value becomes the
  cell's content (`setProm`);
* a `refNew` stays, and its cell is promoted (`newProm`) or not (`newKept`); a `refGet` or
  `refSet` of a cell that is not promoted stays, its cell operand replaced by a target value that
  holds the source's (`getKept`, `setKept`);
* every other instruction and the terminator stay, each operand replaced by a target value that
  holds the source operand's value (`const`, `pure`, `sem`, `callCode`, `TermOK`);
* an edge passes, for each fact of its target block's entry (`E j`), what makes it hold after
  the block's parameters are bound (`SiteOK`, `Established`).

An operation with regions names the promoted cells its regions may write, `Wr`.  Its rule runs
from the facts without the contents of those cells (`dropCells`), and each region's entry facts
are established from those, with the promotion of the cells in `Wr` only (`regFacts`,
`RegionOK`), so a region reads the contents of the other cells and writes none of them.  So after
the operation, the code reads a cell of `Wr` only after a new `setProm` writes it: this is
restrictive, not unsound.

Each step's facts are those before it without what it rebinds (`after`, `dropSrc`, `dropCell`),
with what it establishes; so no fact about a value outlives the value, which is what SSA
dominance gives ref-to-reg, and the certificate does not need dominance.

A certificate is relative to a `CertEnv`: the two modules, a condition `R`/`RT` on each source
instruction and terminator, and each region's entry facts by block.  `ModOK` certifies a module
pair function by function and region by region.  The promotion itself is certified with no
condition on instructions (`PromotionOK`); the rules' certificates come from linking
(`ModOK.withRules`).
-/

namespace Strata.Dyn.RefToRegSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-! ## Edges -/

/-- Value `w`, among the parameters `ps` of a block entered with the arguments `args` and then a
payload, is bound to the value of the source slot `a` (`.inl a`), or to the payload's `i`-th
value (`.inr i`).  A value that is not a parameter keeps its own value. -/
def BoundTo (ps : Exec.Ctx) (args : List Nat) (w : Nat) (s : Nat ⊕ Nat) : Prop :=
  (w ∉ ps.map (·.1) ∧ s = .inl w) ∨
  ∃ k, ∃ hk : k < ps.length, (ps[k]'hk).1 = w ∧
    ((∃ hk₁ : k < args.length, s = .inl (args[k]'hk₁)) ∨
      (args.length ≤ k ∧ s = .inr (k - args.length)))

/-- The parameters of block `j` of `g`, none if there is no such block. -/
def paramsOf (g : LBody M) (j : Nat) : Exec.Ctx := (g.blocks[j]?.map (·.params)).getD []

/-- The fact `φ` of a block's entry holds after an edge from where `F` holds, with source
parameters `ps` bound to `args` and target parameters `ps₁` bound to `args₁`, each then to the
same payload. -/
def Established (F : List Fact) (ps ps₁ : Exec.Ctx) (args args₁ : List Nat) : Fact → Prop
  | .eq u v => ∃ s₁ s, BoundTo ps₁ args₁ u s₁ ∧ BoundTo ps args v s ∧
      match s₁, s with
      | .inl a₁, .inl a => Fact.eq a₁ a ∈ F
      | .inr i₁, .inr i => i₁ = i
      | _, _ => False
  | .cell u c => c ∉ ps.map (·.1) ∧ ∃ a₁, BoundTo ps₁ args₁ u (.inl a₁) ∧ Fact.cell a₁ c ∈ F
  | .prom c => c ∉ ps.map (·.1) ∧ Fact.prom c ∈ F

/-- The source edge `s` and the target edge `s₁` go to the same place, from where `F` holds: to
the exit with values that agree, or to block `j`, establishing its entry facts `E j`. -/
def SiteOK (E : Nat → List Fact) (g g₁ : LBody M) (F : List Fact) (s s₁ : LSite) : Prop :=
  s₁.target = s.target ∧
  match s.target with
  | .exit => All₂ (fun a₁ a => Fact.eq a₁ a ∈ F) s₁.args s.args
  | .block j => ((paramsOf g j).map (·.1)).Nodup ∧ ((paramsOf g₁ j).map (·.1)).Nodup ∧
      ∀ φ ∈ E j, Established F (paramsOf g j) (paramsOf g₁ j) s.args s₁.args φ

/-- Target operands `args₁` hold the values of the source operands `args`, by `F`. -/
abbrev ArgsEq (F : List Fact) (args₁ args : List Nat) : Prop :=
  All₂ (fun a₁ a => Fact.eq a₁ a ∈ F) args₁ args

/-- The facts without the contents of the cells `Wr`. -/
def dropCells (Wr : List Nat) (F : List Fact) : List Fact :=
  F.filter fun | .cell _ c => !Wr.contains c | _ => true

/-- The facts a region of an operation that may write the cells `Wr` starts from: the operation's
facts, without the contents of `Wr`'s cells, and with the promotion of `Wr`'s cells only. -/
def regFacts (Wr : List Nat) (F : List Fact) : List Fact :=
  (dropCells Wr F).filter fun | .prom c => Wr.contains c | _ => true

/-- The cells an operation's regions may write are promoted cells of `F`. -/
def WrOK (F : List Fact) (Wr : List Nat) : Prop := ∀ c ∈ Wr, Fact.prom c ∈ F

/-- The facts of the certificate besides its shape: the source and target modules, a condition
on each source instruction and terminator, and the facts at each block of each region. -/
structure CertEnv (M : RunModel) where
  m : LModule M
  m₁ : LModule M
  R : LInsn M → Prop
  RT : LTerm M → Prop
  ER : Nat → Nat → List Fact

variable (X : CertEnv M)

/-- Region `k` of the source and of the target start from where `F` holds: their entry facts,
`X.ER k 0`, are established by binding the regions' entry parameters to the same payload. -/
def RegionOK (F : List Fact) (k : Nat) : Prop :=
  ∃ g g₁, X.m.regions[k]? = some g ∧ X.m₁.regions[k]? = some g₁ ∧
    ((paramsOf g 0).map (·.1)).Nodup ∧ ((paramsOf g₁ 0).map (·.1)).Nodup ∧
    ∀ φ ∈ X.ER k 0, Established F (paramsOf g 0) (paramsOf g₁ 0) [] [] φ

/-- A target terminator that is the source's, with its operands and edges replaced. -/
inductive TermOK (E : Nat → List Fact) (g g₁ : LBody M) (F : List Fact) : LTerm M → LTerm M → Prop
  | case {ts : List Ty} {ps : List (List Ty)} {f : Fn M.interp (Exit M.interp ps) ts}
      {args args₁ : List Nat} {succs succs₁ : List LSite} :
      X.RT (.case ts ps f args succs) → ArgsEq F args₁ args → All₂ (SiteOK E g g₁ F) succs succs₁ →
      TermOK E g g₁ F (.case ts ps f args succs) (.case ts ps f args₁ succs₁)
  | sem {op : Name} {rs : List (List Ty × Ty)} {ps : List (List Ty)} {re : Rerun M rs ps Empty}
      {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) Empty) re.ts}
      {regs : List Nat} {succs succs₁ : List LSite} {args₁ : List Nat} (Wr : List Nat) :
      X.RT (.sem op rs ps re f regs succs) → WrOK F Wr →
      ArgsEq (dropCells Wr F) args₁ re.args →
      All₂ (SiteOK E g g₁ (dropCells Wr F)) succs succs₁ →
      (∀ k ∈ regs, RegionOK X (regFacts Wr F) k) →
      TermOK E g g₁ F (.sem op rs ps re f regs succs)
        (.sem op rs ps { re with args := args₁ } f regs succs₁)

/-- The rest of a target block promotes the rest of a source block, from facts `F`. -/
inductive CodeOK (E : Nat → List Fact) (g g₁ : LBody M) :
    List Fact → List (LInsn M) → LTerm M → List (LInsn M) → LTerm M → Prop
  | term {F : List Fact} {t t₁ : LTerm M} : TermOK X E g g₁ F t t₁ → CodeOK E g g₁ F [] t [] t₁
  | getProm {F : List Fact} {r : Nat} {ty : Ty} {c u : Nat} {is is₁ : List (LInsn M)}
      {t t₁ : LTerm M} : Fact.cell u c ∈ F →
      CodeOK E g g₁ (.eq u r :: dropSrc r F) is t is₁ t₁ →
      CodeOK E g g₁ F (.refGet r ty c :: is) t is₁ t₁
  | setProm {F : List Fact} {d : Nat} {ty : Ty} {c v u : Nat} {is is₁ : List (LInsn M)}
      {t t₁ : LTerm M} : Fact.prom c ∈ F → Fact.eq u v ∈ F → d ≠ c →
      CodeOK E g g₁ (.cell u c :: dropSrc d (dropCell c F)) is t is₁ t₁ →
      CodeOK E g g₁ F (.refSet d ty c v :: is) t is₁ t₁
  | newProm {F : List Fact} {d : Nat} {ty : Ty} {v u : Nat} {is is₁ : List (LInsn M)}
      {t t₁ : LTerm M} : Fact.eq u v ∈ F → u ≠ d →
      CodeOK E g g₁ (.cell u d :: .prom d :: dropTgt d (dropSrc d F)) is t is₁ t₁ →
      CodeOK E g g₁ F (.refNew d ty v :: is) t (.refNew d ty u :: is₁) t₁
  | newKept {F : List Fact} {d : Nat} {ty : Ty} {v u : Nat} {is is₁ : List (LInsn M)}
      {t t₁ : LTerm M} : Fact.eq u v ∈ F →
      CodeOK E g g₁ (after d F) is t is₁ t₁ →
      CodeOK E g g₁ F (.refNew d ty v :: is) t (.refNew d ty u :: is₁) t₁
  | getKept {F : List Fact} {d : Nat} {ty : Ty} {c c₁ : Nat} {is is₁ : List (LInsn M)}
      {t t₁ : LTerm M} : Fact.eq c₁ c ∈ F →
      CodeOK E g g₁ (after d F) is t is₁ t₁ →
      CodeOK E g g₁ F (.refGet d ty c :: is) t (.refGet d ty c₁ :: is₁) t₁
  | setKept {F : List Fact} {d : Nat} {ty : Ty} {c c₁ v v₁ : Nat} {is is₁ : List (LInsn M)}
      {t t₁ : LTerm M} : Fact.eq c₁ c ∈ F → Fact.eq v₁ v ∈ F →
      CodeOK E g g₁ (after d F) is t is₁ t₁ →
      CodeOK E g g₁ F (.refSet d ty c v :: is) t (.refSet d ty c₁ v₁ :: is₁) t₁
  | const {F : List Fact} {d : Nat} {x : Dyn M.interp} {is is₁ : List (LInsn M)}
      {t t₁ : LTerm M} : X.R (.const d x) → CodeOK E g g₁ (after d F) is t is₁ t₁ →
      CodeOK E g g₁ F (.const d x :: is) t (.const d x :: is₁) t₁
  | pure {F : List Fact} {d : Nat} {ts : List Ty} {r : Ty} {f : Fn M.interp (M.interp r) ts}
      {args args₁ : List Nat} {is is₁ : List (LInsn M)} {t t₁ : LTerm M} :
      X.R (.pure d ts r f args) → ArgsEq F args₁ args → CodeOK E g g₁ (after d F) is t is₁ t₁ →
      CodeOK E g g₁ F (.pure d ts r f args :: is) t (.pure d ts r f args₁ :: is₁) t₁
  | sem {F : List Fact} {op : Name} {d : Nat} {rs : List (List Ty × Ty)} {r : Ty}
      {ps : List (List Ty)} {re : Rerun M rs ps (M.interp r)}
      {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) (M.interp r)) re.ts}
      {regs : List Nat} {succs succs₁ : List LSite} {args₁ : List Nat}
      {is is₁ : List (LInsn M)} {t t₁ : LTerm M} (Wr : List Nat) :
      X.R (.sem op d rs r ps re f regs succs) → WrOK F Wr →
      ArgsEq (dropCells Wr F) args₁ re.args →
      All₂ (SiteOK E g g₁ (dropCells Wr F)) succs succs₁ →
      (∀ k ∈ regs, RegionOK X (regFacts Wr F) k) →
      CodeOK E g g₁ (after d (dropCells Wr F)) is t is₁ t₁ →
      CodeOK E g g₁ F (.sem op d rs r ps re f regs succs :: is) t
        (.sem op d rs r ps { re with args := args₁ } f regs succs₁ :: is₁) t₁
  | callCode {F : List Fact} {d : Nat} {ts : List Ty} {r : Ty} {fn fn₁ : Nat}
      {args args₁ : List Nat} {is is₁ : List (LInsn M)} {t t₁ : LTerm M} :
      Fact.eq fn₁ fn ∈ F → ArgsEq F args₁ args → CodeOK E g g₁ (after d F) is t is₁ t₁ →
      CodeOK E g g₁ F (.callCode d ts r fn args :: is) t (.callCode d ts r fn₁ args₁ :: is₁) t₁

/-- The target body `g₁` promotes the source body `g`, with entry facts `E j` for block `j`:
every block of `g` is certified against the same block of `g₁`. -/
def BodyOK (g g₁ : LBody M) (E : Nat → List Fact) : Prop :=
  ∀ j (hj : j < g.blocks.size), ∃ hj₁ : j < g₁.blocks.size,
    CodeOK X E g g₁ (E j) (g.blocks[j]'hj).insns (g.blocks[j]'hj).term
      (g₁.blocks[j]'hj₁).insns (g₁.blocks[j]'hj₁).term

/-- The entry block's parameters `ps` and the target's `ps₁`, of the same tags and distinct, and
facts `E0` that equate the target's `k`-th parameter with the source's. -/
def StartOK (ps ps₁ : Exec.Ctx) (E0 : List Fact) : Prop :=
  ps₁.map (·.2) = ps.map (·.2) ∧ (ps.map (·.1)).Nodup ∧ (ps₁.map (·.1)).Nodup ∧
  ∀ φ ∈ E0, ∃ k, ∃ hk : k < ps.length, ∃ hk₁ : k < ps₁.length,
    φ = .eq (ps₁[k]'hk₁).1 (ps[k]'hk).1

/-- **The target module promotes the source**, as `X` says: the same number of functions, each
pair certified with entry facts per block, the same name, parameters' tags and result tag, and
the entry parameters bound alike; the same number of regions, each pair certified with the facts
`X.ER`. -/
structure ModOK : Prop where
  funcs_size : X.m₁.funcs.size = X.m.funcs.size
  regions_size : X.m₁.regions.size = X.m.regions.size
  funcs : ∀ i (hi : i < X.m.funcs.size), ∃ hi₁ : i < X.m₁.funcs.size, ∃ E : Nat → List Fact,
    BodyOK X (X.m.funcs[i]'hi) (X.m₁.funcs[i]'hi₁) E ∧
    StartOK (paramsOf (X.m.funcs[i]'hi) 0) (paramsOf (X.m₁.funcs[i]'hi₁) 0) (E 0) ∧
    (X.m₁.funcs[i]'hi₁).name = (X.m.funcs[i]'hi).name ∧
    (X.m₁.funcs[i]'hi₁).params = (X.m.funcs[i]'hi).params ∧
    (X.m₁.funcs[i]'hi₁).ret = (X.m.funcs[i]'hi).ret
  regions : ∀ k (hk : k < X.m.regions.size), ∃ hk₁ : k < X.m₁.regions.size,
    BodyOK X (X.m.regions[k]'hk) (X.m₁.regions[k]'hk₁) (X.ER k)

/-- **The linked module `m₁` promotes the linked module `m`**: a certificate of the promotion
alone, with no condition on the instructions. -/
def PromotionOK (m m₁ : LModule M) : Prop :=
  ∃ ER : Nat → Nat → List Fact, ModOK ⟨m, m₁, fun _ => True, fun _ => True, ER⟩

/-! ## Conditions on instructions -/

section
variable {X : CertEnv M} (R : LInsn M → Prop) (RT : LTerm M → Prop)

/-- A certified terminator that meets `RT` is certified with `RT` as the condition. -/
theorem TermOK.withRules {E : Nat → List Fact} {g g₁ : LBody M} {F : List Fact} {t t₁ : LTerm M}
    (h : TermOK X E g g₁ F t t₁) (ht : RT t) : TermOK { X with R, RT } E g g₁ F t t₁ := by
  cases h with
  | case _ ha hs => exact .case ht ha hs
  | sem Wr _ hWr ha hs hregs => exact .sem Wr ht hWr ha hs hregs

/-- A certified rest of a block whose instructions meet `R` and whose terminator meets `RT` is
certified with `R` and `RT` as the conditions. -/
theorem CodeOK.withRules {E : Nat → List Fact} {g g₁ : LBody M} {F : List Fact}
    {code code₁ : List (LInsn M)} {t t₁ : LTerm M} (h : CodeOK X E g g₁ F code t code₁ t₁)
    (hc : ∀ i ∈ code, R i) (ht : RT t) : CodeOK { X with R, RT } E g g₁ F code t code₁ t₁ := by
  induction h with
  | term h₀ => exact .term (h₀.withRules R RT ht)
  | getProm hu _ ih => exact .getProm hu (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | setProm hp hu hdc _ ih =>
    exact .setProm hp hu hdc (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | newProm hu hud _ ih =>
    exact .newProm hu hud (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | newKept hu _ ih => exact .newKept hu (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | getKept hc₀ _ ih =>
    exact .getKept hc₀ (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | setKept hc₀ hv _ ih =>
    exact .setKept hc₀ hv (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | const _ _ ih =>
    exact .const (hc _ List.mem_cons_self) (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | pure _ ha _ ih =>
    exact .pure (hc _ List.mem_cons_self) ha (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | sem Wr _ hWr ha hs hregs _ ih =>
    exact .sem Wr (hc _ List.mem_cons_self) hWr ha hs hregs
      (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)
  | callCode hf ha _ ih =>
    exact .callCode hf ha (ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) ht)

/-- A certified body pair whose source blocks meet `R` and `RT` is certified with them. -/
theorem BodyOK.withRules {g g₁ : LBody M} {E : Nat → List Fact} (h : BodyOK X g g₁ E)
    (hg : g.All R RT) : BodyOK { X with R, RT } g g₁ E :=
  fun j hj =>
    let ⟨hj₁, hc⟩ := h j hj
    let hb := hg _ (Array.getElem_mem hj)
    ⟨hj₁, hc.withRules R RT hb.1 hb.2⟩

/-- **A certified promotion whose source's instructions meet `R` and `RT`** is certified with
them as the conditions. -/
theorem ModOK.withRules (h : ModOK X)
    (hf : ∀ g ∈ X.m.funcs, g.All R RT) (hr : ∀ g ∈ X.m.regions, g.All R RT) :
    ModOK { X with R, RT } where
  funcs_size := h.funcs_size
  regions_size := h.regions_size
  funcs i hi :=
    let ⟨hi₁, E, hB, hrest⟩ := h.funcs i hi
    ⟨hi₁, E, hB.withRules R RT (hf _ (Array.getElem_mem hi)), hrest⟩
  regions k hk :=
    let ⟨hk₁, hB⟩ := h.regions k hk
    ⟨hk₁, hB.withRules R RT (hr _ (Array.getElem_mem hk))⟩

end

end

end Strata.Dyn.RefToRegSound
