/-
The MRO abstract domain of `../../MRO_DOMAIN.md`, with its core properties
proved.

An MRO is a total order on a class's ancestors. When decorators or metaclasses
leave it uncertain, the analyzer holds a *set* of candidate MROs, abstracted by
the precedence they all agree on -- a strict partial order. This file defines
that abstraction and proves the properties dispatch relies on:

  * the agreed relation is a strict partial order (irreflexive, transitive)
  * the abstraction is sound: every candidate extends it
  * the join is intersection, and it is the least upper bound
  * more candidates never mean more precedence (antitone)
  * **the dispatch theorem**: the class a candidate dispatches to is always
    minimal under the agreed order, so the minimal set over-approximates the
    targets
  * **devirtualization**: a unique minimal element means every candidate
    dispatches to it
  * **`α (γ P) = P`** for the unrestricted `γ` (Szpilrajn, over a finite
    carrier): the abstraction is a Galois *insertion*, so no two abstract
    elements denote the same candidate set

Transitivity and the dispatch theorem both need the candidate lists to be
duplicate-free. That is not an artifact: with a repeated class, `Before` holds in
both directions between the duplicate and its neighbours, which would make the
relation cyclic. C3 linearizations are duplicate-free, so the hypothesis is
discharged at the call site -- but it has to be *stated*, and proving these
properties is what surfaced it.
-/

namespace Pylate
namespace Mro

variable {α : Type}

/-- Duplicate-freedom, spelled out rather than imported, so this file depends on
    nothing outside core. -/
def NoDup : List α → Prop
  | [] => True
  | x :: rest => x ∉ rest ∧ NoDup rest

/-- `a` occurs in the list and `b` occurs strictly after it.

    This is the concrete precedence an MRO gives: `Before a b mro` says a lookup
    walking `mro` reaches `a` before `b`. -/
inductive Before (a b : α) : List α → Prop
  | here {rest : List α} : b ∈ rest → Before a b (a :: rest)
  | there {x : α} {rest : List α} : Before a b rest → Before a b (x :: rest)

theorem Before.left_mem {a b : α} {L : List α} : Before a b L → a ∈ L := by
  intro h
  induction h with
  | here _ => exact List.mem_cons_self ..
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem Before.right_mem {a b : α} {L : List α} : Before a b L → b ∈ L := by
  intro h
  induction h with
  | here hb => exact List.mem_cons_of_mem _ hb
  | there _ ih => exact List.mem_cons_of_mem _ ih

theorem Before.irrefl {L : List α} (hnd : NoDup L) (a : α) :
    ¬ Before a a L := by
  induction L with
  | nil => intro h; cases h
  | cons x rest ih =>
    intro h
    cases h with
    | here hmem => exact hnd.1 hmem
    | there h' => exact ih hnd.2 h'

theorem Before.trans {L : List α} (hnd : NoDup L) {a b c : α}
    (hab : Before a b L) (hbc : Before b c L) : Before a c L := by
  induction L with
  | nil => cases hab
  | cons x rest ih =>
    cases hab with
    | here hb =>
      -- The head is `a`, and `b` is in the tail. `hbc` cannot fire `here`,
      -- because that would put `b` at the head too, and `b` is in the tail.
      cases hbc with
      | here _ => exact absurd hb hnd.1
      | there hbc' => exact Before.here hbc'.right_mem
    | there hab' =>
      cases hbc with
      | here _ =>
        -- The head is `b`, yet `hab'` places `b` in the tail.
        exact absurd hab'.right_mem hnd.1
      | there hbc' => exact Before.there (ih hnd.2 hab' hbc')

/-! ## The abstraction

`Agreed` is `α` of the design document: the precedence every candidate shares. -/

/-- `a` precedes `b` in *every* candidate MRO. -/
def Agreed (cands : List (List α)) (a b : α) : Prop :=
  ∀ L ∈ cands, Before a b L

/-- `L` is a linear extension of `P`: it realises every precedence `P` claims.
    This is membership in `γ P`. -/
def Extends (L : List α) (P : α → α → Prop) : Prop :=
  ∀ a b, P a b → Before a b L

/-- Soundness of the abstraction: every candidate extends the agreed order, so
    `S ⊆ γ (α S)`. One line, which is the point -- the abstraction is defined as
    the property being claimed. -/
theorem agreed_sound {cands : List (List α)} {L : List α} (h : L ∈ cands) :
    Extends L (Agreed cands) :=
  fun _ _ hab => hab L h

/-- The easy half of the Galois insertion: `P ⊆ α (γ P)`. Anything `P` claims is
    agreed by any family of extensions of `P`.

    The converse, `α (γ P) ⊆ P` -- every partial order is the intersection of its
    linear extensions, which follows from Szpilrajn's extension theorem
    (Dushnik--Miller is the *dimension* refinement, a different statement) -- is
    proved below as `agreed_of_extends_conv`, for a finite carrier and a
    decidable `P`. `agreed_gamma_eq` packages the two directions into the
    equality that makes this a Galois *insertion*, so the domain keeps no two
    representations of the same candidate set.

    That is for the *unrestricted* `γ`. Cutting `γ` down to C3-valid
    linearizations turns `α ∘ γ` into a proper closure operator: distinct `P`s can
    then denote the same candidate set, and the insertion claim lapses (the
    connection, and hence soundness, does not). Nothing below depends on the
    converse either way: soundness of dispatch rests on `agreed_sound` and
    `firstDefiner_minimal`. -/
theorem agreed_of_extends {P : α → α → Prop} {cands : List (List α)}
    (h : ∀ L ∈ cands, Extends L P) : ∀ a b, P a b → Agreed cands a b :=
  fun a b hab L hL => h L hL a b hab

theorem Agreed.irrefl {cands : List (List α)} {L : List α} (hL : L ∈ cands)
    (hnd : NoDup L) (a : α) : ¬ Agreed cands a a :=
  fun h => Before.irrefl hnd a (h L hL)

theorem Agreed.trans {cands : List (List α)} (hnd : ∀ L ∈ cands, NoDup L)
    {a b c : α} (hab : Agreed cands a b) (hbc : Agreed cands b c) :
    Agreed cands a c :=
  fun L hL => Before.trans (hnd L hL) (hab L hL) (hbc L hL)

/-! ## The lattice

Join is *intersection* of precedence: joining two candidate sets keeps only the
pairs both agree on. -/

/-- The join is exactly the intersection of the two agreed relations. -/
theorem agreed_append {c₁ c₂ : List (List α)} (a b : α) :
    Agreed (c₁ ++ c₂) a b ↔ (Agreed c₁ a b ∧ Agreed c₂ a b) := by
  constructor
  · intro h
    exact ⟨fun L hL => h L (List.mem_append_left _ hL),
           fun L hL => h L (List.mem_append_right _ hL)⟩
  · intro h L hL
    rcases List.mem_append.mp hL with hl | hr
    · exact h.1 L hl
    · exact h.2 L hr

/-- More candidates never yield more precedence. This is why the join descends a
    finite lattice: the relation only ever loses pairs, and there are at most
    `|V|²` of them, so no widening is required. -/
theorem agreed_antitone {c₁ c₂ : List (List α)} (hsub : ∀ L ∈ c₁, L ∈ c₂)
    {a b : α} (h : Agreed c₂ a b) : Agreed c₁ a b :=
  fun L hL => h L (hsub L hL)

/-! ## Dispatch

What a lookup consumes is not the order but the *first* class in it that defines
the member. -/

/-- The class a lookup of the member resolves to, walking one candidate MRO. -/
def firstDefiner (defines : α → Bool) (L : List α) : Option α :=
  L.find? defines

/-- `x` is minimal among `D` under `P`: nothing in `D` provably precedes it. -/
def Minimal (P : α → α → Prop) (D : List α) (x : α) : Prop :=
  x ∈ D ∧ ∀ y ∈ D, ¬ P y x

/-- `find?` really does return the *first* match: nothing satisfying the
    predicate occurs before the element it found. -/
theorem not_before_find? {defines : α → Bool} {L : List α} {w y : α}
    (hnd : NoDup L) (hf : L.find? defines = some w)
    (hy : defines y = true) : ¬ Before y w L := by
  induction L with
  | nil => simp [List.find?] at hf
  | cons x rest ih =>
    by_cases hx : defines x
    · -- `w` is the head, so anything before it would have to be a duplicate.
      rw [List.find?_cons_of_pos hx] at hf
      have hw : w = x := (Option.some_inj.mp hf).symm
      intro h
      cases h with
      | here hmem => exact hnd.1 (hw ▸ hmem)
      | there h' => exact hnd.1 (hw ▸ h'.right_mem)
    · -- The head does not define, so it cannot be `y`.
      rw [List.find?_cons_of_neg hx] at hf
      intro h
      cases h with
      | here _ => exact hx (by simpa using hy)
      | there h' => exact ih hnd.2 hf h'

/-- **The dispatch theorem.** Whatever a candidate MRO dispatches to is minimal
    under the agreed order.

    So `Minimal (Agreed cands) D` over-approximates the set of possible targets,
    and it is computed from the partial order alone -- no candidate MRO has to be
    enumerated. `D` is the set of ancestors defining the member.

    `hD` and `hw` together are an *exactness* assumption on `D`: every member of
    `D` certainly defines, and the actual target is in `D`. That is the
    `mustOwners = mayOwners` case. When the two differ, minimality
    under-approximates -- with `mayOwners = {A, B}`, `mustOwners = {B}` and
    `A < B`, the only minimal element is `A`, yet `B` is a target in every world
    where `A` does not in fact define the member. `firstDefiner_candidate` below
    is the form that holds for a may/must split, and is the one to implement. -/
theorem firstDefiner_minimal {cands : List (List α)} {defines : α → Bool}
    {D L : List α} {w : α}
    (hL : L ∈ cands) (hnd : NoDup L)
    (hD : ∀ y ∈ D, defines y = true) (hw : w ∈ D)
    (hf : firstDefiner defines L = some w) :
    Minimal (Agreed cands) D w := by
  refine ⟨hw, ?_⟩
  intro y hy hagree
  exact not_before_find? hnd hf (hD y hy) (hagree L hL)

/-- **Devirtualization is sound.** If the agreed order has a unique minimal
    definer, every candidate MRO dispatches to it -- so the site resolves to one
    target even though the MRO is not known.

    This is the property that makes the domain worth having: uncertainty about
    the order does not have to mean uncertainty about the target. -/
theorem devirtualize {cands : List (List α)} {defines : α → Bool}
    {D : List α} {w : α}
    (hnd : ∀ L ∈ cands, NoDup L)
    (hD : ∀ y ∈ D, defines y = true)
    (hresolves : ∀ L ∈ cands, ∃ u, u ∈ D ∧ firstDefiner defines L = some u)
    (hunique : ∀ x, Minimal (Agreed cands) D x → x = w) :
    ∀ L ∈ cands, firstDefiner defines L = some w := by
  intro L hL
  obtain ⟨u, huD, hfu⟩ := hresolves L hL
  have hmin := firstDefiner_minimal hL (hnd L hL) hD huD hfu
  rw [← hunique u hmin]
  exact hfu

/-! ### The may/must form

The class fact carries `mayOwners` and `mustOwners` separately, and the exact-`D`
statement above does not survive the split. `Candidate` is the rule that does:
*may* define, and not provably preceded by anything that *must* define. Only
certain definers can rule a class out, and every possible definer is retained. -/

/-- `x` is a possible dispatch target: it may define the member, and nothing that
    certainly defines the member provably precedes it.

    `Minimal P D` is the special case `Candidate P D D`, i.e. `mayOwners` and
    `mustOwners` coinciding. -/
def Candidate (P : α → α → Prop) (mayD mustD : List α) (x : α) : Prop :=
  x ∈ mayD ∧ ∀ y ∈ mustD, ¬ P y x

/-- **The dispatch theorem, may/must form.** Whatever a candidate MRO dispatches
    to is a `Candidate`. Unlike `firstDefiner_minimal` this assumes nothing about
    the target: `w ∈ mayD` is derived, not hypothesised, because `mayD`
    over-approximates the definers.

    Soundness needs the two approximations to point the right way -- `mayD` must
    contain every definer in the MRO, `mustD` may contain only real definers --
    and nothing relates the two, so `mustD ⊆ mayD` is not required. -/
theorem firstDefiner_candidate {cands : List (List α)} {defines : α → Bool}
    {mayD mustD L : List α} {w : α}
    (hL : L ∈ cands) (hnd : NoDup L)
    (hmay : ∀ y ∈ L, defines y = true → y ∈ mayD)
    (hmust : ∀ y ∈ mustD, defines y = true)
    (hf : firstDefiner defines L = some w) :
    Candidate (Agreed cands) mayD mustD w := by
  refine ⟨hmay w (List.mem_of_find?_eq_some hf) (List.find?_some hf), ?_⟩
  intro y hy hagree
  exact not_before_find? hnd hf (hmust y hy) (hagree L hL)

/-- **Devirtualization, may/must form.** A single candidate target settles the
    site -- provided the member is not also possibly absent, which is what
    `hresolves` rules out: every candidate MRO does resolve. Dropping it would
    leave the `AttributeError` edge unaccounted for, which is exactly the third
    value of the three-valued resolution result. -/
theorem devirtualize_candidate {cands : List (List α)} {defines : α → Bool}
    {mayD mustD : List α} {w : α}
    (hnd : ∀ L ∈ cands, NoDup L)
    (hmay : ∀ L ∈ cands, ∀ y ∈ L, defines y = true → y ∈ mayD)
    (hmust : ∀ y ∈ mustD, defines y = true)
    (hresolves : ∀ L ∈ cands, ∃ u, firstDefiner defines L = some u)
    (hunique : ∀ x, Candidate (Agreed cands) mayD mustD x → x = w) :
    ∀ L ∈ cands, firstDefiner defines L = some w := by
  intro L hL
  obtain ⟨u, hfu⟩ := hresolves L hL
  have hcand := firstDefiner_candidate hL (hnd L hL) (hmay L hL) hmust hfu
  rw [← hunique u hcand]
  exact hfu

/-- The self-first C3 invariant, as the domain sees it: a class defining the
    member itself is the unique target, whatever the rest of the order is.

    This is why a weak agreed order still devirtualizes most sites -- every
    candidate MRO starts with the class itself. -/
theorem self_first_devirtualizes {defines : α → Bool} {c : α} {rest : List α}
    (hc : defines c = true) : firstDefiner defines (c :: rest) = some c := by
  simp only [firstDefiner]
  exact List.find?_cons_of_pos hc

/-! ## `α (γ P) ⊆ P`

The hard half of the Galois insertion. Every finite strict partial order is the
intersection of its linear extensions (Szpilrajn; Dushnik--Miller is the
dimension theorem).

The construction is a rank sort. Ranking each element by *how many elements of the
carrier precede it* gives a numeric key that strictly increases along `P`, because
transitivity makes the predecessors of `x` a subset of those of `y` whenever
`P x y`, and irreflexivity puts `x` itself in the second set and not the first. Any
sort by that key is therefore a linear extension, which discharges the linear
extension existence theorem, and no notion of transitive closure or well-founded
recursion is needed.

To *omit* an unclaimed pair `(a, b)`, the order is first augmented with `b < a`
and closed by hand -- `augment` is that closure written out, since `¬ P a b` means
the only new pairs are the product of the elements at-or-below `b` with those
at-or-above `a`. The sort then places `b` before `a`, so `a` does not precede `b`
in that extension.

This is for the unrestricted `γ`. It says nothing about the C3-restricted `γ`,
where `α ∘ γ` is only a closure operator. -/

/-- `NoDup` agrees with the core predicate, so the permutation lemmas apply. -/
theorem noDup_iff_nodup {L : List α} : NoDup L ↔ L.Nodup := by
  induction L with
  | nil => simp [NoDup]
  | cons x rest ih => simp [NoDup, List.nodup_cons, ih]

/-- A pairwise-sorted list realises its order as `Before`: if `R` fails backwards
    between two of its elements, the list holds them in order. -/
theorem Before.of_pairwise {R : α → α → Prop} (hrefl : ∀ z, R z z) :
    ∀ (L : List α), L.Pairwise R → ∀ (x y : α), x ∈ L → y ∈ L → ¬ R y x →
      Before x y L := by
  intro L
  induction L with
  | nil => intro _ x _ hx _ _; exact absurd hx List.not_mem_nil
  | cons z rest ih =>
    intro hp x y hx hy hne
    obtain ⟨hz, hrest⟩ := List.pairwise_cons.mp hp
    have hxy : x ≠ y := by
      intro h
      apply hne
      rw [h]
      exact hrefl y
    rcases List.mem_cons.mp hx with hxz | hx'
    · have hyr : y ∈ rest := by
        rcases List.mem_cons.mp hy with hyz | hy'
        · exact absurd (hxz.trans hyz.symm) hxy
        · exact hy'
      rw [← hxz]
      exact Before.here hyr
    · have hyr : y ∈ rest := by
        rcases List.mem_cons.mp hy with hyz | hy'
        · exfalso
          apply hne
          rw [hyz]
          exact hz x hx'
        · exact hy'
      exact Before.there (ih hrest x y hx' hyr hne)

/-- The converse: `Before` in a pairwise-sorted list is witnessed by the order. -/
theorem Before.to_pairwise {R : α → α → Prop} {L : List α} {x y : α}
    (h : Before x y L) (hp : L.Pairwise R) : R x y := by
  induction h with
  | here hmem => exact (List.pairwise_cons.mp hp).1 _ hmem
  | there _ ih => exact ih (List.pairwise_cons.mp hp).2

/-! ### Counting predecessors -/

theorem length_filter_le_of_imp {p q : α → Bool} :
    ∀ (V : List α), (∀ z ∈ V, p z = true → q z = true) →
      (V.filter p).length ≤ (V.filter q).length := by
  intro V
  induction V with
  | nil => intro _; simp
  | cons z rest ih =>
    intro h
    have hrest : ∀ w ∈ rest, p w = true → q w = true :=
      fun w hw => h w (List.mem_cons_of_mem _ hw)
    by_cases hp : p z = true
    · have hq : q z = true := h z (List.mem_cons_self ..) hp
      rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
      have := ih hrest
      simp only [List.length_cons]
      omega
    · rw [List.filter_cons_of_neg hp]
      by_cases hq : q z = true
      · rw [List.filter_cons_of_pos hq]
        have := ih hrest
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg hq]
        exact ih hrest

/-- One witness `w` that `q` keeps and `p` drops makes the inequality strict. No
    duplicate-freedom needed: `filter` preserves positions, so the witness is
    counted once on each side. -/
theorem length_filter_lt_of_imp {p q : α → Bool} {w : α} :
    ∀ (V : List α), (∀ z ∈ V, p z = true → q z = true) → w ∈ V →
      q w = true → p w ≠ true →
      (V.filter p).length < (V.filter q).length := by
  intro V
  induction V with
  | nil => intro _ hw _ _; exact absurd hw List.not_mem_nil
  | cons z rest ih =>
    intro h hw hqw hpw
    have hrest : ∀ v ∈ rest, p v = true → q v = true :=
      fun v hv => h v (List.mem_cons_of_mem _ hv)
    rcases List.mem_cons.mp hw with heq | hw'
    · have hpz : p z ≠ true := by rw [← heq]; exact hpw
      have hqz : q z = true := by rw [← heq]; exact hqw
      rw [List.filter_cons_of_neg hpz, List.filter_cons_of_pos hqz]
      have := length_filter_le_of_imp rest hrest
      simp only [List.length_cons]
      omega
    · by_cases hp : p z = true
      · have hq : q z = true := h z (List.mem_cons_self ..) hp
        rw [List.filter_cons_of_pos hp, List.filter_cons_of_pos hq]
        have := ih hrest hw' hqw hpw
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg hp]
        by_cases hq : q z = true
        · rw [List.filter_cons_of_pos hq]
          have := ih hrest hw' hqw hpw
          simp only [List.length_cons]
          omega
        · rw [List.filter_cons_of_neg hq]
          exact ih hrest hw' hqw hpw

/-- How many elements of the carrier `V` precede `x`. -/
def rank (Q : α → α → Bool) (V : List α) (x : α) : Nat :=
  (V.filter (fun z => Q z x)).length

/-- The rank is a strictly increasing key for any strict partial order. This is
    the whole topological sort. -/
theorem rank_lt {Q : α → α → Bool} {V : List α}
    (hirr : ∀ x, Q x x ≠ true)
    (htr : ∀ x y z, Q x y = true → Q y z = true → Q x z = true)
    {x y : α} (hx : x ∈ V) (h : Q x y = true) : rank Q V x < rank Q V y :=
  length_filter_lt_of_imp (p := fun z => Q z x) (q := fun z => Q z y) (w := x) V
    (fun z _ hz => htr z x y hz h) hx h (hirr x)

/-! ### The extension -/

def rankLe (Q : α → α → Bool) (V : List α) (x y : α) : Bool :=
  decide (rank Q V x ≤ rank Q V y)

theorem rankLe_refl (Q : α → α → Bool) (V : List α) (x : α) :
    rankLe Q V x x = true := by simp [rankLe]

theorem rankLe_trans (Q : α → α → Bool) (V : List α) (x y z : α)
    (hxy : rankLe Q V x y = true) (hyz : rankLe Q V y z = true) :
    rankLe Q V x z = true := by
  simp only [rankLe, decide_eq_true_eq] at hxy hyz ⊢
  omega

theorem rankLe_total (Q : α → α → Bool) (V : List α) (x y : α) :
    (rankLe Q V x y || rankLe Q V y x) = true := by
  simp only [rankLe, Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

/-- The carrier sorted by rank: a linear extension of `Q`. -/
def linExt (Q : α → α → Bool) (V : List α) : List α := V.mergeSort (rankLe Q V)

theorem linExt_perm (Q : α → α → Bool) (V : List α) : (linExt Q V).Perm V :=
  List.mergeSort_perm V (rankLe Q V)

theorem linExt_pairwise (Q : α → α → Bool) (V : List α) :
    List.Pairwise (fun x y => rankLe Q V x y = true) (linExt Q V) :=
  List.pairwise_mergeSort (rankLe_trans Q V) (rankLe_total Q V) V

theorem noDup_linExt {Q : α → α → Bool} {V : List α} (hnd : NoDup V) :
    NoDup (linExt Q V) :=
  noDup_iff_nodup.mpr
    ((linExt_perm Q V).nodup_iff.mpr (noDup_iff_nodup.mp hnd))

theorem extends_linExt {Q : α → α → Bool} {V : List α}
    (hirr : ∀ x, Q x x ≠ true)
    (htr : ∀ x y z, Q x y = true → Q y z = true → Q x z = true)
    (hdom : ∀ x y, Q x y = true → x ∈ V ∧ y ∈ V) :
    Extends (linExt Q V) (fun x y => Q x y = true) := by
  intro x y hxy
  obtain ⟨hxV, hyV⟩ := hdom x y hxy
  have hlt : rank Q V x < rank Q V y := rank_lt hirr htr hxV hxy
  refine Before.of_pairwise (R := fun u v => rankLe Q V u v = true)
    (fun z => rankLe_refl Q V z) (linExt Q V) (linExt_pairwise Q V) x y
    ((linExt_perm Q V).mem_iff.mpr hxV) ((linExt_perm Q V).mem_iff.mpr hyV) ?_
  simp only [rankLe, decide_eq_true_eq]
  omega

/-- The extension is strict: it never runs a `Q`-pair backwards. -/
theorem not_before_linExt {Q : α → α → Bool} {V : List α}
    (hirr : ∀ x, Q x x ≠ true)
    (htr : ∀ x y z, Q x y = true → Q y z = true → Q x z = true)
    (hdom : ∀ x y, Q x y = true → x ∈ V ∧ y ∈ V)
    {x y : α} (hxy : Q x y = true) : ¬ Before y x (linExt Q V) := by
  intro hb
  have hlt : rank Q V x < rank Q V y := rank_lt hirr htr (hdom x y hxy).1 hxy
  have hle := hb.to_pairwise (linExt_pairwise Q V)
  simp only [rankLe, decide_eq_true_eq] at hle
  omega

/-- **Linear extension existence** for a finite decidable strict partial order:
    the theorem the abstraction's optimality argument was missing. -/
theorem exists_linear_extension {Q : α → α → Bool} {V : List α}
    (hnd : NoDup V)
    (hirr : ∀ x, Q x x ≠ true)
    (htr : ∀ x y z, Q x y = true → Q y z = true → Q x z = true)
    (hdom : ∀ x y, Q x y = true → x ∈ V ∧ y ∈ V) :
    ∃ L : List α, L.Perm V ∧ NoDup L ∧ Extends L (fun x y => Q x y = true) :=
  ⟨linExt Q V, linExt_perm Q V, noDup_linExt hnd, extends_linExt hirr htr hdom⟩

/-! ### Forcing one pair the other way -/

/-- `P` with the single extra pair `b < a`, transitively closed by hand.
    `x = b ∨ P x b` says `x` is at or below `b`, `y = a ∨ P a y` says `y` is at or
    above `a`; when `¬ P a b`, the closure adds exactly that product. -/
def augment [DecidableEq α] (P : α → α → Bool) (a b x y : α) : Bool :=
  P x y || ((decide (x = b) || P x b) && (decide (y = a) || P a y))

theorem augment_eq_true [DecidableEq α] {P : α → α → Bool} {a b x y : α} :
    augment P a b x y = true ↔
      P x y = true ∨ ((x = b ∨ P x b = true) ∧ (y = a ∨ P a y = true)) := by
  simp [augment]

theorem augment_of_le [DecidableEq α] {P : α → α → Bool} {a b x y : α}
    (h : P x y = true) : augment P a b x y = true :=
  augment_eq_true.mpr (Or.inl h)

theorem augment_pair [DecidableEq α] {P : α → α → Bool} (a b : α) :
    augment P a b b a = true :=
  augment_eq_true.mpr (Or.inr ⟨Or.inl rfl, Or.inl rfl⟩)

/-- Irreflexivity is where `¬ P a b` is spent: without it the added pair closes a
    cycle. `a ≠ b` is spent too, which is why the diagonal is handled separately
    in `agreed_of_extends_conv`. -/
theorem augment_irrefl [DecidableEq α] {P : α → α → Bool} {a b : α}
    (hirr : ∀ x, P x x ≠ true)
    (htr : ∀ x y z, P x y = true → P y z = true → P x z = true)
    (hne : a ≠ b) (hab : P a b ≠ true) (x : α) :
    augment P a b x x ≠ true := by
  intro hc
  rw [augment_eq_true] at hc
  rcases hc with h | ⟨hd, hu⟩
  · exact hirr x h
  · rcases hd with rfl | hd
    · rcases hu with rfl | hu
      · exact hne rfl
      · exact hab hu
    · rcases hu with rfl | hu
      · exact hab hd
      · exact hab (htr a x b hu hd)

theorem augment_trans [DecidableEq α] {P : α → α → Bool} {a b : α}
    (htr : ∀ x y z, P x y = true → P y z = true → P x z = true)
    (x y z : α) (hxy : augment P a b x y = true)
    (hyz : augment P a b y z = true) : augment P a b x z = true := by
  rw [augment_eq_true] at hxy hyz ⊢
  rcases hxy with h1 | ⟨hd, hu⟩
  · rcases hyz with h2 | ⟨hd2, hu2⟩
    · exact Or.inl (htr x y z h1 h2)
    · refine Or.inr ⟨?_, hu2⟩
      rcases hd2 with rfl | hd2
      · exact Or.inr h1
      · exact Or.inr (htr x y b h1 hd2)
  · rcases hyz with h2 | ⟨hd2, hu2⟩
    · refine Or.inr ⟨hd, ?_⟩
      rcases hu with rfl | hu
      · exact Or.inr h2
      · exact Or.inr (htr a y z hu h2)
    · exact Or.inr ⟨hd, hu2⟩

theorem augment_mem [DecidableEq α] {P : α → α → Bool} {V : List α} {a b : α}
    (hdom : ∀ x y, P x y = true → x ∈ V ∧ y ∈ V) (ha : a ∈ V) (hb : b ∈ V)
    (x y : α) (h : augment P a b x y = true) : x ∈ V ∧ y ∈ V := by
  rw [augment_eq_true] at h
  rcases h with h | ⟨hd, hu⟩
  · exact hdom x y h
  · refine ⟨?_, ?_⟩
    · rcases hd with rfl | hd
      · exact hb
      · exact (hdom x b hd).1
    · rcases hu with rfl | hu
      · exact ha
      · exact (hdom a y hu).2

/-! ### The theorem -/

/-- **`α (γ P) ⊆ P`.** If every linear extension of `P` over the carrier `V` puts
    `a` before `b`, then `P` already claims it.

    `γ P` is spelled as the predicate "permutation of `V` that extends `P`" rather
    than as an enumerated list, so `hagree` is literally `(a, b) ∈ α (γ P)` for
    the unrestricted `γ`. `P` is `Bool`-valued because the construction sorts by
    it; that costs nothing here, since the domain's `precedes` is an
    `Fset (String × String)`.

    Membership of `a` and `b` in `V` is not assumed. It follows from `hagree`,
    because `linExt` is itself one of the extensions being quantified over. -/
theorem agreed_of_extends_conv [DecidableEq α] {P : α → α → Bool} {V : List α}
    (hnd : NoDup V)
    (hirr : ∀ x, P x x ≠ true)
    (htr : ∀ x y z, P x y = true → P y z = true → P x z = true)
    (hdom : ∀ x y, P x y = true → x ∈ V ∧ y ∈ V)
    {a b : α}
    (hagree : ∀ L : List α, L.Perm V → Extends L (fun x y => P x y = true) →
      Before a b L) :
    P a b = true := by
  by_cases hab : P a b = true
  · exact hab
  exfalso
  have hbase : Before a b (linExt P V) :=
    hagree (linExt P V) (linExt_perm P V) (extends_linExt hirr htr hdom)
  have ha : a ∈ V := (linExt_perm P V).mem_iff.mp hbase.left_mem
  have hb : b ∈ V := (linExt_perm P V).mem_iff.mp hbase.right_mem
  by_cases hne : a = b
  · -- The diagonal: `P` is irreflexive, and so is `Before` on a duplicate-free
    -- list, so one extension suffices.
    rw [hne] at hbase
    exact Before.irrefl (noDup_linExt hnd) b hbase
  · have hAirr := augment_irrefl hirr htr hne hab
    have hAtr := augment_trans (a := a) (b := b) htr
    have hAdom := augment_mem hdom ha hb
    have hext : Extends (linExt (augment P a b) V) (fun x y => P x y = true) :=
      fun x y hxy => extends_linExt hAirr hAtr hAdom x y (augment_of_le hxy)
    exact not_before_linExt hAirr hAtr hAdom (augment_pair a b)
      (hagree _ (linExt_perm (augment P a b) V) hext)

/-- **The Galois insertion.** `α (γ P) = P` for the unrestricted `γ`: the abstract
    element is recovered exactly from the candidate set it denotes, so the domain
    carries no redundant representations. -/
theorem agreed_gamma_eq [DecidableEq α] {P : α → α → Bool} {V : List α}
    (hnd : NoDup V)
    (hirr : ∀ x, P x x ≠ true)
    (htr : ∀ x y z, P x y = true → P y z = true → P x z = true)
    (hdom : ∀ x y, P x y = true → x ∈ V ∧ y ∈ V)
    (a b : α) :
    P a b = true ↔
      ∀ L : List α, L.Perm V → Extends L (fun x y => P x y = true) →
        Before a b L :=
  ⟨fun h _ _ hext => hext a b h, agreed_of_extends_conv hnd hirr htr hdom⟩

end Mro
end Pylate
