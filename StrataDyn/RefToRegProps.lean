/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToReg
public import StrataDyn.RewriteProps
-- `refToRegWith_ok` unfolds `Module.Raw.check`.
import all StrataDyn.WF

set_option autoImplicit false

/-!
# Ref-to-reg keeps the control-flow graph, and what its check gives

* `refToRegWith_ok`: each function of `refToRegWith`'s output (so of `refToReg`'s) is
  `P.apply S.maps f` for a function `f` of its input and a plan `P` that passes `Plan.check`
  with `S`, the start maps that `Plan.starts` computes from `f`'s dominator trees and `P`.  The
  facts below are about such a function.
* `Func.edgeShape_apply`: `Plan.apply` keeps every block's label and every edge's target, in
  every body, regions included, in order (`edgeShape`, `StrataDyn/RewriteProps.lean`).  In a
  well-formed function each body's blocks are those its edges reach, so this keeps each body's
  control-flow graph, and with it the dominator trees at block level and the loops.
* `Plan.check_read`, `Plan.check_edge`, `Plan.check_entry`: what `Plan.check` gives about each
  event of the walk (`walk`): a removed read is replaced by its cell's content there, an edge
  passes what its target's plan expects, and a body's entry takes nothing new.
* `Plan.edges_apply_ok`: every edge of the rewritten blocks is `P.edge m k` for an edge `k` of
  the walk, leaving where the content map is `m`, that passes the check.
* `Plan.entryParams_apply`: a checked plan keeps the function's parameters; the name, the
  return type and the annotation are kept by definition.
* `cellOp?_plain`, `drops_plain`: the instructions the rewrite removes have no edges and no
  regions.
* `walkInstrs_snd`: the walk's map after a block's instructions is `View.step` folded over them;
  `promoteWith_ok`: a function that `promoteWith` returns is a checked plan's rewrite.

TODO: prove that ref-to-reg keeps each function's behaviour, against a semantics of the IR,
once one is on mainline.  The statement: for modules `m` and `m₁` with `refToReg m = .ok m₁`,
every run of a function of `m` (its result, world and choices drawn) is a run of the same
function of `m₁`, and the converse.  It needs that an operation reads and writes only the
cells it is given or makes (`docs/Dyn.md`, §3), that a region runs only while its owner
runs, and that each run of a region starts from a copy of its owner's frame.  It also needs a
static lemma about the start maps: for each edge of the walk into a block that is not a body's
entry, every entry of the block's start map, except its carried cells, is in the edge's map with
the same value, and no such entry's value is one of the block's parameters.  Until then, the
evidence is `Plan.check`, the well-formedness check of the output, the side-by-side runs of
`RefToRegSim.sameRuns`, and `RefToRegSim.edgesAgree`, which tests that lemma, on the translator
goldens.
-/

namespace Strata.Dyn

public section

namespace RefToReg

variable {env : Env Unit} [base ≼ env] {α : Type}

/-- A base cell operation has no successors and no regions. -/
theorem cellOp?_plain {i : Instruction env α} {o : CellOp} (h : cellOp? i = some o) :
    i.succs = #[] ∧ i.regions = #[] := by
  cases i with
  | const => simp [cellOp?] at h
  | apply _ _ _ _ _ succs regions =>
    simp only [cellOp?] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hp
      simp only [Bool.or_eq_true, Bool.not_eq_true', Array.isEmpty_iff, not_or,
        Bool.not_eq_false] at hp
      simp only [Instruction.succs, Instruction.regions]
      constructor <;> simp_all

/-- An instruction the rewrite removes has no successors and nests no blocks. -/
theorem drops_plain {P : Plan env} {i : Instruction env α} (h : P.drops i = true) :
    i.succs = #[] ∧ i.nestedBlocks = [] := by
  unfold Plan.drops at h
  split at h
  · rename_i o hc
    obtain ⟨hs, hr⟩ := cellOp?_plain hc
    refine ⟨hs, ?_⟩
    cases i with
    | const => rfl
    | apply _ _ _ _ _ _ regions =>
      obtain ⟨regions⟩ := regions
      simp only [Instruction.regions] at hr
      cases regions with
      | nil => rfl
      | cons _ _ => simp at hr
  · rename_i o _ hc
    obtain ⟨hs, hr⟩ := cellOp?_plain hc
    refine ⟨hs, ?_⟩
    cases i with
    | const => rfl
    | apply _ _ _ _ _ _ regions =>
      obtain ⟨regions⟩ := regions
      simp only [Instruction.regions] at hr
      cases regions with
      | nil => rfl
      | cons _ _ => simp at hr
  · simp at h

omit [base ≼ env] in
/-- The edge rewrite keeps the target's label. -/
@[simp] theorem Plan.edge_label (P : Plan env) (m : CMap) (k : Target.Raw) :
    (P.edge m k).label = k.label := rfl

/-! ## The rewrite keeps the graph -/

section apply
variable (P : Plan env) (S : Std.HashMap Label CMap)

mutual

/-- The rewritten instructions have the same edge targets, and nest blocks of the same
shapes. -/
private theorem applyInstrs_shape : ∀ (m : CMap) (is : List (Instruction env α)),
    (applyInstrs P S m is).flatMap (·.succs.toList.map (·.label)) =
        is.flatMap (·.succs.toList.map (·.label)) ∧
      (Instruction.nestedBlocksList (applyInstrs P S m is)).map blockShape =
        (Instruction.nestedBlocksList is).map blockShape
  | _, [] => ⟨rfl, rfl⟩
  | m, i :: is => by
    have ih := applyInstrs_shape (P.step m i) is
    rw [applyInstrs]
    split
    · rename_i hd
      obtain ⟨hs, hn⟩ := drops_plain hd
      simp only [List.flatMap_cons, hs, Array.toList_empty, List.map_nil, List.nil_append,
        Instruction.nestedBlocksList, hn, ih.1, ih.2]
      constructor <;> first | rfl | trivial
    · have hi := applyInstr_shape (m.drop (instrWrites i)) i
      simp only [List.flatMap_cons, Instruction.nestedBlocksList, List.map_append, hi.1, hi.2,
        ih.1, ih.2]
      constructor <;> first | rfl | trivial

/-- The rewritten instruction has the same edge targets, and nests blocks of the same
shapes. -/
private theorem applyInstr_shape : ∀ (m : CMap) (i : Instruction env α),
    (applyInstr P S m i).succs.toList.map (·.label) = i.succs.toList.map (·.label) ∧
      (applyInstr P S m i).nestedBlocks.map blockShape = i.nestedBlocks.map blockShape
  | _, .const .. => ⟨rfl, rfl⟩
  | m, .apply _ _ _ _ _ succs ⟨regions⟩ => by
    refine ⟨?_, applyRegions_shape m regions⟩
    simp [applyInstr, Instruction.succs, Function.comp_def]

/-- The rewritten terminator has the same edge targets, and nests blocks of the same
shapes. -/
private theorem applyTerm_shape : ∀ (m : CMap) (t : Terminator env α),
    (applyTerm P S m t).succs.toList.map (·.label) = t.succs.toList.map (·.label) ∧
      (applyTerm P S m t).nestedBlocks.map blockShape = t.nestedBlocks.map blockShape
  | m, .apply _ _ _ _ succs ⟨regions⟩ => by
    refine ⟨?_, applyRegions_shape m regions⟩
    simp [applyTerm, Terminator.succs, Function.comp_def]

/-- Rewritten regions nest blocks of the same shapes. -/
private theorem applyRegions_shape : ∀ (m : CMap) (rs : List (Region env α)),
    (Region.blocksList (applyRegions P S m rs)).map blockShape =
      (Region.blocksList rs).map blockShape
  | _, [] => rfl
  | m, ⟨⟨blocks⟩⟩ :: rs => by
    simp only [applyRegions, Region.blocksList, List.map_append]
    rw [applyBody_shape (some m) blocks, applyRegions_shape m rs]

/-- A rewritten body's blocks, with what is nested in them, have the same shapes. -/
private theorem applyBody_shape : ∀ (entry : Option CMap) (bs : List (Block env α)),
    (Block.withNestedList (applyBody P S entry bs)).map blockShape =
      (Block.withNestedList bs).map blockShape
  | _, [] => rfl
  | entry, ⟨l, ps, ⟨instrs⟩, t, info⟩ :: bs => by
    have hi := applyInstrs_shape (entry.getD ((P.view S).entryMap l)) instrs
    have ht := applyTerm_shape
      ((instrs.foldl P.step (entry.getD ((P.view S).entryMap l))).drop (termWrites t)) t
    simp only [applyBody, Block.withNestedList, List.map_cons, List.map_append, hi.2, ht.2,
      applyBody_shape none bs]
    simp only [blockShape, hi.1, ht.1]

end

end apply


end RefToReg

open RefToReg

/-- **Ref-to-reg keeps the graph.**  `Plan.apply` keeps every block's label and every edge's
target, in every body, regions included, in order.  The rewrite adds block parameters and edge
arguments, removes instructions that have no edges and no regions, and replaces uses of
values. -/
theorem Func.edgeShape_apply {env : Env Unit} [base ≼ env] {α : Type} (P : Plan env)
    (S : Std.HashMap Label CMap) (fn : Func env α) :
    edgeShape (P.apply S fn).blocks.toList = edgeShape fn.blocks.toList := by
  simp only [Plan.apply]
  rw [Func.edgeShape_mapUses]
  exact applyBody_shape P S (some {}) fn.blocks.toList

/-! ## What the check gives -/

namespace RefToReg.Plan

variable {env : Env Unit} [base ≼ env] {α : Type} {P : Plan env} {S : Starts} {fn : Func env α}

/-- A checked plan meets the rules about the walk's events: a body's entry takes nothing new,
each edge passes what its target expects, and each removed read is replaced by its cell's
content. -/
private theorem events_of_check (h : P.check S fn = true) :
    ((walk P S.maps fn).all fun
      | .entry l => (P.block l).carried.isEmpty && (P.block l).fixed.isEmpty
      | _ => true) = true ∧
    ((walk P S.maps fn).all fun
      | .edge m k => P.edgeOk m k
      | _ => true) = true ∧
    ((walk P S.maps fn).all fun
      | .read r c v => !P.promoted.contains c || (v.isSome && P.sigma.get? r == v)
      | _ => true) = true := by
  simp only [check, rules, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨_, _, _, _, h₅, h₆, h₇, _⟩ := h
  exact ⟨h₅, h₆, h₇⟩

/-- In a checked plan, each removed read is replaced by the content its cell has at the read:
for a `refGet` of a promoted cell `c` with result `r`, the walk knows `c`'s content `u`, and
`sigma` replaces `r` by `u`. -/
theorem check_read (h : P.check S fn = true) {r c : ValId} {v : Option ValId}
    (he : Event.read r c v ∈ walk P S.maps fn) (hc : c ∈ P.promoted) :
    ∃ u, v = some u ∧ P.sigma.get? r = some u := by
  have hr := List.all_eq_true.mp (events_of_check h).2.2 _ he
  have hc₁ : P.promoted.contains c = true := Std.HashSet.mem_iff_contains.mp hc
  simp only [hc₁, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hr
  obtain ⟨hs, hl⟩ := hr
  obtain ⟨u, rfl⟩ := Option.isSome_iff_exists.mp hs
  exact ⟨u, rfl, hl⟩

/-- In a checked plan, each edge passes what its target's plan expects: the edge leaves from
where the content map is `m`, and `edgeOk` holds. -/
theorem check_edge (h : P.check S fn = true) {m : CMap} {k : Target.Raw}
    (he : Event.edge m k ∈ walk P S.maps fn) : P.edgeOk m k = true :=
  List.all_eq_true.mp (events_of_check h).2.1 _ he

/-- In a checked plan, a body's entry block takes no new parameter and no fixed content. -/
theorem check_entry (h : P.check S fn = true) {l : Label} (he : Event.entry l ∈ walk P S.maps fn) :
    (P.block l).carried = [] ∧ (P.block l).fixed = [] := by
  have := List.all_eq_true.mp (events_of_check h).1 _ he
  simpa [List.isEmpty_iff] using this

end RefToReg.Plan

namespace RefToReg

variable {env : Env Unit} [base ≼ env] {α : Type}

/-- The walk's content map after `is` is `View.step` folded over them. -/
theorem walkInstrs_snd (V : View) : ∀ (m : CMap) (is : List (Instruction env α)),
    (walkInstrs V m is).2 = is.foldl V.step m
  | _, [] => rfl
  | m, i :: is => by
    rw [walkInstrs, List.foldl_cons]
    exact walkInstrs_snd V (V.step m i) is

/-- The rewrite made `k₁` from an edge of the events `evs`. -/
@[expose] def FromWalk (P : Plan env) (evs : List Event) (k₁ : Target.Raw) : Prop :=
  ∃ m k, Event.edge m k ∈ evs ∧ k₁ = P.edge m k

section
variable (P : Plan env) (S : Std.HashMap Label CMap)

/-- The plan's walk steps as the plan does, so that `simp` sees one form of the step. -/
@[simp] private theorem view_step (m : CMap) (i : Instruction env α) :
    (P.view S).step m i = P.step m i := rfl

omit [base ≼ env] in
/-- `edgesOf` of two lists is the edges of each. -/
private theorem edgesOf_append (a b : List (Block env α)) :
    edgesOf (a ++ b) = edgesOf a ++ edgesOf b := by
  simp [edgesOf]

mutual
/-- Each edge of rewritten instructions, or of the blocks nested in them, was made from an
edge of their walk. -/
private theorem applyInstrs_from : ∀ (m : CMap) (is : List (Instruction env α)) (k₁ : Target.Raw),
    (k₁ ∈ (applyInstrs P S m is).flatMap (·.succs.toList) ∨
      k₁ ∈ edgesOf (Instruction.nestedBlocksList (applyInstrs P S m is))) →
    FromWalk P (walkInstrs (P.view S) m is).1 k₁
  | _, [], _, h => by simp [applyInstrs, edgesOf, Instruction.nestedBlocksList] at h
  | m, i :: is, k₁, h => by
    have ih := applyInstrs_from (P.step m i) is k₁
    rw [walkInstrs]
    simp only
    rw [applyInstrs] at h
    split at h
    · rename_i hd
      obtain ⟨hs, hn⟩ := drops_plain hd
      have : FromWalk P (walkInstrs (P.view S) (P.step m i) is).1 k₁ := ih (by
        simpa [List.flatMap_cons, hs, Instruction.nestedBlocksList, hn, edgesOf] using h)
      obtain ⟨mm, kk, hm, rfl⟩ := this
      exact ⟨mm, kk, by simp [hm], rfl⟩
    · simp only [List.flatMap_cons, Instruction.nestedBlocksList, edgesOf_append,
        List.mem_append] at h
      rcases h with (h | h) | (h | h)
      · -- an edge of the kept instruction
        have hi := applyInstr_succ (m.drop (instrWrites i)) i k₁ h
        obtain ⟨kk, hk, rfl⟩ := hi
        exact ⟨_, kk, by simp [Array.mem_toList_iff.mp hk], rfl⟩
      · obtain ⟨mm, kk, hm, rfl⟩ := ih (Or.inl h)
        exact ⟨mm, kk, by simp [hm], rfl⟩
      · obtain ⟨mm, kk, hm, rfl⟩ := applyInstr_from (m.drop (instrWrites i)) i k₁ h
        exact ⟨mm, kk, by simp [hm], rfl⟩
      · obtain ⟨mm, kk, hm, rfl⟩ := ih (Or.inr h)
        exact ⟨mm, kk, by simp [hm], rfl⟩

/-- Each edge of a rewritten instruction is one of its edges, rewritten. -/
private theorem applyInstr_succ : ∀ (m : CMap) (i : Instruction env α) (k₁ : Target.Raw),
    k₁ ∈ (applyInstr P S m i).succs.toList → ∃ k ∈ i.succs.toList, k₁ = P.edge m k
  | _, .const .., _, h => by simp [applyInstr, Instruction.succs] at h
  | m, .apply _ _ _ _ _ succs ⟨regions⟩, k₁, h => by
    simp only [applyInstr, Instruction.succs, Array.toList_map, List.mem_map] at h
    obtain ⟨k, hk, rfl⟩ := h
    exact ⟨k, by simpa [Instruction.succs] using hk, rfl⟩

/-- Each edge of the blocks nested in a rewritten instruction was made from an edge of the
walk of its regions. -/
private theorem applyInstr_from : ∀ (m : CMap) (i : Instruction env α) (k₁ : Target.Raw),
    k₁ ∈ edgesOf (applyInstr P S m i).nestedBlocks → FromWalk P (walkInstrRegions (P.view S) m i) k₁
  | _, .const .., _, h => by simp [applyInstr, Instruction.nestedBlocks, edgesOf] at h
  | m, .apply _ _ _ _ _ succs ⟨regions⟩, k₁, h => by
    simp only [applyInstr, Instruction.nestedBlocks] at h
    exact applyRegions_from m regions k₁ h

/-- Each edge of rewritten regions was made from an edge of their walk. -/
private theorem applyRegions_from : ∀ (m : CMap) (rs : List (Region env α)) (k₁ : Target.Raw),
    k₁ ∈ edgesOf (Region.blocksList (applyRegions P S m rs)) →
      FromWalk P (walkRegions (P.view S) m rs) k₁
  | _, [], _, h => by simp [applyRegions, Region.blocksList, edgesOf] at h
  | m, ⟨⟨blocks⟩⟩ :: rs, k₁, h => by
    simp only [applyRegions, Region.blocksList, edgesOf_append, List.mem_append] at h
    rw [walkRegions]
    rcases h with h | h
    · obtain ⟨mm, kk, hm, rfl⟩ := applyBody_from (some m) blocks k₁ h
      exact ⟨mm, kk, by simp [hm], rfl⟩
    · obtain ⟨mm, kk, hm, rfl⟩ := applyRegions_from m rs k₁ h
      exact ⟨mm, kk, by simp [hm], rfl⟩

/-- Each edge of a rewritten body, nested blocks included, was made from an edge of its walk. -/
private theorem applyBody_from :
    ∀ (entry : Option CMap) (bs : List (Block env α)) (k₁ : Target.Raw),
    k₁ ∈ edgesOf (Block.withNestedList (applyBody P S entry bs)) →
    FromWalk P (walkBody (P.view S) entry bs) k₁
  | _, [], _, h => by simp [applyBody, Block.withNestedList, edgesOf] at h
  | entry, ⟨l, ps, ⟨instrs⟩, t, info⟩ :: bs, k₁, h => by
    have key : ∀ m₀ : CMap, entry.getD ((P.view S).entryMap l) = m₀ →
        (walkBody (P.view S) entry (⟨l, ps, ⟨instrs⟩, t, info⟩ :: bs) =
          (match entry with | some _ => [Event.entry l] | none => []) ++
          (walkInstrs (P.view S) m₀ instrs).1 ++
          t.succs.toList.map (Event.edge ((instrs.foldl P.step m₀).drop (termWrites t))) ++
          walkTermRegions (P.view S) ((instrs.foldl P.step m₀).drop (termWrites t)) t ++
          walkBody (P.view S) none bs) := by
      intro m₀ hm₀
      cases entry <;>
        (simp only [Option.getD] at hm₀; subst hm₀; simp only [walkBody, walkInstrs_snd]; rfl)
    rw [key _ rfl]
    simp only [applyBody, Block.withNestedList, edgesOf, List.flatMap_cons, List.mem_append] at h
    rw [← edgesOf, edgesOf_append, edgesOf_append] at h
    simp only [List.mem_append] at h
    rcases h with (h | h) | ((h | h) | h)
    · obtain ⟨mm, kk, hm, rfl⟩ := applyInstrs_from _ instrs k₁ (Or.inl h)
      exact ⟨mm, kk, by simp [hm], rfl⟩
    · obtain ⟨_, _, _, _, succs, ⟨regions⟩⟩ := t
      simp only [applyTerm, Terminator.succs, Array.toList_map, List.mem_map] at h
      obtain ⟨kk, hk, rfl⟩ := h
      exact ⟨_, kk, by simp [Terminator.succs, Array.mem_toList_iff.mp hk], rfl⟩
    · obtain ⟨mm, kk, hm, rfl⟩ := applyInstrs_from _ instrs k₁ (Or.inr h)
      exact ⟨mm, kk, by simp [hm], rfl⟩
    · obtain ⟨_, _, _, _, succs, ⟨regions⟩⟩ := t
      simp only [applyTerm, Terminator.nestedBlocks] at h
      obtain ⟨mm, kk, hm, rfl⟩ := applyRegions_from _ regions k₁ h
      exact ⟨mm, kk, by simp [walkTermRegions, hm], rfl⟩
    · obtain ⟨mm, kk, hm, rfl⟩ := applyBody_from none bs k₁ h
      exact ⟨mm, kk, by simp [hm], rfl⟩

end
end
/-- `insertAt` of nothing changes nothing. -/
private theorem insertAt_nil {β : Type} (a : Array β) (i : Nat) : insertAt a i [] = a := by
  simp [insertAt]

/-- A checked plan keeps the function's parameters: those of its entry block. -/
theorem Plan.entryParams_apply (P : Plan env) (S : Starts) (fn : Func env α)
    (h : P.check S fn = true) :
    (P.apply S.maps fn).blocks.toList.head?.map (·.params) =
      fn.blocks.toList.head?.map (·.params) := by
  rcases hfn : fn with ⟨name, ret, ⟨bs⟩, names, info⟩
  cases bs with
  | nil => simp [Plan.apply, applyBody, Func.mapUses, Block.mapUsesList]
  | cons b bs =>
    obtain ⟨l, ps, ⟨instrs⟩, t, binfo⟩ := b
    have he : Event.entry l ∈ walk P S.maps fn := by
      subst hfn; simp [walk, walkBody]
    have hce := Plan.check_entry h he
    subst hfn
    simp [Plan.apply, applyBody, Func.mapUses, Block.mapUsesList, Block.mapUses, hce.1,
      insertAt_nil]

/-- In a checked plan, every edge of the rewritten blocks (before uses are replaced) is
`P.edge m k` for an edge `k` of the walk that leaves where the content map is `m` and passes
what its target's plan expects. -/
theorem Plan.edges_apply_ok (P : Plan env) (S : Starts) (fn : Func env α)
    (h : P.check S fn = true) (k₁ : Target.Raw)
    (hk : k₁ ∈ edgesOf (Block.withNestedList (applyBody P S.maps (some {}) fn.blocks.toList))) :
    ∃ m k, Event.edge m k ∈ walk P S.maps fn ∧ P.edgeOk m k = true ∧ k₁ = P.edge m k := by
  obtain ⟨m, k, he, rfl⟩ := applyBody_from P S.maps (some {}) fn.blocks.toList k₁ hk
  exact ⟨m, k, he, Plan.check_edge h he, rfl⟩

/-- A function that `promoteWith` returns is a checked plan's rewrite of its input, with the
start maps that the check computes from the function's tree parents and the plan. -/
theorem promoteWith_ok
    {planner : Std.HashMap Label Point → Func env α → Except String (Plan env)}
    {f f₁ : Func env α} (h : promoteWith planner f = .ok f₁) :
    ∃ (parents : Std.HashMap Label Point) (P : Plan env) (S : Starts), trees f = .ok parents ∧
      P.starts parents f = .ok S ∧ P.check S f = true ∧ f₁ = P.apply S.maps f := by
  unfold promoteWith at h
  cases ht : trees f with
  | error e => simp [ht, bind, Except.bind] at h
  | ok parents =>
    cases hp : planner parents f with
    | error e => simp [ht, hp, bind, Except.bind] at h
    | ok P =>
      cases hs : P.starts parents f with
      | error e => simp [ht, hp, hs, bind, Except.bind] at h
      | ok S =>
        simp only [ht, hp, hs, bind, Except.bind] at h
        by_cases hc : P.check S f = true
        · simp only [hc, ite_true, pure, Except.pure, Except.ok.injEq] at h
          exact ⟨parents, P, S, rfl, hs, hc, h.symm⟩
        · simp only [hc] at h
          generalize List.find? _ _ = o at h
          rcases o with _ | ⟨_, _⟩ <;> simp only [Bool.false_eq_true, ite_false] at h <;> cases h

/-- **`refToRegWith`'s output is checked rewrites.**  The output keeps the module's name, and each
of its functions is `P.apply S.maps f` for a function `f` of the input and a plan `P` that passes
`Plan.check` with `S`, the start maps that the check computes from `f`'s tree parents and `P`. -/
theorem refToRegWith_ok
    {planner : Std.HashMap Label Point → Func env α → Except String (Plan env)}
    {m m₁ : Module env α} (h : refToRegWith planner m = .ok m₁) :
    m₁.raw.name = m.raw.name ∧
    ∀ f₁ ∈ m₁.raw.funcs, ∃ f ∈ m.raw.funcs, ∃ (parents : Std.HashMap Label Point)
      (P : Plan env) (S : Starts), trees f = .ok parents ∧ P.starts parents f = .ok S ∧
        P.check S f = true ∧ f₁ = P.apply S.maps f := by
  unfold refToRegWith at h
  simp only at h
  split at h
  · simp at h
  · rename_i hnone
    split at h
    · rename_i m₂ hck
      simp only [Except.ok.injEq] at h
      subst h
      unfold Module.Raw.check at hck
      split at hck
      · simp only [Except.ok.injEq] at hck
        subst hck
        refine ⟨rfl, ?_⟩
        intro f₁ hf₁
        simp only [Array.mem_filterMap, Array.mem_map] at hf₁
        obtain ⟨⟨n, r⟩, ⟨f, hf, hfr⟩, hr⟩ := hf₁
        simp only [Prod.mk.injEq] at hfr
        obtain ⟨rfl, rfl⟩ := hfr
        split at hr
        · rename_i _ _ g hg
          simp only [Option.some.injEq] at hr
          subst hr
          simp only [Prod.mk.injEq] at hg
          obtain ⟨_, hg⟩ := hg
          exact ⟨f, hf, promoteWith_ok hg⟩
        · simp at hr
      · simp at hck
    · simp at h

end RefToReg

end

end Strata.Dyn
