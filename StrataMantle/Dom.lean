/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Scoping, and what it guarantees

This module states where a value may be used, `Func.Scopable`, which `Func.WF` asks for along
with `Func.Reachable`, and what the two guarantee, `Func.DomCorrect`.  The decision is in
`StrataMantle/DomDecide.lean` and the proofs are in `StrataMantle/DomProps.lean` and
`StrataMantle/DomComplete.lean`.

A *body* is a function's top-level blocks, or a region's.  Its first block is its entry.  A
`Point` `⟨l, k⟩` is block `l` after its first `k` instructions.  A *tree* of a body
(`Body.Tree`) gives each block's start a parent, a point of the body.  The parent of
`⟨l, k + 1⟩` is `⟨l, k⟩`, and the parent of `⟨l, 0⟩` is what the tree gives `l`.  `p` is *above*
`q`, an ancestor of it (`Body.Anc`), if `q` is reached from `p` by these parent links.  The tree
is not part of the IR: the rule asks only that a suitable one exist.

A tree is *legal* (`Body.Legal`) when the body's labels are distinct and

* (L1) its entry has no parent;
* (L2) every other block's parent is a point of the body, and its chain of parents reaches the
  entry;
* (L3) every transfer to a block leaves from the block's parent or below it.

(L3) is what makes a parent a dominator: control enters a block only from at or below its
parent, so every path to the block passes through the parent first.

Under a tree, a value is *in scope* at a point (`Body.InScope`) if it is defined at an ancestor
of the point, or is visible where the body is entered.  An instruction at `⟨l, k⟩` uses its
operands and its successors' arguments there, and defines its result at `⟨l, k + 1⟩`; a block's
parameters are defined at `⟨l, 0⟩`; its terminator is at `⟨l, n⟩` for `n` instructions.

A body is *scopable* (`Body.Scopable`) when some legal tree puts every use in scope, and each
region of an instruction or terminator at `y` is scopable in turn, entered where what that tree
puts in scope at `y` is visible.  Each body has a tree of its own.  A function's body is entered
where nothing is visible.

A body is *reachable* (`Body.Reachable`) when its entry reaches every block, at every region
depth.

`Body.DomCorrect` is what the rule guarantees, in terms of the control-flow graph: every value
used at a point is defined at a point that every path from the entry to the use passes through
(`Body.Dom`).  Every scopable body is dominance-correct, and a reachable body is scopable
exactly when it is dominance-correct.
-/

namespace Strata.Mantle

public section

variable {env : Env Unit} {α : Type}

/-- `x` is an operand of the instruction, or an argument passed to one of its successors. -/
@[expose] def Instruction.Uses (i : Instruction env α) (x : ValId) : Prop :=
  x ∈ i.args ∨ ∃ s ∈ i.succs, x ∈ s.args

/-- `x` is an operand of the terminator, or an argument passed to one of its successors. -/
@[expose] def Terminator.Uses (t : Terminator env α) (x : ValId) : Prop :=
  x ∈ t.args ∨ ∃ s ∈ t.succs, x ∈ s.args

namespace Body

/-- A tree of a body: the parent of each block's start, by the block's label. -/
abbrev Tree := Label → Option Point

variable (bs : List (Block env α))

/-! ## Trees -/

/-- The root of the body's trees: its entry, before its first instruction. -/
@[expose] def root : Point :=
  ⟨(bs.head?.map (·.label)).getD default, 0⟩

/-- `p` is `q` or above it in the tree `t`. -/
inductive Anc (t : Tree) : Point → Point → Prop
  | refl (p : Point) : Anc t p p
  | fall {p : Point} {l : Label} {k : Nat} : Anc t p ⟨l, k⟩ → Anc t p ⟨l, k + 1⟩
  | parent {p q : Point} {b : Block env α} :
      Anc t p q → b ∈ bs → t b.label = some q → Anc t p ⟨b.label, 0⟩

/-- `p` is a node of the body: `p` names a block of the body, at a count no greater than its
instruction count. -/
@[expose] def Node (p : Point) : Prop :=
  ∃ b ∈ bs, b.label = p.label ∧ p.count ≤ b.instrs.size

/-- Control may pass from `u` to the start of block `v`: a successor of the instruction or
terminator at `u` names `v`. -/
inductive Jump : Point → Block env α → Prop
  | instr {b v : Block env α} {i : Instruction env α} {k : Nat} {s : BlockValue} :
      b ∈ bs → b.instrs[k]? = some i → s ∈ i.succs → v ∈ bs → v.label = s.target →
      Jump ⟨b.label, k⟩ v
  | term {b v : Block env α} {s : BlockValue} :
      b ∈ bs → s ∈ b.term.succs → v ∈ bs → v.label = s.target →
      Jump ⟨b.label, b.instrs.size⟩ v

/-- The tree `t` of the body is legal. -/
structure Legal (t : Tree) : Prop where
  /-- No two blocks share a label. -/
  distinct : (bs.map (·.label)).Nodup
  /-- (L1) The entry has no parent. -/
  entry : ∀ e ∈ bs.head?, t e.label = none
  /-- (L2) Every other block's parent is a node of the body ... -/
  parent : ∀ b ∈ bs.tail, ∃ p, t b.label = some p ∧ Node bs p
  /-- ... and its chain of parents reaches the root. -/
  rooted : ∀ b ∈ bs, Anc bs t (root bs) ⟨b.label, 0⟩
  /-- (L3) A transfer to a block leaves from the block's parent or below it. -/
  jump : ∀ u v p, Jump bs u v → t v.label = some p → Anc bs t p u

/-! ## Definitions and uses -/

/-- `x` is defined at `p`: a parameter of block `l` at `⟨l, 0⟩`, the result of its instruction
`k` at `⟨l, k + 1⟩`.  Values defined inside its regions are not defined at any point of this
body. -/
inductive DefAt (x : ValId) : Point → Prop
  | param {b : Block env α} {d : ValDecl env} :
      b ∈ bs → d ∈ b.params → d.id = x → DefAt x ⟨b.label, 0⟩
  | result {b : Block env α} {i : Instruction env α} {k : Nat} :
      b ∈ bs → b.instrs[k]? = some i → i.result.id = x → DefAt x ⟨b.label, k + 1⟩

/-- `x` is used at `p`, outside any region: by the instruction `k` of block `l` at `⟨l, k⟩`,
or by its terminator at `⟨l, n⟩`, for `n` instructions. -/
inductive UseAt (x : ValId) : Point → Prop
  | instr {b : Block env α} {i : Instruction env α} {k : Nat} :
      b ∈ bs → b.instrs[k]? = some i → i.Uses x → UseAt x ⟨b.label, k⟩
  | term {b : Block env α} :
      b ∈ bs → b.term.Uses x → UseAt x ⟨b.label, b.instrs.size⟩

/-- `r` is a region of the instruction or terminator at `p`. -/
inductive RegionAt : Point → Region env α → Prop
  | instr {b : Block env α} {i : Instruction env α} {k : Nat} {r : Region env α} :
      b ∈ bs → b.instrs[k]? = some i → r ∈ i.regions → RegionAt ⟨b.label, k⟩ r
  | term {b : Block env α} {r : Region env α} :
      b ∈ bs → r ∈ b.term.regions → RegionAt ⟨b.label, b.instrs.size⟩ r

/-! ## The scoping rule -/

/-- `x` is in scope at `y` under the tree `t`, in a body entered where `Λ` is visible: it is
defined at an ancestor of `y`, or is in `Λ`. -/
@[expose] def InScope (t : Tree) (Λ : ValId → Prop) (x : ValId) (y : Point) : Prop :=
  (∃ d, DefAt bs x d ∧ Anc bs t d y) ∨ Λ x

/-- The tree `t` of the body is legal and, with `Λ` visible on entry, puts in scope every use of
the body outside its regions. -/
structure ScopedBy (Λ : ValId → Prop) (t : Tree) : Prop where
  legal : Legal bs t
  uses : ∀ x y, UseAt bs x y → InScope bs t Λ x y

/-- With `Λ` visible on entry, some tree `t` of the body is legal and puts every use in scope,
and each region of the instruction or terminator at `y` is scopable with what `t` puts in scope
at `y` visible on entry. -/
inductive Scopable : (ValId → Prop) → List (Block env α) → Prop
  | mk {Λ : ValId → Prop} {bs : List (Block env α)} (t : Tree) :
      ScopedBy bs Λ t →
      (∀ y r, RegionAt bs y r → Scopable (InScope bs t Λ · y) r.blocks.toList) →
      Scopable Λ bs

/-! ## Reachability -/

/-- Control may pass from `u` to `w`: by falling through an instruction, or by a transfer to
the start of a block. -/
inductive Edge : Point → Point → Prop
  | fall {b : Block env α} {k : Nat} :
      b ∈ bs → k < b.instrs.size → Edge ⟨b.label, k⟩ ⟨b.label, k + 1⟩
  | jump {u : Point} {v : Block env α} : Jump bs u v → Edge u ⟨v.label, 0⟩

/-- Some path from the root reaches the point. -/
inductive Reach : Point → Prop
  | root : Reach (root bs)
  | step {u w : Point} : Reach u → Edge bs u w → Reach w

/-- The body's entry reaches every block, and so for each of its regions. -/
inductive Reachable : List (Block env α) → Prop
  | mk {bs : List (Block env α)} : (∀ b ∈ bs, Reach bs ⟨b.label, 0⟩) →
      (∀ y r, RegionAt bs y r → Reachable r.blocks.toList) → Reachable bs

/-! ## What the rule guarantees -/

/-- Some path from the root reaches `y` without passing through `d`. -/
inductive ReachAvoid (d : Point) : Point → Prop
  | root : root bs ≠ d → ReachAvoid d (root bs)
  | step {u w : Point} : ReachAvoid d u → Edge bs u w → w ≠ d → ReachAvoid d w

/-- `d` dominates `y`: every path from the root to `y` passes through `d`.  Every point
dominates an unreachable point. -/
@[expose] def Dom (d y : Point) : Prop := ¬ ReachAvoid bs d y

/-- `x` is available at `y`, the body entered where `Λ` is: defined at a point that dominates
`y`, or available on entry. -/
@[expose] def Avail (Λ : ValId → Prop) (x : ValId) (y : Point) : Prop :=
  (∃ d, DefAt bs x d ∧ Dom bs d y) ∨ Λ x

/-- The body is dominance-correct, entered where `Λ` is available: every use is available, and
every region is dominance-correct, entered where what is available at its owner is. -/
inductive DomCorrect : (ValId → Prop) → List (Block env α) → Prop
  | mk {Λ : ValId → Prop} {bs : List (Block env α)} :
      (∀ x y, UseAt bs x y → Avail bs Λ x y) →
      (∀ y r, RegionAt bs y r → DomCorrect (Avail bs Λ · y) r.blocks.toList) →
      DomCorrect Λ bs

end Body

/-- Some legal tree of each body puts every use of the function in scope, its own body entered
where nothing is visible. -/
@[expose] def Func.Scopable (fn : Func env α) : Prop :=
  Body.Scopable (fun _ => False) fn.blocks.toList

/-- The entry of every body of the function, its own and each region's, reaches every block of
that body. -/
@[expose] def Func.Reachable (fn : Func env α) : Prop := Body.Reachable fn.blocks.toList

/-- The function is dominance-correct: its body is, entered where nothing is available. -/
@[expose] def Func.DomCorrect (fn : Func env α) : Prop :=
  Body.DomCorrect (fun _ => False) fn.blocks.toList

end

end Strata.Mantle
