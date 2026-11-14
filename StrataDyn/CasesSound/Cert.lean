/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.SameSigs
public import StrataDyn.Exec.Frame

set_option autoImplicit false

/-!
# A certificate that a linked module lowers another's cases

Case lowering replaces a terminator that picks one of several successors and passes it a payload
by tests of the successors in order and reads of the payload's values, then a jump that passes
the values as arguments.  It also moves the arguments of an edge that carries no payload onto a
jump in a new block.  Everything else stays: each source block is a target block, with the same
parameters and the same instructions, and the new blocks lie between them.

`CasesOK` relates two linked modules so.  It is a certificate of the linked code, and does not
mention the pass.  Its conditions are of two kinds.

* **Shape.**  A map from each source block to its target block (`BodyOK`), under which an edge
  keeps its arguments and goes to the mapped block (`TargetMap`), or, when it carries no payload,
  goes with no arguments to a block that only jumps there with the arguments (`SiteLow`).  A
  block's instructions are the source's (`InsnOK`), and its terminator is the source's
  (`TermOK`) or a chain that lowers it (`Chain`).
* **Laws** of the instructions the lowering adds, stated of the linked instructions and for every
  store.  `Returns` says that an instruction returns a value at once, and `Exits` that a
  terminator leaves at once along a successor; either holds of a pure wrapper and of a rule whose
  tree is an immediate return or exit.  With them: a new block's terminator jumps (`Jumps`), a
  test followed by its branch takes the first edge exactly when the source's terminator picks the
  tested successor (`Tests`), and the reads of a successor's payload return its values in order
  when the source's terminator picks that successor (`Selects`).  Nothing is asked of a read when
  another successor is picked.

The values the lowering adds are slots at or above `n`, the size of the store the source body
runs in: a function's own slots, and for a region those of the function it belongs to, which
`bound` gives.
-/

namespace Strata.Dyn.CasesSound

open Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-! ## Instructions that return or exit at once -/

/-- The position of the successor an exit picks. -/
def armOf {I : Ty → Type} : {ps : List (List Ty)} → Exit I ps → Nat
  | _, .here _ => 0
  | _, .there e => armOf e + 1

/-- The values an exit passes to the successor it picks. -/
def valsOf {I : Ty → Type} : {ps : List (List Ty)} → Exit I ps → List (Dyn I)
  | _, .here xs => Args.toList xs
  | _, .there e => valsOf e

/-- In the store `env`, the instruction returns the value `d` at once: a pure wrapper's result,
or a rule whose tree on its operands is a return. -/
inductive Returns (env : Array (Dyn M.interp)) : LInsn M → Dyn M.interp → Prop
  | pure {dst : Nat} {ts : List Ty} {r : Ty} {f : Fn M.interp (M.interp r) ts} {args : List Nat}
      (h : Typed env args ts) : Returns env (.pure dst ts r f args) ⟨r, applyFn env ts f args h⟩
  | sem {op : Name} {dst : Nat} {rs : List (List Ty × Ty)} {r : Ty} {ps : List (List Ty)}
      {re : Rerun M rs ps (M.interp r)}
      {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) (M.interp r)) re.ts}
      {regs : List Nat} {succs : List LSite} (h : Typed env re.args re.ts) {x : M.interp r} :
      applyFn env re.ts f re.args h = .ret x →
      Returns env (.sem op dst rs r ps re f regs succs) ⟨r, x⟩

/-- In the store `env`, the terminator leaves at once by the exit `e` along its successors
`succs`: a pure wrapper's exit, or a rule whose tree on its operands is an exit. -/
inductive Exits (env : Array (Dyn M.interp)) :
    LTerm M → (ps : List (List Ty)) → List LSite → Exit M.interp ps → Prop
  | case {ts : List Ty} {ps : List (List Ty)} {f : Fn M.interp (Exit M.interp ps) ts}
      {args : List Nat} {succs : List LSite} (h : Typed env args ts) :
      Exits env (.case ts ps f args succs) ps succs (applyFn env ts f args h)
  | sem {op : Name} {rs : List (List Ty × Ty)} {ps : List (List Ty)} {re : Rerun M rs ps Empty}
      {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) Empty) re.ts}
      {regs : List Nat} {succs : List LSite} (h : Typed env re.args re.ts)
      {e : Exit M.interp ps} : applyFn env re.ts f re.args h = .stop (.jump (.exit e)) →
      Exits env (.sem op rs ps re f regs succs) ps succs e

/-- The terminator jumps along `s`, whatever the store. -/
def Jumps (t : LTerm M) (s : LSite) : Prop :=
  ∀ env : Array (Dyn M.interp), Exits env t [[]] [s] (.here .nil)

/-! ## Edges -/

section
variable (bound : Nat → Nat) (n : Nat) (β : Nat → Nat) (g₁ : LBody M)

/-- The target of an edge of the lowered body: the mapped block, or the body's exit. -/
def TargetMap : LTarget → LTarget → Prop
  | .block i, t₁ => t₁ = .block (β i)
  | .exit, t₁ => t₁ = .exit

/-- The rest of a lowered block that delivers the source edge `s`: instructions that define new
values, each once, and a terminator that jumps where `s` goes, passing the new values, in the
instructions' order, after the arguments of `s`. -/
structure Tail (s : LSite) (code : List (LInsn M)) (term : LTerm M) : Prop where
  distinct : (code.map LInsn.dst).Nodup
  fresh : ∀ i ∈ code, n ≤ i.dst
  jump : ∃ s₂, Jumps term s₂ ∧ s₂.args = s.args ++ code.map LInsn.dst ∧
    TargetMap β s.target s₂.target

/-- The edge `s₁` passes nothing to a block without parameters, whose code satisfies `P`. -/
def Via (s₁ : LSite) (P : List (LInsn M) → LTerm M → Prop) : Prop :=
  ∃ j b, s₁ = ⟨.block j, []⟩ ∧ g₁.blocks[j]? = some b ∧ b.params = [] ∧ P b.insns b.term

/-- The lowered edge `s₁` of the source edge `s`, whose payload has the tags `p`: the same
arguments to the mapped target, or, when there is no payload, a block that only jumps there. -/
def SiteLow (p : List Ty) (s s₁ : LSite) : Prop :=
  (s₁.args = s.args ∧ TargetMap β s.target s₁.target) ∨
    (p = [] ∧ Via g₁ s₁ fun code term => code = [] ∧ Tail n β s code term)

/-- The lowered successors of an operation whose payloads have the tags `ps`. -/
inductive SitesLow : List (List Ty) → List LSite → List LSite → Prop
  | nil : SitesLow [] [] []
  | cons {p : List Ty} {ps : List (List Ty)} {s s₁ : LSite} {ss ss₁ : List LSite} :
      SiteLow n β g₁ p s s₁ → SitesLow ps ss ss₁ → SitesLow (p :: ps) (s :: ss) (s₁ :: ss₁)

/-- A lowered instruction: the source's, a rule's with its successors lowered and its regions
running in a store of the same size. -/
def InsnOK : LInsn M → LInsn M → Prop
  | .sem op dst rs r ps re f regs succs, i₁ =>
    ∃ succs₁, i₁ = .sem op dst rs r ps re f regs succs₁ ∧ SitesLow n β g₁ ps succs succs₁ ∧
      ∀ k ∈ regs, bound k = n
  | i, i₁ => i₁ = i

/-- A terminator that stays: the source's, with its successors lowered. -/
def TermOK : LTerm M → LTerm M → Prop
  | .case ts ps f args succs, t₁ =>
    ∃ succs₁, t₁ = .case ts ps f args succs₁ ∧ SitesLow n β g₁ ps succs succs₁
  | .sem op rs ps re f regs succs, t₁ =>
    ∃ succs₁, t₁ = .sem op rs ps re f regs succs₁ ∧ SitesLow n β g₁ ps succs succs₁ ∧
      ∀ k ∈ regs, bound k = n

/-! ## The chain that lowers a case -/

section
variable {ts : List Ty} {ps : List (List Ty)} (f : Fn M.interp (Exit M.interp ps) ts)
  (args : List Nat) (succs : List LSite)

/-- **The law of the reads**: whenever the case picks successor `k`, the instructions of `code`
return, in order, the values it passes. -/
def Selects (k : Nat) (code : List (LInsn M)) : Prop :=
  ∀ (env : Array (Dyn M.interp)) (h : Typed env args ts), armOf (applyFn env ts f args h) = k →
    All₂ (Returns env) code (valsOf (applyFn env ts f args h))

/-- **The law of a test**: in a store that has a slot for the test's value, whenever the case
picks successor `k` or a later one, `test` returns a value at once, and with it bound `br` leaves
along `st` if the case picks `k`, and along `sf` if it picks a later one. -/
def Tests (k : Nat) (test : LInsn M) (br : LTerm M) (st sf : LSite) : Prop :=
  ∀ (env : Array (Dyn M.interp)) (h : Typed env args ts), test.dst < env.size →
    k ≤ armOf (applyFn env ts f args h) →
    ∃ d, Returns env test d ∧ Exits (env.setIfInBounds test.dst d) br [[], []] [st, sf]
      (if armOf (applyFn env ts f args h) = k then .here .nil else .there (.here .nil))

/-- The edge `s₁` delivers successor `k` of the case: the successor's own edge, when it has no
payload, or a block that reads the payload and jumps. -/
def ArmAt (k : Nat) (s₁ : LSite) : Prop :=
  ∃ s, succs[k]? = some s ∧
    ((ps[k]? = some [] ∧ s₁.args = s.args ∧ TargetMap β s.target s₁.target) ∨
      Via g₁ s₁ fun code term => Tail n β s code term ∧ Selects f args k code)

/-- The rest of a lowered block dispatches the case, given that it picks successor `k` or a later
one: there is no such successor; or `k` is the last, and the code reads its payload and jumps; or
the code tests `k`, and the false edge delivers the last successor or leads to a block that
dispatches from `k + 1`. -/
inductive Chain : Nat → List (LInsn M) → LTerm M → Prop
  | none {k : Nat} {code : List (LInsn M)} {term : LTerm M} : ps.length ≤ k → Chain k code term
  | last {k : Nat} {s : LSite} {code : List (LInsn M)} {term : LTerm M} :
      k + 1 = ps.length → succs[k]? = some s → Tail n β s code term → Selects f args k code →
      Chain k code term
  | test {k : Nat} {test : LInsn M} {br : LTerm M} {st sf : LSite} :
      n ≤ test.dst → Tests f args k test br st sf → ArmAt n β g₁ f args succs k st →
      k + 2 = ps.length → ArmAt n β g₁ f args succs (k + 1) sf → Chain k [test] br
  | next {k : Nat} {test : LInsn M} {br : LTerm M} {st sf : LSite} {j : Nat} {b : LBlock M} :
      n ≤ test.dst → Tests f args k test br st sf → ArmAt n β g₁ f args succs k st →
      sf = ⟨.block j, []⟩ → g₁.blocks[j]? = some b → b.params = [] →
      Chain (k + 1) b.insns b.term → Chain k [test] br

end

/-! ## Blocks, bodies and modules -/

/-- The rest of a target block lowers the rest of a source block: the same instructions, then the
source's terminator or the chain that lowers it. -/
inductive CodeOK : List (LInsn M) → LTerm M → List (LInsn M) → LTerm M → Prop
  | cons {i i₁ : LInsn M} {is is₁ : List (LInsn M)} {t t₁ : LTerm M} :
      InsnOK bound n β g₁ i i₁ → CodeOK is t is₁ t₁ → CodeOK (i :: is) t (i₁ :: is₁) t₁
  | term {t t₁ : LTerm M} : TermOK bound n β g₁ t t₁ → CodeOK [] t [] t₁
  | case {ts : List Ty} {ps : List (List Ty)} {f : Fn M.interp (Exit M.interp ps) ts}
      {args : List Nat} {succs : List LSite} {code₁ : List (LInsn M)} {t₁ : LTerm M} :
      Chain n β g₁ f args succs 0 code₁ t₁ → CodeOK [] (.case ts ps f args succs) code₁ t₁

/-- The target body `g₁` lowers the source body `g`, which runs in a store of `n` slots: the
entry block stays the entry block, and each block of `g` is lowered by its mapped block of `g₁`,
with the same parameters. -/
def BodyOK (g : LBody M) : Prop :=
  β 0 = 0 ∧ ∀ j b, g.blocks[j]? = some b → ∃ b₁, g₁.blocks[β j]? = some b₁ ∧
    b₁.params = b.params ∧ CodeOK bound n β g₁ b.insns b.term b₁.insns b₁.term

end

/-- **The linked module `m₁` lowers the cases of the linked module `m`**, with the regions' store
sizes `bound`: the functions keep their signatures, each function is lowered by the function at
its index, which has at least as many slots, and each region by the region at its index. -/
structure CasesOK (bound : Nat → Nat) (m m₁ : LModule M) : Prop where
  sigs : SameSigs m m₁
  funcs : ∀ (i : Nat) (g : LBody M), m.funcs[i]? = some g → ∃ g₁ β, m₁.funcs[i]? = some g₁ ∧
    g.slots ≤ g₁.slots ∧ BodyOK bound g.slots β g₁ g
  regions : ∀ (k : Nat) (g : LBody M), m.regions[k]? = some g → ∃ g₁ β, m₁.regions[k]? = some g₁ ∧
    BodyOK bound (bound k) β g₁ g

/-- **The linked module `m₁` lowers the cases of the linked module `m`.** -/
def LoweringOK (m m₁ : LModule M) : Prop := ∃ bound, CasesOK bound m m₁

end

end Strata.Dyn.CasesSound
