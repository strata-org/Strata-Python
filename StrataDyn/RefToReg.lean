/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Rewrite
public import Std.Data.HashMap
public import Std.Data.HashSet
public import Std.Data.TreeMap

set_option autoImplicit false

/-!
# Ref-to-reg: promoting cells to values

A cell made by `base.refNew` whose register is used only as the cell operand of `base.refGet`
and `base.refSet`, and whose content is known at each of its reads, is *promoted*: each
`refGet` of it is removed and its uses use the value that holds the cell's content there, and
each `refSet` of it is removed.  Where edges with
different contents meet, the target block takes the content as a new parameter, and each edge
passes it.  The `refNew` stays, with its result unused, so the heap's cells keep their
numbering.

The *content map* says, at a point of a body, which value holds each promoted cell's content.
`Plan.step` advances it over one instruction.  An operation with regions forgets every cell
that one of its regions writes, at any depth, on its successor edges and after it, and its
regions start from the map before it minus those cells: an operation may run its regions in
any order and many times.

A `Plan` says which cells are promoted, which value replaces each removed read (`sigma`), and,
for the blocks where a cell's content changes, the cells carried as new parameters (`carried`),
the cells whose content is one value in scope at the block's start (`fixed`), and where the new
parameters go (`ins`).  `plan` computes one; nothing trusts it.  A block takes every other cell's
content from its tree parent in the dominator tree: the check computes, from the tree, the
function and the promoted cells alone, the cells whose content may change on some path into the
block (`changedSets`),
and a block's start map is its parent's map without those cells, with its plan's `fixed` and
`carried` cells (`Plan.starts`).  `Plan.check` decides whether a plan meets each of `Plan.rules`,
by one walk per block of the content map (`walkBody`), and `Plan.apply` rewrites the function by
it, both with the same start maps.  `refToReg` plans, checks and applies every function, then
checks the module's well-formedness again; a failure names the function and the reason.

**Cost.**  The content map is a persistent map, so a block's start shares its parent's map.  The
check, the rewrite and the planner take time about the function's instructions, edges and
dominance-frontier ranges, times the logarithm of the number of cells, plus the sizes of the
changed sets and of the new parameters' incoming values.  On the translator's goldens each
function takes milliseconds.  Compiled, on a function with 1000 locals updated in a loop (3005
blocks), the planner takes 0.16 s, the start maps 0.06 s and the check 0.04 s; computing the
dominator trees takes 0.24 s.
-/

namespace Strata.Dyn

public section

namespace RefToReg

variable {env : Env Unit} [base ≼ env] {α : Type}

/-! ## The cell operations -/

/-- A base cell operation: `cell := refNew init`, `result := refGet cell`, or
`result := refSet cell value`. -/
inductive CellOp where
  | new (cell init : ValId)
  | get (result cell : ValId)
  | set (result cell value : ValId)
deriving DecidableEq, Repr

/-- Which base cell operation `i` is, if any.  An instruction reference is a name with a proof
that the name resolves, so comparing names compares references.  The base's cell operations
have no successors and no regions; an instruction of that name with either is none of them, and
its operands escape. -/
@[expose] def cellOp? : Instruction env α → Option CellOp
  | .apply _ d r _ args succs regions =>
    if !succs.isEmpty || !regions.isEmpty then none
    else if r.name == (Base.refNew.ref (e := env)).name then
      match args.toList with
      | [v] => some (.new d.id v)
      | _ => none
    else if r.name == (Base.refGet.ref (e := env)).name then
      match args.toList with
      | [c] => some (.get d.id c)
      | _ => none
    else if r.name == (Base.refSet.ref (e := env)).name then
      match args.toList with
      | [c, v] => some (.set d.id c v)
      | _ => none
    else none
  | .const .. => none

/-- Every value `i` uses: its operands and the arguments its edges pass. -/
@[expose] def instrUses (i : Instruction env α) : List ValId :=
  i.args.toList ++ i.succs.toList.flatMap (·.args.toList)

/-- Every value `t` uses: its operands and the arguments its edges pass. -/
@[expose] def termUses (t : Terminator env α) : List ValId :=
  t.args.toList ++ t.succs.toList.flatMap (·.args.toList)

/-- The uses of `i` that let a cell escape: all of them, except the cell operand of a
`refGet` or a `refSet`. -/
@[expose] def escapingUses (i : Instruction env α) : List ValId :=
  match cellOp? i with
  | some (.get _ _) => []
  | some (.set _ _ v) => [v]
  | _ => instrUses i

/-- The cells that the `refSet`s of `bs` write. -/
@[expose] def writesIn (bs : List (Block env α)) : List ValId :=
  bs.flatMap fun b => b.instrs.toList.filterMap fun i =>
    match cellOp? i with
    | some (.set _ c _) => some c
    | _ => none

/-- The cells that the regions of `i` write, at any depth. -/
@[expose] def instrWrites (i : Instruction env α) : List ValId :=
  writesIn i.nestedBlocks

/-- The cells that the regions of `t` write, at any depth. -/
@[expose] def termWrites (t : Terminator env α) : List ValId :=
  writesIn t.nestedBlocks

/-- The cells of `fn` that may be promoted: results of `refNew` used only as the cell
operand of `refGet` and `refSet`, whose `refSet`s' results have no use. -/
@[expose] def candidates (fn : Func env α) : List ValId :=
  let bs := fn.allBlocks
  let instrs := bs.flatMap (·.instrs.toList)
  let esc : Std.HashSet ValId :=
    (instrs.flatMap escapingUses ++ bs.flatMap (termUses ·.term)).foldl (·.insert ·) {}
  let uses : Std.HashSet ValId :=
    (instrs.flatMap instrUses ++ bs.flatMap (termUses ·.term)).foldl (·.insert ·) {}
  -- The cells with a `refSet` whose result is used.
  let usedSets : Std.HashSet ValId := instrs.foldl (init := {}) fun m i =>
    match cellOp? i with
    | some (.set d c _) => if uses.contains d then m.insert c else m
    | _ => m
  instrs.filterMap fun i =>
    match cellOp? i with
    | some (.new c _) => if esc.contains c || usedSets.contains c then none else some c
    | _ => none

/-! ## The content map and the plan -/

/-- Values ordered by their ids. -/
@[expose] def cmpId (a b : ValId) : Ordering := compare a.id b.id

/-- Which value holds each promoted cell's content: cell ↦ value.  A persistent map, so that a
block's start shares its dominator's map. -/
abbrev CMap := Std.TreeMap ValId ValId cmpId

/-- `m` without the entries of the cells `cs`. -/
@[expose] def CMap.drop (m : CMap) (cs : List ValId) : CMap :=
  cs.foldl (·.erase ·) m

/-- The plan of one block. -/
structure BlockPlan (env : Env Unit) where
  /-- The cells whose content arrives as a new parameter, each with that parameter. -/
  carried : List (ValId × ValDecl env) := []
  /-- The cells whose content at the block's start is a value in scope there. -/
  fixed : List (ValId × ValId) := []
  /-- Where the new parameters go among the block's parameters. -/
  ins : Nat := 0

/-- A plan for a function. -/
structure Plan (env : Env Unit) where
  /-- The cells the rewrite changes. -/
  promoted : Std.HashSet ValId := {}
  /-- The value that replaces each removed read. -/
  sigma : Std.HashMap ValId ValId := {}
  /-- Each block's plan, by label. A block not listed takes nothing new. -/
  blocks : Std.HashMap Label (BlockPlan env) := {}
  /-- The name of each new parameter. -/
  names : List (ValId × Name) := []

/-- What the walk reads of a plan: whether a cell is promoted, the value that replaces a
removed read, and the content map at the start of each block that is not a body's entry. -/
structure View where
  promoted : ValId → Bool
  sub : ValId → ValId
  start : Label → CMap

namespace View

variable (V : View)

/-- The content map at the start of the block `l`, which is not a body's entry. -/
@[expose] def entryMap (l : Label) : CMap := V.start l

/-- The content map after `i`, from `m` before it. -/
@[expose] def step (m : CMap) (i : Instruction env α) : CMap :=
  let m := m.drop (instrWrites i)
  match cellOp? i with
  | some (.new c v) | some (.set _ c v) =>
    if V.promoted c then m.insert c (V.sub v) else m
  | _ => m

end View

namespace Plan

variable (P : Plan env)

/-- The plan of the block `l`. -/
@[expose] def block (l : Label) : BlockPlan env := P.blocks.getD l {}

/-- `v`, or the value that replaces it if it is a removed read. -/
@[expose] def sub (v : ValId) : ValId := P.sigma.getD v v

/-- The plan as the walk reads it, with the start maps `S` (`Plan.starts`). -/
@[expose] def view (S : Std.HashMap Label CMap) : View :=
  ⟨P.promoted.contains, P.sub, (S.getD · {})⟩

/-- The content map after `i`, from `m` before it. -/
@[expose] def step (m : CMap) (i : Instruction env α) : CMap :=
  (P.view {}).step m i

end Plan

/-! ## The walk -/

/-- What the walk of a body sees: a body's entry block, an edge with the content map where it
leaves, and a `refGet` with the content its cell has there, if the map knows it. -/
inductive Event where
  | entry (l : Label)
  | edge (m : CMap) (k : Target.Raw)
  | read (r c : ValId) (content : Option ValId)

mutual

/-- The events of `is`, from the content map `m` before them, and the map after them. -/
@[expose] def walkInstrs (V : View) : CMap → List (Instruction env α) → List Event × CMap
  | m, [] => ([], m)
  | m, i :: is =>
    let m₀ := m.drop (instrWrites i)
    let here := i.succs.toList.map (Event.edge m₀) ++
      (match cellOp? i with
       | some (.get r c) => [Event.read r c (m.get? c)]
       | _ => []) ++
      walkInstrRegions V m₀ i
    let rest := walkInstrs V (V.step m i) is
    (here ++ rest.1, rest.2)

/-- The events of `i`'s regions, each entered with `m`. -/
@[expose] def walkInstrRegions (V : View) (m : CMap) : Instruction env α → List Event
  | .const .. => []
  | .apply _ _ _ _ _ _ ⟨regions⟩ => walkRegions V m regions

/-- The events of `t`'s regions, each entered with `m`. -/
@[expose] def walkTermRegions (V : View) (m : CMap) : Terminator env α → List Event
  | .apply _ _ _ _ _ ⟨regions⟩ => walkRegions V m regions

/-- The events of regions, each entered with `m`. -/
@[expose] def walkRegions (V : View) (m : CMap) : List (Region env α) → List Event
  | [] => []
  | ⟨⟨blocks⟩⟩ :: rs => walkBody V (some m) blocks ++ walkRegions V m rs

/-- The events of a body's blocks.  The first is entered with `entry` if given; the others
with the map their plan gives. -/
@[expose] def walkBody (V : View) : Option CMap → List (Block env α) → List Event
  | _, [] => []
  | entry, ⟨l, _, ⟨instrs⟩, t, _⟩ :: bs =>
    let start := match entry with
      | some m => (m, [Event.entry l])
      | none => (V.entryMap l, [])
    let body := walkInstrs V start.1 instrs
    let mt := body.2.drop (termWrites t)
    start.2 ++ body.1 ++ t.succs.toList.map (Event.edge mt) ++ walkTermRegions V mt t ++
      walkBody V none bs

end

/-- The events of a function, with the start maps `S` (`Plan.starts`). -/
@[expose] def walk (P : Plan env) (S : Std.HashMap Label CMap) (fn : Func env α) : List Event :=
  walkBody (P.view S) (some {}) fn.blocks.toList

/-! ## Where contents can change

The check computes, from each body's dominator tree, the function and the promoted cells alone,
the cells whose content may change on some path from a block's tree parent to an edge into the
block.  A block's
start map is its tree parent's map without those cells, with the plan's new parameters and fixed
contents. -/

open Std (HashMap)

/-- The bodies of `fn`: its top-level blocks, and each region's blocks, at any depth. -/
@[expose] def bodies (fn : Func env α) : List (List (Block env α)) :=
  fn.blocks.toList :: fn.allBlocks.flatMap fun b =>
    (b.instrs.toList.flatMap (·.regions.toList) ++ b.term.regions.toList).map (·.blocks.toList)

/-- The edges of the blocks `bs`, each from the point it leaves: instruction `j`'s from
`⟨X, j⟩`, the terminator's from `⟨X, n⟩`.  Edges to the exit are left out. -/
@[expose] def pointEdges (bs : List (Block env α)) : List (Point × Label) :=
  bs.flatMap fun b =>
    let n := b.instrs.size
    let fromInstrs := b.instrs.toList.zipIdx.flatMap fun ((i : Instruction env α), j) =>
      i.succs.toList.map fun k => ((⟨b.label, j⟩ : Point), k.label)
    let fromTerm := b.term.succs.toList.map fun k => ((⟨b.label, n⟩ : Point), k.label)
    (fromInstrs ++ fromTerm).filter (·.2 != Label.exit)

/-- A range of a block on the way from an edge into `target` up to `target`'s parent: the
instructions `lo ≤ i ≤ hi`, and the block's start if `whole`. -/
structure Range where
  target : Label
  lo : Nat
  hi : Nat
  whole : Bool

/-- The ranges recorded for one target, by block, with the walk from the point `p` up the tree
`t` to the target's parent `⟨P, k⟩` added, at most `fuel` steps.  The walk stops at the parent's
block, or at a block already recorded, whose upper bound it raises.  `none` if it runs out of
fuel, reaches the root without meeting the parent, or meets the parent's block above the
parent: the tree is then not the dominator tree. -/
@[expose] def climb (t : Body.Tree) (P : Label) (k : Nat) :
    Nat → Point → HashMap Label (Nat × Nat × Bool) → Option (HashMap Label (Nat × Nat × Bool))
  | 0, _, _ => none
  | fuel + 1, p, seen =>
    if p.label == P && p.count < k then none else
    match seen.get? p.label with
    | some (lo, hi, whole) => some (seen.insert p.label (lo, max hi p.count, whole))
    | none =>
      if p.label == P then some (seen.insert P (k, p.count, false))
      else
        let seen := seen.insert p.label (0, p.count, true)
        match t p.label with
        | some q => climb t P k fuel q seen
        | none => none

/-- For each block of the body `bs` with the tree `t`, the ranges in it of every block that is
not the body's entry: Cytron et al.'s dominance frontiers, with points.  A block's ranges for a
target hold the instructions below the target's parent whose change of a cell's content can
reach an edge into the target.  `none` if a walk up the tree fails. -/
@[expose] def frontier (t : Body.Tree) (bs : List (Block env α)) :
    Option (HashMap Label (List Range)) :=
  let into : HashMap Label (List Point) := (pointEdges bs).foldl (init := {}) fun m (p, l) =>
    m.insert l (p :: m.getD l [])
  let fuel := bs.length + 1
  bs.foldlM (init := {}) fun inv y =>
    match t y.label with
    | none => some inv
    | some ⟨P, k⟩ => do
      let seen ← (into.getD y.label []).foldlM (init := {}) fun seen p =>
        climb t P k fuel p seen
      return seen.fold (init := inv) fun inv x (lo, hi, whole) =>
        inv.insert x (⟨y.label, lo, hi, whole⟩ :: inv.getD x [])

/-- Where each candidate's content changes: at instruction `i` of block `X`, a `refNew` or
`refSet` of it, or an instruction whose regions write it; at `n`, a terminator whose regions
write it. -/
@[expose] def changes (isCand : ValId → Bool) (fn : Func env α) :
    HashMap ValId (List (Label × Nat)) :=
  let add (m : HashMap ValId (List (Label × Nat))) (c : ValId) (at_ : Label × Nat) :=
    if isCand c then m.insert c (at_ :: m.getD c []) else m
  fn.allBlocks.foldl (init := {}) fun m b =>
    let m := b.instrs.toList.zipIdx.foldl (init := m) fun m (i, j) =>
      let m := match cellOp? i with
        | some (.new c _) | some (.set _ c _) => add m c (b.label, j)
        | _ => m
      (instrWrites i).foldl (init := m) fun m c => add m c (b.label, j)
    (termWrites b.term).foldl (init := m) fun m c => add m c (b.label, b.instrs.size)

/-- The tree parent of every block that is not a body's entry, in all of `fn`'s bodies, from
each body's dominator tree (`Body.domTree?`), or an error if a body has none. -/
@[expose] def trees (fn : Func env α) : Except String (HashMap Label Point) :=
  (bodies fn).foldlM (init := {}) fun m body =>
    match Body.domTree? body with
    | some t => pure <| body.foldl (init := m) fun m b =>
        match t b.label with
        | some p => m.insert b.label p
        | none => m
    | none => throw "a body has no dominator tree"

/-- The ranges of every body's frontier, by block, from the tree parents `parents`. -/
@[expose] def allRanges (parents : HashMap Label Point) (fn : Func env α) :
    Except String (HashMap Label (List Range)) :=
  (bodies fn).foldlM (init := {}) fun inv body =>
    match frontier (parents.get? ·) body with
    | some f => pure (f.fold (init := inv) fun inv x rs => inv.insert x (rs ++ inv.getD x []))
    | none => throw "a walk up a dominator tree went wrong"

/-- `ch` with the cell `c` in the set of `l`. -/
@[expose] def addChanged (ch : HashMap Label (Std.HashSet ValId)) (l : Label) (c : ValId) :
    HashMap Label (Std.HashSet ValId) :=
  ch.alter l fun s => some ((s.getD {}).insert c)

/-- The changed sets `ch`, closed from the pairs `work` (each block with a cell new in its set):
a cell in the set of a block `X` joins the set of each target of `X`'s ranges that cover `X`'s
start, at most `fuel` steps; `none` if they run out. -/
@[expose] def spread (inv : HashMap Label (List Range)) :
    Nat → List (Label × ValId) → HashMap Label (Std.HashSet ValId) →
      Option (HashMap Label (Std.HashSet ValId))
  | _, [], ch => some ch
  | 0, _ :: _, _ => none
  | fuel + 1, (x, c) :: work, ch =>
    let (ch, more) := (inv.getD x []).foldl (init := (ch, work)) fun (ch, more) r =>
      if r.whole && !(ch.getD r.target {}).contains c then
        (addChanged ch r.target c, (r.target, c) :: more)
      else (ch, more)
    spread inv fuel more ch

/-- The cells of `isCand` whose content may change, on some path, between each block's tree
parent and an edge into the block: a change in one of the block's ranges, or a cell in the set
of a block whose start one of its ranges covers.  The least fixpoint, by `spread`.  The result
is then checked to be closed, in one pass, so that the worklist is not trusted; an error if it
isn't, or if the worklist runs out of fuel. -/
@[expose] def changedSets (isCand : ValId → Bool) (inv : HashMap Label (List Range))
    (fn : Func env α) : Except String (HashMap Label (Std.HashSet ValId)) := do
  -- Each block's changes, as (cell, instruction index).
  let at_ : HashMap Label (List (ValId × Nat)) :=
    (changes isCand fn).fold (init := {}) fun m c pts =>
      pts.foldl (init := m) fun m (x, i) => m.insert x ((c, i) :: m.getD x [])
  let direct (x : Label) (r : Range) : List ValId :=
    (at_.getD x []).filterMap fun (c, i) => if r.lo ≤ i && i ≤ r.hi then some c else none
  let start : HashMap Label (Std.HashSet ValId) × List (Label × ValId) := ({}, [])
  let (ch, work) := inv.fold (init := start) fun (ch, work) x rs =>
      rs.foldl (init := (ch, work)) fun (ch, work) r =>
        (direct x r).foldl (init := (ch, work)) fun (ch, work) c =>
          if (ch.getD r.target {}).contains c then (ch, work)
          else (addChanged ch r.target c, (r.target, c) :: work)
  let ranges := inv.fold (init := 0) fun n _ rs => n + rs.length
  let some ch := spread inv (work.length + (ranges + 1) * (ch.size + 1) *
      (fn.allBlocks.length * ((changes isCand fn).size + 1) + 1)) work ch
    | throw "the changed cells did not settle"
  let closed := inv.toList.all fun (x, rs) => rs.all fun r =>
    let into := ch.getD r.target {}
    (direct x r).all into.contains && (!r.whole || (ch.getD x {}).toList.all into.contains)
  if closed then return ch else throw "the changed cells are not closed"

/-- What the check computes from a function and a plan: each block's changed cells, and the
content map at the start of each block that is not a body's entry. -/
structure Starts where
  changed : HashMap Label (Std.HashSet ValId) := {}
  maps : HashMap Label CMap := {}

/-- The maps recorded at the points that are some block's tree parent, and the start maps. -/
structure Recorded where
  atPoint : HashMap (Label × Nat) CMap := {}
  starts : HashMap Label CMap := {}

/-- `g` with the map `m` at the point `⟨l, k⟩`, if `needed` asks for it.  It takes `g` apart
first, so that the table is changed in place. -/
@[expose] def Recorded.record (g : Recorded) (needed : Std.HashSet (Label × Nat)) (l : Label)
    (k : Nat) (m : CMap) : Recorded :=
  if needed.contains (l, k) then match g with | ⟨a, st⟩ => ⟨a.insert (l, k) m, st⟩ else g

/-- `g` with `m` as the start map of `l`. -/
@[expose] def Recorded.setStart (g : Recorded) (l : Label) (m : CMap) : Recorded :=
  match g with | ⟨a, st⟩ => ⟨a, st.insert l m⟩

mutual

/-- The start maps of the blocks of the regions of `is` and below, from the content map `m`
before them, recording the map before instruction `k` of block `l` (and before the terminator, at
`n`) where `needed` asks; and the map after them.  `fuel` bounds the instructions and bodies along
a path of nesting. -/
@[expose] def startsInstrs (V : View) (plan : Label → BlockPlan env)
    (changed : HashMap Label (Std.HashSet ValId)) (parents : HashMap Label Point)
    (needed : Std.HashSet (Label × Nat)) (l : Label) :
    Nat → Nat → CMap → List (Instruction env α) → Recorded → Option (CMap × Recorded)
  | _, k, m, [], g => some (m, g.record needed l k m)
  | 0, _, _, _ :: _, _ => none
  | fuel + 1, k, m, i :: is, g => do
    let g := g.record needed l k m
    let m₀ := m.drop (instrWrites i)
    let g ← i.regions.toList.foldlM (init := g) fun g r =>
      startsBody V plan changed parents needed fuel m₀ r.blocks.toList g
    startsInstrs V plan changed parents needed l fuel (k + 1) (V.step m i) is g

/-- The start maps of a body's blocks and of what is nested in them, the body entered with
`entry`, in reverse postorder (`Body.rpoLabels`), where each block's tree parent comes before it.
A block other than the entry starts from its tree parent's map without its changed cells, with
its plan's fixed contents and new parameters.  `none` if a parent's map is missing. -/
@[expose] def startsBody (V : View) (plan : Label → BlockPlan env)
    (changed : HashMap Label (Std.HashSet ValId)) (parents : HashMap Label Point)
    (needed : Std.HashSet (Label × Nat)) :
    Nat → CMap → List (Block env α) → Recorded → Option Recorded
  | 0, _, _, _ => none
  | fuel + 1, entry, bs, g => do
    let byLabel : HashMap Label (Block env α) := bs.foldl (init := {}) fun m b => m.insert b.label b
    let first := bs.head?.map (·.label)
    (Body.rpoLabels bs).foldlM (init := g) fun g l => do
      let b ← byLabel.get? l
      let (m, g) ← if some l == first then pure (entry, g) else do
        let p ← parents.get? l
        let base ← g.atPoint.get? (p.label, p.count)
        let m := (changed.getD l {}).fold (·.erase ·) base
        let bp := plan l
        let m := bp.fixed.foldl (init := m) fun m (c, u) => m.insert c u
        let m := bp.carried.foldl (init := m) fun m (c, d) => m.insert c d.id
        pure (m, g.setStart l m)
      let (m, g) ← startsInstrs V plan changed parents needed l fuel 0 m b.instrs.toList g
      let mt := m.drop (termWrites b.term)
      b.term.regions.toList.foldlM (init := g) fun g r =>
        startsBody V plan changed parents needed fuel mt r.blocks.toList g

end

namespace Plan

/-- The start maps of `P` for `fn`, given the tree parents and the changed sets (`changedSets`). -/
@[expose] def startsWith (P : Plan env) (parents : HashMap Label Point)
    (changed : HashMap Label (Std.HashSet ValId)) (fn : Func env α) : Except String Starts := do
  let needed : Std.HashSet (Label × Nat) :=
    parents.fold (init := {}) fun s _ p => s.insert (p.label, p.count)
  let fuel := fn.allBlocks.foldl (init := fn.allBlocks.length + 1) fun n b => n + b.instrs.size
  match startsBody (P.view {}) P.block changed parents needed fuel {} fn.blocks.toList {} with
  | some g => return { changed, maps := g.starts }
  | none => throw "a block's tree parent has no content map"

/-- What the check computes for `P` and `fn`, with the tree parents `parents` (`trees`): the
changed sets of `P`'s promoted cells, and the start maps. -/
@[expose] def starts (P : Plan env) (parents : HashMap Label Point) (fn : Func env α) :
    Except String Starts := do
  let inv ← allRanges parents fn
  let changed ← changedSets P.promoted.contains inv fn
  P.startsWith parents changed fn

end Plan

/-! ## The check -/

/-- The parameters of every block of `fn`, regions included, by label. -/
@[expose] def blockParams (fn : Func env α) : Std.HashMap Label (Array (ValDecl env)) :=
  fn.allBlocks.foldl (init := {}) fun m b => m.insert b.label b.params

/-- Whether the values `vs` are distinct. -/
@[expose] def distinct (vs : List ValId) : Bool :=
  (vs.foldl (·.insert ·) ({} : Std.HashSet ValId)).size == vs.length

namespace Plan

variable (P : Plan env)

/-- The edge `k`, leaving where the content map is `m`, passes what its target's plan
expects. -/
@[expose] def edgeOk (m : CMap) (k : Target.Raw) : Bool :=
  let bp := P.block k.label
  decide (bp.ins ≤ k.args.size) && bp.carried.all (fun (c, _) => m.contains c) &&
    bp.fixed.all fun (c, u) => m.get? c == some u

/-- The plan of the block `l`, whose parameters are `ps`, is consistent. -/
@[expose] def blockOk (ps : Array (ValDecl env)) (bp : BlockPlan env) : Bool :=
  let cells := bp.carried.map (·.1) ++ bp.fixed.map (·.1)
  let params : Std.HashSet ValId :=
    bp.carried.foldl (fun s (_, d) => s.insert d.id) (ps.foldl (·.insert ·.id) {})
  cells.all P.promoted.contains && distinct cells && decide (bp.ins ≤ ps.size) &&
    bp.fixed.all fun (_, u) => !params.contains u

/-- The removed reads: the `refGet`s of promoted cells. -/
@[expose] def removed (evs : List Event) : Std.HashSet ValId :=
  evs.foldl (init := {}) fun s e =>
    match e with
    | .read r c _ => if P.promoted.contains c then s.insert r else s
    | _ => s

/-- The rules a plan for `fn` must meet, with the start maps and changed sets `S`
(`Plan.starts`), each with its name. -/
@[expose] def rules (S : Starts) (fn : Func env α) : List (String × Bool) :=
  let cands : Std.HashSet ValId := (candidates fn).foldl (·.insert ·) {}
  let params := blockParams fn
  let bound := ValDecl.idBound fn.defs
  let evs := walk P S.maps fn
  let gone := P.removed evs
  let news := P.blocks.toList.flatMap fun (_, bp) => bp.carried.map (·.2.id)
  [("the promoted cells are candidates", P.promoted.toList.all cands.contains),
   ("each block's plan is consistent", P.blocks.toList.all fun (l, bp) =>
      match params.get? l with
      | some ps => P.blockOk ps bp
      | none => false),
   ("the new parameters are fresh",
      distinct news && news.all (bound ≤ ·.id)),
   ("each replaced value is a removed read, replaced by a value that is not a removed read",
      P.sigma.toList.all fun (r, u) => gone.contains r && !gone.contains u),
   ("a body's entry takes nothing new", evs.all fun
      | .entry l => (P.block l).carried.isEmpty && (P.block l).fixed.isEmpty
      | _ => true),
   ("each edge passes what its target expects", evs.all fun
      | .edge m k => P.edgeOk m k
      | _ => true),
   ("each removed read is replaced by its cell's content", evs.all fun
      | .read r c v => !P.promoted.contains c || (v.isSome && P.sigma.get? r == v)
      | _ => true),
   ("each block's new cells change there", P.blocks.toList.all fun (l, bp) =>
      let ch := S.changed.getD l {}
      bp.carried.all (ch.contains ·.1) && bp.fixed.all (ch.contains ·.1))]

/-- Whether the plan meets every rule for `fn`. -/
@[expose] def check (S : Starts) (fn : Func env α) : Bool := (P.rules S fn).all (·.2)

end Plan

/-! ## The rewrite -/

/-- `a` with `xs` inserted at `i`. -/
@[expose] def insertAt {β : Type} (a : Array β) (i : Nat) (xs : List β) : Array β :=
  ⟨a.toList.take i ++ xs ++ a.toList.drop i⟩

namespace Plan

/-- The edge `k`, leaving where the content map is `m`, with the contents its target carries
inserted. -/
@[expose] def edge (P : Plan env) (m : CMap) (k : Target.Raw) : Target.Raw :=
  let bp := P.block k.label
  { k with args := insertAt k.args bp.ins (bp.carried.map fun (c, _) => m.getD c c) }

/-- Whether `i` is a read or a write of a promoted cell, which the rewrite removes. -/
@[expose] def drops (P : Plan env) (i : Instruction env α) : Bool :=
  match cellOp? i with
  | some (.get _ c) | some (.set _ c _) => P.promoted.contains c
  | _ => false

end Plan

mutual

/-- `is` rewritten, from the content map `m` before them. -/
@[expose] def applyInstrs (P : Plan env) (S : Std.HashMap Label CMap) :
    CMap → List (Instruction env α) → List (Instruction env α)
  | _, [] => []
  | m, i :: is =>
    let rest := applyInstrs P S (P.step m i) is
    if P.drops i then rest else applyInstr P S (m.drop (instrWrites i)) i :: rest

/-- `i` rewritten, its edges and regions leaving or entered where the content map is `m`. -/
@[expose] def applyInstr (P : Plan env) (S : Std.HashMap Label CMap) (m : CMap) :
    Instruction env α → Instruction env α
  | .const info d c => .const info d c
  | .apply info d r typeArgs args succs ⟨regions⟩ =>
    .apply info d r typeArgs args (succs.map (P.edge m)) ⟨applyRegions P S m regions⟩

/-- `t` rewritten, its edges and regions leaving or entered where the content map is `m`. -/
@[expose] def applyTerm (P : Plan env) (S : Std.HashMap Label CMap) (m : CMap) :
    Terminator env α → Terminator env α
  | .apply info r typeArgs args succs ⟨regions⟩ =>
    .apply info r typeArgs args (succs.map (P.edge m)) ⟨applyRegions P S m regions⟩

/-- Regions rewritten, each entered with `m`. -/
@[expose] def applyRegions (P : Plan env) (S : Std.HashMap Label CMap) (m : CMap) :
    List (Region env α) → List (Region env α)
  | [] => []
  | ⟨⟨blocks⟩⟩ :: rs => ⟨⟨applyBody P S (some m) blocks⟩⟩ :: applyRegions P S m rs

/-- A body's blocks rewritten: each takes its new parameters, the first entered with `entry`
if given. -/
@[expose] def applyBody (P : Plan env) (S : Std.HashMap Label CMap) :
    Option CMap → List (Block env α) → List (Block env α)
  | _, [] => []
  | entry, ⟨l, ps, ⟨instrs⟩, t, info⟩ :: bs =>
    let m₀ := entry.getD ((P.view S).entryMap l)
    let bp := P.block l
    let mt := (instrs.foldl P.step m₀).drop (termWrites t)
    ⟨l, insertAt ps bp.ins (bp.carried.map (·.2)), ⟨applyInstrs P S m₀ instrs⟩, applyTerm P S mt t,
      info⟩ :: applyBody P S none bs

end

namespace Plan

/-- `fn`'s names, with a name for each new parameter.  Names the plan gives other values are
left out. -/
@[expose] def newNames (P : Plan env) (fn : Func env α) : Array Name :=
  let news : Std.HashSet ValId := P.blocks.fold (init := {}) fun s _ bp =>
    bp.carried.foldl (fun s (_, d) => s.insert d.id) s
  let names := P.names.filter fun (v, _) => news.contains v
  let size := names.foldl (fun n (v, _) => max n (v.id + 1)) fn.names.size
  let base := fn.names ++ Array.replicate (size - fn.names.size) Name.base
  names.foldl (fun a (v, n) => a.setIfInBounds v.id n) base

/-- `fn` rewritten by the plan, with the start maps `S` (`Plan.starts`). -/
@[expose] def apply (P : Plan env) (S : Std.HashMap Label CMap) (fn : Func env α) : Func env α :=
  Func.mapUses P.sub
    { fn with blocks := ⟨applyBody P S (some {}) fn.blocks.toList⟩, names := P.newNames fn }

end Plan

/-! ## The planner

Nothing trusts it: `Plan.check` decides whether its plan is consistent.  It uses the check's
own changed sets: a block that is not a body's entry takes a parameter for every candidate whose
content may change on a path into it (the iterated dominance frontier, Cytron et al.).  It walks
with the check's start maps, and keeps only the parameters that a read's content leads to,
directly or through other kept parameters.  A kept parameter whose edges all pass one value
becomes an alias of it, as Braun et al.'s removal of trivial φ-functions does, and a fixed
content of its block; the others are the new parameters, numbered and named.  A candidate whose
content is unknown where it matters (at a read, or at a kept parameter) is dropped, and planning
starts again without it.  Its fixpoints are worklists over hash maps; nothing proves anything
about them. -/

open Std (HashMap)

/-- The labels of the entry blocks of the regions `rs`. -/
@[expose] def regionEntries (rs : Array (Region env α)) : List Label :=
  rs.toList.filterMap (·.blocks[0]?.map (·.label))

/-- The block labels of every body's entry: the function's and each region's. -/
@[expose] def entryLabels (fn : Func env α) : List Label :=
  (fn.blocks[0]?.map (·.label)).toList ++ fn.allBlocks.flatMap fun b =>
    b.instrs.toList.flatMap (regionEntries ·.regions) ++ regionEntries b.term.regions

/-- Every edge of the blocks `bs`, instructions' then terminator's, block by block. -/
@[expose] def edgesOf (bs : List (Block env α)) : List Target.Raw :=
  bs.flatMap fun b => b.instrs.toList.flatMap (·.succs.toList) ++ b.term.succs.toList

/-- Every edge of `fn`, regions included. -/
@[expose] def allEdges (fn : Func env α) : List Target.Raw := edgesOf fn.allBlocks

/-- The content type of each cell that `fn` reads: the type of its `refGet`'s result.  The
planner keeps a parameter only if a read uses it, so the parameter's cell has one. -/
@[expose] def contentTypes (fn : Func env α) : HashMap ValId (TypeExpr env) :=
  fn.allBlocks.foldl (init := {}) fun m b => b.instrs.foldl (init := m) fun m i =>
    match cellOp? i with
    | some (.get _ c) => m.insert c i.result.type
    | _ => m

/-- `v`, followed through `alias` at most `fuel` times. -/
@[expose] def chase (alias : HashMap ValId ValId) : Nat → ValId → ValId
  | 0, v => v
  | fuel + 1, v =>
    match alias.get? v with
    | some u => chase alias fuel u
    | none => v

/-- `v` followed through `alias` at most `fuel` times, and `alias` with each value on the way
pointing to where it ends, so that a later chase takes one step. -/
@[expose] def chaseShort (alias : HashMap ValId ValId) : Nat → ValId → ValId × HashMap ValId ValId
  | 0, v => (v, alias)
  | fuel + 1, v =>
    match alias.get? v with
    | none => (v, alias)
    | some u =>
      let (r, alias) := chaseShort alias fuel u
      (r, if r == u then alias else alias.insert v r)

/-- The one value other than `p` that the values `vs` lead to through `alias`, if there is
exactly one; and `alias` shortened by `chaseShort`.  It stops at the second such value.  `u` is
the value found so far. -/
@[expose] def soleBut (alias : HashMap ValId ValId) (depth : Nat) (p : ValId) :
    Option ValId → List ValId → Option ValId × HashMap ValId ValId
  | u, [] => (u, alias)
  | u, v :: vs =>
    let (v, alias) := chaseShort alias depth v
    if v == p then soleBut alias depth p u vs else
    match u with
    | none => soleBut alias depth p (some v) vs
    | some w => if v == w then soleBut alias depth p u vs else (none, alias)

/-- Make new parameters aliases of the one value their edges pass, followed through the
aliases so far, leaving out the parameter itself (a loop's back edge passes it back); the value
must not be a parameter of the block, old or new.  `news` gives, per new parameter, its block,
the block's new parameter ids, and the values its edges pass.  `users` gives, per value that is
no alias, the new parameters with an edge that passes it or a value whose aliases lead to it.  A
worklist of parameters: when `p` becomes an alias of `u`, the parameters in `users p` are looked
at again, and move to `users u`.  An alias stays an alias, and each new alias puts each
parameter back at most once, so it stops within `(parameters + 1) ^ 2` steps; `fuel` bounds
it. -/
@[expose] def aliasIter (news : HashMap ValId (Label × Std.HashSet ValId × List ValId))
    (params : HashMap Label (Array (ValDecl env))) (depth : Nat) :
    Nat → List ValId → HashMap ValId ValId → HashMap ValId (Std.HashSet ValId) →
      Option (HashMap ValId ValId)
  | _, [], alias, _ => some alias
  | 0, _ :: _, _, _ => none
  | fuel + 1, p :: work, alias, users =>
    match news.get? p with
    | none => aliasIter news params depth fuel work alias users
    | some (l, own, ins) =>
      if alias.contains p then aliasIter news params depth fuel work alias users else
      match soleBut alias depth p none ins with
      | (some u, alias) =>
        if (params.getD l #[]).any (·.id == u) || own.contains u then
          aliasIter news params depth fuel work alias users
        else
          let again := users.getD p {}
          let toU := users.getD u {}
          -- Each table is updated after its last read, so that it is changed in place.
          let users := (users.erase p).erase u
          aliasIter news params depth fuel (again.toList ++ work) (alias.insert p u)
            (users.insert u (again.fold (·.insert ·) toU))
      | (none, alias) => aliasIter news params depth fuel work alias users

/-- The stem and the suffix of a name: `x.3` is `(x, 3)`. -/
@[expose] def splitNum : Name → Name × Option Nat
  | .num n i => (n, some i)
  | n => (n, none)

/-- `P` with its new parameters given ids after every id of `fn`, in the order of the blocks
`order` and of each block's carried cells, each named after its cell's `refNew` operand with a
fresh suffix. -/
@[expose] def Plan.finish (fn : Func env α) (order : List Label) (P : Plan env) : Plan env :=
  let next := max (ValDecl.idBound fn.defs) fn.names.size
  let inits : HashMap ValId ValId := fn.allBlocks.foldl (init := {}) fun m b =>
    b.instrs.foldl (init := m) fun m i =>
      match cellOp? i with
      | some (.new c v) => m.insert c v
      | _ => m
  let stemOf (c : ValId) : Name :=
    match inits.get? c with
    | some v => (splitNum (fn.names[v.id]?.getD .base)).1
    | none => .base
  let olds := order.flatMap fun l => (P.block l).carried.map fun (c, d) => (c, d.id)
  let renum : HashMap ValId ValId := olds.zipIdx.foldl (init := {}) fun m ((_, v), k) =>
    m.insert v ⟨next + k⟩
  let ren (v : ValId) : ValId := renum.getD v v
  let suffixes : HashMap Name Nat := fn.names.foldl (init := {}) fun m nm =>
    match splitNum nm with
    | (s, some i) => m.insert s (max (m.getD s 0) (i + 1))
    | _ => m
  let (names, _) := olds.foldl (init := (([] : List (ValId × Name)), suffixes))
    fun (acc, sfx) (c, v) =>
      let stem := stemOf c
      let k := sfx.getD stem 0
      ((ren v, Name.num stem k) :: acc, sfx.insert stem (k + 1))
  let blocks := P.blocks.map fun _ bp =>
    { bp with
      carried := bp.carried.map fun (c, d) => (c, { d with id := ren d.id })
      fixed := bp.fixed.map fun (c, u) => (c, ren u) }
  { P with blocks, sigma := P.sigma.map fun _ u => ren u, names := names.reverse }

/-- The values used through `v`: `v` itself; if it is a new parameter (`insOf` gives its edges'
values, or `none` if one of them doesn't know its cell), each value its edges pass; if it is a
removed read, its content (`reads`).  The used parameters are found with their values, and the
unknown ones with their cells.  A worklist, at most `fuel` steps; `none` if they run out. -/
@[expose] def markUsed (insOf : ValId → Option (Option (List ValId)))
    (reads : HashMap ValId ValId) :
    Nat → List ValId → Std.HashSet ValId × HashMap ValId (List ValId) × List ValId →
      Option (Std.HashSet ValId × HashMap ValId (List ValId) × List ValId)
  | _, [], acc => some acc
  | 0, _ :: _, _ => none
  | fuel + 1, v :: work, (used, known, unknown) =>
    if used.contains v then markUsed insOf reads fuel work (used, known, unknown) else
    let used := used.insert v
    match insOf v with
    | some (some vs) => markUsed insOf reads fuel (vs ++ work) (used, known.insert v vs, unknown)
    | some none => markUsed insOf reads fuel work (used, known, v :: unknown)
    | none => markUsed insOf reads fuel ((reads.get? v).toList ++ work) (used, known, unknown)

/-- A plan for `fn` with the candidates `cands`, and the candidates it finds unknown where it
matters; or an error if a fixpoint ran out of fuel.  `parents` and `changed` are the check's tree
parents and changed sets.  Every block that is not a body's entry first takes a parameter for
each changed candidate with a content type.  A walk with the check's start maps gives each
parameter's incoming values and each read's content.  A parameter is used if a read's content
leads to it, or a used parameter's incoming value does; only the used ones are looked at
further.  A used parameter with an edge that doesn't know its cell is unknown; one whose edges
all pass one value becomes an alias of it, as Braun et al.'s removal of trivial φ-functions
does.  A candidate with a used unknown parameter, or a read whose content is unknown, is
dropped.  The used parameters that are no aliases are the new ones; the used aliases are the
blocks' fixed contents; every value of the plan is followed through the aliases. -/
@[expose] def planWith (fn : Func env α) (parents : HashMap Label Point)
    (changed : HashMap Label (Std.HashSet ValId)) (cands : List ValId) :
    Except String (Plan env × List ValId) := do
  let candSet : Std.HashSet ValId := cands.foldl (·.insert ·) {}
  let bs := fn.allBlocks
  let fewest : HashMap Label Nat := (allEdges fn).foldl (init := {}) fun m k =>
    m.insert k.label (min (m.getD k.label k.args.size) k.args.size)
  let types := contentTypes fn
  let entrySet : Std.HashSet Label := (entryLabels fn).foldl (·.insert ·) {}
  let base := max (ValDecl.idBound fn.defs) fn.names.size
  -- A parameter for each changed candidate, with a fresh id, in block order and, in a block,
  -- in cell order.
  let (univ, n) := (bs.filter fun b => !entrySet.contains b.label).foldl
    (init := (([] : List (Label × List (ValId × ValDecl env))), base)) fun (acc, n) b =>
      let cells := (((changed.getD b.label {}).toList.filter candSet.contains).mergeSort
        (·.id ≤ ·.id)).filterMap fun c => (types.get? c).map (c, ·)
      let cells := cells.zipIdx.map fun ((c, t), k) =>
        (c, ({ id := ⟨n + k⟩, type := t } : ValDecl env))
      ((b.label, cells) :: acc, n + cells.length)
  let univ := univ.reverse
  let count := n - base
  let blocks₀ : HashMap Label (BlockPlan env) := univ.foldl (init := {}) fun m (l, cells) =>
    m.insert l { carried := cells }
  let P₀ : Plan env := { promoted := candSet, blocks := blocks₀ }
  let S₀ ← P₀.startsWith parents changed fn
  let evs := walk P₀ S₀.maps fn
  -- The content maps of the edges into each block, and each removed read's content, unreplaced.
  let ins : HashMap Label (List CMap) := evs.foldl (init := {}) fun m e =>
    match e with
    | .edge cm k => m.insert k.label (cm :: m.getD k.label [])
    | _ => m
  let (reads, unresolved) := evs.foldl
    (init := (({} : HashMap ValId ValId), ([] : List ValId))) fun (rs, un) e =>
      match e with
      | .read r c (some u) => if candSet.contains c then (rs.insert r u, un) else (rs, un)
      | .read _ c none => if candSet.contains c then (rs, c :: un) else (rs, un)
      | _ => (rs, un)
  let params : HashMap Label (Array (ValDecl env)) :=
    bs.foldl (init := {}) fun m b => m.insert b.label b.params
  -- Each new parameter's block and cell.
  let where_ : HashMap ValId (Label × ValId) := univ.foldl (init := {}) fun m (l, cells) =>
    cells.foldl (init := m) fun m (c, d) => m.insert d.id (l, c)
  -- A parameter's incoming values, or `none` if an edge doesn't know its cell.
  let insOf (v : ValId) : Option (Option (List ValId)) := (where_.get? v).map fun (l, c) =>
    (ins.getD l []).mapM (·.get? c)
  -- The used parameters, found from the reads' contents, with their incoming values, and the
  -- unknown ones among them; only these are looked at further.
  let some (used, known, unknownUsed) := markUsed insOf reads
      (2 * reads.size + (count + 1) * ((allEdges fn).length + 1) + 1) reads.values ({}, {}, [])
    | throw "the used parameters did not settle"
  let unread : Std.HashSet ValId := unresolved.foldl (·.insert ·) {}
  let dropped := unknownUsed.foldl (init := unread) fun d p => match where_.get? p with
      | some (_, c) => d.insert c
      | none => d
  if !dropped.isEmpty then return ({}, dropped.toList)
  -- The used parameters, with their block, the block's new parameters, and their values.
  let own : HashMap Label (Std.HashSet ValId) := univ.foldl (init := {}) fun m (l, cells) =>
    m.insert l (cells.foldl (fun s (_, d) => s.insert d.id) {})
  let news : HashMap ValId (Label × Std.HashSet ValId × List ValId) :=
    known.fold (init := {}) fun m p vs =>
      match where_.get? p with
      | some (l, _) => m.insert p (l, own.getD l {}, vs)
      | none => m
  let depth := count + reads.size + 1
  -- Each parameter under the values its edges pass, followed through the removed reads.
  let users : HashMap ValId (Std.HashSet ValId) := news.fold (init := {}) fun m p (_, _, vs) =>
    vs.foldl (init := m) fun m v =>
      m.alter (chase reads depth v) fun s => some ((s.getD {}).insert p)
  -- In block order, so that a chain of aliases mostly settles in one pass.
  let work := univ.flatMap fun (_, cells) => (cells.map (·.2.id)).filter news.contains
  let some alias := aliasIter news params depth ((count + 1) * (count + reads.size + 2))
      work reads users
    | throw "the parameters did not settle"
  let res := chase alias depth
  let blocks : HashMap Label (BlockPlan env) := univ.foldl (init := {}) fun m (l, cells) =>
    let cells := cells.filter fun (_, d) => used.contains d.id
    if cells.isEmpty then m else
    m.insert l ({ ins := min (fewest.getD l 0) (params.getD l #[]).size
                  carried := cells.filter fun (_, d) => !alias.contains d.id
                  fixed := cells.filterMap fun (c, d) =>
                    if alias.contains d.id then some (c, res d.id) else none } : BlockPlan env)
  let sigma : HashMap ValId ValId := reads.fold (init := {}) fun m r _ => m.insert r (res r)
  return (({ promoted := candSet, blocks, sigma } : Plan env).finish fn (univ.map (·.1)), [])

/-- The plan for `fn`, with the tree parents `parents` (`trees`): candidates whose contents are
known wherever they matter, with everything they need.  Each pass drops the candidates that the
planner finds unknown; at most one per candidate.  The changed sets are computed once, for all
candidates. -/
@[expose] def plan (parents : HashMap Label Point) (fn : Func env α) :
    Except String (Plan env) := do
  let cands := candidates fn
  let candSet : Std.HashSet ValId := cands.foldl (·.insert ·) {}
  let inv ← allRanges parents fn
  let changed ← changedSets candSet.contains inv fn
  go changed (cands.length + 1) cands
where
  go (changed : HashMap Label (Std.HashSet ValId)) : Nat → List ValId → Except String (Plan env)
    | 0, _ => throw "the set of promoted cells did not settle"
    | fuel + 1, cands => do
      let (P, dropped) ← planWith fn parents changed cands
      if dropped.isEmpty then return P
      else
        let gone : Std.HashSet ValId := dropped.foldl (·.insert ·) {}
        go changed fuel (cands.filter (!gone.contains ·))

/-- The candidates of `fn` that a plan leaves as cells. -/
@[expose] def Plan.left (P : Plan env) (fn : Func env α) : List ValId :=
  (candidates fn).filter (!P.promoted.contains ·)

/-- The plan for `fn`, with its own tree parents; for tests and tools. -/
@[expose] def planOf (fn : Func env α) : Except String (Plan env) := do
  plan (← trees fn) fn

/-- `fn` rewritten by `P`, with the start maps that the check computes; for tests and tools. -/
@[expose] def Plan.applyFor (P : Plan env) (fn : Func env α) : Except String (Func env α) := do
  let S ← P.starts (← trees fn) fn
  return P.apply S.maps fn

/-! ## The pass -/

/-- `fn` with the cells of `planner`'s plan promoted, or why not.  The pass computes the tree
parents once, gives them to the planner, and computes the start maps once, for the check and the
rewrite. -/
@[expose] def promoteWith
    (planner : HashMap Label Point → Func env α → Except String (Plan env)) (fn : Func env α) :
    Except String (Func env α) := do
  let parents ← trees fn
  let P ← planner parents fn
  let S ← P.starts parents fn
  if P.check S fn then return P.apply S.maps fn
  match (P.rules S fn).find? (!·.2) with
  | some (rule, _) => throw s!"the plan breaks a rule: {rule}"
  | none => throw "the plan fails its check"

end RefToReg

open RefToReg in
/-- The module with every function's cells promoted by `planner`'s plans, checked; or each
function concerned with the reason. -/
@[expose] def refToRegWith {env : Env Unit} [base ≼ env] {α : Type}
    (planner : Std.HashMap Label Point → Func env α → Except String (Plan env))
    (m : Module env α) :
    Except (Array (Name × String)) (Module env α) :=
  let results := m.raw.funcs.map fun f => (f.name, promoteWith planner f)
  let errs := results.filterMap fun
    | (n, .error e) => some (n, e)
    | _ => none
  if !errs.isEmpty then .error errs else
  let funcs := results.filterMap fun
    | (_, .ok f) => some f
    | _ => none
  match Module.Raw.check { m.raw with funcs } with
  | .ok m₁ => .ok m₁
  | .error names => .error (names.map (·, "the promoted function is not well formed"))

/-- **Ref-to-reg**: the module with every promotable cell promoted, by `RefToReg.plan`. -/
@[expose] def refToReg {env : Env Unit} [base ≼ env] {α : Type} (m : Module env α) :
    Except (Array (Name × String)) (Module env α) :=
  refToRegWith RefToReg.plan m

end

end Strata.Dyn
