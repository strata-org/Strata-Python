/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
public import StrataDyn.DomCompute
public import StrataDyn.DomDecide
public import StrataDyn.Util.LabelMap
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF
import Std.Data.HashMap

set_option autoImplicit false

/-!
# Failures, cycles and `old` in contract regions

A *failure successor* is a successor of an instruction, as opposed to a terminator: where the
operation goes when it fails, such as the `err` successor of a raising operation.  A failure in a
`requires` clause or a checked `ensures` clause gives `false`, one in a `free ensures` clause
gives `true`, and one in a frame region goes to a block that ends in `unreachable`.  `Func.WF`
(`StrataDyn/WF.lean`) makes the IR say so with these predicates:

* `Region.FailsWith`: a failure successor of a clause's or a frame region's own blocks goes to a
  *failure block*, which returns the clause's failure value or ends in `unreachable`;
* `Region.Propagates`: a failure successor of a region nested in a clause goes to a block that
  ends in `unreachable`, or, if the region may propagate, that passes the failure on with
  `base.error`.
  A region may propagate when its owner is an instruction that declares a failure successor,
  and that declares the region's result type as a `base.Except`;
* `Region.EndsInControl`: every block of a contract region ends in control flow, so no terminal
  operation's successor carries a failure;
* `Region.Acyclic`: the blocks of every contract region form an acyclic graph of transfers.

So no failure turns into a value that makes a clause hold or a free clause assume anything.  This
rests on the environment rule (`docs/Dyn.md`): an operation reports a failure only through a
failure successor of an instruction, and the owner of a region that may propagate passes an
`error` that the region returns on through one of its failure successors.

`base.old` runs its region in the state at the call, and two more predicates state its rules:

* `Region.NoOld`: no instruction of the regions applies `base.old`, at any depth.  `Func.WF` asks
  it of the body, the `requires` clauses and the frame regions, so that only an `ensures` clause
  applies it;
* `Region.OldScoped`: each outermost `old` region of a clause sees, from outside it, only the
  function's parameters, the constants of the clause, and the parameters of the regions nested
  in the clause that enclose it.

Each predicate is stated plainly.  `StrataDyn/ContractRegionProps.lean` proves the fast checks
that decide them: `Region.failuresToB`, which looks the targets up in a map built once per
region, and `Body.acyclicFast`, which runs Kahn's algorithm and checks its answer.  Compiled code
runs `Body.acyclicFast` in place of the reference check, `Body.acyclicB`, which the kernel
reduces.  It also states `Region.OldScoped` with `Body.Shaped` and `Body.DomCorrect`
(`Region.oldScoped_iff`).
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-! ## Regions nested at any depth -/

/-- Whether the type is an application of `base.Except`. -/
@[expose] def TypeExpr.isExcept {scope : Array Kind} (t : TypeExpr env scope) : Bool :=
  t.fold (fun _ _ => false) (fun n _ => n == bn "Except") (fun _ => false)

/-- Whether each region of an operation with signature `isig` may propagate: the operation
declares a failure successor, and declares the region's result type as a `base.Except`, before
its type arguments are put in. -/
@[expose] def InsnSig.mayPropagate (isig : InsnSig env) : List Bool :=
  isig.regions.toList.map fun p => !isig.succs.isEmpty && p.type.returnType.isExcept

mutual

/-- The regions of an instruction's operation, each with whether it may propagate
(`InsnSig.mayPropagate`) and followed by the regions nested in it, at any depth. -/
@[expose] def Instruction.regionsWithNested : Instruction env α → List (Region env α × Bool)
  | @Instruction.apply _ _ _ _ isig _ _ _ _ ⟨regions⟩ =>
    Region.withNestedList isig.mayPropagate regions
  | .const .. => []

/-- `Instruction.regionsWithNested` of each. -/
@[expose] def Instruction.regionsWithNestedList :
    List (Instruction env α) → List (Region env α × Bool)
  | [] => []
  | i :: is => i.regionsWithNested ++ Instruction.regionsWithNestedList is

/-- The regions of a terminal operation, none of which may propagate, each followed by the
regions nested in it, at any depth. -/
@[expose] def Terminator.regionsWithNested : Terminator env α → List (Region env α × Bool)
  | .apply _ _ _ _ _ ⟨regions⟩ => Region.withNestedList [] regions

/-- The regions nested in the blocks' instructions and terminators, at any depth, each with
whether it may propagate. -/
@[expose] def Block.nestedRegionsList : List (Block env α) → List (Region env α × Bool)
  | [] => []
  | ⟨_, _, ⟨instrs⟩, t, _⟩ :: bs =>
    Instruction.regionsWithNestedList instrs ++ t.regionsWithNested ++ Block.nestedRegionsList bs

/-- Each region, with the entry of `flags` in its place, or `false` past its end, followed by
the regions nested in it, at any depth. -/
@[expose] def Region.withNestedList :
    List Bool → List (Region env α) → List (Region env α × Bool)
  | _, [] => []
  | fs, ⟨⟨blocks⟩⟩ :: rs =>
    (⟨⟨blocks⟩⟩, fs.headD false) ::
      (Block.nestedRegionsList blocks ++ Region.withNestedList fs.tail rs)

end

/-- The regions nested in the regions `rs`, at any depth, but not `rs` themselves, each with
whether it may propagate. -/
@[expose] def Region.nestedList (rs : List (Region env α)) : List (Region env α × Bool) :=
  rs.flatMap fun r => Block.nestedRegionsList r.blocks.toList

/-- The regions `rs`, and every region nested in them, at any depth. -/
@[expose] def Region.allList (rs : List (Region env α)) : List (Region env α) :=
  (Region.withNestedList [] rs).map (·.1)

/-! ## Where failures go -/

/-- Whether the terminator is `unreachable`. -/
@[expose] def Terminator.isUnreachable : Terminator env α → Bool
  | .apply _ r .. => r.name == bn "unreachable"

/-- The value the terminator returns, if it is a `ret`: a `jump` to `Label.exit` that passes one
value. -/
@[expose] def Terminator.retValue? : Terminator env α → Option ValId
  | .apply _ r _ _ ⟨[⟨l, ⟨[v]⟩⟩]⟩ _ =>
    if r.name == bn "jump" && l == Label.exit then some v else none
  | _ => none

/-- Whether `b` is a *failure block* that gives `value`: its instructions are all constants, and
it ends in `unreachable`, or, if `value` is `some c`, in `ret` of a constant `c` that it
defines. -/
@[expose] def Block.isFailure (value : Option Bool) (b : Block env α) : Bool :=
  b.instrs.toList.all (fun | .const .. => true | .apply .. => false) &&
    (b.term.isUnreachable ||
      match value, b.term.retValue? with
      | some c, some v => b.instrs.toList.any fun
        | .const _ d (.bool c') => d.id == v && c' == c
        | _ => false
      | _, _ => false)

/-- Whether `b` is a *propagating block*: its only instruction applies `base.error` to its last
parameter, the failure it receives, and it ends in `ret` of that instruction's result. -/
@[expose] def Block.isPropagating (b : Block env α) : Bool :=
  match b.instrs.toList, b.params.back? with
  | [.apply _ d r _ args _ _], some p =>
    r.name == bn "error" && args == #[p.id] && b.term.retValue? == some d.id
  | _, _ => false

/-- Every failure successor of the region's own blocks goes to a block of the region that `ok`
accepts.  The blocks of the regions nested in it are not its own.  `Region.failuresToB` decides
it. -/
@[expose] def Region.FailuresTo (ok : Block env α → Bool) (r : Region env α) : Prop :=
  ∀ b ∈ r.blocks.toList, ∀ i ∈ b.instrs.toList, ∀ k ∈ i.succs.toList,
    ∃ t ∈ r.blocks.toList, t.label = k.label ∧ ok t = true

/-- The labels of the blocks of `bs`, as a set. -/
@[expose] def Body.labelSet (bs : List (Block env α)) : LabelMap Unit :=
  bs.foldl (fun m b => m.insert b.label ()) ∅

/-- `Region.FailuresTo`, checked through the set of the labels of the region's blocks that `ok`
accepts, built once. -/
@[expose] def Region.failuresToB (ok : Block env α → Bool) (r : Region env α) : Bool :=
  let good := Body.labelSet (r.blocks.toList.filter ok)
  r.blocks.toList.all fun b => b.instrs.toList.all fun i => i.succs.toList.all fun k =>
    (good.find? k.label).isSome

/-- Every failure successor of the region's own blocks goes to a failure block of the region that
gives `value`, or that ends in `unreachable`.  With `value = none`, every such failure goes to a
block that ends in `unreachable`. -/
@[expose, reducible] def Region.FailsWith (value : Option Bool) (r : Region env α) : Prop :=
  r.FailuresTo (Block.isFailure value)

/-- Every region nested in the regions `rs`, at any depth, passes its failures on: each failure
successor of its own blocks goes to a block of it that ends in `unreachable`, as a failure block
giving no value does, or, if the region may propagate, that propagates the failure.  So a nested
region never turns a failure into a value, and the failure successor of the operation that owns
it carries the failure on. -/
@[expose, reducible] def Region.Propagates (rs : List (Region env α)) : Prop :=
  ∀ p ∈ Region.nestedList rs, p.1.FailuresTo fun t => t.isFailure none || (p.2 && t.isPropagating)

/-- Whether the terminator is control flow: `jump`, which `ret` is, `branch`, `unreachable`, or a
datatype's case instruction, found by its declaration.  None of them fails. -/
@[expose] def Terminator.isControl : Terminator env α → Bool
  | .apply _ r .. =>
    r.name == bn "jump" || r.name == bn "branch" || r.name == bn "unreachable" ||
      r.caseAddr?.isSome

/-- Every block of the regions `rs`, and of every region nested in them, at any depth, ends in
control flow (`Terminator.isControl`).  So no terminal operation's successor carries a
failure. -/
@[expose, reducible] def Region.EndsInControl (rs : List (Region env α)) : Prop :=
  ∀ r ∈ Region.allList rs, ∀ b ∈ r.blocks.toList, b.term.isControl = true

/-! ## Acyclicity -/

/-- Every block of `S` transfers to a block of `S`, as the blocks of a cycle do.  Every nonempty
such list of the blocks of a body contains a cycle, since following the transfers from any of
its blocks never leaves it. -/
@[expose] def Body.Closed (S : List (Block env α)) : Prop :=
  ∀ b ∈ S, ∃ c ∈ S, ∃ e ∈ Body.edges b, e.2 = c.label

/-- The blocks of `bs` that transfer to a block of `bs`, found by its label. -/
@[expose] def Body.unpeeled (bs : List (Block env α)) : List (Block env α) :=
  let ls := Body.labelSet bs
  bs.filter fun b => (Body.edges b).any fun e => (ls.find? e.2).isSome

/-- `Body.unpeeled`, at most `n` times, stopping when it removes no block. -/
@[expose] def Body.peel : Nat → List (Block env α) → List (Block env α)
  | 0, bs => bs
  | n + 1, bs =>
    let rest := Body.unpeeled bs
    if rest.length < bs.length then Body.peel n rest else rest

/-- Whether the blocks `bs` form an acyclic graph of transfers: removing, round after round,
every block that transfers to no block left removes them all.  A round removes at least one
block of an acyclic graph, so `bs.length` rounds are enough.  It is the reference that the
proofs and the kernel use; compiled code runs `Body.acyclicFast`. -/
@[expose] def Body.acyclicB (bs : List (Block env α)) : Bool :=
  (Body.peel bs.length bs).isEmpty

/-- The blocks `bs` form an acyclic graph of transfers: no nonempty list of them is
`Body.Closed` (`Body.acyclicB_iff`). -/
@[expose] def Body.Acyclic (bs : List (Block env α)) : Prop := Body.acyclicB bs = true

/-- The blocks of each of the regions `rs`, and of each region nested in them, at any depth,
form an acyclic graph of transfers. -/
@[expose, reducible] def Region.Acyclic (rs : List (Region env α)) : Prop :=
  ∀ r ∈ Region.allList rs, Body.Acyclic r.blocks.toList

/-! ## A fast acyclicity check

`Body.acyclicB` rebuilds a set of labels each round, and a round may remove a single block, so
it is quadratic on a chain of blocks.  `Body.acyclicFast` runs Kahn's algorithm in linear time.
Nothing proves the algorithm: `Body.acyclicFast` checks the order it gives, and the checks are
proved. -/

/-- The positions in `bs` of the blocks that Kahn's algorithm removes, in the order it removes
them: it next removes a block whose transfers to blocks of `bs` all go to blocks already removed,
sinks first.  A transfer goes to the first block with its target's label.  On an acyclic graph,
it removes every block, each after the blocks it transfers to. -/
def Body.sinkOrder (bs : Array (Block env α)) : Array Nat := Id.run do
  let pos : Std.HashMap Label Nat :=
    bs.zipIdx.foldl (fun m (b, i) => if m.contains b.label then m else m.insert b.label i) {}
  -- Per block, how many of its transfers go to blocks not yet removed, and the blocks that
  -- transfer to it, once per transfer.
  let mut out : Array Nat := Array.replicate bs.size 0
  let mut preds : Array (Array Nat) := Array.replicate bs.size #[]
  for (b, i) in bs.zipIdx do
    for e in Body.edges b do
      if let some j := pos.get? e.2 then
        out := out.modify i (· + 1)
        preds := preds.modify j (·.push i)
  let mut order : Array Nat := (Array.range bs.size).filter fun i => out[i]? == some 0
  -- Each round removes one block, so `bs.size` rounds suffice.
  let mut next := 0
  for _ in [0:bs.size] do
    let some j := order[next]? | break
    next := next + 1
    for i in preds[j]?.getD #[] do
      out := out.modify i (· - 1)
      if out[i]? == some 0 then order := order.push i
  return order

/-- Each block's label, mapped to the place of its position in `order`. -/
def Body.ranksOf (bs : Array (Block env α)) (order : Array Nat) : LabelMap Nat :=
  order.zipIdx.foldl (init := ∅) fun m (i, k) =>
    match bs[i]? with
    | some b => m.insert b.label k
    | none => m

/-- Whether every block of `bs` has a rank in `rank`, and every transfer from a block of `bs` to a
label with a rank goes to a smaller rank than its block's. -/
@[expose] def Body.ranksDecrease (rank : LabelMap Nat) (bs : List (Block env α)) : Bool :=
  bs.all fun b =>
    match rank.find? b.label with
    | none => false
    | some r => (Body.edges b).all fun e =>
      match rank.find? e.2 with
      | some r' => decide (r' < r)
      | none => true

/-- Whether every block of `S` transfers to a block of `S`: `Body.Closed`, checked through the set
of their labels. -/
@[expose] def Body.closedB (S : List (Block env α)) : Bool :=
  let ls := Body.labelSet S
  S.all fun b => (Body.edges b).any fun e => (ls.find? e.2).isSome

/-- The blocks of `bs` whose labels are not those of the blocks at the positions `order`: after
Kahn's algorithm, the blocks of a graph with a cycle that lie on a cycle or lead into one. -/
@[expose] def Body.unremovedBy (bs : List (Block env α)) (order : Array Nat) :
    List (Block env α) :=
  let a := bs.toArray
  let removed : LabelMap Unit := order.foldl (init := ∅) fun m i =>
    match a[i]? with
    | some b => m.insert b.label ()
    | none => m
  bs.filter fun b => (removed.find? b.label).isNone

/-- `Body.acyclicB`, in linear time.  Kahn's algorithm orders the blocks.  If every transfer goes
to a block removed earlier, the graph is acyclic.  Otherwise, if the blocks it did not remove are
a nonempty `Body.Closed` list, the graph has a cycle.  If neither check passes, which a correct
order never causes, it runs `Body.peel`. -/
@[expose] def Body.acyclicFast (bs : List (Block env α)) : Bool :=
  let order := Body.sinkOrder bs.toArray
  if Body.ranksDecrease (Body.ranksOf bs.toArray order) bs then true
  else
    let rest := Body.unremovedBy bs order
    if !rest.isEmpty && Body.closedB rest then false
    else (Body.peel bs.length bs).isEmpty

/-! ## `old` in `ensures` clauses

`base.old` runs its region in the state at the call.  So only an `ensures` clause may apply it,
and its region sees from outside it only the function's parameters, the constants of the clause,
and the parameters of the regions nested in the clause that enclose it, such as a quantifier's
binder.  It never sees the clause's parameter, which is the result, nor another value that the
clause defines outside the `old` region.  An `old` nested in an `old` runs in the state at the call
too, so it may also see the values of the enclosing `old` region: only the outermost `old` regions
are checked. -/

/-- Whether the instruction applies `base.old`. -/
@[expose] def Instruction.isOld : Instruction env α → Bool
  | .apply _ _ r .. => r.name == bn "old"
  | .const .. => false

/-- No instruction of the regions `rs`, or of a region nested in them at any depth, applies
`base.old`.  A terminator never does, since `base.old` returns a value. -/
@[expose, reducible] def Region.NoOld (rs : List (Region env α)) : Prop :=
  ∀ r ∈ Region.allList rs, ∀ b ∈ r.blocks.toList, ∀ i ∈ b.instrs.toList, i.isOld = false

/-- The parameters of a body's entry block, which are those of its region. -/
@[expose] def Body.entryParams (bs : List (Block env α)) : List ValId :=
  (bs.head?.map fun b => b.params.toList.map (·.id)).getD []

mutual

/-- The regions of the outermost applications of `base.old` in an instruction, at any depth, each
with the parameters of the regions that enclose it: those of the regions nested in the
instruction, then `ps`.  An application of `base.old` gives its own regions, with `ps`, and
nothing nested in them. -/
@[expose] def Instruction.oldRegions (ps : List ValId) :
    Instruction env α → List (Region env α × List ValId)
  | .apply _ _ r _ _ _ ⟨regions⟩ =>
    if r.name == bn "old" then regions.map ((·, ps)) else Region.oldRegionsList ps regions
  | .const .. => []

/-- `Instruction.oldRegions` of each. -/
@[expose] def Instruction.oldRegionsList (ps : List ValId) :
    List (Instruction env α) → List (Region env α × List ValId)
  | [] => []
  | i :: is => i.oldRegions ps ++ Instruction.oldRegionsList ps is

/-- The outermost `old` regions in a terminator's regions, as `Instruction.oldRegions` gives
them. -/
@[expose] def Terminator.oldRegions (ps : List ValId) :
    Terminator env α → List (Region env α × List ValId)
  | .apply _ _ _ _ _ ⟨regions⟩ => Region.oldRegionsList ps regions

/-- The outermost `old` regions in the blocks' instructions and terminators, as
`Instruction.oldRegions` gives them. -/
@[expose] def Block.oldRegionsList (ps : List ValId) :
    List (Block env α) → List (Region env α × List ValId)
  | [] => []
  | ⟨_, _, ⟨instrs⟩, t, _⟩ :: bs =>
    Instruction.oldRegionsList ps instrs ++ t.oldRegions ps ++ Block.oldRegionsList ps bs

/-- The outermost `old` regions in the regions `rs`, each with the parameters of the regions that
enclose it, from the innermost one to the region of `rs` that holds it, then `ps`. -/
@[expose] def Region.oldRegionsList (ps : List ValId) :
    List (Region env α) → List (Region env α × List ValId)
  | [] => []
  | ⟨⟨blocks⟩⟩ :: rs =>
    Block.oldRegionsList (Body.entryParams blocks ++ ps) blocks ++ Region.oldRegionsList ps rs

end

/-- The values that the constants of the regions `rs`, and of every region nested in them at any
depth, define. -/
@[expose] def Region.constIds (rs : List (Region env α)) : NatTrie Unit :=
  (Region.allList rs).foldl (init := .leaf) fun m r =>
    r.blocks.foldl (init := m) fun m b => b.instrs.foldl (init := m) fun m i =>
      match i with
      | .const _ d _ => m.insert d.id.id ()
      | .apply .. => m

/-- Whether an outermost `old` region sees `x` from outside it, with `ps` the parameters of the
regions that enclose it: `x` is a parameter of the function, as `isParam` says, a value of `ps`,
or a value that a constant of the clause defines, as `consts` has them. -/
@[expose] def Region.oldSees (isParam : ValId → Bool) (consts : NatTrie Unit) (ps : List ValId)
    (x : ValId) : Bool :=
  isParam x || ps.contains x || (consts.find? x.id).isSome

/-- Each outermost `old` region of the clause `r`, at any depth, is shaped and dominance-correct
as a body entered where only what `Region.oldSees` gives is visible: the function's parameters,
as `isParam` says, the values that the constants of `r` define, and the parameters of the
regions nested in `r` that enclose it.  So it sees neither the parameter of `r`, which is the
function's result, nor any other value that `r` defines outside it.  An `old` nested in it is
part of it.  `Region.oldScoped_iff` states it with `Body.Shaped` and `Body.DomCorrect`. -/
@[expose] def Region.OldScoped (isParam : ValId → Bool) (r : Region env α) : Prop :=
  ∀ p ∈ Block.oldRegionsList [] r.blocks.toList,
    p.1.domOK (Region.oldSees isParam (Region.constIds [r]) p.2) = true

/-- Deciding `Region.OldScoped`, with the constants of the clause collected once. -/
instance (isParam : ValId → Bool) (r : Region env α) : Decidable (r.OldScoped isParam) :=
  let consts := Region.constIds [r]
  decidable_of_iff ((Block.oldRegionsList [] r.blocks.toList).all fun p =>
    p.1.domOK (Region.oldSees isParam consts p.2)) List.all_eq_true

end

end Strata.Dyn
