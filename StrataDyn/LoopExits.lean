/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonical
public import StrataDyn.WF
public import StrataDyn.BodyIndexProps
import all StrataDyn.Util.LabelMapProps
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Reason-carrying loop exits and the preamble

The rest of the canonical form, for a front end whose loops end with a *completion*: a value of a
datatype that says how a construct finished, such as `Normal`, `Break`, `Continue`, `Return v` or
`Raise e`.  For each loop:

* (P4) one block `done(k)`, which takes the completion as its first parameter and is no loop's
  head: no back edge enters it, and no record names it as its head.  No path out of the loop leaves
  the body (returns or raises), or comes back to the head of a loop around it, without passing
  `done`, and some path from each block that the loop leaves for, except an empty block that ends
  in `base.unreachable`, reaches `done`.  A path may instead run forever or fault, and reaching
  `base.unreachable` is a fault.  Code before the loop may also enter `done`.  So a stage may
  assert at `done` what holds when the loop ends by `k`; it may assume there only what it has just
  asserted;
* (P7) `done` holds no instructions, not even a `base.loopInvariant`, so every completion leaves it
  through the arm of its case for that completion.  It absorbs its own loop's `Break` and `Continue`, and forwards every other
  completion out of the loop.

And for the function:

* (F1) the entry block ends in a plain jump to a block that nothing else enters, the *start
  block*, or in `base.unreachable`.  The precondition is assumed at the start of the start block.

The entry block's own instructions run before the start block, and F1 says nothing about them.
So a stage that assumes the precondition at the start block must cover them in two ways.  Runs
whose entry-block instruction transfers elsewhere, such as an argument binding that fails, never
reach the start block.  The stage either proves at each call site that the entry block reaches its
jump, or accounts for those runs at the call site (what they return, what they write, and where
they fault), or verifies those runs in the callee itself, against its frame and its exceptional
result, without assuming the precondition.  On runs that reach the
start block, the stage checks the entry block's code itself: its writes count against the
function's frame, and the state it leaves is the one the precondition is assumed of, so the stage
must relate it to the state at the call, where the caller asserted the precondition.

Two conditions keep P4 meaningful for the stages after the pass.  A fault is a failure, not an
assumption: `reaches` exempts an empty block that ends in `base.unreachable` only because control
that gets there fails, so a lowering encodes `base.unreachable` as a failed assertion, never as an
assumption.  And no pass adds an assumption, which drops the runs that break it, between a loop's
exit and its `done`.  `Body.Leaves`, which `noReturn` uses, sees every normal end of a body's run
("Leaving the body" in `StrataDyn/CanonicalProps.lean`).

The front end supplies two things.  A `CompletionShape` names its completion datatype and the
role of each constructor; the check reads the constructors' order from the environment.  A
`LoopRecord` per loop names its head and its `done`.  Every loop has a record; a loop that control
never leaves has no `done`.  The records are untrusted: the check verifies each one, in the body
that holds its head (`Func.LoopExits.recordHolds`).  They are needed because an enclosing loop's
`done` also meets every exit of an inner loop, so the CFG alone cannot tell which `done` belongs
to which loop.

A record's head need not head a loop of the CFG: a loop whose body always leaves, such as
`while c: return x`, has no back edge.  Then its *scope* is its head alone.  P1 asks for a
preheader all the same, so that the invariant's base case has its block, and the head must
dominate its `done` and every block it leaves for, so that every way into the loop's code passes
through the head.

What the form cannot see, which is the lowering's semantics:
* whether a completion carries the right reason, such as a `break` built as `Normal`;
* whether a record names, as its loop's `done`, a block that an enclosing construct also uses as
  its own, such as a function's `finally` block, when no path between the loop and that block
  returns;
* whether a record of a loop with no back edge names the block where the loop statement starts,
  or a block before it that also dominates the loop's code;
* whether a shape gives the right roles to two constructors that carry no field, such as
  `normal` and `continue`: a front end pins its shape with a test;
* where an arm of `done` sends a completion once it has left the loop: a `return` arm that goes
  round a loop around this one is accepted, as Python's `finally: continue` needs.

Labelled `break` and `continue`, which need a label in their completion, are not part of the
form: a shape's `break` and `continue` carry no field, so the check rejects every function whose
completion type gives `break` or `continue` a label.  A front end with labels, such as one for
JavaScript, needs the form extended first.

## Main definitions

* `CompletionShape`, `LoopRecord`: what the front end supplies, and `CompletionShape.roles?`,
  the shape checked against the environment;
* `Body.Done`, `Body.Absorbs`, `Body.LoopExits`: P4, P7, and both with P1 for every record;
* `Func.LoopExits`, `Func.Preamble`: the function properties;
* `Func.checkLoopExits`, `Func.checkPreamble`: their checks, which
  `StrataDyn/LoopExitsProps.lean` proves to decide them;
* `CanonicalSpec`: what a front end asks of `Canonicalize.run`, and its check.

`Body.loopExitsFastB` and `Func.checkLoopExitsFast` read each record's loop, and the transfers
into and out of it, from the body's index (`Body.Index`, `StrataDyn/BodyIndex.lean`), and each
block's records from a map of the records by head, both computed once.
`Body.loopExitsB_eq_fast` and `Func.checkLoopExits_eq_fast`, proved here so that the code below
and `Canonicalize.run` use them, make them run in place of `Body.loopExitsB` and
`Func.checkLoopExits`.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-- How a front end represents the way a construct finished: the datatype `data` of type `ty`,
and the constructors of each role, by name: the normal end, `break`, `continue`, and those
forwarded out of every loop, such as `return` and `raise`.  `data`'s case instruction branches on
it, with one successor per constructor, in the constructors' order. -/
structure CompletionShape (env : Env Unit) where
  ty : TypeExpr env
  data : Name
  normal : Name
  brk : Name
  cont : Name
  forwarded : List Name

/-- The constructor index of each role of a completion shape, as `CompletionShape.roles?` reads
them from the environment. -/
structure Roles where
  normal : Nat
  brk : Nat
  cont : Nat
  forwarded : List Nat
deriving DecidableEq

/-- Every role's index, in no particular order. -/
@[expose] def Roles.all (ro : Roles) : List Nat := ro.normal :: ro.brk :: ro.cont :: ro.forwarded

/-- The name of the case instruction on the completion. -/
@[expose] def CompletionShape.caseName (s : CompletionShape env) : Name := s.data.caseName

/-- The index of each role, read from the environment's declaration of `s.data`, if the shape is
well formed: each constructor of `s.data` has exactly one role, and the normal end, `break` and
`continue` carry no field.  So a shape cannot give a role to a constructor that carries the wrong
fields, nor leave a constructor without one.  It does not check whether two constructors that
carry no field have their roles swapped. -/
@[expose] def CompletionShape.roles? (s : CompletionShape env) : Option Roles := do
  let (g, i) ← env.dataOf? s.data
  let m ← g.member? i
  let names := m.ctors.toList.map (·.name)
  let idx (n : Name) : Option Nat := names.idxOf? n
  let ro : Roles := { normal := ← idx s.normal, brk := ← idx s.brk, cont := ← idx s.cont,
                      forwarded := ← s.forwarded.mapM idx }
  let arity (k : Nat) : Nat := (m.ctors[k]?.map (·.args.size)).getD 0
  if ro.all.Nodup && ro.all.length = names.length && arity ro.normal = 0 &&
      arity ro.brk = 0 && arity ro.cont = 0 then some ro else none

/-- What a front end states about one of its loops: the block it starts at, and the block `done`
its exits meet at.  A loop that control never leaves has no `done`. -/
structure LoopRecord where
  head : Label
  done : Option Label
deriving DecidableEq

namespace Body

variable (bs : List (Block env α))

/-! ## The properties -/

/-- The point `u` is in the scope of the loop that starts at `h`: in the loop of `h`, or, if no
back edge enters `h`, in `h` itself. -/
@[expose] def InLoopScope (h : Label) (u : Point) : Prop :=
  AtLoop bs h u ∨ (¬ IsHead bs h ∧ u.label = h)

/-- A transfer leaves the scope of `h` for the block labelled `x`. -/
@[expose] def ExitOf (h x : Label) : Prop :=
  ∃ u, Transfer bs u x ∧ InLoopScope bs h u ∧ ¬ InLoopScope bs h ⟨x, 0⟩

/-- The block labelled `l` is empty and ends in `base.unreachable`: control never gets there,
and it transfers nowhere. -/
@[expose] def Unreachable (l : Label) : Prop :=
  ∃ b ∈ bs, b.label = l ∧ b.instrs = #[] ∧ b.term.name = bn "unreachable"

/-- Some path from the start of `x` reaches the block `d`. -/
@[expose] def Reaches (x d : Label) : Prop :=
  x = d ∨ ∃ y, PathAvoid bs ⟨d, 0⟩ ⟨x, 0⟩ y ∧ Transfer bs y d

/-- Some path from a block that the scope of `h` leaves for reaches `u` without passing `d`. -/
@[expose] def PastExit (h d : Label) (u : Point) : Prop :=
  ∃ x, ExitOf bs h x ∧ PathAvoid bs ⟨d, 0⟩ ⟨x, 0⟩ u

/-- (P4) `d` is the `done` of the loop that starts at `h`: it takes the completion first; it is
outside the loop; no point of the loop leaves the body; some path from every block the loop leaves
for reaches it, unless control never gets there; no path from those blocks leaves the body
(returns or raises) before it; and none comes back to the head of a loop around this one before
it.  A path from those blocks may instead run forever.  That `d` is no loop's head is a property
of the records (`Func.LoopExits.done_not_head`): every loop has a record, and no record's head is
a `done`. -/
structure Done (s : CompletionShape env) (h d : Label) : Prop where
  block : ∃ b ∈ bs, b.label = d ∧ (b.params[0]?.map (·.type)) = some s.ty
  outside : ¬ InLoopScope bs h ⟨d, 0⟩
  stays : ∀ u, InLoopScope bs h u → ¬ Leaves bs u
  reaches : ∀ x, ExitOf bs h x → ¬ Unreachable bs x → Reaches bs x d
  noReturn : ∀ u, PastExit bs h d u → ¬ Leaves bs u
  noOuterHead : ∀ h', IsHead bs h' → h' ≠ h → (∃ b, b.label = h ∧ InLoopOf bs h' b) →
    ¬ PastExit bs h d ⟨h', 0⟩

/-- The arm of `done` to `t` leaves the loop of `h` for good: `t` is unreachable, or it is
outside the loop, is not `d`, and no path from the loop's exits reaches it before `d`. -/
@[expose] def ArmOut (h d t : Label) : Prop :=
  Unreachable bs t ∨ (¬ InLoopScope bs h ⟨t, 0⟩ ∧ t ≠ d ∧ ¬ PastExit bs h d ⟨t, 0⟩)

/-- What the arm for constructor `i` of `d`, the `done` of the loop of `h`, must do: the
`continue` arm is unreachable, since a `continue` of the loop goes to its latch; every other arm
leaves the loop for good. -/
@[expose] def ArmOk (ro : Roles) (h d : Label) (i : Nat) (t : Label) : Prop :=
  if i = ro.cont then Unreachable bs t else ArmOut bs h d t

/-- (P7) `d`, the `done` of the loop of `h`, holds no instructions: its terminator, the shape's
case instruction, cases on its completion, one arm per constructor, and each arm does what `ArmOk`
asks. -/
@[expose] def Absorbs (s : CompletionShape env) (ro : Roles) (h d : Label) : Prop :=
  ∃ b ∈ bs, b.label = d ∧ b.instrs = #[] ∧ b.term.name = s.caseName ∧
    (∃ p, b.params[0]? = some p ∧ b.term.args[0]? = some p.id) ∧
    b.term.succs.size = ro.all.length ∧
    ∀ (i : Nat) (sv : Target.Raw), b.term.succs[i]? = some sv →
      ArmOk bs ro h d i sv.label

/-- What a record whose head is a block of the body states: its head has a preheader (P1, which
for a loop of the CFG is part of `LoopsSimplified`); if no back edge enters its head, the head
dominates its `done` and every block it leaves for, so that every way into the loop's code
passes through the head; with a `done`, P4 and P7 hold; without one, control never leaves the
loop: every block it leaves for is unreachable, and no point of it leaves the body. -/
@[expose] def RecordHolds (s : CompletionShape env) (ro : Roles) (r : LoopRecord) : Prop :=
  (∃ pre, Preheader bs r.head pre) ∧
    (¬ IsHead bs r.head → (∀ d, r.done = some d → Dom bs ⟨r.head, 0⟩ ⟨d, 0⟩) ∧
      ∀ x, ExitOf bs r.head x → Dom bs ⟨r.head, 0⟩ ⟨x, 0⟩) ∧
    match r.done with
    | some d => Done bs s r.head d ∧ Absorbs bs s ro r.head d
    | none => (∀ x, ExitOf bs r.head x → Unreachable bs x) ∧
        ∀ u, InLoopScope bs r.head u → ¬ Leaves bs u

/-- Every loop of the body has a record of `recs`, and every record whose head is a block of the
body holds. -/
structure LoopExits (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord) : Prop where
  recorded : ∀ h, IsHead bs h → ∃ r ∈ recs, r.head = h
  each : ∀ r ∈ recs, (∃ b ∈ bs, b.label = r.head) → RecordHolds bs s ro r

/-! ## Their decisions

Each check takes what it needs computed once for the body: its transfers `tr`, the points `ep`
that leave it, its loops' heads `hs`, `lo`, the labels of the loop of each head, and `info`, its
dominator tree.  The function's check computes them once (`Body.loopExitsB`). -/

/-- The labels of the scope of `h`, given `lo`: its loop's, or `h` alone if no back edge enters
it. -/
@[expose] def scopeIn (lo : Label → List Label) (h : Label) : List Label :=
  match lo h with
  | [] => [h]
  | L => L

/-- The labels of the blocks that a transfer of `tr` leaves the labels `S` for. -/
@[expose] def exitsIn (tr : List (Point × Label)) (S : List Label) : List Label :=
  ((tr.filter fun (u, l) => S.contains u.label && !S.contains l).map (·.2)).eraseDups

/-- Whether the block `b` is empty and ends in `base.unreachable`. -/
@[expose] def _root_.Strata.Dyn.Block.unreachableB (b : Block env α) : Bool :=
  b.instrs.isEmpty && b.term.name == bn "unreachable"

/-- Whether the block labelled `l` is empty and ends in `base.unreachable`. -/
@[expose] def unreachableB (l : Label) : Bool :=
  (blockAt? bs l).any (·.unreachableB)

/-- Whether some path from the start of the block labelled `x` reaches `u` without passing `d`. -/
@[expose] def avoidsFromB (d x : Label) (u : Point) : Bool :=
  (blockAt? bs x).any fun xb => reachAvoidB (enteredAt bs xb) ⟨d, 0⟩ u

/-- Whether some path from the start of `x` reaches the block `d`, given the transfers `tr`. -/
@[expose] def reachesB (tr : List (Point × Label)) (x d : Label) : Bool :=
  x == d || tr.any fun (y, l) => l == d && avoidsFromB bs d x y

/-- Whether some path from a block of `X` reaches `u` without passing `d`. -/
@[expose] def pastExitB (X : List Label) (d : Label) (u : Point) : Bool :=
  X.any fun x => avoidsFromB bs d x u

/-- The labels of the blocks whose start a path from the start of `x` reaches without passing
`d`, by one search over the successor map `sm`, against which every point is then tested; none
if `x` is no block. -/
@[expose] def regionOf (sm : LabelMap (List Label)) (d x : Label) : LabelMap Unit :=
  if bs.any (·.label == x) then (searchFrom bs sm d x).seen else ∅

/-- Whether a path from the start of a block reaches `u` without passing `d`, given `R`, that
block's `regionOf`. -/
@[expose] def inRegionB (d : Label) (R : LabelMap Unit) (u : Point) : Bool :=
  (blockAt? bs u.label).any fun b => (R.find? u.label).isSome && (lim ⟨d, 0⟩ b).any (u.count ≤ ·)

/-- The region of each block of `X`. -/
@[expose] def regionsOf (sm : LabelMap (List Label)) (d : Label) (X : List Label) :
    List (Label × LabelMap Unit) :=
  X.map fun x => (x, regionOf bs sm d x)

/-- Whether some region of `Rs` reaches `u`. -/
@[expose] def inRegionsB (d : Label) (Rs : List (Label × LabelMap Unit)) (u : Point) : Bool :=
  Rs.any fun (_, R) => inRegionB bs d R u

/-- Whether some path from the start of `x`, whose region is `R`, reaches the block `d`. -/
@[expose] def reachesInB (tr : List (Point × Label)) (x d : Label) (R : LabelMap Unit) : Bool :=
  x == d || tr.any fun (y, l) => l == d && inRegionB bs d R y

/-- Whether `d` is where every way out of the loop that starts at `h` meets (P4), given the
body's transfers `tr`, the points `ep` that leave it, its heads `hs`, their loops `lo`, and `Rs`,
the regions of the blocks the loop leaves for. -/
@[expose] def doneB (tr : List (Point × Label)) (ep : List Point) (hs : List Label)
    (lo : Label → List Label) (s : CompletionShape env) (h d : Label)
    (Rs : List (Label × LabelMap Unit)) : Bool :=
  let S := scopeIn lo h
  (blockAt? bs d).any (fun b => decide ((b.params[0]?.map (·.type)) = some s.ty)) &&
    !S.contains d &&
    ep.all (fun u => !S.contains u.label) &&
    Rs.all (fun (x, R) => unreachableB bs x || reachesInB bs tr x d R) &&
    ep.all (fun u => !inRegionsB bs d Rs u) &&
    ((hs.filter fun h' => h' != h && (lo h').contains h).map (⟨·, 0⟩)).all fun u =>
      !inRegionsB bs d Rs u

/-- Whether the arm of `done` to `t` leaves the scope `S`, whose exits have the regions `Rs`, for
good. -/
@[expose] def armOutB (S : List Label) (Rs : List (Label × LabelMap Unit)) (d t : Label) : Bool :=
  unreachableB bs t || (!S.contains t && t != d && !inRegionsB bs d Rs ⟨t, 0⟩)

/-- Whether the arm for constructor `i` of `d` to `t` does what `ArmOk` asks, given the scope
`S` of the loop and the regions `Rs` of its exits. -/
@[expose] def armOkB (S : List Label) (Rs : List (Label × LabelMap Unit)) (ro : Roles) (d : Label)
    (i : Nat) (t : Label) : Bool :=
  if i = ro.cont then unreachableB bs t else armOutB bs S Rs d t

/-- Whether the block `b` holds no instructions and dispatches on its first parameter with the
case of `s`, with `n` successors, the `i`th of which satisfies `arm i`. -/
@[expose] def _root_.Strata.Dyn.Block.absorbsB (s : CompletionShape env) (n : Nat)
    (arm : Nat → Label → Bool) (b : Block env α) : Bool :=
  b.instrs.isEmpty && b.term.name == s.caseName &&
    (b.params[0]?).any (fun p => b.term.args[0]? == some p.id) &&
    b.term.succs.size == n &&
    (List.range b.term.succs.size).all fun i => (b.term.succs[i]?).all fun sv => arm i sv.label

/-- Whether `d` absorbs the `break` and `continue` of the loop of `h` and forwards the rest (P7),
given `Rs`, the regions of the blocks the loop leaves for. -/
@[expose] def absorbsB (lo : Label → List Label) (s : CompletionShape env) (ro : Roles)
    (h d : Label) (Rs : List (Label × LabelMap Unit)) : Bool :=
  (blockAt? bs d).any (Block.absorbsB s ro.all.length (armOkB bs (scopeIn lo h) Rs ro d))

/-- Whether the head of record `r` is a loop head, or dominates its `done` and every block its
scope leaves for, given the body's transfers, its heads, their loops and its dominator tree. -/
@[expose] def headDominatesB (tr : List (Point × Label)) (hs : List Label) (lo : Label → List Label)
    (info : Option (LabelMap (Block env α) × Tree × AncMap × Nat)) (r : LoopRecord) : Bool :=
  hs.contains r.head ||
    (r.done.all (fun d => domWith bs info ⟨d, 0⟩ r.head)) &&
      (exitsIn tr (scopeIn lo r.head)).all fun x => domWith bs info ⟨x, 0⟩ r.head

/-- Whether the record `r` holds, given the body's transfers, its points that leave, its heads,
their loops, `info`, the body's dominator tree for `domWith`, and `sm`, its successor map.  It
searches once from each block the loop leaves for. -/
@[expose] def recordHoldsB (tr : List (Point × Label)) (ep : List Point) (hs : List Label)
    (lo : Label → List Label) (info : Option (LabelMap (Block env α) × Tree × AncMap × Nat))
    (sm : LabelMap (List Label)) (s : CompletionShape env) (ro : Roles) (r : LoopRecord) : Bool :=
  preheaderB bs (lo r.head) r.head && headDominatesB bs tr hs lo info r &&
    match r.done with
    | some d =>
      let Rs := regionsOf bs sm d (exitsIn tr (scopeIn lo r.head))
      doneB bs tr ep hs lo s r.head d Rs && absorbsB bs lo s ro r.head d Rs
    | none => (exitsIn tr (scopeIn lo r.head)).all (unreachableB bs) &&
        ep.all fun u => !(scopeIn lo r.head).contains u.label

/-- Whether every loop of the body has a record, and every record whose head is a block of the
body holds, given what the body's check computes once. -/
@[expose] def loopExitsWith (tr : List (Point × Label)) (ep : List Point) (hs : List Label)
    (lo : Label → List Label) (info : Option (LabelMap (Block env α) × Tree × AncMap × Nat))
    (sm : LabelMap (List Label)) (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord) :
    Bool :=
  hs.all (fun h => recs.any (·.head == h)) &&
    recs.all fun r => !bs.any (·.label == r.head) ||
      recordHoldsB bs tr ep hs lo info sm s ro r

/-- The loop of a head, looked up in a table of heads and their loops; no loop for any other
label. -/
@[expose] def lookupLoop (tbl : List (Label × List Label)) (h : Label) : List Label :=
  ((tbl.find? (·.1 == h)).map (·.2)).getD []

/-- Whether every loop of the body has a record, and every record whose head is a block of the
body holds.  The transfers, the points that leave, the back edges, every loop, the dominator
tree and the successor map are computed once. -/
@[expose] def loopExitsB (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord) : Bool :=
  let be := backEdges bs
  let tbl := tableOf be (loopsOf bs be)
  loopExitsWith bs (transfers bs) (exitPoints bs) (tbl.map (·.1)) (lookupLoop tbl) (domInfo bs)
    (succMap bs) s ro recs

/-! ## The check with an index

`Body.Index` (`StrataDyn/BodyIndex.lean`) holds, for each label, the transfers into it and out of
its block, each loop's labels as a set and as a list, and the heads whose loops hold it.  The
check below reads them from it, and finds the records of a head through `rm`, the records by
head.  So the check of a record reads only the blocks of its scope, the transfers into and out of
them, and the regions of its exits, where `loopExitsB` scans the body's transfers, its heads and
the records for each record. -/

namespace Index

variable (ix : Index env α)

/-- Whether `x` is in the scope of the loop that starts at `h`: in its loop, or `h` itself if no
back edge enters `h`. -/
@[expose] def inScope (h x : Label) : Bool :=
  if ix.isHead h then ix.inLoop h x else x == h

/-- The labels of the scope of the loop that starts at `h`. -/
@[expose] def scopeList (h : Label) : List Label :=
  if ix.isHead h then ix.loopList h else [h]

/-- `unreachableB`, with the index's blocks by label. -/
@[expose] def unreachableB (l : Label) : Bool :=
  (ix.blocks.find? l).any (·.unreachableB)

/-- `regionOf` of the body's successor map, with the index's blocks by label, successor map and
number of blocks. -/
@[expose] def regionOf (d x : Label) : LabelMap Unit :=
  if (ix.blocks.find? x).isSome then
    (if x == d then ⟨[], ∅, []⟩
     else search ix.succ d ix.size ⟨[x], [x].foldl (fun m l => m.insert l ()) ∅, [x]⟩).seen
  else ∅

/-- `regionsOf` of the body's successor map, with the index. -/
@[expose] def regionsOf (d : Label) (X : List Label) : List (Label × LabelMap Unit) :=
  X.map fun x => (x, ix.regionOf d x)

/-- `inRegionB`, with the index's blocks by label. -/
@[expose] def inRegionB (d : Label) (R : LabelMap Unit) (u : Point) : Bool :=
  (ix.blocks.find? u.label).any fun b =>
    (R.find? u.label).isSome && (lim ⟨d, 0⟩ b).any (u.count ≤ ·)

/-- `inRegionsB`, with the index's blocks by label. -/
@[expose] def inRegionsB (d : Label) (Rs : List (Label × LabelMap Unit)) (u : Point) : Bool :=
  Rs.any fun (_, R) => ix.inRegionB d R u

/-- `reachesInB`, with the index: it reads only the transfers to `d`. -/
@[expose] def reachesInB (x d : Label) (R : LabelMap Unit) : Bool :=
  x == d || (LabelMap.listAt ix.into d).any fun y => ix.inRegionB d R y

/-- `doneB`, with the index: the loops around the one of `h` are the heads whose loops hold
`h`. -/
@[expose] def doneB (ep : List Point) (s : CompletionShape env) (h d : Label)
    (Rs : List (Label × LabelMap Unit)) : Bool :=
  (ix.blocks.find? d).any (fun b => decide ((b.params[0]?.map (·.type)) = some s.ty)) &&
    !ix.inScope h d &&
    ep.all (fun u => !ix.inScope h u.label) &&
    Rs.all (fun (x, R) => ix.unreachableB x || ix.reachesInB x d R) &&
    ep.all (fun u => !ix.inRegionsB d Rs u) &&
    (LabelMap.listAt ix.around h).all fun h' => h' == h || !ix.inRegionsB d Rs ⟨h', 0⟩

/-- `armOutB` of the scope of `h`, with the index. -/
@[expose] def armOutB (h : Label) (Rs : List (Label × LabelMap Unit)) (d t : Label) : Bool :=
  ix.unreachableB t || (!ix.inScope h t && t != d && !ix.inRegionsB d Rs ⟨t, 0⟩)

/-- `armOkB` of the scope of `h`, with the index. -/
@[expose] def armOkB (Rs : List (Label × LabelMap Unit)) (ro : Roles) (h d : Label) (i : Nat)
    (t : Label) : Bool :=
  if i = ro.cont then ix.unreachableB t else ix.armOutB h Rs d t

/-- `absorbsB`, with the index. -/
@[expose] def absorbsB (s : CompletionShape env) (ro : Roles) (h d : Label)
    (Rs : List (Label × LabelMap Unit)) : Bool :=
  (ix.blocks.find? d).any (Block.absorbsB s ro.all.length (ix.armOkB Rs ro h d))

/-- `recordHoldsB` of the body's transfers, heads, loops, dominance and successor map, with the
index.  It computes once the blocks that the scope leaves for. -/
@[expose] def recordHoldsB (ep : List Point) (s : CompletionShape env) (ro : Roles)
    (r : LoopRecord) : Bool :=
  let X := ix.exitsOf (ix.scopeList r.head) (ix.inScope r.head)
  ix.preheaderB r.head &&
    (ix.isHead r.head || (r.done.all fun d => domWith bs ix.info ⟨d, 0⟩ r.head) &&
      X.all fun x => domWith bs ix.info ⟨x, 0⟩ r.head) &&
    match r.done with
    | some d =>
      let Rs := ix.regionsOf d X
      ix.doneB ep s r.head d Rs && ix.absorbsB s ro r.head d Rs
    | none => X.all ix.unreachableB && ep.all fun u => !ix.inScope r.head u.label

/-- `loopExitsWith` of the body's transfers, heads, loops, dominance and successor map, with the
index and `rm`, the records by head: it checks the records of each block's label. -/
@[expose] def loopExitsB (ep : List Point) (s : CompletionShape env) (ro : Roles)
    (rm : LabelMap (List LoopRecord)) : Bool :=
  ix.heads.all (fun h => !(LabelMap.listAt rm h).isEmpty) &&
    bs.all fun b => (LabelMap.listAt rm b.label).all (ix.recordHoldsB bs ep s ro)

end Index

/-- `loopExitsB`, given `rm`, the records of `recs` by head: with the body's index if its labels
are distinct, and as defined if not. -/
@[expose] def loopExitsByB (rm : LabelMap (List LoopRecord)) (s : CompletionShape env)
    (ro : Roles) (recs : List LoopRecord) : Bool :=
  match tree? bs with
  | some tm =>
    let ep := exitPoints bs
    (Index.of bs tm (domInfo bs) ep).loopExitsB bs ep s ro rm
  | none => loopExitsB bs s ro recs

/-- `loopExitsB`, with the records by head computed for the body. -/
@[expose] def loopExitsFastB (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord) :
    Bool :=
  loopExitsByB bs (LabelMap.groupBy (·.head) id recs) s ro recs

end Body

end

namespace Body

variable {env : Env Unit} {α : Type} {bs : List (Block env α)} {ep : List Point}
  {ix : Index env α}

/-! ## The check with an index, proved equal -/

/-- A label that no back edge enters has no loop. -/
theorem loopOf_of_not_mem_heads {h : Label} (hh : h ∉ heads bs) : loopOf bs h = [] := by
  unfold loopOf
  rw [List.flatMap_eq_nil_iff]
  intro e he
  obtain ⟨he, heq⟩ := List.mem_filter.mp he
  refine absurd ?_ hh
  simp only [heads, List.mem_eraseDups, List.mem_map]
  exact ⟨e, he, beq_iff_eq.mp heq⟩

/-- The table of the body's heads and their loops, looked up, is `loopOf`. -/
theorem lookupLoop_table :
    lookupLoop (tableOf (backEdges bs) (loopsOf bs (backEdges bs))) = loopOf bs := by
  funext h
  rw [tableOf_loopsOf, lookupLoop]
  by_cases hh : h ∈ heads bs
  · obtain ⟨p, hp, hpe⟩ : ∃ p ∈ (heads bs).map (fun h => (h, loopOf bs h)), (p.1 == h) = true :=
      ⟨(h, loopOf bs h), List.mem_map.mpr ⟨h, hh, rfl⟩, beq_self_eq_true h⟩
    cases hf : ((heads bs).map fun h => (h, loopOf bs h)).find? (·.1 == h) with
    | none => exact absurd hpe (List.find?_eq_none.mp hf p hp)
    | some q =>
      have hq := List.find?_some hf
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
      have hk : k = h := beq_iff_eq.mp hq
      subst hk
      rfl
  · rw [loopOf_of_not_mem_heads hh]
    have : ((heads bs).map fun h => (h, loopOf bs h)).find? (·.1 == h) = none := by
      rw [List.find?_eq_none]
      intro q hq hqe
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
      exact hh (beq_iff_eq.mp hqe ▸ hk)
    rw [this]
    rfl

/-- The heads of the table of the body's loops are its heads. -/
theorem table_heads :
    (tableOf (backEdges bs) (loopsOf bs (backEdges bs))).map (·.1) = heads bs := by
  rw [tableOf_loopsOf, List.map_map]
  exact List.map_id _

/-- A label has no loop exactly when no back edge enters it. -/
private theorem loopOf_eq_nil_iff {h : Label} :
    loopOf bs h = [] ↔ ¬ ∃ u, (u, h) ∈ backEdges bs := by
  constructor
  · rintro hn ⟨u, hu⟩
    have hh : h ∈ loopOf bs h := mem_loopOf.mpr ⟨u, hu, mem_loopBlocks_self hu⟩
    rw [hn] at hh
    exact List.not_mem_nil hh
  · intro hh
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨u, hu, -⟩ := mem_loopOf.mp hx
    exact hh ⟨u, hu⟩

/-- A label is in the scope of `h`, given `lo`, exactly when it is in `lo h`, or `lo h` is empty
and it is `h`. -/
private theorem mem_scopeIn {lo : Label → List Label} {h x : Label} :
    x ∈ scopeIn lo h ↔ x ∈ lo h ∨ (lo h = [] ∧ x = h) := by
  unfold scopeIn
  cases hL : lo h with
  | nil => simp
  | cons a as => simp

/-- The index tells the scope of each loop as `scopeIn` of `loopOf` lists it. -/
private theorem Index.inScope_eq (hs : ix.Spec bs ep) (h x : Label) :
    ix.inScope h x = (scopeIn (loopOf bs) h).contains x := by
  have hl := Index.inLoop_eq hs h x
  have hn : loopOf bs h = [] ↔ ¬ ix.isHead h = true := by
    rw [loopOf_eq_nil_iff, hs.isHead]
  unfold Index.inScope scopeIn
  cases hL : loopOf bs h with
  | nil =>
    rw [ite_eq_right (hn.mp hL)]
    by_cases hx : x = h <;> simp [hx]
  | cons a as =>
    have hh : ix.isHead h = true := Classical.byContradiction fun hh => by
      rw [hn.mpr hh] at hL
      exact List.cons_ne_nil a as hL.symm
    rw [ite_eq_left hh, hl, hL]

/-- The index lists the scope of each loop as `scopeIn` of `loopOf` does. -/
private theorem Index.mem_scopeList (hs : ix.Spec bs ep) {h x : Label} :
    x ∈ ix.scopeList h ↔ x ∈ scopeIn (loopOf bs) h := by
  rw [← List.contains_iff_mem (as := scopeIn (loopOf bs) h), ← Index.inScope_eq hs]
  unfold Index.scopeList Index.inScope
  by_cases hh : ix.isHead h = true
  · rw [ite_eq_left hh, ite_eq_left hh, Index.mem_loopList hs, Index.inLoop_eq hs,
      List.contains_iff_mem]
  · rw [ite_eq_right hh, ite_eq_right hh]
    by_cases hx : x = h <;> simp [hx]

/-- The index's exits of the scope of `h` are those `exitsIn` lists. -/
private theorem Index.mem_exitsOf_scope (hs : ix.Spec bs ep) {h l : Label} :
    l ∈ ix.exitsOf (ix.scopeList h) (ix.inScope h) ↔
      l ∈ exitsIn (transfers bs) (scopeIn (loopOf bs) h) := by
  rw [Index.mem_exitsOf hs (fun x => by
    rw [Index.mem_scopeList hs, Index.inScope_eq hs, List.contains_iff_mem])]
  simp only [exitsIn, List.mem_eraseDups, List.mem_map, List.mem_filter, Bool.and_eq_true,
    Bool.not_eq_true', Index.inScope_eq hs]
  constructor
  · rintro ⟨u, ht, hu, hl⟩
    exact ⟨(u, l), ⟨ht, hu, hl⟩, rfl⟩
  · rintro ⟨⟨u, l'⟩, ⟨ht, hu, hl⟩, rfl⟩
    exact ⟨u, ht, hu, hl⟩

/-- The index's `unreachableB` is `unreachableB`. -/
private theorem Index.unreachableB_eq (hs : ix.Spec bs ep) (l : Label) :
    ix.unreachableB l = Body.unreachableB bs l := by
  rw [Index.unreachableB, Body.unreachableB, blockAt?, hs.blocks]

/-- The index's `regionOf` is `regionOf` of the body's successor map. -/
private theorem Index.regionOf_eq (hs : ix.Spec bs ep) (d x : Label) :
    ix.regionOf d x = Body.regionOf bs (succMap bs) d x := by
  have hx : (ix.blocks.find? x).isSome = bs.any (·.label == x) := by
    rw [hs.blocks]
    apply Bool.eq_iff_iff.mpr
    rw [List.find?_isSome, List.any_eq_true]
  rw [Index.regionOf, Body.regionOf, hx, hs.succ, hs.size, searchFrom]

/-- The regions of two lists of exits with the same labels have the same elements. -/
private theorem Index.mem_regionsOf (hs : ix.Spec bs ep) {d : Label}
    {X X' : List Label} (hX : ∀ x, x ∈ X ↔ x ∈ X') (p : Label × LabelMap Unit) :
    p ∈ Body.regionsOf bs (succMap bs) d X ↔ p ∈ ix.regionsOf d X' := by
  simp only [Body.regionsOf, Index.regionsOf, Index.regionOf_eq hs, List.mem_map, hX]

/-- The index's `inRegionB` is `inRegionB`. -/
private theorem Index.inRegionB_eq (hs : ix.Spec bs ep) (d : Label) (R : LabelMap Unit)
    (u : Point) : ix.inRegionB d R u = Body.inRegionB bs d R u := by
  rw [Index.inRegionB, Body.inRegionB, blockAt?, hs.blocks]

/-- The index's `inRegionsB` of a list of regions is `inRegionsB` of a list with the same
elements. -/
private theorem Index.inRegionsB_eq (hs : ix.Spec bs ep) {Rs Rs' : List (Label × LabelMap Unit)}
    (hR : ∀ p, p ∈ Rs ↔ p ∈ Rs') (d : Label) (u : Point) :
    ix.inRegionsB d Rs' u = Body.inRegionsB bs d Rs u := by
  unfold Index.inRegionsB Body.inRegionsB
  exact any_eq_of_mem_iff (fun p => (hR p).symm) fun ⟨_, R⟩ => Index.inRegionB_eq hs d R u

/-- The index's `reachesInB` is `reachesInB` of the body's transfers. -/
private theorem Index.reachesInB_eq (hs : ix.Spec bs ep) (x d : Label) (R : LabelMap Unit) :
    ix.reachesInB x d R = Body.reachesInB bs (transfers bs) x d R := by
  unfold Index.reachesInB Body.reachesInB
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, hs.into, Index.inRegionB_eq hs, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨y, hy, hr⟩
    exact ⟨(y, d), hy, rfl, hr⟩
  · rintro ⟨⟨y, l⟩, hy, rfl, hr⟩
    exact ⟨y, hy, hr⟩

/-- The index's `doneB` is `doneB`, with the body's transfers, heads and loops, of a list of
regions with the same elements. -/
private theorem Index.doneB_eq (hs : ix.Spec bs ep) {Rs Rs' : List (Label × LabelMap Unit)}
    (hR : ∀ p, p ∈ Rs ↔ p ∈ Rs') (s : CompletionShape env) (h d : Label) :
    ix.doneB ep s h d Rs' =
      Body.doneB bs (transfers bs) ep (Body.heads bs) (loopOf bs) s h d Rs := by
  have e₁ : (Rs'.all fun (x, R) => ix.unreachableB x || ix.reachesInB x d R) =
      Rs.all fun (x, R) => Body.unreachableB bs x || Body.reachesInB bs (transfers bs) x d R :=
    all_eq_of_mem_iff (fun p => (hR p).symm) fun ⟨x, R⟩ => by
      dsimp only
      rw [Index.unreachableB_eq hs, Index.reachesInB_eq hs]
  have e₂ : ((LabelMap.listAt ix.around h).all fun h' => h' == h || !ix.inRegionsB d Rs' ⟨h', 0⟩) =
      (((Body.heads bs).filter fun h' => h' != h && (loopOf bs h').contains h).map (⟨·, 0⟩)).all
        fun u => !Body.inRegionsB bs d Rs u := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_map, List.mem_filter, Bool.and_eq_true, bne_iff_ne,
      ne_eq, List.contains_iff_mem, hs.around, Index.inRegionsB_eq hs hR, Bool.or_eq_true,
      beq_iff_eq, mem_heads, mem_loopOf]
    constructor
    · rintro hall _ ⟨h', ⟨-, hne, u, hu, hx⟩, rfl⟩
      exact (hall h' ⟨u, hu, hx⟩).resolve_left hne
    · intro hall h' ⟨u, hu, hx⟩
      by_cases hne : h' = h
      · exact .inl hne
      · exact .inr (hall _ ⟨h', ⟨⟨u, hu⟩, hne, u, hu, hx⟩, rfl⟩)
  unfold Index.doneB Body.doneB
  rw [e₁, e₂]
  simp only [Index.inScope_eq hs, Index.inRegionsB_eq hs hR, blockAt?, hs.blocks]

/-- The index's `armOutB` of the scope of `h` is `armOutB` of it, of a list of regions with the
same elements. -/
private theorem Index.armOutB_eq (hs : ix.Spec bs ep) {Rs Rs' : List (Label × LabelMap Unit)}
    (hR : ∀ p, p ∈ Rs ↔ p ∈ Rs') (h d t : Label) :
    ix.armOutB h Rs' d t = Body.armOutB bs (scopeIn (loopOf bs) h) Rs d t := by
  rw [Index.armOutB, Body.armOutB, Index.unreachableB_eq hs, Index.inScope_eq hs,
    Index.inRegionsB_eq hs hR]

/-- The index's `armOkB` for the loop of `h` is `armOkB` of the scope of `h`, given a list of
regions with the same elements. -/
private theorem Index.armOkB_eq (hs : ix.Spec bs ep) {Rs Rs' : List (Label × LabelMap Unit)}
    (hR : ∀ p, p ∈ Rs ↔ p ∈ Rs') (ro : Roles) (h d : Label) (i : Nat) (t : Label) :
    ix.armOkB Rs' ro h d i t = Body.armOkB bs (scopeIn (loopOf bs) h) Rs ro d i t := by
  unfold Index.armOkB Body.armOkB
  rw [Index.unreachableB_eq hs, Index.armOutB_eq hs hR]

/-- The index's `absorbsB` is `absorbsB` of the body's loops, of a list of regions with the same
elements. -/
private theorem Index.absorbsB_eq (hs : ix.Spec bs ep) {Rs Rs' : List (Label × LabelMap Unit)}
    (hR : ∀ p, p ∈ Rs ↔ p ∈ Rs') (s : CompletionShape env) (ro : Roles) (h d : Label) :
    ix.absorbsB s ro h d Rs' = Body.absorbsB bs (loopOf bs) s ro h d Rs := by
  unfold Index.absorbsB Body.absorbsB
  rw [blockAt?, ← hs.blocks]
  congr 2
  funext i t
  exact Index.armOkB_eq hs hR ro h d i t

/-- The index's `recordHoldsB` is `recordHoldsB` of the body's transfers, heads and loops. -/
private theorem Index.recordHoldsB_eq (hs : ix.Spec bs ep) (s : CompletionShape env) (ro : Roles)
    (r : LoopRecord) :
    ix.recordHoldsB bs ep s ro r = Body.recordHoldsB bs (transfers bs) ep (Body.heads bs)
      (loopOf bs) (domInfo bs) (succMap bs) s ro r := by
  have hX : ∀ l, l ∈ exitsIn (transfers bs) (scopeIn (loopOf bs) r.head) ↔
      l ∈ ix.exitsOf (ix.scopeList r.head) (ix.inScope r.head) :=
    fun l => (Index.mem_exitsOf_scope hs).symm
  have hhead : ix.isHead r.head = (Body.heads bs).contains r.head := by
    apply Bool.eq_iff_iff.mpr
    rw [hs.isHead, List.contains_iff_mem, mem_heads]
  have e₁ : ((ix.exitsOf (ix.scopeList r.head) (ix.inScope r.head)).all fun x =>
      domWith bs ix.info ⟨x, 0⟩ r.head) =
        (exitsIn (transfers bs) (scopeIn (loopOf bs) r.head)).all
          fun x => domWith bs (domInfo bs) ⟨x, 0⟩ r.head := by
    rw [hs.info]
    exact all_eq_of_mem_iff (fun l => (hX l).symm) fun _ => rfl
  unfold Index.recordHoldsB Body.recordHoldsB headDominatesB
  dsimp only
  rw [Index.preheaderB_eq hs, hhead, e₁, hs.info]
  congr 1
  cases r.done with
  | some d =>
    dsimp only
    rw [Index.doneB_eq hs (Index.mem_regionsOf hs hX),
      Index.absorbsB_eq hs (Index.mem_regionsOf hs hX)]
  | none =>
    dsimp only
    rw [all_eq_of_mem_iff (fun l => (hX l).symm) (Index.unreachableB_eq hs)]
    simp only [Index.inScope_eq hs]

/-- The index's `loopExitsB` is `loopExitsWith` of the body's transfers, heads and loops, and of
the records `recs`, whose records by head are `rm`. -/
private theorem Index.loopExitsB_eq (hs : ix.Spec bs ep) {rm : LabelMap (List LoopRecord)}
    {recs : List LoopRecord} (hrm : ∀ h r, r ∈ LabelMap.listAt rm h ↔ r ∈ recs ∧ r.head = h)
    (s : CompletionShape env) (ro : Roles) :
    ix.loopExitsB bs ep s ro rm = loopExitsWith bs (transfers bs) ep (Body.heads bs) (loopOf bs)
      (domInfo bs) (succMap bs) s ro recs := by
  unfold Index.loopExitsB loopExitsWith
  congr 1
  · refine all_eq_of_mem_iff (fun h => by rw [hs.heads, mem_heads]) fun h => ?_
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem, hrm, List.any_eq_true,
      beq_iff_eq]
  · apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, hrm, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false,
      beq_iff_eq, Index.recordHoldsB_eq hs]
    constructor
    · intro hall r hr
      by_cases hb : ∃ b ∈ bs, b.label = r.head
      · obtain ⟨b, hb, hbl⟩ := hb
        exact .inr (hall b hb r ⟨hr, hbl.symm⟩)
      · exact .inl fun b hb' hbl => hb ⟨b, hb', hbl⟩
    · intro hall b hb r ⟨hr, hrl⟩
      exact (hall r hr).resolve_left fun hn => hn b hb hrl.symm

/-- `loopExitsByB` gives the same answer as `loopExitsB` on every body, given `rm`, the records
of `recs` by head. -/
theorem loopExitsB_eq_by {rm : LabelMap (List LoopRecord)} {recs : List LoopRecord}
    (hrm : ∀ h r, r ∈ LabelMap.listAt rm h ↔ r ∈ recs ∧ r.head = h) (s : CompletionShape env)
    (ro : Roles) : loopExitsB bs s ro recs = loopExitsByB bs rm s ro recs := by
  unfold loopExitsByB
  split
  next tm ht =>
    dsimp only
    rw [Index.loopExitsB_eq (Index.spec_of ht _) hrm, loopExitsB, lookupLoop_table, table_heads]
  next => rfl

/-- `groupBy` of the records by head lists the records of each head. -/
theorem mem_listAt_groupBy_head {recs : List LoopRecord} (h : Label) (r : LoopRecord) :
    r ∈ LabelMap.listAt (LabelMap.groupBy (·.head) id recs) h ↔ r ∈ recs ∧ r.head = h := by
  rw [LabelMap.mem_listAt_groupBy]
  constructor
  · rintro ⟨r', hr', hh, rfl⟩
    exact ⟨hr', hh⟩
  · exact fun ⟨hr, hh⟩ => ⟨r, hr, hh, rfl⟩

/-- The fast check gives the same answer as `loopExitsB` on every body, so that it runs in its
place.  It is proved before `Func.checkLoopExits` uses the check, because a `@[csimp]` lemma
replaces a definition only in code compiled after it. -/
@[csimp] public theorem loopExitsB_eq_fast : @loopExitsB = @loopExitsFastB := by
  funext env α bs s ro recs
  exact loopExitsB_eq_by mem_listAt_groupBy_head s ro

end Body

public section

variable {env : Env Unit} {α : Type}

/-- P4 and P7 hold in every body of the function for the records `recs`, which name blocks of
the function's bodies, name each head and each `done` once, and never name a `done` as a head; and
the shape is well formed.  A record whose head is a block of a contract clause is rejected: no body
that the check visits holds it, so no check would apply to it. -/
@[expose] def Func.LoopExits (s : CompletionShape env) (recs : List LoopRecord)
    (fn : Func env α) : Prop :=
  ∃ ro, s.roles? = some ro ∧ Body.Every (Body.LoopExits · s ro recs) fn.blocks.toList ∧
    (recs.map (·.head) ++ recs.filterMap (·.done)).Nodup ∧ ∀ r ∈ recs, r.head ∈ fn.bodyLabels

/-- Whether the function holds `Func.LoopExits`, for a function whose bodies have distinct
labels. -/
@[expose] def Func.checkLoopExits (s : CompletionShape env) (recs : List LoopRecord)
    (fn : Func env α) : Bool :=
  match s.roles? with
  | none => false
  | some ro =>
    Body.everyB (Body.loopExitsB · s ro recs) fn.blocks.toList &&
      (recs.map (·.head) ++ recs.filterMap (·.done)).Nodup &&
      recs.all fun r => fn.bodyLabels.contains r.head

/-- `Func.checkLoopExits`, with the records by head computed once for every body, and the
duplicates and the labels found through label sets. -/
@[expose] def Func.checkLoopExitsFast (s : CompletionShape env) (recs : List LoopRecord)
    (fn : Func env α) : Bool :=
  match s.roles? with
  | none => false
  | some ro =>
    let rm := LabelMap.groupBy (·.head) id recs
    let ls := LabelMap.setOf fn.bodyLabels
    Body.everyB (Body.loopExitsByB · rm s ro recs) fn.blocks.toList &&
      (LabelMap.ofDistinct? (recs.map (·.head) ++ recs.filterMap (·.done))).isSome &&
      recs.all fun r => (ls.find? r.head).isSome

/-- The fast check gives the same answer as `Func.checkLoopExits` on every function.  It is
proved here, before `CanonicalSpec.check` uses the check, because a `@[csimp]` lemma replaces a
definition only in code compiled after it. -/
@[csimp] theorem Func.checkLoopExits_eq_fast :
    @Func.checkLoopExits = @Func.checkLoopExitsFast := by
  funext env α s recs fn
  unfold Func.checkLoopExits Func.checkLoopExitsFast
  split
  next => rfl
  next ro _ =>
    dsimp only
    have hb : (fun bs : List (Block env α) => Body.loopExitsB bs s ro recs) =
        fun bs => Body.loopExitsByB bs (LabelMap.groupBy (·.head) id recs) s ro recs :=
      funext fun bs => Body.loopExitsB_eq_by Body.mem_listAt_groupBy_head s ro
    have hd : ∀ ls : List Label, decide ls.Nodup = (LabelMap.ofDistinct? ls).isSome :=
      fun ls => Bool.eq_iff_iff.mpr (by rw [decide_eq_true_iff, LabelMap.ofDistinct?_isSome_iff])
    have hl : ∀ r : LoopRecord,
        fn.bodyLabels.contains r.head = ((LabelMap.setOf fn.bodyLabels).find? r.head).isSome :=
      fun r => Bool.eq_iff_iff.mpr (by rw [List.contains_iff_mem, LabelMap.find?_setOf])
    rw [hb, hd]
    simp only [hl]

/-- (F1) The function's entry block ends in a plain jump to a block that nothing else enters, or it
is empty and ends in `base.unreachable`, so that no code of the function ever runs.  The entry
block's own instructions run before that block: a run whose entry-block instruction transfers
elsewhere, such as an argument binding that fails, never reaches it. -/
@[expose] def Func.Preamble (fn : Func env α) : Prop :=
  ∀ e, fn.blocks[0]? = some e → (e.instrs = #[] ∧ e.term.name = bn "unreachable") ∨
    ∃ b ∈ fn.blocks.toList, Body.EndsIn e b.label ∧ e.term.succs.size = 1 ∧
      ∀ u, Body.Transfer fn.blocks.toList u b.label → u = Body.endOf e

/-- Whether the function holds `Func.Preamble`. -/
@[expose] def Func.checkPreamble (fn : Func env α) : Bool :=
  let bs := fn.blocks.toList
  (fn.blocks[0]?).all fun e =>
    (e.instrs.isEmpty && e.term.name == bn "unreachable") ||
      (e.term.name == bn "jump" && e.term.regions.isEmpty &&
        match e.term.succs.toList with
        | [sv] =>
          bs.any (·.label == sv.label) &&
            (Body.transfers bs).all fun (u, l) => l != sv.label || u == Body.endOf e
        | _ => false)

/-- What a front end asks of `Canonicalize.run` beyond the loop and return blocks: with `shape`, P4 and P7 for
the loop records that `records` reads from a function's annotation; with `preamble`, F1. -/
structure CanonicalSpec (env : Env Unit) (α : Type) where
  shape : Option (CompletionShape env) := none
  records : α → List LoopRecord := fun _ => []
  preamble : Bool := false

/-- What `spec` asks of `g`. -/
@[expose] def CanonicalSpec.Holds (spec : CanonicalSpec env α) (g : Func env α) : Prop :=
  (∀ s, spec.shape = some s → g.LoopExits s (spec.records g.info)) ∧
    (spec.preamble = true → g.Preamble)

/-- Whether `g` holds what `spec` asks, for a function whose bodies have distinct labels. -/
@[expose] def CanonicalSpec.check (spec : CanonicalSpec env α) (g : Func env α) : Bool :=
  (spec.shape.all fun s => g.checkLoopExits s (spec.records g.info)) &&
    (!spec.preamble || g.checkPreamble)

end

end Strata.Dyn
