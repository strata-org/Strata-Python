/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonical
public import StrataDyn.WF
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Reason-carrying loop exits and the preamble

The rest of the canonical form, for a front end whose loops end with a *completion*: a value of a
datatype that says how a construct finished, such as `Normal`, `Break`, `Continue`, `Return v` or
`Raise e`.  For each loop:

* (P4) one block `done(k)`, whose first parameter is the completion, where every way out of the
  loop meets.  What holds when the loop ends by `k` is asserted there;
* (P7) `done` absorbs its own loop's `Break` and `Continue`, and forwards every other completion
  out of the loop.

And for the function:

* (F1) the entry block ends in a plain jump to a block that nothing else enters, or in
  `base.unreachable`.  The precondition is assumed at the start of that block.

The front end supplies two things.  A `CompletionShape` names its completion datatype and the
role of each constructor; the check reads the constructors' order from the environment.  A
`LoopRecord` per loop names its head and its `done`, and the label a labelled `break` carries, if
the language has them.  Every loop has a record; a loop that control never leaves has no `done`.  The records are
untrusted: the check verifies each one.  They are needed because an enclosing loop's `done` also
meets every exit of an inner loop, so the CFG alone cannot tell which `done` belongs to which loop.

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
  `normal` and `continue`: a front end pins its shape with a test.

A labelled exit that leaves through a `finally` between two loops is not expressible: another
loop's label must go straight to the `done`, the head or the latch of a loop around this one, or
to the dedicated exit that the pass puts in front of that `done`.

## Main definitions

* `CompletionShape`, `LoopRecord`: what the front end supplies, and `CompletionShape.roles?`,
  the shape checked against the environment;
* `Body.Done`, `Body.Absorbs`, `Body.LoopExits`: P4, P7, and both with P1 for every record;
* `Func.LoopExits`, `Func.Preamble`: the function properties;
* `Func.checkLoopExits`, `Func.checkPreamble`: their checks, which
  `StrataDyn/LoopExitsProps.lean` proves to decide them;
* `CanonicalSpec`: what a front end asks of `Canonicalize.run`, and its check.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

/-- How a front end represents the way a construct finished: the datatype `data` of type `ty`,
and the constructors of each role, by name: the normal end, `break`, `continue`, and those
forwarded out of every loop, such as `return` and `raise`.  `data`'s case instruction branches on
it, with one successor per constructor, in the constructors' order.  With `labelTest`, `break` and
`continue` carry the label of their loop as their only field, an `base.Int`, and `labelTest` names
a terminal operation on two operands, a label and a constant, whose first successor is taken when
they are equal and the second when not. -/
structure CompletionShape (env : Env Unit) where
  ty : TypeExpr env
  data : Name
  normal : Name
  brk : Name
  cont : Name
  forwarded : List Name
  labelTest : Option Name := none

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
`continue` carry no field, or one with `labelTest`.  So a shape cannot give a role to a constructor
that carries the wrong fields, nor leave a constructor without one.  It does not check whether two
constructors that carry the same fields have their roles swapped, nor the label test's
signature. -/
@[expose] def CompletionShape.roles? (s : CompletionShape env) : Option Roles := do
  let (g, i) ← env.dataOf? s.data
  let m ← g.member? i
  let names := m.ctors.toList.map (·.name)
  let idx (n : Name) : Option Nat := names.idxOf? n
  let ro : Roles := { normal := ← idx s.normal, brk := ← idx s.brk, cont := ← idx s.cont,
                      forwarded := ← s.forwarded.mapM idx }
  let fields := if s.labelTest.isSome then 1 else 0
  let arity (k : Nat) : Nat := (m.ctors[k]?.map (·.args.size)).getD 0
  if ro.all.Nodup && ro.all.length = names.length && arity ro.normal = 0 &&
      arity ro.brk = fields && arity ro.cont = fields then some ro else none

/-- What a front end states about one of its loops: the block it starts at, the block `done` its
exits meet at, and the label its `break` and `continue` carry, if the language has labels.  A loop
that control never leaves has no `done`. -/
structure LoopRecord where
  head : Label
  done : Option Label
  label : Option Int := none
deriving DecidableEq

/-- The value an instruction defines and the integer it holds, if it is an integer constant. -/
@[expose] def Instruction.intConst? : Instruction env α → Option (ValId × Int)
  | .const _ d (.int n) => some (d.id, n)
  | _ => none

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

/-- (P4) `d` is where every way out of the loop that starts at `h` meets: it takes the completion
first; it is outside the loop; no point of the loop leaves the body; every block the loop leaves
for reaches it, unless control never gets there; no path from those blocks returns from the
function before it; and none comes back to the head of a loop around this one before it. -/
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

/-- The block `t` tests the label its first parameter carries against `n` with `lt`, and its
two successors satisfy `own` (equal) and `other` (different). -/
@[expose] def LabelArm (lt : Name) (n : Int) (own other : Label → Prop) (t : Label) : Prop :=
  ∃ b ∈ bs, b.label = t ∧ b.term.name = lt ∧
    ∃ p v s₁ s₂, b.params[0]? = some p ∧ b.term.args = #[p.id, v] ∧
      (∃ i ∈ b.instrs, i.intConst? = some (v, n)) ∧ b.term.succs = #[s₁, s₂] ∧
      own s₁.label ∧ other s₂.label

/-- The record `r'` of `recs` is of a loop around the loop of `r`. -/
@[expose] def Encloses (r r' : LoopRecord) : Prop :=
  r'.head ≠ r.head ∧ InLoopScope bs r'.head ⟨r.head, 0⟩

/-- The block `t` is unreachable, or it is the `done` of a loop around the loop of `r`, or an
empty block that ends in a plain jump to that `done`: where a `break` with another loop's label
goes.  The empty block is the dedicated exit that the pass puts in front of the outer `done`, so
that no code runs on the way. -/
@[expose] def ToOuterDone (recs : List LoopRecord) (r : LoopRecord) (t : Label) : Prop :=
  Unreachable bs t ∨ ∃ r' ∈ recs, Encloses bs r r' ∧ ∃ d, r'.done = some d ∧
    (t = d ∨ ∃ b ∈ bs, b.label = t ∧ b.instrs = #[] ∧ EndsIn b d)

/-- The block `t` is unreachable, or the `done`, the head or the latch of a loop around the loop
of `r`: where a `continue` with another loop's label goes.  `continue outer` goes to the head of
the outer loop, and once the pass has given that loop its latch, to the latch: an empty block of
the loop that ends in a plain jump to its head, so that no code of the loop runs on the way. -/
@[expose] def ToOuterLoop (recs : List LoopRecord) (r : LoopRecord) (t : Label) : Prop :=
  ToOuterDone bs recs r t ∨ ∃ r' ∈ recs, Encloses bs r r' ∧
    (t = r'.head ∨ ∃ b ∈ bs, b.label = t ∧ b.instrs = #[] ∧ EndsIn b r'.head ∧
      InLoopScope bs r'.head ⟨t, 0⟩)

/-- What the arm for constructor `i` of `d`, the `done` of record `r`, must do: the `continue`
arm is unreachable, since a `continue` of the loop goes to its latch; every other arm leaves the
loop for good.  With labels, the `break` and `continue` arms test the label, and send any other
loop's label to a loop around this one.  The `continue` arm may also be unreachable, for a front
end with no labelled `continue` to test. -/
@[expose] def ArmOk (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord)
    (r : LoopRecord) (d : Label) (i : Nat) (t : Label) : Prop :=
  match s.labelTest, r.label with
  | none, none =>
    if i = ro.cont then Unreachable bs t else ArmOut bs r.head d t
  | some lt, some n =>
    if i = ro.cont then
      Unreachable bs t ∨ LabelArm bs lt n (Unreachable bs) (ToOuterLoop bs recs r) t
    else if i = ro.brk then
      LabelArm bs lt n (ArmOut bs r.head d) (ToOuterDone bs recs r) t
    else ArmOut bs r.head d t
  | _, _ => False

/-- (P7) `d`, the `done` of record `r`, cases on its completion with the shape's case instruction,
one arm per constructor, and each arm does what `ArmOk` asks. -/
@[expose] def Absorbs (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord)
    (r : LoopRecord) (d : Label) : Prop :=
  ∃ b ∈ bs, b.label = d ∧ b.term.name = s.caseName ∧
    (∃ p, b.params[0]? = some p ∧ b.term.args[0]? = some p.id) ∧
    b.term.succs.size = ro.all.length ∧
    ∀ (i : Nat) (sv : Target.Raw), b.term.succs[i]? = some sv →
      ArmOk bs s ro recs r d i sv.label

/-- What a record whose head is a block of the body states: its head has a preheader (P1, which
for a loop of the CFG is part of `LoopsSimplified`); if no back edge enters its head, the head
dominates its `done` and every block it leaves for, so that every way into the loop's code
passes through the head; with a `done`, P4 and P7 hold; without one, control never leaves the
loop: every block it leaves for is unreachable, and no point of it leaves the body. -/
@[expose] def RecordHolds (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord)
    (r : LoopRecord) : Prop :=
  (∃ pre, Preheader bs r.head pre) ∧
    (¬ IsHead bs r.head → (∀ d, r.done = some d → Dom bs ⟨r.head, 0⟩ ⟨d, 0⟩) ∧
      ∀ x, ExitOf bs r.head x → Dom bs ⟨r.head, 0⟩ ⟨x, 0⟩) ∧
    match r.done with
    | some d => Done bs s r.head d ∧ Absorbs bs s ro recs r d
    | none => (∀ x, ExitOf bs r.head x → Unreachable bs x) ∧
        ∀ u, InLoopScope bs r.head u → ¬ Leaves bs u

/-- Every loop of the body has a record of `recs`, and every record whose head is a block of the
body holds. -/
structure LoopExits (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord) : Prop where
  recorded : ∀ h, IsHead bs h → ∃ r ∈ recs, r.head = h
  each : ∀ r ∈ recs, (∃ b ∈ bs, b.label = r.head) → RecordHolds bs s ro recs r

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

/-- Whether the block labelled `l` is empty and ends in `base.unreachable`. -/
@[expose] def unreachableB (l : Label) : Bool :=
  (blockAt? bs l).any fun b => b.instrs.isEmpty && b.term.name == bn "unreachable"

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

/-- Whether the block `t` tests its first parameter's label against `n` with `lt`, with
successors that satisfy `own` and `other`. -/
@[expose] def labelArmB (lt : Name) (n : Int) (own other : Label → Bool) (t : Label) : Bool :=
  (blockAt? bs t).any fun b =>
    b.term.name == lt &&
      match b.params[0]?, b.term.args.toList, b.term.succs.toList with
      | some p, [x, v], [s₁, s₂] =>
        x == p.id && b.instrs.any (fun i => i.intConst? == some (v, n)) &&
          own s₁.label && other s₂.label
      | _, _, _ => false

/-- Whether the record `r'` is of a loop around the loop of `r`, given `lo`. -/
@[expose] def enclosesB (lo : Label → List Label) (r r' : LoopRecord) : Bool :=
  r'.head != r.head && (scopeIn lo r'.head).contains r.head

/-- Whether the block `t` is empty and ends in a plain jump to `h`. -/
@[expose] def jumpsToB (t h : Label) : Bool :=
  (blockAt? bs t).any fun b => b.instrs.isEmpty && endsAtB bs (endOf b) h

/-- Whether `t` is unreachable, or the `done` of a loop around the loop of `r`, or an empty block
that ends in a plain jump to it. -/
@[expose] def toOuterDoneB (lo : Label → List Label) (recs : List LoopRecord) (r : LoopRecord)
    (t : Label) : Bool :=
  unreachableB bs t || recs.any fun r' => enclosesB lo r r' &&
    r'.done.any fun d => t == d || jumpsToB bs t d

/-- Whether `t` is unreachable, or the `done`, the head or the latch of a loop around the loop of
`r`. -/
@[expose] def toOuterLoopB (lo : Label → List Label) (recs : List LoopRecord) (r : LoopRecord)
    (t : Label) : Bool :=
  toOuterDoneB bs lo recs r t || recs.any fun r' => enclosesB lo r r' &&
    (r'.head == t || (jumpsToB bs t r'.head && (scopeIn lo r'.head).contains t))

/-- Whether the arm for constructor `i` of `d` to `t` does what `ArmOk` asks, given the scope
`S` of `r`'s loop and the regions `Rs` of its exits. -/
@[expose] def armOkB (lo : Label → List Label) (S : List Label)
    (Rs : List (Label × LabelMap Unit)) (s : CompletionShape env)
    (ro : Roles) (recs : List LoopRecord) (r : LoopRecord) (d : Label) (i : Nat) (t : Label) :
    Bool :=
  match s.labelTest, r.label with
  | none, none => if i = ro.cont then unreachableB bs t else armOutB bs S Rs d t
  | some lt, some n =>
    if i = ro.cont then
      unreachableB bs t || labelArmB bs lt n (unreachableB bs) (toOuterLoopB bs lo recs r) t
    else if i = ro.brk then labelArmB bs lt n (armOutB bs S Rs d) (toOuterDoneB bs lo recs r) t
    else armOutB bs S Rs d t
  | _, _ => false

/-- Whether `d` absorbs its own loop's `break` and `continue` and forwards the rest (P7), given
`Rs`, the regions of the blocks the loop leaves for. -/
@[expose] def absorbsB (lo : Label → List Label) (s : CompletionShape env) (ro : Roles)
    (recs : List LoopRecord) (r : LoopRecord) (d : Label) (Rs : List (Label × LabelMap Unit)) :
    Bool :=
  let S := scopeIn lo r.head
  (blockAt? bs d).any fun b =>
    b.term.name == s.caseName &&
      (b.params[0]?).any (fun p => b.term.args[0]? == some p.id) &&
      b.term.succs.size == ro.all.length &&
      (List.range b.term.succs.size).all fun i =>
        (b.term.succs[i]?).all fun sv => armOkB bs lo S Rs s ro recs r d i sv.label

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
    (sm : LabelMap (List Label)) (s : CompletionShape env) (ro : Roles) (recs : List LoopRecord)
    (r : LoopRecord) : Bool :=
  preheaderB bs (lo r.head) r.head && headDominatesB bs tr hs lo info r &&
    match r.done with
    | some d =>
      let Rs := regionsOf bs sm d (exitsIn tr (scopeIn lo r.head))
      doneB bs tr ep hs lo s r.head d Rs && absorbsB bs lo s ro recs r d Rs
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
      recordHoldsB bs tr ep hs lo info sm s ro recs r

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

end Body

/-- P4 and P7 hold in every body of the function for the records `recs`, which name blocks
of the function, each head and each `done` once, and the shape is well formed. -/
@[expose] def Func.LoopExits (s : CompletionShape env) (recs : List LoopRecord)
    (fn : Func env α) : Prop :=
  ∃ ro, s.roles? = some ro ∧ Body.Every (Body.LoopExits · s ro recs) fn.blocks.toList ∧
    (recs.map (·.head)).Nodup ∧ (recs.filterMap (·.done)).Nodup ∧
    ∀ r ∈ recs, r.head ∈ fn.labels

/-- Whether the function holds `Func.LoopExits`, for a function whose bodies have distinct
labels. -/
@[expose] def Func.checkLoopExits (s : CompletionShape env) (recs : List LoopRecord)
    (fn : Func env α) : Bool :=
  match s.roles? with
  | none => false
  | some ro =>
    Body.everyB (Body.loopExitsB · s ro recs) fn.blocks.toList &&
      (recs.map (·.head)).Nodup && (recs.filterMap (·.done)).Nodup &&
      recs.all fun r => fn.labels.contains r.head

/-- (F1) The function's entry block ends in a plain jump to a block that nothing else enters, or it
is empty and ends in `base.unreachable`, so that no code of the function ever runs.  So the block
after it starts where every run of the body does. -/
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
