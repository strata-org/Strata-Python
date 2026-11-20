/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.CanonicalProps
public import StrataDyn.LoopExitsProps
public import StrataDyn.DDM
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Putting a function in canonical form

`Canonicalize.canonicalize` puts a function in the canonical form of
`StrataDyn/Canonical.lean`, as LLVM's LoopSimplify does for its loops.  It only adds
*forwarding blocks*: a block that takes the parameters of a block `t`, has no instructions, and
jumps to `t` with them.  It then sends some of the transfers to `t` to the forwarding block
instead.  So control reaches the same blocks
with the same values, one `jump` later.  That the pass changes nothing else is tested, not
proved: an oracle in the tests (`StrataDynTest/Unforward.lean`) removes the forwarding blocks from
the result and compares what is left with the input.

1. In the function's own body, unless it already leaves through at most one block, outside
   every loop, a forwarding block `post` takes every transfer to the exit, and returns what it
   receives (F2).
2. In every body, inner regions first, it fixes loop properties round by round, until none is
   left to fix.  A round gives every loop the same kind of block, smallest loop first:
   * a loop without a latch gets one, which takes every back edge (P2);
   * a loop without a preheader gets one, which takes every entry from outside (P1);
   * a block that a transfer leaves a loop for, and that code outside the loop also enters, gets
     a forwarding block that takes the loop's transfers (P3).

Step 1 comes first, so that a return from inside a loop becomes a transfer to `post`, which
step 2 then gives a dedicated exit.  A function that is canonical already comes back as it is,
without either step.  A loop inside a region that leaves the region is not fixed:
the region's exit is not a block, and its type is the region's.

`Canonicalize.run` takes a well-formed function, and checks the result: it gives the function
with proofs that it is well formed, canonical, and that every loop has one entry
(`Func.Reducible`), or a failure that says which does not hold.  For the last, a depth-first
order suggests a rank of the labels, and a proved check confirms that every transfer that is not
a back edge goes up in it.

A front end whose loops end with a completion also passes a `CanonicalSpec`: its completion shape, how to
read the loop records from a function's annotation, and whether the preamble is asked for
(`StrataDyn/LoopExits.lean`).  `run` then also gives a preheader to every recorded loop that
the CFG does not see, and its result carries proofs of P4, P7 and F1 (`CanonicalSpec.Holds`).  The pass
does not build `done`: only the front end knows why a loop was left.

## Main definitions

* `Canonicalize.canonicalize`: the pass;
* `Canonicalize.check`: the check alone, which never changes the function;
* `Canonicalize.run`: the pass, and `check` of its result;
* `Canonicalize.runModule`, `Canonicalize.checkModule`: `run` and `check` on every function of a
  module.
-/

namespace Strata.Dyn

public section

variable {env : Env Unit} {α : Type}

namespace Canonicalize

/-! ## Fresh labels and values -/

/-- What the pass allocates from: the labels taken in the function, and its value names, by
id.  A new value's id is the number of names so far.  `takenNames` holds the names of `names`,
and `nextLabel` and `nextName` the next suffix to try for each base, so that a fresh label or
name costs no scan of the function.  Labels and names are only ever added, so starting from the
next suffix finds the same label or name as starting from 0. -/
structure Fresh where
  labels : Std.HashSet Label
  names : Array Name
  takenNames : Std.HashSet Name
  nextLabel : Std.HashMap String Nat := {}
  nextName : Std.HashMap Name Nat := {}

/-- An allocator with nothing taken, to leave in place of one that is taken out to be updated. -/
@[expose] def Fresh.empty : Fresh := { labels := {}, names := #[], takenNames := {} }

/-- What the pass allocates from in a function with the labels `labels` and the value names
`names`. -/
@[expose] def Fresh.ofFunc (labels : List Label) (names : Array Name) : Fresh :=
  { labels := Std.HashSet.ofList labels, names, takenNames := Std.HashSet.ofList names.toList }

/-- The first label `base.k`, from `k`, that `taken` does not hold, trying at most `fuel`. -/
@[expose] def firstLabel (taken : Std.HashSet Label) (base : String) : (fuel k : Nat) → Label × Nat
  | 0, k => (⟨.num (.str .base base) k⟩, k)
  | f + 1, k =>
    let l : Label := ⟨.num (.str .base base) k⟩
    if taken.contains l then firstLabel taken base f (k + 1) else (l, k)

/-- The first name `stem.k`, from `k`, that `taken` does not hold, trying at most `fuel`. -/
@[expose] def firstName (taken : Std.HashSet Name) (stem : Name) : (fuel k : Nat) → Name × Nat
  | 0, k => (.num stem k, k)
  | f + 1, k =>
    if taken.contains (.num stem k) then firstName taken stem f (k + 1) else (.num stem k, k)

/-- A label `base.k` that no block of the function has. -/
@[expose] def Fresh.label (st : Fresh) (base : String) : Label × Fresh :=
  let (l, k) := firstLabel st.labels base (st.labels.size + 1) (st.nextLabel.getD base 0)
  (l, { st with labels := st.labels.insert l, nextLabel := st.nextLabel.insert base (k + 1) })

/-- A new value of type `t`, named after `stem`. -/
@[expose] def Fresh.value (st : Fresh) (stem : Name) (t : TypeExpr env) : ValDecl env × Fresh :=
  let (n, k) := firstName st.takenNames stem (st.names.size + 1) (st.nextName.getD stem 0)
  let st' : Fresh :=
    { st with
      names := st.names.push n
      takenNames := st.takenNames.insert n
      nextName := st.nextName.insert stem (k + 1) }
  (⟨⟨st.names.size⟩, t⟩, st')

/-- New values with the types of `ps`, each named after the one it copies. -/
@[expose] def Fresh.copies (st : Fresh) (ps : Array (ValDecl env)) : Array (ValDecl env) × Fresh :=
  ps.foldl (init := (#[], st)) fun (acc, st) d =>
    let stem := match st.names[d.id.id]? with
      | some (Name.num s _) => s
      | some n => n
      | none => .str .base "v"
    let (d', st) := st.value stem d.type
    (acc.push d', st)

/-- A forwarding block to `t`, labelled `base.k`: it takes `t`'s parameters and jumps to `t`
with them. -/
@[expose] def Fresh.forward [base ≼ env] (st : Fresh) (base : String) (t : Block env α) :
    Block env α × Fresh :=
  let (l, st) := st.label base
  let (ps, st) := st.copies t.params
  ({ label := l, params := ps, instrs := #[], term := .jump t.info ⟨t.label, ps.map (·.id)⟩,
     info := t.info }, st)

/-! ## Redirecting transfers -/

/-- `s`, sent to `l` if `p s`. -/
@[expose] def redirectSucc (p : Target.Raw → Bool) (l : Label) (s : Target.Raw) : Target.Raw :=
  if p s then { s with label := l } else s

/-- The block, with `f` applied to each successor of its instructions and its terminator.
Successors inside their regions are left alone: they belong to other bodies. -/
@[expose] def Block.mapSuccs (f : Target.Raw → Target.Raw) (b : Block env α) : Block env α :=
  { b with
    instrs := b.instrs.map fun
      | .const info d c => .const info d c
      | .apply info d r ta args succs regions => .apply info d r ta args (succs.map f) regions
    term := match b.term with
      | .apply info r ta args succs regions => .apply info r ta args (succs.map f) regions }

/-- The blocks, with each transfer of block `b` that `p b` picks sent to `l`. -/
@[expose] def redirect (bs : List (Block env α)) (p : Block env α → Target.Raw → Bool)
    (l : Label) : List (Block env α) :=
  bs.map fun b => Block.mapSuccs (redirectSucc (p b) l) b

/-! ## The steps -/

/-- The body's index (`StrataDyn/BodyIndex.lean`), built once, if its labels are distinct. -/
@[expose] def loopIndex? (bs : List (Block env α)) : Option (Body.Index env α) :=
  (Body.tree? bs).map fun tm => Body.Index.of bs tm (Body.domInfo bs) (Body.exitPoints bs)

/-- The heads of the body's loops, each with the labels of its loop, smallest loop first, read
from the index `ix`.  The heads come in the order of their first back edge, and loops of the same
size keep that order, as in `loopsInnerFirst`. -/
@[expose] def loopsOfIndex (ix : Body.Index env α) : List (Label × List Label) :=
  let loops := ix.heads.reverse.map fun h => let L := ix.loopList h; (L.length, h, L)
  (loops.mergeSort fun a b => a.1 ≤ b.1).map (·.2)

/-- Whether the body leaves through its exit from at most one block, which ends in a plain jump
and is in no loop.  A body whose labels are not distinct, which a well-formed function does not
have, counts as done: `run` never gives one to the pass, and given one directly, the pass leaves
it as it is, and the result is not well formed. -/
@[expose] def exitDone (bs : List (Block env α)) : Bool :=
  match loopIndex? bs with
  | none => true
  | some ix =>
    Body.oneExitB bs && (Body.exitPoints bs).all fun u => (ix.around.find? u.label).isNone

/-- Step 1: unless `exitDone` holds, a block `post` that takes every transfer to the exit and
returns what it receives.  `retType` is what the body returns. -/
@[expose] def oneExit [base ≼ env] (st : Fresh) (retType : TypeExpr env) (info : α)
    (bs : List (Block env α)) : List (Block env α) × Fresh :=
  if exitDone bs then (bs, st)
  else
    let (l, st) := st.label "post"
    let (r, st) := st.value (.str .base "ret") retType
    let post : Block env α :=
      { label := l, params := #[r], instrs := #[], term := .ret info r.id, info }
    (redirect bs (fun _ s => s.label == Label.exit) l ++ [post], st)

/-- The heads of the body's loops, each with the labels of its loop, smallest loop first, given
the body's back edges `be`.  A loop nested in another is a strict part of it, so inner loops come
first. -/
@[expose] def loopsInnerFirst (be : List (Point × Label)) (bs : List (Block env α)) :
    List (Label × List Label) :=
  let loops := (Body.tableOf be (Body.loopsOf bs be)).map fun (h, L) => (L.eraseDups.length, h, L)
  (loops.mergeSort fun a b => a.1 ≤ b.1).map (·.2)

/-- One fix of a loop property of the body, if one is needed, which `fixRound` uses as a
fallback: of the loops without a latch, a preheader or dedicated exits, the smallest gets the
forwarding block it lacks.  So an inner loop is finished first, and its dedicated exits can serve
the loops around it.  The back edges and the transfers are computed once. -/
@[expose] def fixOne [base ≼ env] (st : Fresh) (bs : List (Block env α)) :
    Option (List (Block env α) × Fresh) :=
  let be := Body.backEdges bs
  let tr := Body.transfers bs
  (loopsInnerFirst be bs).findSome? fun (h, L) =>
    (Body.blockAt? bs h).bind fun hb =>
      let latchOk := Body.theOneB ((be.filter (·.2 == h)).map (·.1)) (Body.endsAtB bs · h)
      let preOk := Body.theOneB
        ((tr.filter fun (u, l) => l == h && !L.contains u.label).map (·.1)) (Body.endsAtB bs · h)
      if !latchOk then
        let (lb, st) := st.forward "latch" hb
        some (redirect bs (fun b s => L.contains b.label && s.label == h) lb.label ++ [lb], st)
      else if !preOk then
        let (pb, st) := st.forward "pre" hb
        some (redirect bs (fun b s => !L.contains b.label && s.label == h) pb.label ++ [pb], st)
      else
        let exits := (tr.filter fun (u, l) => L.contains u.label && !L.contains l).map (·.2)
        exits.findSome? fun x =>
          if tr.any fun (w, l) => l == x && !L.contains w.label then
            (Body.blockAt? bs x).map fun xb =>
              let (eb, st) := st.forward "loopexit" xb
              (redirect bs (fun b s => L.contains b.label && s.label == x) eb.label ++ [eb], st)
          else none

/-! ## One round, without scans of the body

A round reads the body through maps built once, and makes all its redirections in one pass over
the blocks, so that its cost grows with the size of the body and not with the number of loops
times that size.  It makes the same blocks, in the same order, with the same labels, as fixing
the loops one at a time with `redirect`.  Latches and preheaders of different loops redirect
transfers to different heads, so they never redirect the same transfer.  Exits keep the maps up
to date as they go, so that a loop that shares a block with one fixed before it sees the body as
those fixes left it, and a transfer redirected twice goes straight to its last new block. -/

/-- The body as a round reads it: each block by its label, each block's position, the points
that transfer to each label, and each block's transfers, both in the order of `Body.transfers`,
and the points that back edges to each head leave from. -/
structure Info (env : Env Unit) (α : Type) where
  blocks : Std.HashMap Label (Block env α)
  pos : Std.HashMap Label Nat
  into : Std.HashMap Label (Array Point)
  outOf : Std.HashMap Label (Array (Point × Label))
  back : Std.HashMap Label (Array Point)

/-- `m` with `x` pushed onto the array under `k`, without copying that array. -/
@[expose] def pushAt {β : Type} (m : Std.HashMap Label (Array β)) (k : Label) (x : β) :
    Std.HashMap Label (Array β) :=
  if m.contains k then m.modify k (·.push x) else m.insert k #[x]

/-- `Info` of the body `bs`, whose transfers are `tr` and whose back edges are `be`. -/
@[expose] def Info.of (bs : List (Block env α)) (tr be : List (Point × Label)) : Info env α :=
  { blocks := bs.foldl (init := {}) fun m b => m.insert b.label b
    pos := (bs.zipIdx).foldl (init := {}) fun m (b, i) => m.insert b.label i
    into := tr.foldl (init := {}) fun m (u, l) => pushAt m l u
    outOf := tr.foldl (init := {}) fun m (u, l) => pushAt m u.label (u, l)
    back := be.foldl (init := {}) fun m (u, h) => pushAt m h u }

/-- `I` after the transfers of block `b` to `t` are sent to `e`: its transfer maps follow the
redirection, but its blocks stay as the round found them, so `Info.endsAt`, `needsLatch` and
`needsPre` must not read a block after a redirection of it. -/
@[expose] def Info.redirect (I : Info env α) (b t e : Label) : Info env α :=
  let outs := I.outOf.getD b #[]
  let moved := (outs.filter (·.2 == t)).map (·.1)
  { I with
    outOf := I.outOf.insert b (outs.map fun (u, l) => if l == t then (u, e) else (u, l))
    into := moved.foldl (init := I.into.insert t ((I.into.getD t #[]).filter (·.label != b)))
      fun m u => pushAt m e u }

/-- `I` with the new block `eb`, at position `k`, which jumps to `x`. -/
@[expose] def Info.addForward (I : Info env α) (eb : Block env α) (k : Nat) (x : Label) :
    Info env α :=
  let u : Point := ⟨eb.label, eb.instrs.size⟩
  { I with
    blocks := I.blocks.insert eb.label eb
    pos := I.pos.insert eb.label k
    outOf := I.outOf.insert eb.label #[(u, x)]
    into := pushAt I.into x u }

/-- `Body.endsAtB`, by the block map of `I`. -/
@[expose] def Info.endsAt (I : Info env α) (u : Point) (l : Label) : Bool :=
  (I.blocks.get? u.label).any (·.endsAtB u.count l)

/-- Whether the loop of `h` needs a latch: no single back edge, ending in a plain jump. -/
@[expose] def Info.needsLatch (I : Info env α) (h : Label) : Bool :=
  !Body.theOneB (I.back.getD h #[]).toList (I.endsAt · h)

/-- Whether the loop of `h`, whose labels are `S`, needs a preheader. -/
@[expose] def Info.needsPre (I : Info env α) (h : Label) (S : Std.HashSet Label) : Bool :=
  !Body.theOneB ((I.into.getD h #[]).toList.filter fun u => !S.contains u.label) (I.endsAt · h)

/-- The labels of `L`, each once, in the order of the body. -/
@[expose] def Info.inOrder (I : Info env α) (L : List Label) : List Label :=
  let seen := (L.foldl (init := (#[], (∅ : Std.HashSet Label))) fun (acc, s) l =>
    if s.contains l then (acc, s) else (acc.push l, s.insert l)).1
  (seen.toList.mergeSort fun a b => I.pos.getD a 0 ≤ I.pos.getD b 0)

/-- The exits to fix of the loop whose labels are `L`, by the maps of `I`: the targets of the
loop's transfers out of it, each once, in the order of the body's transfers, that code outside
the loop also enters. -/
@[expose] def Info.exitsToFix (I : Info env α) (L : List Label) : List Label :=
  let S : Std.HashSet Label := Std.HashSet.ofList L
  let outs := (I.inOrder L).flatMap fun b => (I.outOf.getD b #[]).toList
  let xs := (outs.foldl (init := (#[], (∅ : Std.HashSet Label))) fun (acc, seen) (_, l) =>
    if S.contains l || seen.contains l then (acc, seen) else (acc.push l, seen.insert l)).1
  xs.toList.filter fun x => (I.into.getD x #[]).any fun w => !S.contains w.label

/-- The transfers that a round redirects: by the label of the block that transfers, and the
label it transfers to, the label of the new block that takes it. -/
abbrev Redirects := Std.HashMap (Label × Label) Label

/-- The successor `s` of block `b`, sent to the block that `r` names for it, if any. -/
@[expose] def redirectBy (r : Redirects) (b : Label) (s : Target.Raw) : Target.Raw :=
  match r.get? (b, s.label) with
  | some l => { s with label := l }
  | none => s

/-- The blocks, with each transfer that `r` names sent to its new block, in one pass.  Transfers
inside their regions are left alone, as `redirect` leaves them. -/
@[expose] def redirectAll (bs : List (Block env α)) (r : Redirects) : List (Block env α) :=
  if r.isEmpty then bs
  else bs.map fun b => Block.mapSuccs (redirectBy r b.label) b

/-- What `addExits` carries: the body as it is so far, as maps; its number of blocks; for each
transfer redirected so far, by its block and its original target, its new target, and the inverse,
by its block and its new target, its original target; the new blocks; the allocator; the exit
blocks added, by the target each forwards to; whether some loop was fixed; and the labels of the
loops fixed.  The redirections are made on the blocks once, at the end of the round. -/
structure ExitsAcc (env : Env Unit) (α : Type) where
  info : Info env α
  count : Nat
  cur : Redirects
  orig : Redirects
  added : Array (Block env α)
  st : Fresh
  exitsTo : Std.HashMap Label (Array Label)
  any : Bool
  taken : Std.HashSet Label

/-- `acc` after the transfers of block `b` to `t` are sent to `e`: in its maps, and in the
redirections, composed with an earlier one that sent them to `t`. -/
@[expose] def ExitsAcc.redirect (acc : ExitsAcc env α) (b t e : Label) : ExitsAcc env α :=
  let o := acc.orig.getD (b, t) t
  { acc with
    info := acc.info.redirect b t e
    cur := acc.cur.insert (b, o) e
    orig := (acc.orig.erase (b, t)).insert (b, e) o }

/-- Dedicated exits for the loops `loops`, smallest first, with `I` read from the body at the
start of the round.  A loop that shares a block with a loop already fixed sees the body as the
fixes so far left it, and holds the exit blocks added for its targets inside it.  A loop with a
head among its exits waits for a later round. -/
@[expose] def addExits [base ≼ env] (heads : Std.HashSet Label) (I : Info env α) :
    List (Label × List Label) → ExitsAcc env α → ExitsAcc env α
  | [], acc => acc
  | (_, L₀) :: loops, acc =>
    let overlap := L₀.any acc.taken.contains
    let (L, J) :=
      if overlap then
        (L₀ ++ L₀.flatMap fun x => (acc.exitsTo.getD x #[]).toList, acc.info)
      else (L₀, I)
    let xs := J.exitsToFix L
    if xs.isEmpty || xs.any heads.contains then addExits heads I loops acc
    else
      -- Read what the fixes need from `J` before they change `acc.info`, so that `J`, which may
      -- be `acc.info` itself, is no longer held and the maps are changed in place.
      let srcs := J.inOrder L
      let targets := xs.filterMap fun x => (J.blocks.get? x).map (x, ·)
      -- The allocator is carried beside `acc`, not in it, so that it is updated in place.
      let st := acc.st
      let (acc, st) := targets.foldl (init := ({ acc with st := Fresh.empty }, st))
        fun (acc, st) (x, xb) =>
          let (eb, st) := st.forward "loopexit" xb
          let froms := srcs.filter fun b =>
            (acc.info.outOf.getD b #[]).any (·.2 == x)
          let acc := froms.foldl (init := acc) fun acc b => acc.redirect b x eb.label
          ({ acc with
            info := acc.info.addForward eb acc.count x
            count := acc.count + 1
            added := acc.added.push eb
            exitsTo := acc.exitsTo.insert x ((acc.exitsTo.getD x #[]).push eb.label) }, st)
      let acc := { acc with st }
      addExits heads I loops
        { acc with any := true, taken := L.foldl (init := acc.taken) fun t l => t.insert l }

/-- One round of fixes, if one is needed: a latch for every loop without one; or else a
preheader for every loop without one; or else dedicated exits for every loop, smallest first.
A loop with a head among its exits waits, and if no loop could be fixed this way, `fixOne` makes
one fix.  This happens when a loop's latch lies in a loop nested in it: that inner loop then
leaves to the outer head. -/
@[expose] def fixRound [base ≼ env] (st : Fresh) (bs : List (Block env α)) :
    Option (List (Block env α) × Fresh) :=
  -- A body whose labels are not distinct, which a well-formed function does not have, gets no
  -- round: the pass leaves it as it is, and the result is not well formed.
  match loopIndex? bs with
  | none => none
  | some ix =>
  let (be, tr, loops) := (ix.be, ix.tr, loopsOfIndex ix)
  let I := Info.of bs tr be
  let needLatch := loops.filter fun (h, _) => I.needsLatch h
  if !needLatch.isEmpty then
    let (r, added, st) := needLatch.foldl (init := (({} : Redirects), (#[] : Array (Block env α)), st))
      fun (r, added, st) (h, L) =>
        match I.blocks.get? h with
        | none => (r, added, st)
        | some hb =>
          let S : Std.HashSet Label := Std.HashSet.ofList L
          let (lb, st) := st.forward "latch" hb
          let r := ((I.into.getD h #[]).filter fun u => S.contains u.label).foldl (init := r)
            fun r u => r.insert (u.label, h) lb.label
          (r, added.push lb, st)
    some (redirectAll bs r ++ added.toList, st)
  else
    let sets := loops.map fun (h, L) => (h, L, (Std.HashSet.ofList L : Std.HashSet Label))
    let needPre := sets.filter fun (h, _, S) => I.needsPre h S
    if !needPre.isEmpty then
      let (r, added, st) := needPre.foldl (init := (({} : Redirects), (#[] : Array (Block env α)), st))
        fun (r, added, st) (h, _, S) =>
          match I.blocks.get? h with
          | none => (r, added, st)
          | some hb =>
            let (pb, st) := st.forward "pre" hb
            let r := ((I.into.getD h #[]).filter fun u => !S.contains u.label).foldl (init := r)
              fun r u => r.insert (u.label, h) pb.label
            (r, added.push pb, st)
      some (redirectAll bs r ++ added.toList, st)
    else
      let heads : Std.HashSet Label := Std.HashSet.ofList (loops.map (·.1))
      let acc := addExits heads I loops
        { info := I, count := bs.length, cur := {}, orig := {}, added := #[], st, exitsTo := {},
          any := false, taken := {} }
      if acc.any then some (redirectAll (bs ++ acc.added.toList) acc.cur, acc.st)
      else if loops.all fun x => (I.exitsToFix x.2).isEmpty then none
      else fixOne st bs

/-- Step 2 on one body: `fixRound`, until it finds nothing to fix, at most `fuel` times. -/
@[expose] def simplifyLoops [base ≼ env] (st : Fresh) (bs : List (Block env α)) :
    (fuel : Nat) → List (Block env α) × Fresh
  | 0 => (bs, st)
  | f + 1 =>
    match fixRound st bs with
    | none => (bs, st)
    | some (bs', st') => simplifyLoops st' bs' f

/-- Step 2, with fuel for three rounds per transfer.  The bound is not proved: if the fuel runs
out, the body is left unfinished, and `run` reports that the result is not canonical. -/
@[expose] def simplifyBody [base ≼ env] (st : Fresh) (bs : List (Block env α)) :
    List (Block env α) × Fresh :=
  simplifyLoops st bs (3 * (Body.transfers bs).length + 3)

/-! ## Every body -/

mutual

/-- The instruction, with `f` applied to every body nested in it, inner ones first. -/
@[expose] def Instruction.mapBodies (f : Fresh → List (Block env α) → List (Block env α) × Fresh)
    (st : Fresh) : Instruction env α → Instruction env α × Fresh
  | .const info d c => (.const info d c, st)
  | .apply info d r ta args succs ⟨regions⟩ =>
    let (rs, st) := Region.mapBodiesList f st regions
    (.apply info d r ta args succs ⟨rs⟩, st)

/-- `Instruction.mapBodies` of each. -/
@[expose] def Instruction.mapBodiesList
    (f : Fresh → List (Block env α) → List (Block env α) × Fresh) (st : Fresh) :
    List (Instruction env α) → List (Instruction env α) × Fresh
  | [] => ([], st)
  | i :: is =>
    let (i, st) := Instruction.mapBodies f st i
    let (is, st) := Instruction.mapBodiesList f st is
    (i :: is, st)

/-- The terminator, with `f` applied to every body nested in it, inner ones first. -/
@[expose] def Terminator.mapBodies (f : Fresh → List (Block env α) → List (Block env α) × Fresh)
    (st : Fresh) : Terminator env α → Terminator env α × Fresh
  | .apply info r ta args succs ⟨regions⟩ =>
    let (rs, st) := Region.mapBodiesList f st regions
    (.apply info r ta args succs ⟨rs⟩, st)

/-- The blocks, with `f` applied to every body nested in them. -/
@[expose] def Block.mapBodiesList (f : Fresh → List (Block env α) → List (Block env α) × Fresh)
    (st : Fresh) : List (Block env α) → List (Block env α) × Fresh
  | [] => ([], st)
  | ⟨l, ps, ⟨is⟩, t, info⟩ :: bs =>
    let (is, st) := Instruction.mapBodiesList f st is
    let (t, st) := Terminator.mapBodies f st t
    let (bs, st) := Block.mapBodiesList f st bs
    (⟨l, ps, ⟨is⟩, t, info⟩ :: bs, st)

/-- The region, with `f` applied to every body nested in it, then to its own. -/
@[expose] def Region.mapBodies (f : Fresh → List (Block env α) → List (Block env α) × Fresh)
    (st : Fresh) : Region env α → Region env α × Fresh
  | ⟨⟨bs⟩⟩ =>
    let (bs, st) := Block.mapBodiesList f st bs
    let (bs, st) := f st bs
    (⟨bs.toArray⟩, st)

/-- `Region.mapBodies` of each. -/
@[expose] def Region.mapBodiesList (f : Fresh → List (Block env α) → List (Block env α) × Fresh)
    (st : Fresh) : List (Region env α) → List (Region env α) × Fresh
  | [] => ([], st)
  | r :: rs =>
    let (r, st) := Region.mapBodies f st r
    let (rs, st) := Region.mapBodiesList f st rs
    (r :: rs, st)

end

/-! ## The pass -/

/-- The function in canonical form: step 1 on its own body, then step 2 on every body. -/
@[expose] def canonicalize [base ≼ env] (fn : Func env α) : Func env α :=
  if fn.checkCanonicalCFG then fn else
  let st := Fresh.ofFunc fn.labels fn.names
  let (bs, st) := oneExit st fn.retType fn.info fn.blocks.toList
  let (r, st) := Region.mapBodies simplifyBody st ⟨bs.toArray⟩
  { fn with blocks := r.blocks, names := st.names }

/-- A preheader for each block of `hs` that no back edge enters and that lacks one: a forwarding
block that takes every transfer to it.  The body's entry block gets none: nothing may enter it,
so the check reports that it has no preheader.  A body whose labels are not distinct, which a
well-formed function does not have, is left as it is, and the result is not well formed. -/
@[expose] def recordPreheaders [base ≼ env] (hs : List Label) (st : Fresh)
    (bs : List (Block env α)) : List (Block env α) × Fresh :=
  match loopIndex? bs with
  | none => (bs, st)
  | some ix =>
    -- One preheader per head: a second record of the same head finds it.
    let hs := (hs.foldl (init := (#[], (∅ : Std.HashSet Label))) fun (acc, seen) h =>
      if seen.contains h then (acc, seen) else (acc.push h, seen.insert h)).1.toList
    let (r, added, st) := hs.foldl (init := (({} : Redirects), (#[] : Array (Block env α)), st))
      fun (r, added, st) h =>
        -- The body's first block is its entry, which no transfer may enter.
        if ix.isHead h || bs.head?.any (·.label == h) then (r, added, st)
        else match ix.blocks.find? h with
          | none => (r, added, st)
          | some hb =>
            if ix.preheaderB h then (r, added, st)
            else
              let (pb, st) := st.forward "pre" hb
              let r := (LabelMap.listAt ix.into h).foldl (init := r) fun r u =>
                r.insert (u.label, h) pb.label
              (r, added.push pb, st)
    (redirectAll bs r ++ added.toList, st)

/-- `canonicalize`, then a preheader for every head of `hs` that the CFG does not see as a loop's:
the heads of the front end's loop records. -/
@[expose] def canonicalizeWith [base ≼ env] (hs : List Label) (fn : Func env α) : Func env α :=
  let g := canonicalize fn
  if hs.isEmpty then g
  else
    let (r, st) := Region.mapBodies (recordPreheaders hs) (Fresh.ofFunc g.labels g.names) ⟨g.blocks⟩
    { g with blocks := r.blocks, names := st.names }

/-- Why `spec.check` fails, for a message: the first record or rule that does not hold. -/
@[expose] def whyNot (spec : CanonicalSpec env α) (g : Func env α) : String :=
  let bs := g.blocks.toList
  let recs := spec.records g.info
  let name (l : Label) := ToDDM.nameText l.name
  let tr := Body.transfers bs
  let ep := Body.exitPoints bs
  let be := Body.backEdges bs
  let tbl := Body.tableOf be (Body.loopsOf bs be)
  let hs := tbl.map (·.1)
  let lo := Body.lookupLoop tbl
  let info := Body.domInfo bs
  let sm := Body.succMap bs
  let loopWhy : Option String := spec.shape.bind fun s =>
    match s.roles? with
    | none => some "the completion shape does not match its datatype's constructors"
    | some ro =>
      match hs.find? (fun h => !recs.any (·.head == h)) with
      | some h => some s!"the loop at {name h} has no record"
      | none =>
        if !(recs.map (·.head)).Nodup then some "two records name the same loop"
        else if !(recs.filterMap (·.done)).Nodup then some "two records name the same done block"
        else recs.findSome? fun r =>
          if !g.labels.contains r.head then some s!"the record's loop {name r.head} is no block"
          else if !bs.any (·.label == r.head) then none
          else if !Body.preheaderB bs (lo r.head) r.head then
            some s!"the loop at {name r.head} has no preheader"
          else if !Body.headDominatesB bs tr hs lo info r then
            some s!"{name r.head} does not dominate its loop's done and exits"
          else match r.done with
            | none =>
              if (Body.exitsIn tr (Body.scopeIn lo r.head)).all (Body.unreachableB bs) then none
              else some s!"control leaves the loop at {name r.head}, but its record names no done"
            | some d =>
              let Rs := Body.regionsOf bs sm d (Body.exitsIn tr (Body.scopeIn lo r.head))
              if !Body.doneB bs tr ep hs lo s r.head d Rs then
                some s!"the exits of the loop at {name r.head} do not all meet at {name d}"
              else if !Body.absorbsB bs lo s ro r.head d Rs then
                some s!"{name d} does not absorb the break and continue of the loop at \
                  {name r.head}"
              else none
  match loopWhy with
  | some w => w
  | none =>
    if spec.preamble && !g.checkPreamble then
      "the entry block does not end in a plain jump to a block that nothing else enters"
    else "a loop inside a region does not hold its record"

/-- Why `run` or `check` gives no function. -/
inductive Failure where
  /-- The function has a cycle that no back edge closes: a loop with two entries. -/
  | irreducible (name : Name)
  /-- The canonicalized function is not well formed: a bug in the pass. -/
  | notWF (name : Name)
  /-- The canonicalized function is well formed but not canonical.  This happens when a loop
  inside a region leaves the region, which the pass does not fix, or when the pass runs out of
  fuel. -/
  | notCanonical (name : Name)
  /-- The canonicalized functions do not form a module: a bug in the pass. -/
  | notModule (names : Array Name)
  /-- The function, canonicalized or given to `check`, does not hold what the front end's
  `CanonicalSpec` asks, for the reason
  `why`: the front end's loops or entry block are not as stated. -/
  | notAsSpecified (name : Name) (why : String)
  /-- The function given to `check` is well formed but not canonical. -/
  | notCanonicalGiven (name : Name)

instance : ToString Failure where
  toString
    | .irreducible n => s!"{ToDDM.nameText n}: a loop has two entries"
    | .notWF n => s!"{ToDDM.nameText n}: not well formed after canonicalization"
    | .notCanonical n => s!"{ToDDM.nameText n}: not canonical after canonicalization"
    | .notModule ns => s!"{ns.map ToDDM.nameText}: do not form a module after canonicalization"
    | .notAsSpecified n w => s!"{ToDDM.nameText n}: {w}"
    | .notCanonicalGiven n => s!"{ToDDM.nameText n}: not canonical"

/-- The heads of the loop records of `fn` that `spec` reads, if it asks for P4 and P7. -/
@[expose] def recordHeads (spec : CanonicalSpec env α) (fn : Func env α) : List Label :=
  if spec.shape.isSome then (spec.records fn.info).map (·.head) else []

/-- The well-formed function `fn` itself, with proofs that it is canonical, that every loop in it
has one entry, and that it holds what `spec` asks, or why it is not.  Unlike `run`, it never
changes `fn`: it rejects a function that the pass would repair.  So a stage after a pass that
should keep the form can confirm that the form still holds, without hiding a break that the pass
would repair. -/
@[expose] def check [base ≼ env] (fn : {f : Func env α // f.WF})
    (spec : CanonicalSpec env α := {}) :
    Except Failure
      {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible ∧ spec.Holds g} :=
  if hc : Body.everyB Body.loopsCheckB fn.val.blocks.toList = true ∧
      Body.oneExitB fn.val.blocks.toList = true then
    if hs : spec.check fn.val = true then
      .ok ⟨fn.val, fn.property, Func.of_loopsCheck fn.property.distinct hc.1 hc.2 |>.1,
        Func.of_loopsCheck fn.property.distinct hc.1 hc.2 |>.2,
        CanonicalSpec.holds_of_check fn.property.distinct hs⟩
    else .error (.notAsSpecified fn.val.name (whyNot spec fn.val))
  else if Body.everyB Body.reducibleB fn.val.blocks.toList then
    .error (.notCanonicalGiven fn.val.name)
  else .error (.irreducible fn.val.name)

/-- The well-formed function `fn` in canonical form, with proofs that it is well formed,
canonical, that every loop in it has one entry, and that it holds what `spec` asks, or why it is
not: the pass, then `check`.  A loop with two entries has no head, so no contract could be placed
on it. -/
@[expose] def run [base ≼ env] (fn : {f : Func env α // f.WF}) (spec : CanonicalSpec env α := {}) :
    Except Failure
      {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible ∧ spec.Holds g} :=
  let g := canonicalizeWith (recordHeads spec fn.val) fn.val
  if h : g.WF then
    match check ⟨g, h⟩ spec with
    | .error (.notCanonicalGiven n) => .error (.notCanonical n)
    | r => r
  else .error (.notWF g.name)

/-- A module whose every function is in canonical form, with one entry per loop, and holds what
`spec` asks. -/
structure CanonicalModule (env : Env Unit) [base ≼ env] (α : Type) (spec : CanonicalSpec env α := {}) where
  module : Module env α
  canonical : ∀ f ∈ module.raw.funcs, f.CanonicalCFG ∧ f.Reducible ∧ spec.Holds f

/-- The errors of `rs`, in order. -/
@[expose] def errorsOf {β γ : Type} (rs : List (Except β γ)) : List β :=
  rs.filterMap fun | .error e => some e | .ok _ => none

/-- The results of `rs`, in order. -/
@[expose] def resultsOf {β γ : Type} (rs : List (Except β γ)) : List γ :=
  rs.filterMap fun | .ok g => some g | .error _ => none

/-- The module `m` with `step` applied to every function, and its ghosts as they are, with the
proofs, or the failure of each function that `step` rejects. -/
@[expose] def moduleWith [base ≼ env] {spec : CanonicalSpec env α}
    (step : {f : Func env α // f.WF} →
      Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible ∧ spec.Holds g})
    (m : Module env α) : Except (Array Failure) (CanonicalModule env α spec) :=
  let rs := m.raw.funcs.toList.attach.map fun ⟨f, hf⟩ =>
    step ⟨f, m.wf.funcs f (Array.mem_toList_iff.mp hf)⟩
  let errs := errorsOf rs
  if !errs.isEmpty then .error errs.toArray
  else
    let fs := resultsOf rs
    let gs := m.raw.ghosts.attach.map fun ⟨g, hg⟩ => ⟨g, m.wf.ghosts g hg⟩
    match h : Module.ofChecked m.raw.name (fs.map fun g => ⟨g.val, g.property.1⟩).toArray
        m.raw.info gs with
    | .ok m' => .ok ⟨m', fun f hf => by
        rw [Module.ofChecked_funcs h] at hf
        simp only [List.map_toArray, List.map_map, List.mem_toArray, List.mem_map,
          Function.comp] at hf
        obtain ⟨g, -, rfl⟩ := hf
        exact g.property.2⟩
    | .error ns => .error #[.notModule ns]

/-- The module `m` with every function put in canonical form by `run spec`, with the proofs, or
the failure of each function that `run` rejects.  A `notModule` failure can only come from a bug
in the pass, since the pass keeps the module's name, ghosts and annotation, and every function's
name, signature and constants. -/
@[expose] def runModule [base ≼ env] (m : Module env α) (spec : CanonicalSpec env α := {}) :
    Except (Array Failure) (CanonicalModule env α spec) :=
  moduleWith (run · spec) m

/-- The module `m` itself, with the proofs that `check spec` gives for each function, or the
failure of each function that `check` rejects. -/
@[expose] def checkModule [base ≼ env] (m : Module env α) (spec : CanonicalSpec env α := {}) :
    Except (Array Failure) (CanonicalModule env α spec) :=
  moduleWith (check · spec) m

end Canonicalize

end

end Strata.Dyn
