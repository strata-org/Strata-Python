/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.CanonicalProps
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
step 2 then gives a dedicated exit.  A loop inside a region that leaves the region is not fixed:
the region's exit is not a block, and its type is the region's.

`Canonicalize.run` takes a well-formed function, and checks the result: it gives the function
with proofs that it is well formed, canonical, and that every loop has one entry
(`Func.Reducible`), or a failure that says which does not hold.  For the last, a depth-first
order suggests a rank of the labels, and a proved check confirms that every transfer that is not
a back edge goes up in it.

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
id.  A new value's id is the number of names so far. -/
structure Fresh where
  labels : List Label
  names : Array Name

/-- The first label `base.k`, from `k`, that `taken` does not hold, trying at most `fuel`. -/
@[expose] def firstLabel (taken : List Label) (base : String) : (fuel k : Nat) → Label
  | 0, k => ⟨.num (.str .base base) k⟩
  | f + 1, k =>
    let l : Label := ⟨.num (.str .base base) k⟩
    if taken.contains l then firstLabel taken base f (k + 1) else l

/-- The first name `stem.k`, from `k`, that `taken` does not hold, trying at most `fuel`. -/
@[expose] def firstName (taken : Array Name) (stem : Name) : (fuel k : Nat) → Name
  | 0, k => .num stem k
  | f + 1, k => if taken.contains (.num stem k) then firstName taken stem f (k + 1) else .num stem k

/-- A label `base.k` that no block of the function has. -/
@[expose] def Fresh.label (st : Fresh) (base : String) : Label × Fresh :=
  let l := firstLabel st.labels base (st.labels.length + 1) 0
  (l, { st with labels := l :: st.labels })

/-- A new value of type `t`, named after `stem`. -/
@[expose] def Fresh.value (st : Fresh) (stem : Name) (t : TypeExpr env) : ValDecl env × Fresh :=
  let n := firstName st.names stem (st.names.size + 1) 0
  (⟨⟨st.names.size⟩, t⟩, { st with names := st.names.push n })

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

/-- The instruction, with each successor that `p` picks sent to `l`. -/
@[expose] def Instruction.redirect (p : Target.Raw → Bool) (l : Label) :
    Instruction env α → Instruction env α
  | .const info d c => .const info d c
  | .apply info d r ta args succs regions =>
    .apply info d r ta args (succs.map (redirectSucc p l)) regions

/-- The terminator, with each successor that `p` picks sent to `l`. -/
@[expose] def Terminator.redirect (p : Target.Raw → Bool) (l : Label) :
    Terminator env α → Terminator env α
  | .apply info r ta args succs regions =>
    .apply info r ta args (succs.map (redirectSucc p l)) regions

/-- The blocks, with each transfer of block `b` that `p b` picks sent to `l`.  Transfers inside
their regions are left alone: they belong to other bodies. -/
@[expose] def redirect (bs : List (Block env α)) (p : Block env α → Target.Raw → Bool)
    (l : Label) : List (Block env α) :=
  bs.map fun b => { b with
    instrs := b.instrs.map (Instruction.redirect (p b) l)
    term := Terminator.redirect (p b) l b.term }

/-! ## The steps -/

/-- Whether the body leaves through its exit from at most one block, which ends in a plain jump
and is in no loop. -/
@[expose] def exitDone (bs : List (Block env α)) : Bool :=
  Body.oneExitB bs &&
    let be := Body.backEdges bs
    let L := (Body.tableOf be (Body.loopsOf bs be)).flatMap (·.2)
    (Body.exitPoints bs).all fun u => !L.contains u.label

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

/-- The exit targets of the loop whose labels are `L` that code outside the loop also enters,
given the body's transfers `tr`. -/
@[expose] def exitsToFix (tr : List (Point × Label)) (L : List Label) : List Label :=
  ((tr.filter fun (u, l) => L.contains u.label && !L.contains l).map (·.2)).eraseDups.filter
    fun x => tr.any fun (w, l) => l == x && !L.contains w.label

/-- Dedicated exits for the loops `loops`, smallest first.  `bs₀` is the body at the start of the
round, and `tr₀` its transfers.  The accumulator holds the blocks, the allocator, the exit blocks
added so far with their targets, whether some loop was fixed, and the labels of the loops fixed.
A loop that shares a block with a loop already fixed sees the transfers again, and holds the exit
blocks added for its targets inside it.  A loop with a head among its exits waits for a later
round. -/
@[expose] def addExits [base ≼ env] (heads : List Label) (tr₀ : List (Point × Label)) :
    List (Label × List Label) →
      List (Block env α) × Fresh × List (Label × Label) × Bool × List Label →
      List (Block env α) × Fresh × List (Label × Label) × Bool × List Label
  | [], acc => acc
  | (_, L₀) :: loops, (bs, st, added, any, taken) =>
    let overlap := L₀.any taken.contains
    let L := if overlap then L₀ ++ (added.filter fun (_, x) => L₀.contains x).map (·.1) else L₀
    let tr := if overlap then Body.transfers bs else tr₀
    let xs := exitsToFix tr L
    if xs.isEmpty || xs.any heads.contains then addExits heads tr₀ loops (bs, st, added, any, taken)
    else
      let (bs, st, added) := xs.foldl (init := (bs, st, added)) fun (bs, st, added) x =>
        match Body.blockAt? bs x with
        | none => (bs, st, added)
        | some xb =>
          let (eb, st) := st.forward "loopexit" xb
          (redirect bs (fun b s => L.contains b.label && s.label == x) eb.label ++ [eb], st,
            added ++ [(eb.label, x)])
      addExits heads tr₀ loops (bs, st, added, true, taken ++ L)

/-- One round of fixes, if one is needed: a latch for every loop without one; or else a
preheader for every loop without one; or else dedicated exits for every loop, smallest first.
Latches and preheaders of different loops redirect transfers to different heads, so they do not
interfere; for exits, `addExits` lets a loop that overlaps one already fixed see the new blocks.
A loop with a head among its exits waits, and if no loop could be fixed this way, `fixOne` makes
one fix.  This happens when a loop's latch lies in a loop nested in it: that inner loop then
leaves to the outer head. -/
@[expose] def fixRound [base ≼ env] (st : Fresh) (bs : List (Block env α)) :
    Option (List (Block env α) × Fresh) :=
  let be := Body.backEdges bs
  let tr := Body.transfers bs
  let loops := loopsInnerFirst be bs
  let needLatch := loops.filter fun (h, _) =>
    !Body.theOneB ((be.filter (·.2 == h)).map (·.1)) (Body.endsAtB bs · h)
  if !needLatch.isEmpty then
    some (needLatch.foldl (init := (bs, st)) fun (bs', st) (h, L) =>
      match Body.blockAt? bs h with
      | none => (bs', st)
      | some hb =>
        let (lb, st) := st.forward "latch" hb
        (redirect bs' (fun b s => L.contains b.label && s.label == h) lb.label ++ [lb], st))
  else
    let needPre := loops.filter fun (h, L) =>
      !Body.theOneB ((tr.filter fun (u, l) => l == h && !L.contains u.label).map (·.1))
        (Body.endsAtB bs · h)
    if !needPre.isEmpty then
      some (needPre.foldl (init := (bs, st)) fun (bs', st) (h, L) =>
        match Body.blockAt? bs h with
        | none => (bs', st)
        | some hb =>
          let (pb, st) := st.forward "pre" hb
          (redirect bs' (fun b s => !L.contains b.label && s.label == h) pb.label ++ [pb], st))
    else
      let (bs', st', _, any, _) := addExits (loops.map (·.1)) tr loops (bs, st, [], false, [])
      if any then some (bs', st')
      else if loops.all fun x => (exitsToFix tr x.2).isEmpty then none
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
  let st : Fresh := ⟨fn.labels, fn.names⟩
  let (bs, st) := oneExit st fn.retType fn.info fn.blocks.toList
  let (r, st) := Region.mapBodies simplifyBody st ⟨bs.toArray⟩
  { fn with blocks := r.blocks, names := st.names }

/-- Why `run` gives no function. -/
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
  /-- The function given to `check` is well formed but not canonical. -/
  | notCanonicalGiven (name : Name)

instance : ToString Failure where
  toString
    | .irreducible n => s!"{ToDDM.nameText n}: a loop has two entries"
    | .notWF n => s!"{ToDDM.nameText n}: not well formed after canonicalization"
    | .notCanonical n => s!"{ToDDM.nameText n}: not canonical after canonicalization"
    | .notModule ns => s!"{ns.map ToDDM.nameText}: do not form a module after canonicalization"
    | .notCanonicalGiven n => s!"{ToDDM.nameText n}: not canonical"

/-- The well-formed function `fn` itself, with proofs that it is canonical and that every loop in
it has one entry, or why it is not.  Unlike `run`, it never changes `fn`: it rejects a function
that the pass would repair.  So a stage after a pass that should keep the form can confirm that the
form still holds, without hiding a break that the pass would repair. -/
@[expose] def check [base ≼ env] (fn : {f : Func env α // f.WF}) :
    Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible} :=
  if hc : Body.everyB Body.loopsCheckB fn.val.blocks.toList = true ∧
      Body.oneExitB fn.val.blocks.toList = true then
    .ok ⟨fn.val, fn.property, Func.of_loopsCheck fn.property.distinct hc.1 hc.2⟩
  else if Body.everyB Body.reducibleB fn.val.blocks.toList then
    .error (.notCanonicalGiven fn.val.name)
  else .error (.irreducible fn.val.name)

/-- The well-formed function `fn` in canonical form, with proofs that it is well formed,
canonical, and that every loop in it has one entry, or why it is not: the pass, then `check`.  A
loop with two entries has no head, so no contract could be placed on it. -/
@[expose] def run [base ≼ env] (fn : {f : Func env α // f.WF}) :
    Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible} :=
  let g := canonicalize fn.val
  if h : g.WF then
    match check ⟨g, h⟩ with
    | .error (.notCanonicalGiven n) => .error (.notCanonical n)
    | r => r
  else .error (.notWF g.name)

/-- A module whose every function is in canonical form, with one entry per loop. -/
structure CanonicalModule (env : Env Unit) [base ≼ env] (α : Type) where
  module : Module env α
  canonical : ∀ f ∈ module.raw.funcs, f.CanonicalCFG ∧ f.Reducible

/-- The errors of `rs`, in order. -/
@[expose] def errorsOf {β γ : Type} (rs : List (Except β γ)) : List β :=
  rs.filterMap fun | .error e => some e | .ok _ => none

/-- The results of `rs`, in order. -/
@[expose] def resultsOf {β γ : Type} (rs : List (Except β γ)) : List γ :=
  rs.filterMap fun | .ok g => some g | .error _ => none

/-- The module `m` with `step` applied to every function, and its ghosts as they are, with the
proofs, or the failure of each function that `step` rejects. -/
@[expose] def moduleWith [base ≼ env]
    (step : {f : Func env α // f.WF} →
      Except Failure {g : Func env α // g.WF ∧ g.CanonicalCFG ∧ g.Reducible})
    (m : Module env α) : Except (Array Failure) (CanonicalModule env α) :=
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

/-- The module `m` with every function put in canonical form by `run`, with the proofs, or the
failure of each function that `run` rejects.  A `notModule` failure can only come from a bug in
the pass, since the pass keeps the module's name, ghosts and annotation, and every function's name,
signature and constants. -/
@[expose] def runModule [base ≼ env] (m : Module env α) :
    Except (Array Failure) (CanonicalModule env α) :=
  moduleWith run m

/-- The module `m` itself, with the proofs that `check` gives for each function, or the failure of
each function that `check` rejects. -/
@[expose] def checkModule [base ≼ env] (m : Module env α) :
    Except (Array Failure) (CanonicalModule env α) :=
  moduleWith check m

end Canonicalize

end

end Strata.Dyn
