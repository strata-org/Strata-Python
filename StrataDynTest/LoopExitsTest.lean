/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.LoopExits
public import StrataDynTest.Blocks
import StrataDyn.Env.WF
meta import StrataDyn.LoopExits
meta import StrataDynTest.Blocks

set_option autoImplicit false

/-!
# Tests of reason-carrying loop exits and the preamble

Bodies written by hand in `Demo.env`, with `demo.Completion` as the completion type, each beside
a twin that breaks one clause.  The bodies are about the shape of the control-flow graph, so they
need not be well formed.
-/

namespace Strata.Dyn.LoopExitsTest

open Strata.Dyn.DSLTest Strata.Dyn.Blocks

/-- `demo.Completion`: normal, returned, raised, broke, continued. -/
private def shape : CompletionShape E :=
  { ty := Demo.Completion, data := Demo.Completion.name, normal := Demo.Completion.normal.name,
    brk := Demo.Completion.broke.name, cont := Demo.Completion.continued.name,
    forwarded := [Demo.Completion.returned.name, Demo.Completion.raised.name] }

/-- `demo.LCompletion`, whose `break` and `continue` carry a label, tested with
`demo.labelIs`. -/
private def lshape : CompletionShape E :=
  { ty := Demo.LCompletion, data := Demo.LCompletion.name,
    normal := Demo.LCompletion.lnormal.name, brk := Demo.LCompletion.lbroke.name,
    cont := Demo.LCompletion.lcontinued.name,
    forwarded := [Demo.LCompletion.lreturned.name, Demo.LCompletion.lraised.name],
    labelTest := some Demo.labelIs.name }

/-! ## The shape, checked against the datatype -/

#guard shape.roles? == some { normal := 0, brk := 3, cont := 4, forwarded := [1, 2] }
#guard lshape.roles? == some { normal := 0, brk := 3, cont := 4, forwarded := [1, 2] }
-- `raised` as `continue` and `continued` as forwarded: `raised` carries a field, which
-- `continue` must not, so the swap is caught.
private def swapped : CompletionShape E :=
  { shape with cont := Demo.Completion.raised.name,
               forwarded := [Demo.Completion.returned.name, Demo.Completion.continued.name] }

#guard swapped.roles? == none
-- A constructor with no role.
#guard ({ shape with forwarded := [Demo.Completion.returned.name] }).roles? == none
-- A constructor with two roles.
#guard ({ shape with brk := Demo.Completion.normal.name }).roles? == none
-- A role that names no constructor of the datatype.
#guard ({ shape with brk := Demo.Box.empty.name }).roles? == none
-- A labelled shape over a datatype whose `break` carries no label.
#guard ({ shape with labelTest := some Demo.labelIs.name }).roles? == none

/-- Block `s` that takes the completion `%k`, numbered `k`, of type `t`. -/
private def blkK (s : String) (k : Nat) (t : TypeExpr E) (is : Array (Instruction E Unit))
    (term : Terminator E Unit) : Block E Unit :=
  { label := lbl s, params := #[⟨⟨k⟩, t⟩], instrs := is, term, info := () }

/-- `case %k` over the completion, to `arms` in the constructors' order: normal, returned,
raised, broke, continued. -/
private def caseT (k : Nat) (arms : List String) : Terminator E Unit :=
  .apply () Demo.Completion.case.ref ⟨#[], rfl⟩ #[⟨k⟩] (arms.map fun a => ⟨lbl a, #[]⟩).toArray #[]

/-- `case %k` over the labelled completion. -/
private def lcaseT (k : Nat) (arms : List String) : Terminator E Unit :=
  .apply () Demo.LCompletion.case.ref ⟨#[], rfl⟩ #[⟨k⟩] (arms.map fun a => ⟨lbl a, #[]⟩).toArray #[]

/-- `base.unreachable`. -/
private def unreachableT : Terminator E Unit := .unreachable ()

/-- `%v = n`: an integer constant. -/
private def intC (v : Nat) (n : Int) : Instruction E Unit := .const () ⟨⟨v⟩, Base.Int⟩ (.int n)

/-- Block `s` that takes the label `%l`, holds `%v = n`, and tests `labelIs(%l, %v)`, to `yes`
or `no`. -/
private def labelBlk (s : String) (l v : Nat) (n : Int) (yes no : String) : Block E Unit :=
  { label := lbl s, params := #[⟨⟨l⟩, Base.Int⟩], instrs := #[intC v n],
    term := .apply () Demo.labelIs.ref ⟨#[], rfl⟩ #[⟨l⟩, ⟨v⟩] #[⟨lbl yes, #[]⟩, ⟨lbl no, #[]⟩] #[],
    info := () }

/-- A record of the loop at `h`, whose exits meet at `d`. -/
private def rec (h d : String) (label : Option Int := none) : LoopRecord :=
  { head := lbl h, done := some (lbl d), label }

/-- A record of the loop at `h`, which control never leaves. -/
private def recNoDone (h : String) : LoopRecord := { head := lbl h, done := none }

private def check (s : CompletionShape E) (recs : List LoopRecord) (f : Func E Unit) : Bool :=
  f.checkLoopExits s recs

/-! ## A `while` loop with `break` -/

/-- `while c: if d: break`: the guard's false edge goes to `normal`, the `break` to `brk`, and
both go on to `done`, which goes on to `after`.  The blocks build no completion: the check does
not look at which constructor builds one. -/
private def whileBrk (brkTo : String) : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (jump brkTo),
      blkK "done" 7 Demo.Completion #[] (caseT 7 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

#guard check shape [rec "head" "done"] (whileBrk "done")
-- The `break` skips `done`: it reaches no `done`, and it returns before one.
#guard !check shape [rec "head" "done"] (whileBrk "after")
-- A loop with no record.
#guard !check shape [] (whileBrk "done")
-- A record whose `done` is the loop's `after`, which takes no completion.
#guard !check shape [rec "head" "after"] (whileBrk "done")
-- Two records with the same head.
#guard !check shape [rec "head" "done", rec "head" "done"] (whileBrk "done")
-- A record whose head is no block.
#guard !check shape [rec "head" "done", rec "nowhere" "done"] (whileBrk "done")

/-! ## Each clause of P4 alone

Each twin below breaks one clause only. -/

/-- `whileBrk`, whose `break` block either goes on to `done` or returns at once. -/
private def brkReturns : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (branch "done" "early"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "early" #[] ret, blk "after" #[] ret]

-- A path from an exit returns before `done` (`noReturn`).
#guard !check shape [rec "head" "done"] brkReturns

/-- `whileBrk`, whose `break` block runs an instruction whose failure leaves the body, as a raise
does that a handler sends to the function's exit, before it goes on to `done`. -/
private def brkRaises : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[addExit 9] (jump "done"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

-- A path from an exit leaves the body through an instruction's failure before `done`
-- (`noReturn`): an instruction's successor to the exit leaves the body as `ret` does.
#guard !check shape [rec "head" "done"] brkRaises

/-- `whileBrk`, whose `break` block spins forever, never reaching `done` and never returning. -/
private def brkSpins : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (jump "spin"), blk "spin" #[] (jump "spin"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

-- An exit that never reaches `done` (`reaches`).
#guard !check shape [rec "head" "done", recNoDone "spin"] brkSpins

/-- `whileBrk`, whose `break` block goes on to `done`, or to `spin`, through `spre`: a loop of
its own that never ends. -/
private def brkMaySpin : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (branch "done" "spre"),
      blk "spre" #[] (jump "spin"), blk "spin" #[] (jump "spin"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

-- A path out of the loop may run forever instead of reaching `done`: some path from each block
-- that the loop leaves for reaches `done`, and none leaves the body before it.
#guard check shape [rec "head" "done", recNoDone "spin"] brkMaySpin

/-- An outer loop at `ohead` that never ends, and an inner loop whose `break` block `ib` goes on
to the outer latch, so it continues the outer loop without passing the inner `done`. -/
private def brkContinuesOuter : Func E Unit :=
  fn [blk "entry" #[] (jump "opre"), blk "opre" #[] (jump "ohead"),
      blk "ohead" #[] (jump "ipre"),
      blk "ipre" #[] (jump "ihead"), blk "ihead" #[] (branch "ibody" "inormal"),
      blk "ibody" #[] (branch "ilatch" "ib"),
      blk "ilatch" #[] (jump "ihead"), blk "inormal" #[] (jump "idone"),
      blk "ib" #[] (jump "olatch"),
      blkK "idone" 7 Demo.Completion #[] (caseT 7 ["iafter", "unr", "unr", "iafter", "unr"]),
      blk "iafter" #[] (jump "olatch"), blk "olatch" #[] (jump "ohead"),
      blk "unr" #[] unreachableT]

-- A path from an exit comes back to the head of a loop around this one before `done`
-- (`noOuterHead`).
#guard !check shape [recNoDone "ohead", rec "ihead" "idone"] brkContinuesOuter

/-- `whileBrk`, with `done` taking a value instead of the completion. -/
private def doneTakesValue : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (jump "done"),
      blkK "done" 7 valT #[] (caseT 7 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

-- `done`'s first parameter is not the completion.
#guard !check shape [rec "head" "done"] doneTakesValue

/-! ## Each clause of P7 alone -/

/-- `whileBrk`, whose `break` block goes to `done` or to `mid`, which also goes to `done`; `done`'s
normal arm is `normalTo`. -/
private def armVia (normalTo : String) : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (branch "done" "mid"),
      blk "mid" #[] (jump "done"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 [normalTo, "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

#guard check shape [rec "head" "done"] (armVia "after")
-- An arm to a block that an exit also reaches before `done`: the loop's code past its exits.
#guard !check shape [rec "head" "done"] (armVia "mid")

/-- `whileBrk`, whose `done` ends in `term`. -/
private def doneEndsIn (term : Terminator E Unit) : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (jump "done"),
      blkK "done" 7 Demo.Completion #[] term,
      blk "unr" #[] unreachableT, blk "after" #[] ret]

#guard check shape [rec "head" "done"] (doneEndsIn (caseT 7 ["after", "unr", "unr", "after", "unr"]))
-- A case instruction of another datatype.
#guard !check shape [rec "head" "done"]
  (doneEndsIn (lcaseT 7 ["after", "unr", "unr", "after", "unr"]))
-- A case on another value than `done`'s parameter.
#guard !check shape [rec "head" "done"] (doneEndsIn (caseT 8 ["after", "unr", "unr", "after", "unr"]))

/-- `while c: pass` inside `while True:`: the inner loop at `ihead` leaves to `done`, but the
outer loop at `head` never ends, so its record names no `done`. -/
private def neverEnds : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (jump "ipre"), blk "ipre" #[] (jump "ihead"),
      blk "ihead" #[] (branch "ilatch" "normal"), blk "ilatch" #[] (jump "ihead"),
      blk "normal" #[] (jump "done"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 ["latch", "unr", "unr", "latch", "unr"]),
      blk "latch" #[] (jump "head"), blk "unr" #[] unreachableT]

#guard check shape [recNoDone "head", rec "ihead" "done"] neverEnds
-- Every loop has a record, the one that never ends too.
#guard !check shape [rec "ihead" "done"] neverEnds
-- The inner loop is left, so its record must name its `done`.
#guard !check shape [recNoDone "head", recNoDone "ihead"] neverEnds

/-- `while c: pass` whose exit block runs an instruction, which can raise to `out`, before
`unreachable`: control leaves the loop through that instruction. -/
private def leavesThroughInsn : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "latch" "x"), blk "latch" #[] (jump "head"),
      blk "x" #[add 1 "out"] unreachableT, blk "out" #[] ret]

-- A block with an instruction before `unreachable` is not unreachable: the loop is left, so a
-- record without `done` does not hold.
#guard !check shape [recNoDone "head"] leavesThroughInsn

/-! ## What `done`'s arms may do -/

/-- The loop of `whileBrk`, with `done`'s arms `arms`. -/
private def whileArms (arms : List String) : Func E Unit :=
  fn [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head"),
      blk "head" #[] (branch "body" "normal"), blk "body" #[] (branch "latch" "brk"),
      blk "latch" #[] (jump "head"),
      blk "normal" #[] (jump "done"), blk "brk" #[] (jump "done"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 arms),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

#guard check shape [rec "head" "done"] (whileArms ["after", "after", "after", "after", "unr"])
-- The `continue` arm is not unreachable: a `continue` of the loop belongs at its latch.
#guard !check shape [rec "head" "done"] (whileArms ["after", "unr", "unr", "after", "after"])
-- A forwarded arm goes back into the loop.
#guard !check shape [rec "head" "done"] (whileArms ["after", "head", "unr", "after", "unr"])
-- An arm back to `done` itself.
#guard !check shape [rec "head" "done"] (whileArms ["after", "done", "unr", "after", "unr"])
-- Too few arms for the shape's roles.
#guard !check shape [rec "head" "done"] (whileArms ["after", "unr", "unr", "after"])
-- A shape whose roles name one constructor twice.
#guard !check { shape with brk := Demo.Completion.normal.name } [rec "head" "done"]
  (whileArms ["after", "unr", "unr", "after", "unr"])
-- The swapped shape would accept an unreachable raise arm, but the check rejects the shape.
#guard !check swapped [rec "head" "done"] (whileArms ["after", "after", "unr", "after", "after"])
-- A limit: swapping two constructors that carry no field, `normal` and `continued`, gives a
-- shape that the check cannot tell from the right one.  A front end pins its shape with a test.
private def swappedNoFields : CompletionShape E :=
  { shape with normal := Demo.Completion.continued.name, cont := Demo.Completion.normal.name }

#guard swappedNoFields.roles?.isSome

/-! ## Nested loops -/

/-- An outer loop at `ohead` and an inner loop at `ihead`.  The inner `break` goes to `ibrk`,
which builds the completion for `idone`, or with `toOuter` to `obrk`, which builds one for the
outer loop's `done`.  Only the block used is there: a block that no path reaches is dominated by
every point, so its transfers count as back edges. -/
private def nested (toOuter : Bool) : Func E Unit :=
  fn ([blk "entry" #[] (jump "opre"), blk "opre" #[] (jump "ohead"),
      blk "ohead" #[] (branch "obody" "onormal"), blk "obody" #[] (jump "ipre"),
      blk "ipre" #[] (jump "ihead"), blk "ihead" #[] (branch "ibody" "inormal"),
      blk "ibody" #[] (branch "ilatch" (if toOuter then "obrk" else "ibrk")),
      blk "ilatch" #[] (jump "ihead"), blk "inormal" #[] (jump "idone")] ++
    (if toOuter then [blk "obrk" #[] (jump "odone")] else [blk "ibrk" #[] (jump "idone")]) ++
    [blkK "idone" 7 Demo.Completion #[] (caseT 7 ["iafter", "unr", "unr", "iafter", "unr"]),
      blk "iafter" #[] (jump "olatch"), blk "olatch" #[] (jump "ohead"),
      blk "onormal" #[] (jump "odone"),
      blkK "odone" 8 Demo.Completion #[] (caseT 8 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret])

#guard check shape [rec "ohead" "odone", rec "ihead" "idone"] (nested false)
-- The inner `break` goes to the outer loop's `brk`: it never reaches the inner `done`.
#guard !check shape [rec "ohead" "odone", rec "ihead" "idone"] (nested true)
-- The record names the outer `done` for the inner loop: the inner exits reach it, but past them
-- control comes back to the outer head, and the two records share a `done`.
#guard !check shape [rec "ohead" "odone", rec "ihead" "odone"] (nested false)

/-! ## A loop below another loop's exit -/

/-- The shape of `g05_tail_not_in_loop.py`: the outer loop at `ohead` leaves to `ipre`, which runs an
inner loop and then sends a return completion to the outer `done` from `tail`. -/
private def tailBelowExit : Func E Unit :=
  fn [blk "entry" #[] (jump "opre"), blk "opre" #[] (jump "ohead"),
      blk "ohead" #[] (branch "obody" "onormal"), blk "obody" #[] (branch "inc" "ipre"),
      blk "inc" #[] (jump "olatch"), blk "olatch" #[] (jump "ohead"),
      blk "ipre" #[] (jump "ihead"), blk "ihead" #[] (branch "ibody" "inormal"),
      blk "ibody" #[] (jump "ilatch"), blk "ilatch" #[] (jump "ihead"),
      blk "inormal" #[] (jump "idone"),
      blkK "idone" 7 Demo.Completion #[] (caseT 7 ["tail", "unr", "unr", "tail", "unr"]),
      blk "tail" #[] (jump "odone"), blk "onormal" #[] (jump "odone"),
      blkK "odone" 8 Demo.Completion #[] (caseT 8 ["after", "retb", "unr", "after", "unr"]),
      blk "retb" #[] ret, blk "unr" #[] unreachableT, blk "after" #[] ret]

#guard check shape [rec "ohead" "odone", rec "ihead" "idone"] tailBelowExit

/-! ## A loop that the CFG does not see -/

/-- `while c: return x`: no back edge enters `head`, so its scope is `head` alone.  `entry`
enters it through `pre`, unless `direct`. -/
private def noBackEdge (direct : Bool) : Func E Unit :=
  fn ((if direct then [blk "entry" #[] (branch "head" "after")]
      else [blk "entry" #[] (jump "pre"), blk "pre" #[] (jump "head")]) ++
    [blk "head" #[] (branch "body" "normal"),
      blk "body" #[] (jump "done"), blk "normal" #[] (jump "done"),
      blkK "done" 7 Demo.Completion #[] (caseT 7 ["after", "retb", "unr", "after", "unr"]),
      blk "retb" #[] ret, blk "unr" #[] unreachableT, blk "after" #[] ret])

#guard check shape [rec "head" "done"] (noBackEdge false)
-- A record whose head is `normal`, a block of the loop that the path into the body does not pass:
-- its head does not dominate its loop's exits.  (`CanonicalizeTest` runs this through the pass,
-- which gives `normal` a preheader, so that only this clause fails.)
#guard !check shape [rec "normal" "done"] (noBackEdge false)
-- Its head has no preheader, so the invariant's base case has no block.
#guard !check shape [rec "head" "done"] (noBackEdge true)
-- Its head dominates the loop's exits, but code before the loop also enters `done`.
#guard !check shape [rec "head" "done"]
  (fn ((noBackEdge false).blocks.toList.map fun b =>
    if b.label == lbl "entry" then { b with term := branch "pre" "done" } else b))

/-! ## Labelled `break` -/

/-- The loops of `nested`, with labels 1 (outer) and 2 (inner).  The inner `done`'s `break` and
`continue` arms test the label: the inner loop's own label goes on to `iafter` (or nowhere, for
`continue`), and any other goes to `otherTo`. -/
private def labelled (otherTo : String) (contOther : String := otherTo) : Func E Unit :=
  fn [blk "entry" #[] (jump "opre"), blk "opre" #[] (jump "ohead"),
      blk "ohead" #[] (branch "obody" "onormal"), blk "obody" #[] (jump "ipre"),
      blk "ipre" #[] (jump "ihead"), blk "ihead" #[] (branch "ibody" "inormal"),
      blk "ibody" #[] (branch "ilatch" "ibrk"), blk "ilatch" #[] (jump "ihead"),
      blk "inormal" #[] (jump "idone"), blk "ibrk" #[] (jump "idone"),
      blkK "idone" 7 Demo.LCompletion #[]
        (lcaseT 7 ["iafter", "unr", "unr", "ibl", "icl"]),
      labelBlk "ibl" 9 10 2 "iafter" otherTo, labelBlk "icl" 11 12 2 "unr" contOther,
      blk "iafter" #[] (jump "olatch"), blk "olatch" #[] (jump "ohead"),
      blk "onormal" #[] (jump "odone"),
      blkK "odone" 8 Demo.LCompletion #[]
        (lcaseT 8 ["after", "unr", "unr", "obl", "ocl"]),
      labelBlk "obl" 13 14 1 "after" "unr", labelBlk "ocl" 15 16 1 "unr" "unr",
      blk "unr" #[] unreachableT, blk "after" #[] ret]

#guard check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)] (labelled "odone")
-- `continue outer` from the inner loop goes straight to the outer loop's head.
#guard check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)]
  (labelled "odone" "ohead")
-- `break outer` must leave the outer loop through its `done`, not continue it at its head.
#guard !check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)]
  (labelled "ohead" "odone")
-- Another loop's label is absorbed at the inner loop's `after`.
#guard !check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)]
  (labelled "iafter")
-- `break outer` may go through an empty block that jumps to the outer `done`, such as the
-- dedicated exit that the pass puts in front of it, but not through a block that runs code.
#guard check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)]
  (fn ((labelled "fwd" "ohead").blocks.toList ++ [blk "fwd" #[] (jump "odone")]))
#guard !check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)]
  (fn ((labelled "fwd" "ohead").blocks.toList ++ [blk "fwd" #[add 1 "unr"] (jump "odone")]))
/-- `labelled`, with no labelled `continue`: the inner `done`'s `continue` arm goes to `contTo`. -/
private def noLabelledContinue (contTo : String) : Func E Unit :=
  fn ((labelled "odone" "unr").blocks.toList.filterMap fun b =>
    if b.label == lbl "idone" then
      some { b with term := lcaseT 7 ["iafter", "unr", "unr", "ibl", contTo] }
    else if b.label == lbl "icl" && contTo != "icl" then none
    else some b)
-- The `continue` arm may then be unreachable.
#guard check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)]
  (noLabelledContinue "unr")
-- A limit: a label test whose two successors are unreachable is an exit of the outer loop that
-- does not reach the outer `done`, so the check rejects it.
#guard !check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 2)]
  (noLabelledContinue "icl")
-- A labelled shape with records that carry no label.
#guard !check lshape [rec "ohead" "odone", rec "ihead" "idone"] (labelled "odone")
-- A record whose label is not the one the arms test.
#guard !check lshape [rec "ohead" "odone" (some 1), rec "ihead" "idone" (some 3)]
  (labelled "odone")

/-! ## A loop inside a region -/

/-- A loop at `rh` inside the `then` region of an `if`, with its own `done`. -/
private def inRegion : Func E Unit :=
  fn [blk "entry" #[ifI 9
        ⟨#[blk "rentry" #[] (jump "rpre"), blk "rpre" #[] (jump "rh"),
           blk "rh" #[] (branch "rl" "rn"), blk "rl" #[] (jump "rh"),
           blk "rn" #[] (jump "rd"),
           blkK "rd" 7 Demo.Completion #[] (caseT 7 ["rafter", "runr", "runr", "rafter", "runr"]),
           blk "runr" #[] unreachableT, blk "rafter" #[] ret]⟩
        ⟨#[blk "e" #[] ret]⟩] (jump "x"),
      blk "x" #[] ret]

#guard check shape [rec "rh" "rd"] inRegion
-- The region's loop needs its record too.
#guard !check shape [] inRegion

/-- A recorded loop at `rh` inside a region, which the CFG does not see, whose head runs an
instruction that leaves the region when it fails. -/
private def leavesFromRegion : Func E Unit :=
  fn [blk "entry" #[ifI 9
        ⟨#[blk "rentry" #[] (jump "rpre"), blk "rpre" #[] (jump "rh"),
           blk "rh" #[addExit 1] (jump "rd"),
           blkK "rd" 7 Demo.Completion #[] (caseT 7 ["rafter", "runr", "runr", "rafter", "runr"]),
           blk "runr" #[] unreachableT, blk "rafter" #[] ret]⟩
        ⟨#[blk "e" #[] ret]⟩] (jump "x"),
      blk "x" #[] ret]

-- The failure leaves the region without passing `rd`.
#guard !check shape [rec "rh" "rd"] leavesFromRegion

/-- A recorded loop at `rh` inside a region, with no `done`, whose head runs an instruction that
leaves the region when it fails, then says `unreachable`. -/
private def leavesNoDone : Func E Unit :=
  fn [blk "entry" #[ifI 9
        ⟨#[blk "rentry" #[] (jump "rpre"), blk "rpre" #[] (jump "rh"),
           blk "rh" #[addExit 1] unreachableT]⟩
        ⟨#[blk "e" #[] ret]⟩] (jump "x"),
      blk "x" #[] ret]

-- Control leaves the loop through the failure, so a record without `done` does not hold.
#guard !check shape [recNoDone "rh"] leavesNoDone

/-! ## What the check cannot see

Both are the lowering's semantics, which differential tests against CPython check. -/

-- A `break` whose block builds a normal completion instead of a `break` one is accepted: the
-- check does not look at which constructor builds a completion.  `CanonicalizeTest` pins it on
-- a well-formed function.

/-- A loop whose record names, as its `done`, a block `fin` that code before the loop also
enters, as a function's `finally` block would be. -/
private def sharedDone : Func E Unit :=
  fn [blk "entry" #[] (branch "pre" "early"), blk "early" #[] (jump "fin"),
      blk "pre" #[] (jump "head"), blk "head" #[] (branch "latch" "normal"),
      blk "latch" #[] (jump "head"), blk "normal" #[] (jump "fin"),
      blkK "fin" 7 Demo.Completion #[] (caseT 7 ["after", "unr", "unr", "after", "unr"]),
      blk "unr" #[] unreachableT, blk "after" #[] ret]

-- Accepted: no path between the loop and `fin` returns, so the check cannot tell `fin` from the
-- loop's own `done`.
#guard check shape [rec "head" "fin"] sharedDone

/-! ## The preamble (F1) -/

/-- An entry block that ends in a plain jump to `body`, which `again` also enters if `twice`. -/
private def preamble (twice : Bool) : Func E Unit :=
  fn [blk "entry" #[] (jump "body"), blk "body" #[] (branch "out" "again"),
      blk "again" #[] (jump (if twice then "body" else "out")), blk "out" #[] ret]

#guard (preamble false).checkPreamble
-- `body` is entered again later, so its start is not where every run starts.
#guard !(preamble true).checkPreamble
-- An entry block that branches.
#guard !(fn [blk "entry" #[] (branch "a" "b"), blk "a" #[] ret, blk "b" #[] ret]).checkPreamble
-- An empty entry block that ends in `unreachable`: no code of the function ever runs.
#guard (fn [blk "entry" #[] unreachableT]).checkPreamble
-- An entry block that runs an instruction, whose failure goes to `h`, before `unreachable`.
#guard !(fn [blk "entry" #[add 1 "h"] unreachableT, blk "h" #[] ret]).checkPreamble
-- F1 says nothing about the entry block's own instructions: here a run whose instruction fails
-- goes to `h` and returns, without reaching `body`, the block where the precondition is assumed,
-- as a translated Python function does whose argument binding fails.
#guard (fn [blk "entry" #[add 1 "h"] (jump "body"), blk "body" #[] ret, blk "h" #[] ret]).checkPreamble

end Strata.Dyn.LoopExitsTest
