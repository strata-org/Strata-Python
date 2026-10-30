/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonicalize
public import StrataDyn.DDMRead
public import StrataDynTest.DSLTest
public import StrataDynTest.Unforward
import StrataDyn.Env.WF
-- The reader, the pass and the printer run as compiled code below.
meta import StrataDyn.Canonicalize
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF
meta import StrataDynTest.DSLTest
meta import StrataDynTest.Unforward

set_option autoImplicit false

/-!
# Putting functions in canonical form

Functions read from text in `Demo.env`, put in canonical form by `Canonicalize.runModule`, and
printed again.  Each output is also taken back to its input with `Unforward`, which sends each
transfer to a forwarding block on to the end of its chain of forwarding blocks, and drops the
forwarding blocks.  The result must print as the input does.  The first has a loop with every
problem the pass fixes: two back edges, a return from inside the loop, and a handler that code
before the loop also raises to.  The second is canonical already, and comes back unchanged.  The
third has a loop head with two parameters, and a handler that gets an argument and the exception.
The fourth has a loop nested in another, whose exit is the outer loop's head, and a loop inside a
region.  Then what the pass cannot fix: a loop inside a region that leaves the region.  Then a loop
whose only return is inside it, two loops that leave to the same block, two loops in a row that one
round fixes together, a latch inside a nested loop, which needs the single fix, and a loop with two
entries, which `run` rejects.  Last, modules with several functions: `runModule` puts each one in
canonical form, or reports every function it rejects, in order.  `checkModule` rejects the first
function, which the pass repairs, and accepts the second unchanged; on the pass's output, each
loop's head, preheader and latch are named by `Body.loopRoles`.
-/

namespace Strata.Dyn.CanonicalizeTest

open Strata.Dyn.DSLTest

/-- Read `text` in `Demo.env`, put the module in canonical form with `Canonicalize.runModule`,
check that undoing the forwarding blocks gives back the module (`Unforward.moduleUndoesTo`), and
print the module, or why it could not be read or put in canonical form. -/
private def canonText (text : String) : IO Unit := do
  match ← Module.read Demo.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match Canonicalize.runModule m with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok cm =>
      unless Unforward.moduleUndoesTo m.raw cm.module.raw do
        IO.println "the output does not undo to the input"
      IO.println (toString cm.module)

/-- Read `text` in `Demo.env`, check it with `Canonicalize.checkModule`, and print the module that
`checkModule` gives, or why it rejects each function. -/
private def checkText (text : String) : IO Unit := do
  match ← Module.read Demo.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match Canonicalize.checkModule m with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok cm => IO.println (toString cm.module)

/-- Read `text` in `Demo.env`, put it in canonical form with `Canonicalize.runModule`, check the
result again with `Canonicalize.checkModule`, and print each loop of each function's own body as
its head, its preheader and its latch (`Body.loopRoles`). -/
private def rolesText (text : String) : IO Unit := do
  match ← Module.read Demo.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match Canonicalize.runModule m with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok cm =>
      match Canonicalize.checkModule cm.module with
      | .error fs => for f in fs do IO.println (toString f)
      | .ok cm' =>
        for f in cm'.module.raw.funcs do
          for r in Body.loopRoles f.blocks.toList do
            IO.println s!"{ToDDM.nameText f.name}: head {ToDDM.nameText r.head.name}, \
              preheader {ToDDM.nameText r.preheader.name}, latch {ToDDM.nameText r.latch.name}"

/-! ## A loop with every problem

    entry: add ^catch; branch ^head ^exit   -- no preheader
    head:  branch ^body ^exit
    body:  add ^catch; branch ^cont ^more
    cont:  jump ^head                       -- back edge 1
    more:  branch ^done ^head               -- back edge 2
    done:  ret                              -- one of three returns
    catch: ret                              -- also entered from entry
-/

private def everything : String := "module m {
  func @m.f(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^catch.0()
      branch(%c.0) ^head.0() ^exit.0()
    head.0():
      branch(%c.0) ^body.0() ^exit.0()
    body.0():
      %y.1 : demo.Value = demo.add(%x.0, %x.0) ^catch.0()
      branch(%c.0) ^cont.0() ^more.0()
    cont.0():
      jump ^head.0()
    more.0():
      branch(%c.0) ^done.0() ^head.0()
    done.0():
      ret(%y.1)
    exit.0():
      ret(%x.0)
    catch.0(%e.0 : demo.Value):
      ret(%e.0)
  }
}
"

/-- info: module m {
  func @m.f(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^catch.0()
      branch(%c.0) ^pre.0() ^exit.0()
    head.0():
      branch(%c.0) ^body.0() ^loopexit.0()
    body.0():
      %y.1 : demo.Value = demo.add(%x.0, %x.0) ^loopexit.1()
      branch(%c.0) ^cont.0() ^more.0()
    cont.0():
      jump ^latch.0()
    more.0():
      branch(%c.0) ^done.0() ^latch.0()
    done.0():
      jump ^post.0(%y.1)
    exit.0():
      jump ^post.0(%x.0)
    catch.0(%e.0 : demo.Value):
      jump ^post.0(%e.0)
    post.0(%ret.0 : demo.Value):
      ret(%ret.0)
    latch.0():
      jump ^head.0()
    pre.0():
      jump ^head.0()
    loopexit.0():
      jump ^exit.0()
    loopexit.1(%e.1 : demo.Value):
      jump ^catch.0(%e.1)
  }
}
-/
#guard_msgs in
#eval canonText everything

-- `checkModule` rejects the function that the pass repairs, and leaves it as it is.
/-- info: m.f: not canonical -/
#guard_msgs in
#eval checkText everything

-- The pass's output passes `checkModule`.  Its loop's preheader and latch are the blocks that the
-- pass added.
/-- info: m.f: head head.0, preheader pre.0, latch latch.0 -/
#guard_msgs in
#eval rolesText everything

/-! ## A canonical function comes back unchanged -/

private def canonical : String := "module m {
  func @m.g(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^head.0()
    head.0():
      branch(%c.0) ^latch.0() ^exit.0()
    latch.0():
      jump ^head.0()
    exit.0():
      ret(%x.0)
  }
}
"

/-- info: module m {
  func @m.g(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^head.0()
    head.0():
      branch(%c.0) ^latch.0() ^exit.0()
    latch.0():
      jump ^head.0()
    exit.0():
      ret(%x.0)
  }
}
-/
#guard_msgs in
#eval canonText canonical

-- `checkModule` accepts the canonical function unchanged.  Its preheader and latch are blocks it
-- already had: `entry.0` and `latch.0`.
/-- info: module m {
  func @m.g(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^head.0()
    head.0():
      branch(%c.0) ^latch.0() ^exit.0()
    latch.0():
      jump ^head.0()
    exit.0():
      ret(%x.0)
  }
}
-/
#guard_msgs in
#eval checkText canonical

/-- info: m.g: head head.0, preheader entry.0, latch latch.0 -/
#guard_msgs in
#eval rolesText canonical

/-! ## Blocks with several parameters

The head `head` takes two parameters.  The entry passes it different arguments on its two
transfers, and so do the two back edges.  The handler `h` takes an argument from each raising
instruction, and the exception.  The new blocks take the same parameters, and pass them on in
the same order. -/

private def params : String := "module m {
  func @m.p(%c.0 : base.Bool, %x.0 : demo.Value, %z.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value, %z.0 : demo.Value):
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^h.0(%z.0)
      branch(%c.0) ^head.0(%x.0, %z.0) ^head.0(%z.0, %x.0)
    head.0(%i.0 : demo.Value, %s.0 : demo.Value):
      %y.1 : demo.Value = demo.add(%i.0, %s.0) ^h.0(%s.0)
      branch(%c.0) ^head.0(%s.0, %i.0) ^more.0()
    more.0():
      branch(%c.0) ^head.0(%y.1, %i.0) ^out.0()
    out.0():
      ret(%x.0)
    h.0(%p.0 : demo.Value, %e.0 : demo.Value):
      ret(%p.0)
  }
}
"

/-- info: module m {
  func @m.p(%c.0 : base.Bool, %x.0 : demo.Value, %z.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value, %z.0 : demo.Value):
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^h.0(%z.0)
      branch(%c.0) ^pre.0(%x.0, %z.0) ^pre.0(%z.0, %x.0)
    head.0(%i.0 : demo.Value, %s.0 : demo.Value):
      %y.1 : demo.Value = demo.add(%i.0, %s.0) ^loopexit.0(%s.0)
      branch(%c.0) ^latch.0(%s.0, %i.0) ^more.0()
    more.0():
      branch(%c.0) ^latch.0(%y.1, %i.0) ^out.0()
    out.0():
      jump ^post.0(%x.0)
    h.0(%p.0 : demo.Value, %e.0 : demo.Value):
      jump ^post.0(%p.0)
    post.0(%ret.0 : demo.Value):
      ret(%ret.0)
    latch.0(%i.1 : demo.Value, %s.1 : demo.Value):
      jump ^head.0(%i.1, %s.1)
    pre.0(%i.2 : demo.Value, %s.2 : demo.Value):
      jump ^head.0(%i.2, %s.2)
    loopexit.0(%p.1 : demo.Value, %e.1 : demo.Value):
      jump ^h.0(%p.1, %e.1)
  }
}
-/
#guard_msgs in
#eval canonText params

/-! ## Nested loops, and a loop inside a region

The inner loop gets a latch, and the outer loop gets one for its back edge `ih → oh`, in the
same round.  The outer latch is then the inner loop's dedicated exit too.  The inner loop also
gets a preheader.  The region's loop has two back edges, and gets a latch of its own. -/

private def nested : String := "module m {
  func @m.h(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^oh.0()
    oh.0():
      branch(%c.0) ^ih.0() ^exit.0()
    ih.0():
      branch(%c.0) ^ih.0() ^oh.0()
    exit.0():
      %r.0 : demo.Value = demo.if[demo.Value](%c.0) {
        rentry.0():
          jump ^rh.0()
        rh.0():
          branch(%c.0) ^rl.0() ^rexit.0()
        rl.0():
          branch(%c.0) ^rh.0() ^rh.0()
        rexit.0():
          ret(%x.0)
      } {
        else.0():
          ret(%x.0)
      }
      ret(%r.0)
  }
}
"

/-- info: module m {
  func @m.h(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^oh.0()
    oh.0():
      branch(%c.0) ^pre.0() ^exit.0()
    ih.0():
      branch(%c.0) ^latch.1() ^latch.2()
    exit.0():
      %r.0 : demo.Value = demo.if[demo.Value](%c.0) {
        rentry.0():
          jump ^rh.0()
        rh.0():
          branch(%c.0) ^rl.0() ^rexit.0()
        rl.0():
          branch(%c.0) ^latch.0() ^latch.0()
        rexit.0():
          ret(%x.0)
        latch.0():
          jump ^rh.0()
      } {
        else.0():
          ret(%x.0)
      }
      ret(%r.0)
    latch.1():
      jump ^ih.0()
    latch.2():
      jump ^oh.0()
    pre.0():
      jump ^ih.0()
  }
}
-/
#guard_msgs in
#eval canonText nested

/-! ## What the pass cannot fix

In the region, `rl` returns, but its failure repeats the loop, so `rl` is in the loop.  A loop
inside a region that leaves the region is not fixed, so `run` says the result is not
canonical. -/

private def leavesRegion : String := "module m {
  func @m.k(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      %r.0 : demo.Value = demo.if[demo.Value](%c.0) {
        rentry.0():
          jump ^rh.0()
        rh.0():
          branch(%c.0) ^rl.0() ^rl.0()
        rl.0():
          %y.0 : demo.Value = demo.add(%x.0, %x.0) ^again.0()
          ret(%y.0)
        again.0(%e.0 : demo.Value):
          jump ^rh.0()
      } {
        else.0():
          ret(%x.0)
      }
      ret(%r.0)
  }
}
"

/-- info: m.k: not canonical after canonicalization -/
#guard_msgs in
#eval canonText leavesRegion

/-! ## The only return is inside the loop

`head` returns, and its failure repeats the loop, so the return gets a block `post` outside the
loop, though it is the only one. -/

private def returnInLoop : String := "module m {
  func @m.a(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^head.0()
    head.0():
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^again.0()
      ret(%y.0)
    again.0(%e.0 : demo.Value):
      jump ^head.0()
  }
}
"

/-- info: module m {
  func @m.a(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^head.0()
    head.0():
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^again.0()
      jump ^post.0(%y.0)
    again.0(%e.0 : demo.Value):
      jump ^head.0()
    post.0(%ret.0 : demo.Value):
      ret(%ret.0)
  }
}
-/
#guard_msgs in
#eval canonText returnInLoop

/-! ## Two loops that leave to the same block

Both `oh` and `ih` leave to `x`, which the entry also enters.  The inner loop gets a dedicated
exit first.  That block is outside the outer loop and entered only from it, so the outer loop
needs only one more, for `oh`'s transfer. -/

private def sharedExit : String := "module m {
  func @m.s(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^opre.0() ^x.0()
    opre.0():
      jump ^oh.0()
    oh.0():
      branch(%c.0) ^ipre.0() ^x.0()
    ipre.0():
      jump ^ih.0()
    ih.0():
      branch(%c.0) ^ibody.0() ^x.0()
    ibody.0():
      branch(%c.0) ^ilatch.0() ^olatch.0()
    ilatch.0():
      jump ^ih.0()
    olatch.0():
      jump ^oh.0()
    x.0():
      ret(%x.0)
  }
}
"

/-- info: module m {
  func @m.s(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^opre.0() ^x.0()
    opre.0():
      jump ^oh.0()
    oh.0():
      branch(%c.0) ^ipre.0() ^loopexit.1()
    ipre.0():
      jump ^ih.0()
    ih.0():
      branch(%c.0) ^ibody.0() ^loopexit.0()
    ibody.0():
      branch(%c.0) ^ilatch.0() ^olatch.0()
    ilatch.0():
      jump ^ih.0()
    olatch.0():
      jump ^oh.0()
    x.0():
      ret(%x.0)
    loopexit.0():
      jump ^x.0()
    loopexit.1():
      jump ^x.0()
  }
}
-/
#guard_msgs in
#eval canonText sharedExit

/-! ## Two loops in a row, fixed together

Both loops lack a latch and a preheader, and both leave to `x`.  One round gives both their
latches, the next both their preheaders, and the next both their dedicated exits to `x`. -/

private def siblings : String := "module m {
  func @m.r(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^a.0() ^b.0()
    a.0():
      jump ^h1.0()
    b.0():
      jump ^h1.0()
    h1.0():
      branch(%c.0) ^b1.0() ^m.0()
    b1.0():
      branch(%c.0) ^h1.0() ^x.0()
    m.0():
      branch(%c.0) ^h2.0() ^n.0()
    n.0():
      jump ^h2.0()
    h2.0():
      branch(%c.0) ^b2.0() ^x.0()
    b2.0():
      branch(%c.0) ^h2.0() ^x.0()
    x.0():
      ret(%x.0)
  }
}
"

/-- info: module m {
  func @m.r(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^a.0() ^b.0()
    a.0():
      jump ^pre.0()
    b.0():
      jump ^pre.0()
    h1.0():
      branch(%c.0) ^b1.0() ^m.0()
    b1.0():
      branch(%c.0) ^latch.0() ^loopexit.0()
    m.0():
      branch(%c.0) ^pre.1() ^n.0()
    n.0():
      jump ^pre.1()
    h2.0():
      branch(%c.0) ^b2.0() ^loopexit.1()
    b2.0():
      branch(%c.0) ^latch.1() ^loopexit.1()
    x.0():
      ret(%x.0)
    latch.0():
      jump ^h1.0()
    latch.1():
      jump ^h2.0()
    pre.0():
      jump ^h1.0()
    pre.1():
      jump ^h2.0()
    loopexit.0():
      jump ^x.0()
    loopexit.1():
      jump ^x.0()
  }
}
-/
#guard_msgs in
#eval canonText siblings

/-! ## A latch inside a nested loop

`n3` is the outer loop's only back edge and the inner loop's head: its failure goes to `hd0`,
which jumps back to it.  So the inner loop leaves to the outer head `n1`.  The round of exits
waits for a head, and the single fix gives the exit `loopexit.0`. -/

private def latchInInner : String := "module m {
  func @m.q(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^n1.0()
    n1.0():
      branch(%c.0) ^n2.0() ^n3.0()
    n2.0():
      ret(%x.0)
    n3.0():
      %y1.0 : demo.Value = demo.add(%x.0, %x.0) ^hd0.0()
      jump ^n1.0()
    hd0.0(%e0.0 : demo.Value):
      jump ^n3.0()
  }
}
"

/-- info: module m {
  func @m.q(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^n1.0()
    n1.0():
      branch(%c.0) ^n2.0() ^pre.0()
    n2.0():
      ret(%x.0)
    n3.0():
      %y1.0 : demo.Value = demo.add(%x.0, %x.0) ^hd0.0()
      jump ^loopexit.0()
    hd0.0(%e0.0 : demo.Value):
      jump ^n3.0()
    pre.0():
      jump ^n3.0()
    loopexit.0():
      jump ^n1.0()
  }
}
-/
#guard_msgs in
#eval canonText latchInInner

/-! ## A loop with two entries

`a` and `b` form a cycle that no back edge closes, so `run` rejects the function. -/

private def twoEntries : String := "module m {
  func @m.t(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^a.0() ^b.0()
    a.0():
      branch(%c.0) ^b.0() ^out.0()
    b.0():
      branch(%c.0) ^a.0() ^out.0()
    out.0():
      ret(%x.0)
  }
}
"

/-- info: m.t: a loop has two entries -/
#guard_msgs in
#eval canonText twoEntries

/-! ## Modules with several functions

Two functions that the pass rejects, around one that it accepts: both failures are reported, in
the order of the functions. -/

private def twoRejected : String := "module m {
  func @m.t(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^a.0() ^b.0()
    a.0():
      branch(%c.0) ^b.0() ^out.0()
    b.0():
      branch(%c.0) ^a.0() ^out.0()
    out.0():
      ret(%x.0)
  }
  func @m.ok(%x.0 : demo.Value) -> demo.Value {
    entry.0(%x.0 : demo.Value):
      ret(%x.0)
  }
  func @m.k(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      %r.0 : demo.Value = demo.if[demo.Value](%c.0) {
        rentry.0():
          jump ^rh.0()
        rh.0():
          branch(%c.0) ^rl.0() ^rl.0()
        rl.0():
          %y.0 : demo.Value = demo.add(%x.0, %x.0) ^again.0()
          ret(%y.0)
        again.0(%e.0 : demo.Value):
          jump ^rh.0()
      } {
        else.0():
          ret(%x.0)
      }
      ret(%r.0)
  }
}
"

/-- info: m.t: a loop has two entries
m.k: not canonical after canonicalization -/
#guard_msgs in
#eval canonText twoRejected

-- Two functions that the pass accepts: each is put in canonical form, and they keep their order.
private def twoAccepted : String := "module m {
  func @m.a(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^head.0()
    head.0():
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^again.0()
      ret(%y.0)
    again.0(%e.0 : demo.Value):
      jump ^head.0()
  }
  func @m.ok(%x.0 : demo.Value) -> demo.Value {
    entry.0(%x.0 : demo.Value):
      ret(%x.0)
  }
}
"

/-- info: module m {
  func @m.a(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^head.0()
    head.0():
      %y.0 : demo.Value = demo.add(%x.0, %x.0) ^again.0()
      jump ^post.0(%y.0)
    again.0(%e.0 : demo.Value):
      jump ^head.0()
    post.0(%ret.0 : demo.Value):
      ret(%ret.0)
  }
  func @m.ok(%x.0 : demo.Value) -> demo.Value {
    entry.0(%x.0 : demo.Value):
      ret(%x.0)
  }
}
-/
#guard_msgs in
#eval canonText twoAccepted

/-- A module whose extern's precondition reads a ghost: the pass keeps the ghost, so the
contract's ghost reference still resolves. -/
private def withGhost : String := "module m {
  ghost @m.count : base.Int = {
    init.0():
      ret(0)
  }
  func @m.f(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^head.0() ^exit.0()
    head.0():
      branch(%c.0) ^head.0() ^exit.0()
    exit.0():
      ret(%x.0)
  }
  extern func @m.tick(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %n.0 : base.Int = base.refGet[base.Int](ghost @m.count)
        ret(true)
    }
}
"

/-- info: module m {
  ghost @m.count : base.Int = {
    init.0():
      ret(0)
  }
  func @m.f(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      branch(%c.0) ^pre.0() ^exit.0()
    head.0():
      branch(%c.0) ^latch.0() ^loopexit.0()
    exit.0():
      ret(%x.0)
    latch.0():
      jump ^head.0()
    pre.0():
      jump ^head.0()
    loopexit.0():
      jump ^exit.0()
  }
  extern func @m.tick(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %n.0 : base.Int = base.refGet[base.Int](ghost @m.count)
        ret(true)
    }
}
-/
#guard_msgs in
#eval canonText withGhost

end Strata.Dyn.CanonicalizeTest
