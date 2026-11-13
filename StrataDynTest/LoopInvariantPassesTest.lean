/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Canonicalize
public import StrataDyn.RefToReg
public import StrataDyn.Cases.Shape
public import StrataDyn.Demote
public import StrataDyn.DDMRead
public import StrataDynTest.DSLTest
import StrataDyn.Env.WF
import StrataDyn.DSL
-- The reader and the passes run as compiled code below.
meta import StrataDyn.Canonicalize
meta import StrataDyn.RefToReg
meta import StrataDyn.Cases.Shape
meta import StrataDyn.Demote
meta import StrataDyn.DDMRead
meta import StrataDyn.Env.WF
meta import StrataDynTest.DSLTest

set_option autoImplicit false

/-!
# Loop invariants through canonicalization and ref-to-reg

A front end puts a loop's invariants at the start of the loop's head, and a later stage finds
them through `Body.loopRoles` after canonicalization.  So canonicalization must keep each
invariant at the start of its head, and ref-to-reg must keep it there too.  Ref-to-reg still
promotes a cell that an invariant reads: the invariant then reads the head's new parameter.

Each test before the last section reads a function, puts it in canonical form with
`Canonicalize.runModule`, runs `refToReg` on the result, and prints the module after each pass.
It then checks that the result of ref-to-reg is still canonical, and prints, for each loop that
`Body.loopRoles` names, its head, its preheader, its latch and how many invariants lead its head,
and each block that holds an invariant but heads no loop.

The loops: one whose counter lives in a cell; one with a `continue` and a `break`; one left by a
failure and by a `return`; a `for`-shaped one; nested ones; a head that no back edge reaches; one
inside a region of the body; one whose failure handler jumps back to the head; one whose back edge
is a failure successor; and one with cells that ref-to-reg promotes or keeps, next to an `old` read
of a parameter cell.  Then two that canonicalization rejects: a loop with two entries, and a loop
that leaves its region.  Then a latch that canonicalization adds and ref-to-reg extends with a
cell's content.  Then two blocks that hold an invariant but head no loop: a join block, which
ref-to-reg extends with a cell's content, and a region's entry block, whose invariant ref-to-reg
rewrites to read the cell's content.  Then a loop of a front end whose loops end with a completion,
under its `CanonicalSpec`.  Last, two tests run the same passes and print only whether case
lowering (`CasesInput`) and demotion (`Demotable`) take the result.  Both take only bodies whose
instructions have no regions, so neither takes a function with an invariant. -/

namespace Strata.Dyn.LoopInvariantPassesTest

/-- Integer operations, one that may fail, one that writes, and an operation that runs a
region. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- `lhs < rhs`. -/
  pure insn lt (lhs rhs : Int) : Bool
  /-- `lhs + rhs`. -/
  pure insn add (lhs rhs : Int) : Int
  /-- `a / b`.  It fails, with an error code, when `b` is zero. -/
  calls insn div (a b : Int) (^err (e : Int)) : Int
  /-- The next element of a sequence that `c` walks, or a transfer to `stop` at its end. -/
  calls insn next (c : Ref Int) (^stop) : Int
  /-- Passes `c` to code that the IR does not show. -/
  writes insn use (c : Ref Int) : Unit
  /-- Runs `body` once, and returns its value. -/
  pure insn once (&body : Int) : Int
  end demo

private abbrev E := Demo.env

variable {env : Env Unit} [base ≼ env]

/-- The number of loop invariants that lead the block labelled `l` in `bs`. -/
private def leading (bs : List (Block env Info)) (l : Label) : Nat :=
  match bs.find? (·.label == l) with
  | some b => (b.instrs.toList.takeWhile (·.isLoopInvariant)).length
  | none => 0

/-- The bodies of `f`: its own, then each region's, at any depth. -/
private def bodies (f : Func env Info) : List (List (Block env Info)) :=
  f.blocks.toList :: (Region.allList (f.blocks.toList.flatMap fun b =>
    b.instrs.toList.flatMap (·.regions.toList) ++ b.term.regions.toList)).map (·.blocks.toList)

/-- Each loop of each body of `m`'s functions, as `Body.loopRoles` names it, with the number of
invariants that lead its head; then each block that holds an invariant but heads no loop, which
a consumer that handles invariants only at loop heads rejects. -/
private def roles (m : Module env Info) : List String :=
  m.raw.funcs.toList.flatMap fun f => (bodies f).flatMap fun bs =>
    let rs := Body.loopRoles bs
    (rs.map fun r =>
      s!"{ToDDM.nameText f.name}: head {ToDDM.nameText r.head.name} with \
        {leading bs r.head} invariants, preheader {ToDDM.nameText r.preheader.name}, \
        latch {ToDDM.nameText r.latch.name}") ++
    (bs.filter fun b => leading bs b.label > 0 && !rs.any (·.head == b.label)).map fun b =>
      s!"{ToDDM.nameText f.name}: {ToDDM.nameText b.label.name} holds an invariant and heads no loop"

/-- Read `text` in `env`, put it in canonical form with `spec`, run ref-to-reg, check that the
result is still canonical, and print both modules and the loops of the last one. -/
private def passes (env : Env Unit) [base ≼ env] (text : String)
    (spec : CanonicalSpec env Info := {}) : IO Unit := do
  match ← Module.read env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match Canonicalize.runModule m spec with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok cm =>
      IO.println "-- canonical"
      IO.print (toString cm.module)
      match refToReg cm.module with
      | .error es => for (n, e) in es do IO.println s!"{ToDDM.nameText n}: {e}"
      | .ok m₁ =>
        IO.println "-- ref-to-reg"
        IO.print (toString m₁)
        match Canonicalize.checkModule m₁ spec with
        | .error fs => for f in fs do IO.println (toString f)
        | .ok cm₁ => for r in roles cm₁.module do IO.println r

/-- A loop whose counter lives in a cell, with an invariant that reads the cell. -/
private def counter := "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %ok.0 : base.Bool = demo.ge(%v.0, 0)
          ret(%ok.0)
      }
      %v.1 : base.Int = base.refGet[base.Int](%c.0)
      %k.0 : base.Bool = demo.lt(%v.1, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %v.2 : base.Int = base.refGet[base.Int](%c.0)
      %j.0 : base.Int = demo.add(%v.2, 1)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %j.0)
      jump ^head.0()
    done.0():
      %v.3 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.3)
  }
}
"

/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %ok.0 : base.Bool = demo.ge(%v.0, 0)
          ret(%ok.0)
      }
      %v.1 : base.Int = base.refGet[base.Int](%c.0)
      %k.0 : base.Bool = demo.lt(%v.1, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %v.2 : base.Int = base.refGet[base.Int](%c.0)
      %j.0 : base.Int = demo.add(%v.2, 1)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %j.0)
      jump ^head.0()
    done.0():
      %v.3 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.3)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0(0)
    head.0(%c.4 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%c.4, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%c.4, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%c.4, 1)
      jump ^head.0(%j.0)
    done.0():
      ret(%c.4)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch body.0 -/
#guard_msgs in
#eval passes E counter

-- A loop with a `continue` and a `break`: two back edges, which canonicalization merges into one
-- latch, and an exit from the body.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      %b.0 : base.Bool = demo.ge(%j.0, 10)
      branch(%b.0) ^done.0() ^more.0()
    more.0():
      %c.0 : base.Bool = demo.ge(%j.0, 5)
      branch(%c.0) ^latch.0(%j.0) ^tail.0()
    tail.0():
      jump ^latch.0(%j.0)
    done.0():
      ret(%i.0)
    latch.0(%i.1 : base.Int):
      jump ^head.0(%i.1)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      %b.0 : base.Bool = demo.ge(%j.0, 10)
      branch(%b.0) ^done.0() ^more.0()
    more.0():
      %c.0 : base.Bool = demo.ge(%j.0, 5)
      branch(%c.0) ^latch.0(%j.0) ^tail.0()
    tail.0():
      jump ^latch.0(%j.0)
    done.0():
      ret(%i.0)
    latch.0(%i.1 : base.Int):
      jump ^head.0(%i.1)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch latch.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      %b.0 : base.Bool = demo.ge(%j.0, 10)
      branch(%b.0) ^done.0() ^more.0()
    more.0():
      %c.0 : base.Bool = demo.ge(%j.0, 5)
      branch(%c.0) ^head.0(%j.0) ^tail.0()
    tail.0():
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
}
"

-- A loop left by a failure (a raise out of the loop) and by a `return` from the body.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, %i.0) ^raised.0()
      %b.0 : base.Bool = demo.ge(%q.0, 3)
      branch(%b.0) ^early.0() ^step.0()
    step.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    early.0():
      jump ^post.0(%q.0)
    done.0():
      jump ^post.0(%i.0)
    raised.0(%e.0 : base.Int):
      jump ^post.0(%e.0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, %i.0) ^raised.0()
      %b.0 : base.Bool = demo.ge(%q.0, 3)
      branch(%b.0) ^early.0() ^step.0()
    step.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    early.0():
      jump ^post.0(%q.0)
    done.0():
      jump ^post.0(%i.0)
    raised.0(%e.0 : base.Int):
      jump ^post.0(%e.0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch step.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, %i.0) ^raised.0()
      %b.0 : base.Bool = demo.ge(%q.0, 3)
      branch(%b.0) ^early.0() ^step.0()
    step.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    early.0():
      ret(%q.0)
    done.0():
      ret(%i.0)
    raised.0(%e.0 : base.Int):
      ret(%e.0)
  }
}
"

-- A `for`-shaped loop: the head takes the next element, and leaves the loop when there is none.
/-- info: -- canonical
module m {
  func @m.f(%it.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%it.0 : base.Ref(base.Int)):
      jump ^head.0(0)
    head.0(%s.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%s.0, 0)
          ret(%ok.0)
      }
      %x.0 : base.Int = demo.next(%it.0) ^done.0()
      %s.1 : base.Int = demo.add(%s.0, %x.0)
      jump ^head.0(%s.1)
    done.0():
      ret(%s.0)
  }
}
-- ref-to-reg
module m {
  func @m.f(%it.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%it.0 : base.Ref(base.Int)):
      jump ^head.0(0)
    head.0(%s.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%s.0, 0)
          ret(%ok.0)
      }
      %x.0 : base.Int = demo.next(%it.0) ^done.0()
      %s.1 : base.Int = demo.add(%s.0, %x.0)
      jump ^head.0(%s.1)
    done.0():
      ret(%s.0)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch head.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%it.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%it.0 : base.Ref(base.Int)):
      jump ^head.0(0)
    head.0(%s.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%s.0, 0)
          ret(%ok.0)
      }
      %x.0 : base.Int = demo.next(%it.0) ^done.0()
      %s.1 : base.Int = demo.add(%s.0, %x.0)
      jump ^head.0(%s.1)
    done.0():
      ret(%s.0)
  }
}
"

-- Nested loops, each with an invariant at its head.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^outer.0(0)
    outer.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^pre.0(0) ^done.0()
    inner.0(%j.0 : base.Int):
      %inv.1 : base.Unit = base.loopInvariant {
        inv.1():
          %ok.1 : base.Bool = demo.ge(%j.0, 0)
          ret(%ok.1)
      }
      %d.0 : base.Bool = demo.lt(%j.0, %i.0)
      branch(%d.0) ^step.0() ^next.0()
    step.0():
      %j.1 : base.Int = demo.add(%j.0, 1)
      jump ^inner.0(%j.1)
    next.0():
      %i.1 : base.Int = demo.add(%i.0, 1)
      jump ^outer.0(%i.1)
    done.0():
      ret(%i.0)
    pre.0(%j.2 : base.Int):
      jump ^inner.0(%j.2)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^outer.0(0)
    outer.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^pre.0(0) ^done.0()
    inner.0(%j.0 : base.Int):
      %inv.1 : base.Unit = base.loopInvariant {
        inv.1():
          %ok.1 : base.Bool = demo.ge(%j.0, 0)
          ret(%ok.1)
      }
      %d.0 : base.Bool = demo.lt(%j.0, %i.0)
      branch(%d.0) ^step.0() ^next.0()
    step.0():
      %j.1 : base.Int = demo.add(%j.0, 1)
      jump ^inner.0(%j.1)
    next.0():
      %i.1 : base.Int = demo.add(%i.0, 1)
      jump ^outer.0(%i.1)
    done.0():
      ret(%i.0)
    pre.0(%j.2 : base.Int):
      jump ^inner.0(%j.2)
  }
}
m.f: head inner.0 with 1 invariants, preheader pre.0, latch step.0
m.f: head outer.0 with 1 invariants, preheader entry.0, latch next.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^outer.0(0)
    outer.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%i.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^inner.0(0) ^done.0()
    inner.0(%j.0 : base.Int):
      %inv.1 : base.Unit = base.loopInvariant {
        inv.1():
          %ok.1 : base.Bool = demo.ge(%j.0, 0)
          ret(%ok.1)
      }
      %d.0 : base.Bool = demo.lt(%j.0, %i.0)
      branch(%d.0) ^step.0() ^next.0()
    step.0():
      %j.1 : base.Int = demo.add(%j.0, 1)
      jump ^inner.0(%j.1)
    next.0():
      %i.1 : base.Int = demo.add(%i.0, 1)
      jump ^outer.0(%i.1)
    done.0():
      ret(%i.0)
  }
}
"

-- A head that no back edge reaches (`while c: return x`): `Body.loopRoles` names no loop, and
-- the invariant stays where it is.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      jump ^post.0(%n.0)
    done.0():
      jump ^post.0(0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      jump ^post.0(%n.0)
    done.0():
      jump ^post.0(0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
  }
}
m.f: head.0 holds an invariant and heads no loop -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      ret(%n.0)
    done.0():
      ret(0)
  }
}
"

-- A loop inside a region of the body, whose cell ref-to-reg promotes inside the region.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %r.0 : base.Int = demo.once {
        once.0():
          %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
          jump ^head.0()
        head.0():
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %v.0 : base.Int = base.refGet[base.Int](%c.0)
              %ok.0 : base.Bool = demo.ge(%v.0, 0)
              ret(%ok.0)
          }
          %v.1 : base.Int = base.refGet[base.Int](%c.0)
          %k.0 : base.Bool = demo.lt(%v.1, %n.0)
          branch(%k.0) ^body.0() ^done.0()
        body.0():
          %v.2 : base.Int = base.refGet[base.Int](%c.0)
          %j.0 : base.Int = demo.add(%v.2, 1)
          %u.0 : base.Unit = base.refSet[base.Int](%c.0, %j.0)
          jump ^head.0()
        done.0():
          %v.3 : base.Int = base.refGet[base.Int](%c.0)
          ret(%v.3)
      }
      ret(%r.0)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %r.0 : base.Int = demo.once {
        once.0():
          %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
          jump ^head.0(0)
        head.0(%c.4 : base.Int):
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %ok.0 : base.Bool = demo.ge(%c.4, 0)
              ret(%ok.0)
          }
          %k.0 : base.Bool = demo.lt(%c.4, %n.0)
          branch(%k.0) ^body.0() ^done.0()
        body.0():
          %j.0 : base.Int = demo.add(%c.4, 1)
          jump ^head.0(%j.0)
        done.0():
          ret(%c.4)
      }
      ret(%r.0)
  }
}
m.f: head head.0 with 1 invariants, preheader once.0, latch body.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %r.0 : base.Int = demo.once {
        once.0():
          %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
          jump ^head.0()
        head.0():
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %v.0 : base.Int = base.refGet[base.Int](%c.0)
              %ok.0 : base.Bool = demo.ge(%v.0, 0)
              ret(%ok.0)
          }
          %v.1 : base.Int = base.refGet[base.Int](%c.0)
          %k.0 : base.Bool = demo.lt(%v.1, %n.0)
          branch(%k.0) ^body.0() ^done.0()
        body.0():
          %v.2 : base.Int = base.refGet[base.Int](%c.0)
          %j.0 : base.Int = demo.add(%v.2, 1)
          %u.0 : base.Unit = base.refSet[base.Int](%c.0, %j.0)
          jump ^head.0()
        done.0():
          %v.3 : base.Int = base.refGet[base.Int](%c.0)
          ret(%v.3)
      }
      ret(%r.0)
  }
}
"

-- A failure handler that jumps back to the head: the failure of `div` goes to `again.0`, whose jump
-- is the back edge.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, 0) ^again.0()
      jump ^loopexit.0(%q.0)
    again.0(%e.0 : base.Int):
      jump ^head.0()
    done.0():
      jump ^post.0(0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
    loopexit.0(%ret.1 : base.Int):
      jump ^post.0(%ret.1)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, 0) ^again.0()
      jump ^loopexit.0(%q.0)
    again.0(%e.0 : base.Int):
      jump ^head.0()
    done.0():
      jump ^post.0(0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
    loopexit.0(%ret.1 : base.Int):
      jump ^post.0(%ret.1)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch again.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, 0) ^again.0()
      ret(%q.0)
    again.0(%e.0 : base.Int):
      jump ^head.0()
    done.0():
      ret(0)
  }
}
"

-- A head whose back edge is a failure successor: the failure of `div` goes to the head itself,
-- with the error code as the head's parameter.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%e.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%e.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, 0) ^latch.0()
      jump ^loopexit.0(%q.0)
    done.0():
      jump ^post.0(0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
    latch.0(%e.1 : base.Int):
      jump ^head.0(%e.1)
    loopexit.0(%ret.1 : base.Int):
      jump ^post.0(%ret.1)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%e.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%e.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, 0) ^latch.0()
      jump ^loopexit.0(%q.0)
    done.0():
      jump ^post.0(0)
    post.0(%ret.0 : base.Int):
      ret(%ret.0)
    latch.0(%e.1 : base.Int):
      jump ^head.0(%e.1)
    loopexit.0(%ret.1 : base.Int):
      jump ^post.0(%ret.1)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch latch.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(0)
    head.0(%e.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%e.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%n.0, 3)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %q.0 : base.Int = demo.div(%n.0, 0) ^head.0()
      ret(%q.0)
    done.0():
      ret(0)
  }
}
"

-- Cells: `%a.0`, which only the invariant reads and the loop writes, is promoted; `%b.0`, which
-- escapes to `use`, is not; and the `old` region's read of the parameter cell `%p.0` stays a
-- read in the state at the call.
/-- info: -- canonical
module m {
  func @m.f(%p.0 : base.Ref(base.Int), %n.0 : base.Int) -> base.Int {
    entry.0(%p.0 : base.Ref(base.Int), %n.0 : base.Int):
      %a.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %b.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = demo.use(%b.0)
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%a.0)
          %w.0 : base.Int = base.refGet[base.Int](%b.0)
          %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
            old.0():
              %x.0 : base.Int = base.refGet[base.Int](%p.0)
              %y.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
              ret(%y.0)
          }
          %s.0 : base.Int = demo.add(%v.0, %w.0)
          %ok.0 : base.Bool = demo.ge(%s.0, %o.0)
          ret(%ok.0)
        fail.0(%e.0 : base.Int):
          ret(false)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %u.1 : base.Unit = base.refSet[base.Int](%a.0, %i.0)
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
}
-- ref-to-reg
module m {
  func @m.f(%p.0 : base.Ref(base.Int), %n.0 : base.Int) -> base.Int {
    entry.0(%p.0 : base.Ref(base.Int), %n.0 : base.Int):
      %a.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %b.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = demo.use(%b.0)
      jump ^head.0(0, 0)
    head.0(%i.0 : base.Int, %c.5 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %w.0 : base.Int = base.refGet[base.Int](%b.0)
          %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
            old.0():
              %x.0 : base.Int = base.refGet[base.Int](%p.0)
              %y.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
              ret(%y.0)
          }
          %s.0 : base.Int = demo.add(%c.5, %w.0)
          %ok.0 : base.Bool = demo.ge(%s.0, %o.0)
          ret(%ok.0)
        fail.0(%e.0 : base.Int):
          ret(false)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0, %i.0)
    done.0():
      ret(%i.0)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch body.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%p.0 : base.Ref(base.Int), %n.0 : base.Int) -> base.Int {
    entry.0(%p.0 : base.Ref(base.Int), %n.0 : base.Int):
      %a.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %b.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = demo.use(%b.0)
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%a.0)
          %w.0 : base.Int = base.refGet[base.Int](%b.0)
          %o.0 : base.Int = base.old[base.Int, base.Int] ^fail.0() {
            old.0():
              %x.0 : base.Int = base.refGet[base.Int](%p.0)
              %y.0 : base.Except(base.Int, base.Int) = base.ok[base.Int, base.Int](%x.0)
              ret(%y.0)
          }
          %s.0 : base.Int = demo.add(%v.0, %w.0)
          %ok.0 : base.Bool = demo.ge(%s.0, %o.0)
          ret(%ok.0)
        fail.0(%e.0 : base.Int):
          ret(false)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %u.1 : base.Unit = base.refSet[base.Int](%a.0, %i.0)
      %j.0 : base.Int = demo.add(%i.0, 1)
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
}
"

-- A loop with two entries, which `Canonicalize.run` rejects: the function fails, and nothing
-- drops its invariant silently.
/-- info: m.f: a loop has two entries -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%c.0 : base.Bool, %n.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %n.0 : base.Int):
      branch(%c.0) ^a.0() ^b.0()
    a.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%n.0, 0)
          ret(%ok.0)
      }
      branch(%c.0) ^b.0() ^done.0()
    b.0():
      branch(%c.0) ^a.0() ^done.0()
    done.0():
      ret(%n.0)
  }
}
"

-- A loop inside a region that leaves the region from inside the loop, which the pass reports as
-- not canonical: the function is rejected, so its invariant is not dropped silently.
/-- info: m.f: not canonical after canonicalization -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %r.0 : base.Int = demo.once {
        once.0():
          jump ^head.0()
        head.0():
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %ok.0 : base.Bool = demo.ge(%n.0, 0)
              ret(%ok.0)
          }
          %q.0 : base.Int = demo.div(%n.0, 0) ^again.0()
          ret(%q.0)
        again.0(%e.0 : base.Int):
          jump ^head.0()
      }
      ret(%r.0)
  }
}
"

-- A loop whose `continue` and whose body's end leave different contents in a cell that only the
-- invariant reads: canonicalization merges the two back edges into a latch, and ref-to-reg gives
-- that latch the cell's content as a new parameter.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %ok.0 : base.Bool = demo.ge(%v.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      %b.0 : base.Bool = demo.ge(%j.0, 5)
      branch(%b.0) ^a.0() ^bb.0()
    a.0():
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %j.0)
      jump ^latch.0(%j.0)
    bb.0():
      %u.1 : base.Unit = base.refSet[base.Int](%c.0, %i.0)
      jump ^latch.0(%j.0)
    done.0():
      ret(%i.0)
    latch.0(%i.1 : base.Int):
      jump ^head.0(%i.1)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0(0, 0)
    head.0(%i.0 : base.Int, %c.6 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%c.6, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      %b.0 : base.Bool = demo.ge(%j.0, 5)
      branch(%b.0) ^a.0() ^bb.0()
    a.0():
      jump ^latch.0(%j.0, %j.0)
    bb.0():
      jump ^latch.0(%j.0, %i.0)
    done.0():
      ret(%i.0)
    latch.0(%i.1 : base.Int, %c.7 : base.Int):
      jump ^head.0(%i.1, %c.7)
  }
}
m.f: head head.0 with 1 invariants, preheader entry.0, latch latch.0 -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0(0)
    head.0(%i.0 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %ok.0 : base.Bool = demo.ge(%v.0, 0)
          ret(%ok.0)
      }
      %k.0 : base.Bool = demo.lt(%i.0, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %j.0 : base.Int = demo.add(%i.0, 1)
      %b.0 : base.Bool = demo.ge(%j.0, 5)
      branch(%b.0) ^a.0() ^bb.0()
    a.0():
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %j.0)
      jump ^head.0(%j.0)
    bb.0():
      %u.1 : base.Unit = base.refSet[base.Int](%c.0, %i.0)
      jump ^head.0(%j.0)
    done.0():
      ret(%i.0)
  }
}
"

-- An invariant in a join block, which heads no loop, that alone reads a cell with two contents:
-- ref-to-reg gives the join block the content as a new parameter.
/-- info: -- canonical
module m {
  func @m.f(%b.0 : base.Bool, %n.0 : base.Int) -> base.Int {
    entry.0(%b.0 : base.Bool, %n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      branch(%b.0) ^l.0() ^r.0()
    l.0():
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, 1)
      jump ^join.0()
    r.0():
      %u.1 : base.Unit = base.refSet[base.Int](%c.0, %n.0)
      jump ^join.0()
    join.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %ok.0 : base.Bool = demo.ge(%v.0, 0)
          ret(%ok.0)
      }
      ret(%n.0)
  }
}
-- ref-to-reg
module m {
  func @m.f(%b.0 : base.Bool, %n.0 : base.Int) -> base.Int {
    entry.0(%b.0 : base.Bool, %n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      branch(%b.0) ^l.0() ^r.0()
    l.0():
      jump ^join.0(1)
    r.0():
      jump ^join.0(%n.0)
    join.0(%c.4 : base.Int):
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %ok.0 : base.Bool = demo.ge(%c.4, 0)
          ret(%ok.0)
      }
      ret(%n.0)
  }
}
m.f: join.0 holds an invariant and heads no loop -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%b.0 : base.Bool, %n.0 : base.Int) -> base.Int {
    entry.0(%b.0 : base.Bool, %n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      branch(%b.0) ^l.0() ^r.0()
    l.0():
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, 1)
      jump ^join.0()
    r.0():
      %u.1 : base.Unit = base.refSet[base.Int](%c.0, %n.0)
      jump ^join.0()
    join.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          %v.0 : base.Int = base.refGet[base.Int](%c.0)
          %ok.0 : base.Bool = demo.ge(%v.0, 0)
          ret(%ok.0)
      }
      ret(%n.0)
  }
}
"

-- An invariant in a region's entry block, which heads no loop, reading a cell of the body.
/-- info: -- canonical
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %n.0)
      %r.0 : base.Int = demo.once {
        once.0():
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %v.0 : base.Int = base.refGet[base.Int](%c.0)
              %ok.0 : base.Bool = demo.ge(%v.0, 0)
              ret(%ok.0)
          }
          %v.1 : base.Int = base.refGet[base.Int](%c.0)
          ret(%v.1)
      }
      ret(%r.0)
  }
}
-- ref-to-reg
module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %r.0 : base.Int = demo.once {
        once.0():
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %ok.0 : base.Bool = demo.ge(%n.0, 0)
              ret(%ok.0)
          }
          ret(%n.0)
      }
      ret(%r.0)
  }
}
m.f: once.0 holds an invariant and heads no loop -/
#guard_msgs in
#eval passes E "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %n.0)
      %r.0 : base.Int = demo.once {
        once.0():
          %inv.0 : base.Unit = base.loopInvariant {
            inv.0():
              %v.0 : base.Int = base.refGet[base.Int](%c.0)
              %ok.0 : base.Bool = demo.ge(%v.0, 0)
              ret(%ok.0)
          }
          %v.1 : base.Int = base.refGet[base.Int](%c.0)
          ret(%v.1)
      }
      ret(%r.0)
  }
}
"

/-! ## With a front end's spec

The front end of `DSLTest`'s `Demo.env` ends its loops with a completion, and states each loop's
head and `done` block in a `LoopRecord`, as a Python front end does.  Canonicalization then also
checks that every way out of the loop meets in `done`. -/

/-- The roles of the completion datatype of `DSLTest`'s `Demo.env`. -/
private def demoShape : CompletionShape DSLTest.Demo.env :=
  { ty := DSLTest.Demo.Completion, data := DSLTest.Demo.Completion.name,
    normal := DSLTest.Demo.Completion.normal.name, brk := DSLTest.Demo.Completion.broke.name,
    cont := DSLTest.Demo.Completion.continued.name,
    forwarded := [DSLTest.Demo.Completion.returned.name, DSLTest.Demo.Completion.raised.name] }

/-- The spec of a function whose only loop has head `head.0` and `done` block `done.0`. -/
private def specOf : CanonicalSpec DSLTest.Demo.env Info :=
  let r : LoopRecord :=
    { head := ⟨.num (.str .base "head") 0⟩, done := some ⟨.num (.str .base "done") 0⟩ }
  { shape := some demoShape, preamble := true, records := fun _ => [r] }

-- `while c: if c: break`, whose invariant stays at the head.
/-- info: -- canonical
module m {
  func @m.w(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^body.0()
    body.0():
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(%c.0)
      }
      branch(%c.0) ^loop.0() ^normal.0()
    loop.0():
      branch(%c.0) ^latch.0() ^brk.0()
    normal.0():
      %k.0 : demo.Completion = demo.normal
      jump ^done.0(%k.0)
    brk.0():
      %k.1 : demo.Completion = demo.broke
      jump ^done.0(%k.1)
    done.0(%k.2 : demo.Completion):
      demo.Completion.case(%k.2) ^after.0() ^ret.0() ^unr.0() ^after.0() ^unr.1()
    ret.0(%v.0 : demo.Value):
      jump ^post.0(%v.0)
    unr.0(%e.0 : demo.Value):
      unreachable
    unr.1():
      unreachable
    after.0():
      jump ^post.0(%x.0)
    post.0(%ret.0 : demo.Value):
      ret(%ret.0)
    latch.0():
      jump ^head.0()
  }
}
-- ref-to-reg
module m {
  func @m.w(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^body.0()
    body.0():
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(%c.0)
      }
      branch(%c.0) ^loop.0() ^normal.0()
    loop.0():
      branch(%c.0) ^latch.0() ^brk.0()
    normal.0():
      %k.0 : demo.Completion = demo.normal
      jump ^done.0(%k.0)
    brk.0():
      %k.1 : demo.Completion = demo.broke
      jump ^done.0(%k.1)
    done.0(%k.2 : demo.Completion):
      demo.Completion.case(%k.2) ^after.0() ^ret.0() ^unr.0() ^after.0() ^unr.1()
    ret.0(%v.0 : demo.Value):
      jump ^post.0(%v.0)
    unr.0(%e.0 : demo.Value):
      unreachable
    unr.1():
      unreachable
    after.0():
      jump ^post.0(%x.0)
    post.0(%ret.0 : demo.Value):
      ret(%ret.0)
    latch.0():
      jump ^head.0()
  }
}
m.w: head head.0 with 1 invariants, preheader body.0, latch latch.0 -/
#guard_msgs in
#eval passes DSLTest.Demo.env "module m {
  func @m.w(%c.0 : base.Bool, %x.0 : demo.Value) -> demo.Value {
    entry.0(%c.0 : base.Bool, %x.0 : demo.Value):
      jump ^body.0()
    body.0():
      jump ^head.0()
    head.0():
      %inv.0 : base.Unit = base.loopInvariant {
        inv.0():
          ret(%c.0)
      }
      branch(%c.0) ^loop.0() ^normal.0()
    loop.0():
      branch(%c.0) ^head.0() ^brk.0()
    normal.0():
      %k.0 : demo.Completion = demo.normal
      jump ^done.0(%k.0)
    brk.0():
      %k.1 : demo.Completion = demo.broke
      jump ^done.0(%k.1)
    done.0(%k.2 : demo.Completion):
      demo.Completion.case(%k.2) ^after.0() ^ret.0() ^unr.0() ^after.0() ^unr.1()
    ret.0(%v.0 : demo.Value):
      ret(%v.0)
    unr.0(%e.0 : demo.Value):
      unreachable
    unr.1():
      unreachable
    after.0():
      ret(%x.0)
  }
}
" specOf

/-! ## Case lowering and demotion

Case lowering (`CasesInput`) and demotion (`Demotable`) take only bodies whose instructions have
no regions, and an invariant has a region.  So neither pass takes ref-to-reg's result for the
first test's loop, but both take it for the same loop without its invariant. -/

/-- Read `text`, run canonicalization and ref-to-reg, and print whether case lowering and
demotion take the result. -/
private def lowerable (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match Canonicalize.runModule m {} with
    | .error fs => for f in fs do IO.println (toString f)
    | .ok cm =>
      match refToReg cm.module with
      | .error es => for (n, e) in es do IO.println s!"{ToDDM.nameText n}: {e}"
      | .ok m₁ =>
        IO.println s!"case lowering takes it: {decide (CasesInput m₁.raw)}"
        IO.println s!"demotion takes it: {decide (Demotable m₁.raw)}"

/--
info: case lowering takes it: false
demotion takes it: false
-/
#guard_msgs in
#eval lowerable counter

/-- `counter` without its invariant. -/
private def counterPlain := "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %c.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0()
    head.0():
      %v.1 : base.Int = base.refGet[base.Int](%c.0)
      %k.0 : base.Bool = demo.lt(%v.1, %n.0)
      branch(%k.0) ^body.0() ^done.0()
    body.0():
      %v.2 : base.Int = base.refGet[base.Int](%c.0)
      %j.0 : base.Int = demo.add(%v.2, 1)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %j.0)
      jump ^head.0()
    done.0():
      %v.3 : base.Int = base.refGet[base.Int](%c.0)
      ret(%v.3)
  }
}
"

/--
info: case lowering takes it: true
demotion takes it: true
-/
#guard_msgs in
#eval lowerable counterPlain

end Strata.Dyn.LoopInvariantPassesTest
