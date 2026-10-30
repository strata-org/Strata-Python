/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToReg
public import StrataDyn.DDMRead
public import StrataDyn.DDM
public import StrataDynTest.RefToRegSim
import StrataDyn.Env.WF
import StrataDyn.DSL
-- The reader, the pass and the printer run as compiled code below.
meta import StrataDyn.RefToReg
meta import StrataDyn.DDMRead
meta import StrataDyn.DDM
meta import StrataDynTest.RefToRegSim
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Ref-to-reg

Small modules, read from their printed form, promoted, and printed again.  The environment has
an operation that raises, one that a cell escapes through, and operations with regions: one
region, two regions, a region over an item, and a terminator with a region and a successor.
-/

namespace Strata.Dyn.RefToRegTest

open Strata.Dyn.RefToReg
open Strata.Dyn.ToDDM (nameText)

/-- The operations the tests use. -/
public environment R2R extends Base where
  namespace r2r
  open base
  /-- `a + b`. -/
  insn add (a b : Int) : Int
  /-- `a < b`. -/
  insn lt (a b : Int) : Bool
  /-- `x`, or a raised `e` to `err`. -/
  insn may (x : Int) (^err (e : Int)) : Int
  /-- An operation that a cell escapes through. -/
  insn use (c : Ref Int) : Unit
  /-- Run `then` if `cond` holds, else `else`. -/
  insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  /-- Run `body`; if it raises, run `handler` on the exception. -/
  insn «try» (&body : Int) (&handler (e : Int) : Int) : Int
  /-- Run `body` once per item below `n`. -/
  insn each (n : Int) (&body (item : Int) : Unit) : Unit
  /-- Run `body` until it returns `false`, then leave to `exit`. -/
  terminal insn loop (&body : Bool) (^exit)
  /-- Run `body` once per item below `n`, or raise `e` to `err`. -/
  insn eachMay (n : Int) (&body (item : Int) : Unit) (^err (e : Int)) : Unit
  end r2r

/-- For each function of `m`, its plan's start maps disagree with an edge of the walk, if they
do (`RefToRegSim.edgesAgree`); nothing is printed when they agree. -/
private def agree (m : Module R2R.env StrataDDM.SourceRange) : IO Unit :=
  for f in m.raw.funcs do
    let check : Except String (Option String) := do
      let parents ← trees f
      let P ← plan parents f
      let S ← P.starts parents f
      return RefToRegSim.edgesAgree P S f
    match check with
    | .ok (some d) => IO.println s!"{nameText f.name}: {d}"
    | _ => pure ()

/-- Read `text`, promote its cells, and print the result, or the errors. -/
private def promote (text : String) : IO Unit := do
  match ← Module.read R2R.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    agree m
    match refToReg m with
    | .ok m' => IO.print (toString m')
    | .error es => for (n, e) in es do IO.println s!"{nameText n}: {e}"

/-- Read `text`, and print, per function, the candidates the plan leaves as cells. -/
private def left (text : String) : IO Unit := do
  match ← Module.read R2R.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    agree m
    for f in m.raw.funcs do
      match planOf f with
      | .ok P =>
        let names := (P.left f).map fun v => nameText (f.names[v.id]?.getD .base)
        IO.println s!"{nameText f.name}: {names}"
      | .error e => IO.println s!"{nameText f.name}: {e}"

/-! ## Straight-line code

A write then a read: the read is the written value.  The `refNew` stays. -/

/-- info: module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %s.0 : base.Int = r2r.add(%a.0, %a.0)
      ret(%s.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %a.0)
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %s.0 : base.Int = r2r.add(%r.0, %r.0)
      ret(%s.0)
  }
}
"

/-! ## An `if` that merges two writes: the join takes the content as a new parameter -/

/-- info: module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^yes.0() ^join.0(%a.0)
    yes.0():
      jump ^join.0(%b.0)
    join.0(%a.1 : base.Int):
      ret(%a.1)
  }
} -/
#guard_msgs in
#eval promote "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^yes.0() ^join.0()
    yes.0():
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
      jump ^join.0()
    join.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-! ## A loop: the head takes the content, the back edge passes the new one -/

/-- info: module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0(0)
    head.0(%c.2 : base.Int):
      %t.0 : base.Bool = r2r.lt(%c.2, %n.0)
      branch(%t.0) ^body.0() ^done.0()
    body.0():
      %s.0 : base.Int = r2r.add(%c.2, 1)
      jump ^head.0(%s.0)
    done.0():
      ret(%c.2)
  }
} -/
#guard_msgs in
#eval promote "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0()
    head.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %t.0 : base.Bool = r2r.lt(%r.0, %n.0)
      branch(%t.0) ^body.0() ^done.0()
    body.0():
      %r.1 : base.Int = base.refGet[base.Int](%x.0)
      %s.0 : base.Int = r2r.add(%r.1, 1)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
      jump ^head.0()
    done.0():
      %r.2 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.2)
  }
}
"

/-! ## Exception edges: two raising instructions around a write, into one handler

Each edge passes the content at its own point, so the handler takes a parameter. -/

/-- info: module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %p.0 : base.Int = r2r.may(%a.0) ^catch.0(0)
      %p.1 : base.Int = r2r.may(%a.0) ^catch.0(1)
      ret(1)
    catch.0(%c.2 : base.Int, %e.0 : base.Int):
      ret(%c.2)
  }
} -/
#guard_msgs in
#eval promote "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %p.0 : base.Int = r2r.may(%a.0) ^catch.0()
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, 1)
      %p.1 : base.Int = r2r.may(%a.0) ^catch.0()
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
    catch.0(%e.0 : base.Int):
      %r.1 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.1)
  }
}
"

/-! The handler is entered from the raising instruction, and from `late.0` after a write in
`entry.0`, below the point where the raising instruction's edge leaves.  The two edges pass
different contents, so the handler takes a parameter. -/

/-- info: module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0(0)
      branch(%c.0) ^late.0() ^done.0()
    late.0():
      jump ^h.0(1, 5)
    done.0():
      ret(%p.0)
    h.0(%c.4 : base.Int, %e.0 : base.Int):
      %s.0 : base.Int = r2r.add(%c.4, %e.0)
      ret(%s.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0()
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, 1)
      branch(%c.0) ^late.0() ^done.0()
    late.0():
      jump ^h.0(5)
    done.0():
      ret(%p.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %s.0 : base.Int = r2r.add(%r.0, %e.0)
      ret(%s.0)
  }
}
"

/-! ## Placement

A merge whose edges pass the same value takes no parameter, and the block below it reads that
value. -/

/-- info: module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^yes.0() ^no.0()
    yes.0():
      jump ^join.0()
    no.0():
      jump ^join.0()
    join.0():
      jump ^next.0()
    next.0():
      ret(%b.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^yes.0() ^no.0()
    yes.0():
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
      jump ^join.0()
    no.0():
      %u.1 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
      jump ^join.0()
    join.0():
      jump ^next.0()
    next.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-! A write on one branch of an `if` inside a loop: the merge after the `if` takes a parameter,
and so does the loop's head, whose back edge passes the merge's. -/

/-- info: module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0(0)
    head.0(%c.2 : base.Int):
      %t.0 : base.Bool = r2r.lt(%c.2, %n.0)
      branch(%t.0) ^body.0() ^done.0()
    body.0():
      %t.1 : base.Bool = r2r.lt(%n.0, %c.2)
      branch(%t.1) ^yes.0() ^join.0(%c.2)
    yes.0():
      %s.0 : base.Int = r2r.add(%c.2, 1)
      jump ^join.0(%s.0)
    join.0(%c.3 : base.Int):
      jump ^head.0(%c.3)
    done.0():
      ret(%c.2)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0()
    head.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %t.0 : base.Bool = r2r.lt(%r.0, %n.0)
      branch(%t.0) ^body.0() ^done.0()
    body.0():
      %t.1 : base.Bool = r2r.lt(%n.0, %r.0)
      branch(%t.1) ^yes.0() ^join.0()
    yes.0():
      %s.0 : base.Int = r2r.add(%r.0, 1)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
      jump ^join.0()
    join.0():
      jump ^head.0()
    done.0():
      ret(%r.0)
  }
}
"

/-! A region with a merge inside: the cell `y`, made in the region, takes a parameter at the
merge, and the merge reads `x`, made outside, whose content comes from the owner. -/

/-- info: module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %v.0 : base.Int = r2r.if[base.Int](%c.0) {
        then.0():
          %y.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
          branch(%c.0) ^set.0() ^merge.0(0)
        set.0():
          jump ^merge.0(1)
        merge.0(%c.3 : base.Int):
          %s.0 : base.Int = r2r.add(%c.3, %a.0)
          ret(%s.0)
      } {
        else.0():
          ret(%a.0)
      }
      ret(%v.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %v.0 : base.Int = r2r.if[base.Int](%c.0) {
        then.0():
          %y.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
          branch(%c.0) ^set.0() ^merge.0()
        set.0():
          %u.0 : base.Unit = base.refSet[base.Int](%y.0, 1)
          jump ^merge.0()
        merge.0():
          %p.0 : base.Int = base.refGet[base.Int](%y.0)
          %q.0 : base.Int = base.refGet[base.Int](%x.0)
          %s.0 : base.Int = r2r.add(%p.0, %q.0)
          ret(%s.0)
      } {
        else.0():
          ret(%a.0)
      }
      ret(%v.0)
  }
}
"

/-! An irreducible loop: `p.0` and `q.0` enter each other, and both are entered from `entry.0`.
No block writes the cell, so no block takes a parameter. -/

/-- info: module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^p.0() ^q.0()
    p.0():
      %t.0 : base.Bool = r2r.lt(%a.0, 0)
      branch(%t.0) ^q.0() ^done.0()
    q.0():
      jump ^p.0()
    done.0():
      ret(%a.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^p.0() ^q.0()
    p.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %t.0 : base.Bool = r2r.lt(%r.0, 0)
      branch(%t.0) ^q.0() ^done.0()
    q.0():
      jump ^p.0()
    done.0():
      ret(%a.0)
  }
}
"

/-! `y.0` is entered from `h.0`, which the raising instruction enters before the write, and from
`entry.0` after the write.  The two edges pass different contents (`%a.0` and `5`), so `y.0`
takes a parameter. -/

/-- info: module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0()
      jump ^y.0(5)
    h.0(%e.0 : base.Int):
      jump ^y.0(%a.0)
    y.0(%a.1 : base.Int):
      ret(%a.1)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0()
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, 5)
      jump ^y.0()
    h.0(%e.0 : base.Int):
      jump ^y.0()
    y.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-! A handler entered by the `err` edge of an `eachMay` whose region writes `x`, and from `k.0`,
which knows `x`: the edge from the `eachMay` doesn't know `x`, so `x` stays a cell. -/

/-- info: m.f: [x.0] -/
#guard_msgs in
#eval left "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^k.0() ^w.0()
    k.0():
      jump ^h.0(%a.0)
    w.0():
      %q.0 : base.Unit = r2r.eachMay(%a.0) ^h.0() {
        body.0(%i.0 : base.Int):
          %s.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%a.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-! A handler entered by a raising instruction after a write: its tree parent is the point
of the raising instruction, in the middle of `entry.0`, and it takes the cell's content from the
map there, with no parameter. -/

/-- info: module m {
  func @m.f(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0()
      ret(%p.0)
    h.0(%e.0 : base.Int):
      ret(%b.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0()
      ret(%p.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-! A region write makes `x` unknown before a branch; one arm writes `x` again, and so does one
arm of a second branch, before a read at the second join.  The join's content comes from the
first join, whose content is unknown on one edge, so `x` stays a cell. -/

/-- info: m.f: [x.0] -/
#guard_msgs in
#eval left "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      branch(%c.0) ^p.0() ^s.0()
    s.0():
      %v.0 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
      jump ^p.0()
    p.0():
      branch(%c.0) ^q.0() ^t.0()
    t.0():
      %y.0 : base.Unit = base.refSet[base.Int](%x.0, %a.0)
      jump ^q.0()
    q.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-! The same unknown content, but nothing reads `x` after it: `x` is read only before the
region, and is promoted. -/

/-- info: m.g: [] -/
#guard_msgs in
#eval left "module m {
  func @m.g(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      branch(%c.0) ^p.0() ^s.0()
    s.0():
      %v.0 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
      jump ^p.0()
    p.0():
      ret(%r.0)
  }
}
"

/-! ## Escapes: through an operation, and as a stored value; nothing changes -/

/-- info: module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %y.0 : base.Ref(base.Ref(base.Int)) = base.refNew[base.Ref(base.Int)](%x.0)
      %w.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = r2r.use(%w.0)
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %q.0 : base.Int = base.refGet[base.Int](%w.0)
      %s.0 : base.Int = r2r.add(%r.0, %q.0)
      ret(%s.0)
  }
} -/
#guard_msgs in
#eval promote "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %y.0 : base.Ref(base.Ref(base.Int)) = base.refNew[base.Ref(base.Int)](%x.0)
      %w.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = r2r.use(%w.0)
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %q.0 : base.Int = base.refGet[base.Int](%w.0)
      %s.0 : base.Int = r2r.add(%r.0, %q.0)
      ret(%s.0)
  }
}
"

/-! ## Regions

A read in a region that no region writes is the content at the operation.  A write then a
read in a region: the read is the written value. -/

/-- info: module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %y.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %v.0 : base.Int = r2r.if[base.Int](%c.0) {
        then.0():
          ret(%a.0)
      } {
        else.0():
          ret(2)
      }
      ret(%v.0)
  }
} -/
#guard_msgs in
#eval promote "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %y.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %v.0 : base.Int = r2r.if[base.Int](%c.0) {
        then.0():
          %r.0 : base.Int = base.refGet[base.Int](%x.0)
          ret(%r.0)
      } {
        else.0():
          %u.0 : base.Unit = base.refSet[base.Int](%y.0, 2)
          %r.1 : base.Int = base.refGet[base.Int](%y.0)
          ret(%r.1)
      }
      ret(%v.0)
  }
}
"

/-! A cell that a region writes is unknown after the operation, and in its other regions. -/

/-- info: m.after: [x.0]
m.sibling: [x.0]
m.again: [x.0]
m.term: [x.0] -/
#guard_msgs in
#eval left "module m {
  func @m.after(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
  func @m.sibling(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %v.0 : base.Int = r2r.try() {
        body.0():
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %a.0)
          ret(%a.0)
      } {
        handler.0(%e.0 : base.Int):
          %r.0 : base.Int = base.refGet[base.Int](%x.0)
          ret(%r.0)
      }
      ret(%v.0)
  }
  func @m.again(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %r.0 : base.Int = base.refGet[base.Int](%x.0)
          %s.0 : base.Int = r2r.add(%r.0, %i.0)
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%a.0)
  }
  func @m.term(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      r2r.loop ^out.0() {
        body.0():
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %a.0)
          %f.0 : base.Bool = const false
          ret(%f.0)
      }
    out.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-! A cell made inside a loop body, and a block whose edges pass different prefixes. -/

/-- info: module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(%n.0)
    head.0(%k.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%k.0)
      %p.0 : base.Int = r2r.may(%k.0) ^h.0(%k.0)
      %t.0 : base.Bool = r2r.lt(%k.0, 0)
      branch(%t.0) ^head.0(%k.0) ^h.0(5, %k.0)
    h.0(%k.1 : base.Int, %e.0 : base.Int):
      ret(%k.1)
  }
} -/
#guard_msgs in
#eval promote "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      jump ^head.0(%n.0)
    head.0(%k.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%k.0)
      %p.0 : base.Int = r2r.may(%k.0) ^h.0()
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %t.0 : base.Bool = r2r.lt(%r.0, 0)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, 5)
      branch(%t.0) ^head.0(%r.0) ^h.0(%r.0)
    h.0(%e.0 : base.Int):
      %r.1 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.1)
  }
}
"

/-! ## More cells that stay

A cell passed on an edge (`%e.0`), a cell stored in a cell by `refSet` (`%z.0`), and a cell
whose `refSet`'s result is used (`%w.0`) are not candidates, and stay.  `%y.0`, which nothing
reads, is promoted: its `refSet` goes. -/

/-- info: module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %e.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %z.1 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %y.0 : base.Ref(base.Ref(base.Int)) = base.refNew[base.Ref(base.Int)](%z.1)
      %z.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %w.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = base.refSet[base.Int](%w.0, 1)
      %v.0 : base.Unit = r2r.if[base.Unit](true) {
        then.0():
          ret(%u.0)
      } {
        else.0():
          ret(%u.0)
      }
      jump ^next.0(%e.0)
    next.0(%c.0 : base.Ref(base.Int)):
      %r.0 : base.Int = base.refGet[base.Int](%c.0)
      %q.0 : base.Int = base.refGet[base.Int](%z.0)
      %p.0 : base.Int = base.refGet[base.Int](%w.0)
      %t.0 : base.Int = base.refGet[base.Int](%e.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %e.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %z.1 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %y.0 : base.Ref(base.Ref(base.Int)) = base.refNew[base.Ref(base.Int)](%z.1)
      %z.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %s.0 : base.Unit = base.refSet[base.Ref(base.Int)](%y.0, %z.0)
      %w.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = base.refSet[base.Int](%w.0, 1)
      %v.0 : base.Unit = r2r.if[base.Unit](true) {
        then.0():
          ret(%u.0)
      } {
        else.0():
          ret(%u.0)
      }
      jump ^next.0(%e.0)
    next.0(%c.0 : base.Ref(base.Int)):
      %r.0 : base.Int = base.refGet[base.Int](%c.0)
      %q.0 : base.Int = base.refGet[base.Int](%z.0)
      %p.0 : base.Int = base.refGet[base.Int](%w.0)
      %t.0 : base.Int = base.refGet[base.Int](%e.0)
      ret(%r.0)
  }
}
"

/-! A write two regions deep makes the cell unknown after the outer operation.  A cell made
inside a region is promoted there. -/

/-- info: m.deep: [x.0] -/
#guard_msgs in
#eval left "module m {
  func @m.deep(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %v.0 : base.Unit = r2r.if[base.Unit](%c.0) {
            then.0():
              %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
              %o.0 : base.Unit = base.unit
              ret(%o.0)
          } {
            else.0():
              %o.1 : base.Unit = base.unit
              ret(%o.1)
          }
          ret(%v.0)
      }
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-- info: module m {
  func @m.inner(%a.0 : base.Int) -> base.Unit {
    entry.0(%a.0 : base.Int):
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %y.0 : base.Ref(base.Int) = base.refNew[base.Int](%i.0)
          %s.0 : base.Int = r2r.add(%i.0, %i.0)
          %t.0 : base.Bool = r2r.lt(%s.0, %a.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%u.0)
  }
} -/
#guard_msgs in
#eval promote "module m {
  func @m.inner(%a.0 : base.Int) -> base.Unit {
    entry.0(%a.0 : base.Int):
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %y.0 : base.Ref(base.Int) = base.refNew[base.Int](%i.0)
          %r.0 : base.Int = base.refGet[base.Int](%y.0)
          %s.0 : base.Int = r2r.add(%r.0, %r.0)
          %w.0 : base.Unit = base.refSet[base.Int](%y.0, %s.0)
          %q.0 : base.Int = base.refGet[base.Int](%y.0)
          %t.0 : base.Bool = r2r.lt(%q.0, %a.0)
          %v.0 : base.Unit = base.refSet[base.Int](%y.0, %q.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%u.0)
  }
}
"

/-! A cell that an instruction's region writes is unknown on the instruction's own `err` edge,
and a terminator's region that reads a cell and then writes it reads it unknown: each cell
stays.  A cell passed on an instruction's edge escapes, and nothing changes. -/

/-- info: m.err: [x.0]
m.loopRead: [x.0] -/
#guard_msgs in
#eval left "module m {
  func @m.err(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      %u.0 : base.Unit = r2r.eachMay(%a.0) ^h.0() {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%a.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
  func @m.loopRead(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      r2r.loop ^out.0() {
        body.0():
          %r.0 : base.Int = base.refGet[base.Int](%x.0)
          %s.0 : base.Int = r2r.add(%r.0, %a.0)
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
          %t.0 : base.Bool = r2r.lt(%s.0, %a.0)
          ret(%t.0)
      }
    out.0():
      ret(%a.0)
  }
}
"

/-- info: module m {
  func @m.edge(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, 5)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0(%x.0)
      ret(%p.0)
    h.0(%c.0 : base.Ref(base.Int), %e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%r.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.edge(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, 5)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0(%x.0)
      ret(%p.0)
    h.0(%c.0 : base.Ref(base.Int), %e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%c.0)
      ret(%r.0)
  }
}
"

/-! Many raising edges into each handler of a chain: each handler's parameter for `x` becomes
an alias of the value the edges pass, and the planner settles. -/

/-- A chain of `m` handlers, each reached from `n` raising edges of the block before it, then by
a jump; the last block reads `x`. -/
private def raisingChain (m n : Nat) : String := Id.run do
  let mut s := "module m {\n  func @m.f(%a.0 : base.Int) -> base.Int {\n    entry.0(%a.0 : base.Int):\n" ++
    "      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)\n      jump ^h.0(0)\n"
  for i in [0:m] do
    s := s ++ s!"    h.{i}(%e.{i} : base.Int):\n"
    for k in [0:n] do
      s := s ++ s!"      %p{i}.{k} : base.Int = r2r.may(%a.0) ^h.{i+1}()\n"
    s := s ++ s!"      jump ^h.{i+1}(1)\n"
  s := s ++ s!"    h.{m}(%e.{m} : base.Int):\n      %r.0 : base.Int = base.refGet[base.Int](%x.0)\n" ++
    "      ret(%r.0)\n  }\n}\n"
  return s

/-- info: m.f: [] -/
#guard_msgs in
#eval left (raisingChain 10 8)

/-- A chain of `m` diamonds: both arms write the same value, then enter the join by `n` raising
edges and a jump, and each join reads the cell.  Each join takes a parameter, which then becomes
an alias of the value, behind many edges that pass it. -/
private def diamonds (m n : Nat) : String := Id.run do
  let mut s := "module m {\n  func @m.f(%a.0 : base.Int, %c.0 : base.Bool) -> base.Int {\n" ++
    "    entry.0(%a.0 : base.Int, %c.0 : base.Bool):\n" ++
    "      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)\n      jump ^j.0(0)\n"
  for i in [0:m] do
    s := s ++ s!"    j.{i}(%e.{i} : base.Int):\n" ++
      s!"      %r{i} : base.Int = base.refGet[base.Int](%x.0)\n" ++
      s!"      branch(%c.0) ^l.{i}() ^r.{i}()\n"
    for side in ["l", "r"] do
      s := s ++ s!"    {side}.{i}():\n" ++
        s!"      %w{side}{i} : base.Unit = base.refSet[base.Int](%x.0, %a.0)\n"
      for k in [0:n] do
        s := s ++ s!"      %p{side}{i}.{k} : base.Int = r2r.may(%a.0) ^j.{i+1}()\n"
      s := s ++ s!"      jump ^j.{i+1}(1)\n"
  s := s ++ s!"    j.{m}(%e.{m} : base.Int):\n" ++
    "      %z : base.Int = base.refGet[base.Int](%x.0)\n      ret(%z)\n  }\n}\n"
  return s

-- Every join's parameter becomes an alias, and the cell is promoted.
/-- info: m.f: [] -/
#guard_msgs in
#eval left (diamonds 40 16)

/-- A loop whose head reads, adds to and writes `x` `w` times, then loops or leaves to a block
that reads `x`. -/
private def manyWrites (w : Nat) : String := Id.run do
  let mut s := "module m {\n  func @m.f(%a.0 : base.Int, %c.0 : base.Bool) -> base.Int {\n" ++
    "    entry.0(%a.0 : base.Int, %c.0 : base.Bool):\n" ++
    "      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)\n      jump ^head.0()\n" ++
    "    head.0():\n"
  for k in [0:w] do
    s := s ++ s!"      %r{k}.0 : base.Int = base.refGet[base.Int](%x.0)\n" ++
      s!"      %s{k}.0 : base.Int = r2r.add(%r{k}.0, 1)\n" ++
      s!"      %u{k}.0 : base.Unit = base.refSet[base.Int](%x.0, %s{k}.0)\n"
  s := s ++ "      branch(%c.0) ^head.0() ^out.0()\n    out.0():\n" ++
    "      %q.0 : base.Int = base.refGet[base.Int](%x.0)\n      ret(%q.0)\n  }\n}\n"
  return s

/-- A block that copies a value between two cells `w` times: each read's content is the
previous read. -/
private def copies (w : Nat) : String := Id.run do
  let mut s := "module m {\n  func @m.f(%a.0 : base.Int) -> base.Int {\n" ++
    "    entry.0(%a.0 : base.Int):\n" ++
    "      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)\n" ++
    "      %y.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)\n"
  for k in [0:w] do
    let (src, dst) := if k % 2 == 0 then ("x", "y") else ("y", "x")
    s := s ++ s!"      %r{k}.0 : base.Int = base.refGet[base.Int](%{src}.0)\n" ++
      s!"      %u{k}.0 : base.Unit = base.refSet[base.Int](%{dst}.0, %r{k}.0)\n"
  s := s ++ "      %q.0 : base.Int = base.refGet[base.Int](%x.0)\n      ret(%q.0)\n  }\n}\n"
  return s

-- Twenty copies: both cells are promoted.
/-- info: m.f: [] -/
#guard_msgs in
#eval left (copies 20)

-- Twenty writes of one cell in one block: the cell is promoted.
/-- info: m.f: [] -/
#guard_msgs in
#eval left (manyWrites 20)

/-! A cell known at one read but unknown at another stays a cell as a whole: both reads and
the write stay. -/

/-- info: module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      %q.0 : base.Int = base.refGet[base.Int](%x.0)
      %s.0 : base.Int = r2r.add(%r.0, %q.0)
      ret(%s.0)
  }
}
-/
#guard_msgs in
#eval promote "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      %q.0 : base.Int = base.refGet[base.Int](%x.0)
      %s.0 : base.Int = r2r.add(%r.0, %q.0)
      ret(%s.0)
  }
}
"

/-! ## Wrong plans fail visibly

`refToRegWith` with planners that change `plan`'s plans, each so that it breaks one rule. -/

/-- The `if` above. -/
private def merge : String := "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^yes.0() ^join.0()
    yes.0():
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %b.0)
      jump ^join.0()
    join.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-- Read `text`, and promote it with `plan`'s plans changed by `tweak`. -/
private def promoteBy (text : String)
    (tweak : Func R2R.env StrataDDM.SourceRange → Plan R2R.env → Except String (Plan R2R.env)) :
    IO Unit := do
  match ← Module.read R2R.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match refToRegWith (fun T f => do tweak f (← plan T f)) m with
    | .ok m' => IO.print (toString m')
    | .error es => for (n, e) in es do IO.println s!"{nameText n}: {e}"

/-- Every block's plan, changed by `g`. -/
private def everyBlock (g : BlockPlan R2R.env → BlockPlan R2R.env) (P : Plan R2R.env) :
    Plan R2R.env :=
  { P with blocks := P.blocks.map fun _ bp => g bp }

/-- `P` with each removed read replaced by `v`. -/
private def readsAs (v : ValId) (P : Plan R2R.env) : Plan R2R.env :=
  { P with sigma := P.sigma.map fun _ _ => v }

/-- info: m.f: no plan -/
#guard_msgs in
#eval promoteBy merge fun _ _ => throw "no plan"

-- `%w.0` escapes through `r2r.use`, but the plan promotes it.
/-- info: m.f: the plan breaks a rule: the promoted cells are candidates -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %w.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %u.0 : base.Unit = r2r.use(%w.0)
      %q.0 : base.Int = base.refGet[base.Int](%w.0)
      ret(%q.0)
  }
}
" fun _ P => pure { P with promoted := .ofList [⟨1⟩], sigma := .ofList [(⟨3⟩, ⟨0⟩)] }

-- The plan replaces `%a.0`, which is not a removed read, by `%b.0`.
/-- info: m.f: the plan breaks a rule: each replaced value is a removed read, replaced by a value that is not a removed read -/
#guard_msgs in
#eval promoteBy merge fun _ P => pure { P with sigma := P.sigma.insert ⟨1⟩ ⟨2⟩ }

-- The join both carries its cell and fixes it to the join's own new parameter.
/-- info: m.f: the plan breaks a rule: each block's plan is consistent -/
#guard_msgs in
#eval promoteBy merge fun _ P => pure (everyBlock (fun bp =>
  { bp with fixed := bp.carried.map fun (c, d) => (c, d.id), carried := bp.carried }) P)

-- The join's content is fixed to `%a.0`, and its read replaced by it, but the edge from
-- `yes.0` passes `%b.0`.
/-- info: m.f: the plan breaks a rule: each edge passes what its target expects -/
#guard_msgs in
#eval promoteBy merge fun _ P => pure (readsAs ⟨1⟩ (everyBlock (fun bp =>
  { bp with carried := [], fixed := bp.carried.map fun (c, _) => (c, ⟨1⟩) }) P))

-- The join takes a parameter for `%y.0`, which the edge from `entry.0` doesn't know: `%y.0`
-- is made only in `yes.0`.
/-- info: m.f: the plan breaks a rule: each edge passes what its target expects -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      branch(%c.0) ^yes.0() ^join.0()
    yes.0():
      %y.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %r.0 : base.Int = base.refGet[base.Int](%y.0)
      jump ^join.0()
    join.0():
      ret(%a.0)
  }
}
" fun f P => pure (match f.blocks[2]? with
  | some b =>
    let bp : BlockPlan R2R.env := { carried := [(⟨2⟩, { id := ⟨9⟩, type := Base.Int })] }
    { P with blocks := .ofList [(b.label, bp)] }
  | none => P)

-- The handler's parameter would go after the exception that the `err` edge passes.
/-- info: m.f: the plan breaks a rule: each edge passes what its target expects -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0()
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, 5)
      jump ^h.0(%p.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %s.0 : base.Int = r2r.add(%r.0, %e.0)
      ret(%s.0)
  }
}
" fun _ P => pure (everyBlock (fun bp => { bp with ins := 1 }) P)

-- The function's entry block takes a parameter.
/-- info: m.f: the plan breaks a rule: a body's entry takes nothing new -/
#guard_msgs in
#eval promoteBy merge fun f P => pure (match f.blocks[0]? with
  | some b =>
    let bp : BlockPlan R2R.env := { carried := [(⟨3⟩, { id := ⟨9⟩, type := Base.Int })] }
    { P with blocks := P.blocks.insert b.label bp }
  | none => P)

-- The new parameter reuses the id of `%a.0`, and the read is replaced by it.
/-- info: m.f: the plan breaks a rule: the new parameters are fresh -/
#guard_msgs in
#eval promoteBy merge fun _ P => pure (readsAs ⟨1⟩ (everyBlock (fun bp =>
  { bp with carried := bp.carried.map fun (c, d) => (c, { d with id := ⟨1⟩ }) }) P))

-- The read is not replaced.
/-- info: m.f: the plan breaks a rule: each removed read is replaced by its cell's content -/
#guard_msgs in
#eval promoteBy merge fun _ P => pure { P with sigma := {} }

-- The new parameter has the wrong type: the plan meets every rule, but the module is not well
-- formed.
/-- info: m.f: the promoted function is not well formed -/
#guard_msgs in
#eval promoteBy merge fun _ P => pure (everyBlock (fun bp =>
  { bp with carried := bp.carried.map fun (c, d) => (c, { d with type := Base.Bool }) }) P)

/-- The value named `n` in `f`. -/
private def idOf (f : Func R2R.env StrataDDM.SourceRange) (n : String) : ValId :=
  match f.names.toList.zipIdx.find? (fun (nm, _) => nameText nm == n) with
  | some (_, k) => ⟨k⟩
  | none => ⟨999⟩

/-- A plan that promotes `x.0` and replaces the read `r.0` by `b.0`, the cell's initial value,
and gives the block `l`, if any, `b.0` as `x.0`'s fixed content. -/
private def initialValue (l : Option Label) (f : Func R2R.env StrataDDM.SourceRange) :
    Plan R2R.env :=
  let x := idOf f "x.0"
  let b := idOf f "b.0"
  let bp : BlockPlan R2R.env := { fixed := [(x, b)] }
  { promoted := .ofList [x], sigma := .ofList [(idOf f "r.0", b)],
    blocks := match l with | some l => .ofList [(l, bp)] | none => {} }

-- The handler is entered by the `err` edge of an `eachMay` whose region writes `x`, but the
-- plan says that `x` holds its initial value there.
/-- info: m.err: the plan breaks a rule: each edge passes what its target expects -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.err(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%b.0)
      %u.0 : base.Unit = r2r.eachMay(%a.0) ^h.0() {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%a.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
" fun f _ => pure (initialValue (f.blocks[1]?.map (·.label)) f)

-- A region that reads `x` and then writes it.  A run of the region may follow one that wrote
-- `x`, so the region starts without `x`, but the plan replaces the read by the initial value.
/-- info: m.f: the plan breaks a rule: each removed read is replaced by its cell's content -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.f(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%b.0)
      %u.0 : base.Unit = r2r.each(%a.0) {
        body.0(%i.0 : base.Int):
          %r.0 : base.Int = base.refGet[base.Int](%x.0)
          %s.0 : base.Int = r2r.add(%r.0, %i.0)
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%a.0)
  }
}
" fun f _ => pure (initialValue none f)

-- The same in a terminator's region.
/-- info: m.f: the plan breaks a rule: each removed read is replaced by its cell's content -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.f(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%b.0)
      r2r.loop ^out.0() {
        body.0():
          %r.0 : base.Int = base.refGet[base.Int](%x.0)
          %s.0 : base.Int = r2r.add(%r.0, %a.0)
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
          %t.0 : base.Bool = r2r.lt(%s.0, %a.0)
          ret(%t.0)
      }
    out.0():
      ret(%a.0)
  }
}
" fun f _ => pure (initialValue none f)

/-! Wrong plans that leave out a parameter the cell needs.  The block's start map then lacks
the cell, since its content may change on a path into the block, and the read below fails the
read rule, or an edge that should pass the cell fails the edge rule. -/

/-- The plan without the block plans of the blocks named `ls`. -/
private def without (ls : List String) (f : Func R2R.env StrataDDM.SourceRange)
    (P : Plan R2R.env) : Plan R2R.env :=
  { P with blocks := f.allBlocks.foldl (init := P.blocks) fun m b =>
      if ls.contains (nameText b.label.name) then m.erase b.label else m }

/-- info: m.f: the plan breaks a rule: each removed read is replaced by its cell's content -/
#guard_msgs in
#eval promoteBy merge fun f P => pure (without ["join.0"] f P)

-- The handler of the `eachMay` whose region writes `x`, with no plan for it.
/-- info: m.err: the plan breaks a rule: each removed read is replaced by its cell's content -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.err(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%b.0)
      %u.0 : base.Unit = r2r.eachMay(%a.0) ^h.0() {
        body.0(%i.0 : base.Int):
          %w.0 : base.Unit = base.refSet[base.Int](%x.0, %i.0)
          %o.0 : base.Unit = base.unit
          ret(%o.0)
      }
      ret(%a.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
" fun f _ => pure (initialValue none f)

-- An `if` inside a loop writes `x` on one arm, and the plan leaves out the loop head's
-- parameter: the head learns of the write only through the inner join's start.  The head and
-- the loop's body then start without `x`, so the edge into the inner join, which carries `x`,
-- doesn't know it.
/-- info: m.f: the plan breaks a rule: each edge passes what its target expects -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.f(%n.0 : base.Int) -> base.Int {
    entry.0(%n.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](0)
      jump ^head.0()
    head.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %t.0 : base.Bool = r2r.lt(%r.0, %n.0)
      branch(%t.0) ^body.0() ^done.0()
    body.0():
      %t.1 : base.Bool = r2r.lt(%n.0, %r.0)
      branch(%t.1) ^yes.0() ^join.0()
    yes.0():
      %s.0 : base.Int = r2r.add(%r.0, 1)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
      jump ^join.0()
    join.0():
      jump ^head.0()
    done.0():
      ret(%r.0)
  }
}
" fun f P => pure (without ["head.0"] f P)

-- An irreducible loop: `p.0` and `q.0` enter each other, both entered from `entry.0`, and
-- `p.0` writes `x`; the plan leaves out both blocks' parameters.
/-- info: m.f: the plan breaks a rule: each removed read is replaced by its cell's content -/
#guard_msgs in
#eval promoteBy "module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^p.0() ^q.0()
    p.0():
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      %s.0 : base.Int = r2r.add(%r.0, 1)
      %u.0 : base.Unit = base.refSet[base.Int](%x.0, %s.0)
      %t.0 : base.Bool = r2r.lt(%r.0, 0)
      branch(%t.0) ^q.0() ^done.0()
    q.0():
      jump ^p.0()
    done.0():
      ret(%a.0)
  }
}
" fun f P => pure (without ["p.0", "q.0"] f P)

-- `yes.0` carries `x`, but no content of `x` can change on the way into `yes.0`.
/-- info: m.f: the plan breaks a rule: each block's new cells change there -/
#guard_msgs in
#eval promoteBy merge fun f P => pure (match f.blocks[1]? with
  | some b =>
    let bp : BlockPlan R2R.env := { carried := [(⟨3⟩, { id := ⟨99⟩, type := Base.Int })] }
    { P with blocks := P.blocks.insert b.label bp }
  | none => P)

-- A name the plan gives `%a.0` is left out.
/-- info: module m {
  func @m.f(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%c.0 : base.Bool, %a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      branch(%c.0) ^yes.0() ^join.0(%a.0)
    yes.0():
      jump ^join.0(%b.0)
    join.0(%a.1 : base.Int):
      ret(%a.1)
  }
}
-/
#guard_msgs in
#eval promoteBy merge fun _ P =>
  pure { P with names := P.names ++ [(⟨1⟩, .num (.str .base "z") 0)] }

/-! ## The pass accepts its own output, and changes nothing more -/

/-- Read `text`, promote it twice, and say whether the second time changed anything. -/
private def twice (text : String) : IO Unit := do
  match ← Module.read R2R.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    match refToReg m with
    | .error _ => IO.println "the first run failed"
    | .ok m₁ =>
      match refToReg m₁ with
      | .error _ => IO.println "the second run failed"
      | .ok m₂ => IO.println (toString m₁ == toString m₂)

/-- info: true -/
#guard_msgs in
#eval twice merge

/-! ## Running both forms side by side

`RefToRegSim.sameRuns` runs each function and its promoted form along 200 random paths and one
path per edge, and finds no difference.  A wrong rewrite, here the join's parameter replaced by
`%a.0`, is caught. -/

/-- Read `text`, and run each function and its promoted form, changed by `spoil`, side by side. -/
private def sideBySide (text : String) (spoil : ValId → ValId := id) : IO Unit := do
  match ← Module.read R2R.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    for f in m.raw.funcs do
      match planOf f with
      | .error e => IO.println s!"{nameText f.name}: {e}"
      | .ok P =>
        match P.applyFor f with
        | .error e => IO.println s!"{nameText f.name}: {e}"
        | .ok f₁ =>
          match RefToRegSim.sameRuns P f (f₁.mapUses spoil) 7 200 400 with
          | none => IO.println s!"{nameText f.name}: the same"
          | some d => IO.println s!"{nameText f.name}: {d}"

/-- info: m.f: the same -/
#guard_msgs in
#eval sideBySide merge

/-- Read `text`, and run each function and the rewrite by its plan changed by `tweak`, without
the check, side by side. -/
private def sideBySideBy (text : String) (tweak : Plan R2R.env → Plan R2R.env) : IO Unit := do
  match ← Module.read R2R.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    for f in m.raw.funcs do
      match planOf f with
      | .error e => IO.println s!"{nameText f.name}: {e}"
      | .ok P =>
        let P := tweak P
        match P.applyFor f with
        | .error e => IO.println s!"{nameText f.name}: {e}"
        | .ok f₁ =>
          match RefToRegSim.sameRuns P f f₁ 7 200 400 with
          | none => IO.println s!"{nameText f.name}: the same"
          | some d => IO.println s!"{nameText f.name}: {d}"

-- `%w.0` escapes through `r2r.use`, which may read it, but a wrong plan promotes it: its write
-- goes, and `r2r.use` sees a different content.
/-- info: m.f: r2r.use defining %4: escaped cell 0 holds #1 and #0 -/
#guard_msgs in
#eval sideBySideBy "module m {
  func @m.f(%a.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int):
      %w.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %s.0 : base.Unit = base.refSet[base.Int](%w.0, 5)
      %u.0 : base.Unit = r2r.use(%w.0)
      ret(%a.0)
  }
}
" fun P => { P with promoted := .ofList [⟨1⟩] }

-- The same cell, left by the exit to the caller instead.
/-- info: m.f: an exit: escaped cell 0 holds #1 and #0 -/
#guard_msgs in
#eval sideBySideBy "module m {
  func @m.f(%a.0 : base.Int) -> base.Ref(base.Int) {
    entry.0(%a.0 : base.Int):
      %w.0 : base.Ref(base.Int) = base.refNew[base.Int](%a.0)
      %s.0 : base.Unit = base.refSet[base.Int](%w.0, 5)
      ret(%w.0)
  }
}
" fun P => { P with promoted := .ofList [⟨1⟩] }

/-- info: m.f: an exit: operand %5 is #2, but %1 is #1 -/
#guard_msgs in
#eval sideBySide merge fun v => if v.id == 6 then ⟨1⟩ else v

/-- Read `text`, and run each function and the rewrite by its plan changed by `tweak`, side by
side along the covering paths only: one per edge, and no random path. -/
private def covering (text : String) (tweak : Plan R2R.env → Plan R2R.env := id) : IO Unit := do
  match ← Module.read R2R.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    for f in m.raw.funcs do
      match planOf f with
      | .error e => IO.println s!"{nameText f.name}: {e}"
      | .ok P =>
        let P := tweak P
        match P.applyFor f with
        | .error e => IO.println s!"{nameText f.name}: {e}"
        | .ok f₁ =>
          match RefToRegSim.sameRuns P f f₁ 7 0 400 with
          | none => IO.println s!"{nameText f.name}: the same"
          | some d => IO.println s!"{nameText f.name}: {d}"

/-- A handler entered only by a raising edge.  The covering path of that edge finds a wrong
plan, which replaces the handler's read `%r.0` by `%a.0` instead of the cell's content `%b.0`. -/
private def handlerOnly : String := "module m {
  func @m.f(%a.0 : base.Int, %b.0 : base.Int) -> base.Int {
    entry.0(%a.0 : base.Int, %b.0 : base.Int):
      %x.0 : base.Ref(base.Int) = base.refNew[base.Int](%b.0)
      %p.0 : base.Int = r2r.may(%a.0) ^h.0()
      ret(%p.0)
    h.0(%e.0 : base.Int):
      %r.0 : base.Int = base.refGet[base.Int](%x.0)
      ret(%r.0)
  }
}
"

/-- info: m.f: the same -/
#guard_msgs in
#eval covering handlerOnly

/-- info: m.f: an exit: operand %5 is #1, but %0 is #0 -/
#guard_msgs in
#eval covering handlerOnly fun P => { P with sigma := P.sigma.insert ⟨5⟩ ⟨0⟩ }

-- The chain of raising edges above, side by side.
/-- info: m.f: the same -/
#guard_msgs in
#eval sideBySide (raisingChain 10 8)

-- The chain of diamonds above, side by side.
/-- info: m.f: the same -/
#guard_msgs in
#eval sideBySide (diamonds 10 8)

end Strata.Dyn.RefToRegTest
