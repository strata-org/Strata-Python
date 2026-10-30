/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDyn.DDM
public import StrataDyn.DDMRead
import StrataDyn.Env.WF
import StrataDyn.DSL
import StrataDynTest.WFParts
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataDyn.Build
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.WF
meta import StrataDyn.Env.WF
meta import StrataDynTest.WFParts

set_option autoImplicit false

/-!
# Frames that name sets of locations

An entry of a `reads` or `writes` frame is a cell among the parameters, or a *frame region*: a
region that takes no arguments and returns a `base.Loc`, a set of locations.  `base.cellLoc` gives
the location of a cell's contents.  A frame region is a contract region, so these rules of
`Func.WF` apply to it:

* `contract`: it takes no arguments and returns a `base.Loc`, it sees only the parameters and its
  own values, as a clause does, and it applies no operation declared `writes`;
* `failures`: a failure successor of its own blocks goes to a block that ends in `unreachable`;
* `propagates`, `terminators` and `acyclic`, as in a clause;
* `old`: it does not apply `base.old`.

Each function accepted here is built, printed, and read back unchanged.  Each function rejected
here breaks exactly one rule of `Func.WF`, and the reader names the problem.
-/

namespace Strata.Dyn.FrameTest

open Strata.Dyn.WFParts (broken failing)

/-- An operation that may fail, an operation that runs a region, and a terminal operation. -/
public environment Demo extends Base where
  namespace demo
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- The cell at position `i` of `cs`.  It fails, with an error code, when `i` is out of range. -/
  pure insn nth (cs : Sequence (Ref Int)) (i : Int) (^err (e : Int)) : Ref Int
  /-- Runs `body`: the value of an `ok`, or a transfer to `err` with the error of an `error`. -/
  pure insn attempt [a] (&body : Except Int a) (^err (e : Int)) : a
  /-- The cell at position `i` of `cs`, which ends its block: it continues at `ok` with the cell,
  or at `err` when `i` is out of range. -/
  pure terminal insn tryNth (cs : Sequence (Ref Int)) (i : Int) (^ok (c : Ref Int)) (^err (e : Int))
  end demo

open Strata.Dyn.Build (freshVal startBlock startFreshBlock freshLabel emitConst emitApply
  finishBlock terminate goto build FailedFunc region withFailureBlock withPropagatingBlock)

private abbrev E := Demo.env

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

/-- The misuses of a failed build, or none. -/
private def misuses (b : Built) : Array String :=
  match b with
  | .ok _ => #[]
  | .error e => e.misuses

private def intT : TypeExpr E := Base.Int
private def boolT : TypeExpr E := Base.Bool
private def locT : TypeExpr E := Base.Loc
private def cellT : TypeExpr E := Base.Ref intT
private def cellsT : TypeExpr E := Base.Sequence cellT
/-- `base.Except(base.Int, base.Loc)`, what the region of `demo.attempt` returns here. -/
private def exT : TypeExpr E := Base.Except intT locT

private def nm (s : String) : Name := .str .base s

/-- Check that the built function `b` prints as the module `text`, and that reading `text` gives
it back.  Print the module where it differs, or the diagnostics. -/
private def agrees (b : Built) (text : String) : IO Unit := do
  match b with
  | .error e => IO.println s!"not built: {e}"
  | .ok f =>
    match Module.ofChecked (nm "m") #[f] () with
    | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
    | .ok m => unless toString m == text do IO.println m
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-- Read `text` in `Demo.env`, and print the diagnostics, or the module if it prints otherwise. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read E text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-! ## Builders -/

/-- `@m.f(c, cs, i) = i`, over the cell `c` and the sequence of cells `cs`, with the contract that
`contract c cs i` emits after the body. -/
private def withContract (contract : ValId → ValId → ValId → BuildM E Unit Unit) : Built :=
  build (.str (nm "m") "f") intT () do
    let c ← freshVal (nm "c") cellT
    let cs ← freshVal (nm "cs") cellsT
    let i ← freshVal (nm "i") intT
    let _ ← startFreshBlock #[c, cs, i] "entry"
    finishBlock (.ret () i.id)
    contract c.id cs.id i.id

/-- `cellLoc(c)`, named `l`. -/
private def cellLoc (c : ValId) : BuildM E Unit ValId :=
  emitApply (nm "l") locT Base.cellLoc.ref #[c] (typeArgs := ta[intT])

/-- `cellLoc(c)`, returned: the location of the contents of the cell `c`. -/
private def retLoc (c : ValId) : BuildM E Unit Unit := do
  finishBlock (.ret () (← cellLoc c))

/-- `cellLoc(nth(cs, i))`, returned, with the failure of `nth` going to `fail`. -/
private def retNthLoc (fail : Label) (cs i : ValId) : BuildM E Unit Unit := do
  retLoc (← emitApply (nm "n") cellT Demo.nth.ref #[cs, i] (succs := #[goto fail]))

/-- `ok(cellLoc(c))`, returned from a region of `attempt`. -/
private def okLoc (c : ValId) : BuildM E Unit Unit := do
  let k ← emitApply (nm "k") locT Base.cellLoc.ref #[c] (typeArgs := ta[intT])
  finishBlock (.ret () (← emitApply (nm "v") exT Base.Except.ok.ref #[k]))

/-- `i ≥ 0`, returned. -/
private def nonNeg (i : ValId) : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitApply (nm "ok") boolT Demo.ge.ref #[i, ← emitConst (nm "zero") (.int 0)]))

/-- `@m.f(c, cs, i) -> base.Int` with the contract `clauses`, returning `i`. -/
private def withClauses (clauses : String) : String := s!"module m \{
  func @m.f(%c.0 : base.Ref(base.Int), %cs.0 : base.Sequence(base.Ref(base.Int)), %i.0 : base.Int) -> base.Int
{clauses}
  \{
    entry.0(%c.0 : base.Ref(base.Int), %cs.0 : base.Sequence(base.Ref(base.Int)), %i.0 : base.Int):
      ret(%i.0)
  }
}
"

/-! ## Locations in the base -/

-- `base.cellLoc` denotes a location by identity and reads no state.
#guard (Base.cellLoc.sig (e := E)).effect == .pure
#guard (Base.cellLoc.sig (e := E)).succs.isEmpty && (Base.cellLoc.sig (e := E)).regions.isEmpty

/-! ## What the rules accept -/

/-- A `writes` frame of one region: the contents of the cell `c`. -/
private def cellFrame : Built := withContract fun c _ _ => do
  Build.writes #[.region (retLoc c)]

private def cellFrameText : String := withClauses "    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    })"

#guard failing cellFrame == []
#guard cellFrame.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees cellFrame cellFrameText

/-- A frame that mixes a cell and a region, whose failure goes to a block that ends in
`unreachable`: the contents of the cell at position `i` of `cs`. -/
private def mixed : Built := withContract fun c cs i => do
  Build.writes #[.cell c, .region (withFailureBlock #[intT] none fun fail =>
    retNthLoc fail cs i)]

private def mixedText : String := withClauses "    writes(%c.0, {
      loc.0():
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^fail.0()
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })"

#guard failing mixed == []
#guard mixed.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees mixed mixedText

-- `Func.map` keeps the frame's region.
#guard mixed.toOption.any fun f => (f.val.map fun _ => ({} : Info)).format .full == f.val.format .full

-- The entries keep their order and their kinds.
#guard mixed.toOption.any fun f =>
  f.val.contract.writes.map (·.map (·.cell?)) == some #[some ⟨0⟩, none] &&
    f.val.contract.reads.isNone

/-- A `requires` clause, a `reads` frame with a cell and a region, which may rely on the `requires`
clause, and a `writes` frame with a region. -/
private def readsWrites : Built := withContract fun c cs i => do
  Build.requires (nonNeg i)
  Build.reads #[.cell c, .region (withFailureBlock #[intT] none fun fail =>
    retNthLoc fail cs i)]
  Build.writes #[.region (retLoc c)]

private def readsWritesText : String := withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = demo.ge(%i.0, 0)
        ret(%ok.0)
    }
    reads(%c.0, {
      loc.0():
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^fail.0()
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })
    writes({
      loc.1():
        %l.1 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.1)
    })"

#guard failing readsWrites == []
#guard readsWrites.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees readsWrites readsWritesText

-- A contract's regions are its clauses', then its `reads` frame's, then its `writes` frame's, as
-- they print, and their values come after the body's.
#guard readsWrites.toOption.any fun f =>
  f.val.contract.regions.map (fun r => r.blocks[0]?.map (ToDDM.nameText ·.label.name)) ==
    [some "pre.0", some "loc.0", some "loc.1"]

#guard readsWrites.toOption.any fun f => f.val.defs.map (·.id.id) == List.range 9

/-- The extern `@m.g(cs) -> base.Unit`, which may change the contents of the first cell of `cs`.
Its frame is trusted. -/
private def ext : Built :=
  Build.buildExtern (.str (nm "m") "g") #[(nm "cs", cellsT)] Base.Unit () fun ps => do
    if let some cs := ps[0]? then
      Build.writes #[.region (withFailureBlock #[intT] none fun fail => do
        retNthLoc fail cs (← emitConst (nm "zero") (.int 0)))]

private def extText : String := "module m {
  extern func @m.g(%cs.0 : base.Sequence(base.Ref(base.Int))) -> base.Unit
    writes({
      loc.0():
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, 0) ^fail.0()
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })
}
"

#guard failing ext == []
#guard ext.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees ext extText

-- In full, the constant of the frame region is a value of the region.
/-- info: module m {
  extern func @m.g(%cs.0 : base.Sequence(base.Ref(base.Int))) -> base.Unit
    writes({
      loc.0():
        %c.0 : base.Int = const 0
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %c.0) ^fail.0()
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })
} -/
#guard_msgs in
#eval do
  match ← Module.read E extText "t.dyn" with
  | .error e => IO.println e
  | .ok m => IO.println (m.format .full)

/-- A frame region with a nested region that passes the failure of `nth` on with `base.error`, so
that the failure of `attempt` carries it to the frame region's block that ends in
`unreachable`. -/
private def nested : Built := withContract fun _ cs i => do
  Build.writes #[.region (withFailureBlock #[intT] none fun fail => do
    let body := region #[] (base := "body") do
      withPropagatingBlock intT locT fun prop => do
        okLoc (← emitApply (nm "n") cellT Demo.nth.ref #[cs, i] (succs := #[goto prop]))
    finishBlock (.ret () (← emitApply (nm "l") locT Demo.attempt.ref #[] (succs := #[goto fail])
      (regions := #[body]))))]

private def nestedText : String := withClauses "    writes({
      loc.0():
        %l.0 : base.Loc = demo.attempt[base.Loc] ^fail.0() {
          body.0():
            %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^propagate.0()
            %k.0 : base.Loc = base.cellLoc[base.Int](%n.0)
            %v.0 : base.Except(base.Int, base.Loc) = base.ok[base.Int, base.Loc](%k.0)
            ret(%v.0)
          propagate.0(%exc.0 : base.Int):
            %err.0 : base.Except(base.Int, base.Loc) = base.error[base.Int, base.Loc](%exc.0)
            ret(%err.0)
        }
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })"

#guard failing nested == []
#guard nested.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees nested nestedText

-- A `writes` frame whose region reads a cell: the call may change the contents of the cell that
-- `%cc.0` holds at the call.  A frame region may read state, since it runs in the state at the call.
#guard_msgs in
#eval readBack "module m {
  func @m.h(%cc.0 : base.Ref(base.Ref(base.Int))) -> base.Int
    writes({
      loc.0():
        %c.0 : base.Ref(base.Int) = base.refGet[base.Ref(base.Int)](%cc.0)
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    })
  {
    entry.0(%cc.0 : base.Ref(base.Ref(base.Int))):
      %c.1 : base.Ref(base.Int) = base.refGet[base.Ref(base.Int)](%cc.0)
      %u.0 : base.Unit = base.refSet[base.Int](%c.1, 0)
      ret(0)
  }
}
"

/-! ## What the rules reject

Each rejection breaks one rule, in the builder and in the reader. -/

/-! ### A frame region takes no arguments and returns a `base.Loc` -/

-- A frame region that returns an integer.
#guard failing (withContract fun _ _ i => do
  Build.writes #[.region (finishBlock (.ret () i))]) == ["contract"]

/-- info: t.dyn:5:8: a frame region of @m.f returns base.Int, but a frame region returns a base.Loc -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        ret(%i.0)
    })")

-- The same, with a literal.
/-- info: t.dyn:5:8: a frame region of @m.f returns base.Int, but a frame region returns a base.Loc -/
#guard_msgs in
#eval readBack (withClauses "    reads({
      loc.0():
        ret(5)
    })")

-- When the value that the `ret` passes is defined after it in the printed order, the reader checks
-- its type at the end of the function, with its general message.
/-- info: t.dyn:7:12: %b.0 has type base.Bool, but ret, operand 1 takes base.Loc -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        jump ^b.0()
      c.0():
        ret(%b.0)
      b.0():
        %b.0 : base.Bool = demo.ge(%i.0, 0)
        jump ^c.0()
    })")

-- A frame region with an argument.
-- The builder emits only frame regions without arguments, so this one goes into the contract
-- directly.
#guard failing (withContract fun c _ _ => do
  let p ← freshVal (nm "p") intT
  let r ← region #[p] (retLoc c) "loc"
  modify fun s => { s with contract.writes := some #[.region r] }) == ["contract"]

/-- info: t.dyn:3:11: a frame region takes no arguments -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0(%p.0 : base.Int):
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    })")

/-! ### A frame region sees only the parameters and its own values -/

-- A frame region that uses the result of an `ensures` clause: `%r.0`, value 3.
#guard failing (withContract fun _ cs _ => do
  Build.ensures (nm "r") intT fun _ => do finishBlock (.ret () (← emitConst (nm "t") (.bool true)))
  Build.writes #[.region (withFailureBlock #[intT] none fun fail =>
    retNthLoc fail cs ⟨3⟩)]) == ["contract"]

/-- info: t.dyn:9:52: a contract of @m.f uses %r.0, which is neither a parameter of @m.f nor defined in the frame region -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }
    writes({
      loc.0():
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %r.0) ^fail.0()
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })")

-- A frame region that uses a value of another frame region: `%l.0`, value 3.
#guard failing (withContract fun c _ _ => do
  Build.writes #[.region (retLoc c), .region (finishBlock (.ret () ⟨3⟩))]) ==
  ["contract"]

/-- info: t.dyn:9:12: a contract of @m.f uses %l.0, which is neither a parameter of @m.f nor defined in the frame region -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    }, {
      loc.1():
        ret(%l.0)
    })")

-- The same, with a value of a later frame region.
/-- info: t.dyn:5:12: %l.1 is not defined in its frame region -/
#guard_msgs in
#eval readBack (withClauses "    reads({
      loc.0():
        ret(%l.1)
    })
    writes({
      loc.1():
        %l.1 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.1)
    })")

-- A frame region that uses a value of the body: `%l.0`, value 1.
#guard failing (build (.str (nm "m") "f") intT () do
  let c ← freshVal (nm "c") cellT
  let _ ← startFreshBlock #[c] "entry"
  let l ← cellLoc c.id
  finishBlock (.ret () (← emitConst (nm "z") (.int 0)))
  Build.writes #[.region (finishBlock (.ret () l))]) == ["contract"]

/-- info: t.dyn:5:12: a contract of @m.f uses %l.0, which is neither a parameter of @m.f nor defined in the frame region -/
#guard_msgs in
#eval readBack "module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    writes({
      loc.0():
        ret(%l.0)
    })
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
      ret(0)
  }
}
"

-- A frame region that uses a value of a `requires` clause: `%l.0`, value 3.
#guard failing (withContract fun c _ _ => do
  Build.requires do
    let _ ← cellLoc c
    finishBlock (.ret () (← emitConst (nm "t") (.bool true)))
  Build.writes #[.region (finishBlock (.ret () ⟨3⟩))]) == ["contract"]

/-- info: t.dyn:10:12: a contract of @m.f uses %l.0, which is neither a parameter of @m.f nor defined in the frame region -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(true)
    }
    writes({
      loc.0():
        ret(%l.0)
    })")

-- The body sees none of the values of the frame regions: `%l.0`, value 1.
#guard failing (build (.str (nm "m") "k") locT () do
  let c ← freshVal (nm "c") cellT
  let _ ← startFreshBlock #[c] "entry"
  finishBlock (.ret () ⟨1⟩)
  Build.writes #[.region (retLoc c.id)]) == ["scoping"]

/-- info: t.dyn:10:10: the body of @m.k uses %l.0, a value of its contract -/
#guard_msgs in
#eval readBack "module m {
  func @m.k(%c.0 : base.Ref(base.Int)) -> base.Loc
    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    })
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      ret(%l.0)
  }
}
"

-- A frame still names a cell once, with a region between the two entries.
#guard failing (withContract fun c _ _ => do
  Build.writes #[.cell c, .region (retLoc c), .cell c]) == ["contract"]

/-- info: t.dyn:7:7: writes names %c.0 twice -/
#guard_msgs in
#eval readBack (withClauses "    writes(%c.0, {
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    }, %c.0)")

-- A frame region is scoped as a body of its own: a block that its entry does not reach.
/-- info: t.dyn:2:2: @m.f is not well formed
  in a frame region, block `dead.0` is unreachable from the entry -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
      dead.0():
        unreachable
    })")

/-! ### A frame region applies no operation declared `writes` -/

-- `base.refSet` in a frame region.
#guard failing (withContract fun c _ _ => do
  Build.writes #[.region do
    let _ ← emitApply (nm "u") Base.Unit Base.refSet.ref #[c, ← emitConst (nm "zero") (.int 0)]
    retLoc c]) == ["contract"]

/-- info: t.dyn:5:8: a contract region of @m.f may not change state, but base.refSet is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        %u.0 : base.Unit = base.refSet[base.Int](%c.0, 0)
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    })")

/-! ### A failure in a frame region goes to a block that ends in `unreachable` -/

-- A failure that goes to a block that returns a location.
#guard failing (withContract fun c cs i => do
  Build.writes #[.region do
    let l ← cellLoc c
    let fail ← freshLabel "fail"
    retNthLoc fail cs i
    let _ ← Build.startBlockWith fail (nm "e") intT
    finishBlock (.ret () l)]) == ["failures"]

/-- info: t.dyn:6:8: in a frame region of @m.f, the failure successor of %n.0 goes to fail.0, which does not end in unreachable; a failure must be unreachable -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^fail.0()
        %l.1 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.1)
      fail.0(%e.0 : base.Int):
        ret(%l.0)
    })")

-- A failure that goes to a block that computes a location, then ends in `unreachable`.
#guard failing (withContract fun c cs i => do
  Build.writes #[.region do
    let fail ← freshLabel "fail"
    retNthLoc fail cs i
    let _ ← Build.startBlockWith fail (nm "e") intT
    let _ ← cellLoc c
    finishBlock (.unreachable ())]) == ["failures"]

/-- info: t.dyn:5:8: in a frame region of @m.f, the failure successor of %n.0 goes to fail.0, which does more than define constants; a failure must be unreachable -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^fail.0()
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        %l.1 : base.Loc = base.cellLoc[base.Int](%c.0)
        unreachable
    })")

-- A failure in a region nested in a frame region that turns into a value.
#guard failing (withContract fun c cs i => do
  Build.writes #[.region (withFailureBlock #[intT] none fun fail => do
    let body := region #[] (base := "body") do
      let recover ← freshLabel "recover"
      okLoc (← emitApply (nm "n") cellT Demo.nth.ref #[cs, i] (succs := #[goto recover]))
      let _ ← Build.startBlockWith recover (nm "e") intT
      okLoc c
    finishBlock (.ret () (← emitApply (nm "l") locT Demo.attempt.ref #[] (succs := #[goto fail])
      (regions := #[body]))))]) == ["propagates"]

/-- info: t.dyn:7:12: in a region nested in a contract of @m.f, the failure successor of %n.0 goes to recover.0, which does not pass the failure on with base.error -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        %l.0 : base.Loc = demo.attempt[base.Loc] ^fail.0() {
          body.0():
            %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^recover.0()
            %k.0 : base.Loc = base.cellLoc[base.Int](%n.0)
            %v.0 : base.Except(base.Int, base.Loc) = base.ok[base.Int, base.Loc](%k.0)
            ret(%v.0)
          recover.0(%e.0 : base.Int):
            %k.1 : base.Loc = base.cellLoc[base.Int](%c.0)
            %v.1 : base.Except(base.Int, base.Loc) = base.ok[base.Int, base.Loc](%k.1)
            ret(%v.1)
        }
        ret(%l.0)
      fail.0(%e.1 : base.Int):
        unreachable
    })")

/-! ### A frame region ends its blocks in control flow and has no cycle -/

-- A terminal operation with successors, `tryNth`, in a frame region.
#guard failing (withContract fun _ cs i => do
  Build.writes #[.region do
    let ok ← freshLabel "ok"
    let no ← freshLabel "no"
    terminate Demo.tryNth.ref #[cs, i] (succs := #[goto ok, goto no])
    retLoc (← Build.startBlockWith ok (nm "n") cellT)
    let _ ← Build.startBlockWith no (nm "e") intT
    Build.unreachable]) == ["terminators"]

/-- info: t.dyn:5:8: a contract region of @m.f ends loc.0 with demo.tryNth; a contract region may end a block only with ret, jump, branch, unreachable or a case instruction -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        demo.tryNth(%cs.0, %i.0) ^ok.0() ^no.0()
      ok.0(%n.0 : base.Ref(base.Int)):
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      no.0(%e.0 : base.Int):
        unreachable
    })")

-- A frame region with a loop.
#guard failing (withContract fun c _ i => do
  Build.writes #[.region do
    let loop ← freshLabel "loop"
    let done ← freshLabel "done"
    finishBlock (.jump () (goto loop #[i]))
    let n ← freshVal (nm "n") intT
    startBlock loop #[n]
    let ok ← emitApply (nm "ok") boolT Demo.ge.ref #[n.id, ← emitConst (nm "zero") (.int 0)]
    finishBlock (.branch () ok (goto done) (goto loop #[n.id]))
    startBlock done
    retLoc c]) == ["acyclic"]

/-- info: t.dyn:6:6: a contract region of @m.f has a cycle through loop.0 -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        jump ^loop.0(%i.0)
      loop.0(%n.0 : base.Int):
        %ok.0 : base.Bool = demo.ge(%n.0, 0)
        branch(%ok.0) ^done.0() ^loop.0(%n.0)
      done.0():
        %l.0 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.0)
    })")

/-! ### A frame region does not apply `base.old` -/

#guard failing (withContract fun c _ _ => do
  Build.writes #[.region (withFailureBlock #[intT] none fun fail => do
    finishBlock (.ret () (← Build.old (nm "o") intT locT fail fun _ => okLoc c)))]) == ["old"]

/-- info: t.dyn:5:8: base.old is allowed only in an ensures clause, but @m.f uses it in a frame region -/
#guard_msgs in
#eval readBack (withClauses "    writes({
      loc.0():
        %o.0 : base.Loc = base.old[base.Int, base.Loc] ^fail.0() {
          old.0():
            %k.0 : base.Loc = base.cellLoc[base.Int](%c.0)
            %v.0 : base.Except(base.Int, base.Loc) = base.ok[base.Int, base.Loc](%k.0)
            ret(%v.0)
        }
        ret(%o.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })")

/-! ## The builder's order

`Build.reads` and `Build.writes` run the body of each frame region themselves, in the order of the
entries.  The clauses come in the order they print: `requires`, `ensures`, then the `reads` frame
and the `writes` frame.  A frame region's values come after the clauses', so a clause emitted after
a frame is a misuse. -/

/-- A `requires` clause, an `ensures` clause, a `reads` frame with a region, and a `writes` frame
with a cell and a region, emitted in that order. -/
private def allParts : Built := withContract fun c cs i => do
  Build.requires (nonNeg i)
  Build.ensures (nm "r") intT nonNeg
  Build.reads #[.region (withFailureBlock #[intT] none fun fail => retNthLoc fail cs i)]
  Build.writes #[.cell c, .region (retLoc c)]

private def allPartsText : String := "module m {
  func @m.f(%c.0 : base.Ref(base.Int), %cs.0 : base.Sequence(base.Ref(base.Int)), %i.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = demo.ge(%i.0, 0)
        ret(%ok.0)
    }
    ensures {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = demo.ge(%r.0, 0)
        ret(%ok.1)
    }
    reads({
      loc.0():
        %n.0 : base.Ref(base.Int) = demo.nth(%cs.0, %i.0) ^fail.0()
        %l.0 : base.Loc = base.cellLoc[base.Int](%n.0)
        ret(%l.0)
      fail.0(%e.0 : base.Int):
        unreachable
    })
    writes(%c.0, {
      loc.1():
        %l.1 : base.Loc = base.cellLoc[base.Int](%c.0)
        ret(%l.1)
    })
  {
    entry.0(%c.0 : base.Ref(base.Int), %cs.0 : base.Sequence(base.Ref(base.Int)), %i.0 : base.Int):
      ret(%i.0)
  }
}
"

#guard failing allParts == []
#guard allParts.toOption.any (decide ·.val.Canonical)

#guard_msgs in
#eval agrees allParts allPartsText

#guard misuses (withContract fun c _ i => do
  Build.writes #[.region (retLoc c)]
  Build.requires (nonNeg i)) == #["a requires clause after a frame"]

#guard misuses (withContract fun c _ i => do
  Build.reads #[.region (retLoc c)]
  Build.ensures (nm "r") intT fun _ => nonNeg i) == #["an ensures clause after a frame"]

#guard misuses (withContract fun c _ _ => do
  Build.writes #[.region (retLoc c)]
  Build.reads #[.region (retLoc c)]) == #["a reads clause after the writes clause"]

-- A frame region that leaves a block open.
#guard misuses (withContract fun _ _ _ => do
  Build.writes #[.region (do let _ ← emitConst (nm "zero") (.int 0))]) ==
  #["region loc ends with block loc.0 open"]

end Strata.Dyn.FrameTest
