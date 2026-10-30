/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env.Handle
import StrataDyn.Env.WF
import StrataDyn.DSL
-- The commands below read the record at elaboration time.
meta import StrataDyn.DSL.Model

set_option autoImplicit false

/-!
# The `environment` command: the record

Each `environment` command records its declarations' signatures, resolved, for its children
and for anything else that reads them, such as the typed emitters.  `Rec` declares one of each
kind of declaration and `RecChild` extends it; the record of each instruction is printed as a
block would write it.
-/

namespace Strata.Dyn.DSLRecordTest

/-- One of each kind of declaration. -/
environment Rec where
  namespace rec
  type Int
  type Bool
  type Seq (+a)
  type Fn (args : list) (ret)
  data Box (+a) where
    | box (contents : a)
    | empty
  abbrev ints := Seq Int
  insn add (lhs rhs : Int) : Int
  insn pick [a] (cond : Bool) (x y : a) : a
  insn sum (*xs : Int) : Int
  insn div (lhs rhs : Int) (^err (code : Int) (msg : Bool)) : Int
  insn loop [a] (&body (i : Int) : Box a) : ints
  insn callFn [(as : list) r] (f : Fn as r) (*args : as) : r
  insn bind [(cs : list)] (f : Fn [*cs, Int] Bool) (*xs : cs) : Fn [Int] Bool
  insn unpack [(ts : list)] (f : Fn ts Int) (^k (*xs : ts)) : Int
  terminal insn branch (cond : Bool) (^t ^f)
  end rec

/-- A child: its record holds only its own declarations, and the parent's is reachable. -/
environment RecChild extends Rec where
  namespace child
  open rec
  insn first [a] (xs : Seq a) (^none) : a
  end child

open Lean Elab Command DSL

/-- Print the record of the environment `ns` and its ancestors, nearest last. -/
meta def printRecord (ns : Lean.Name) : CommandElabM Unit := do
  let env ← getEnv
  let kind : OpKind → String
    | .decl => "decl"
    | .ctor d i => s!"ctor {d} {i}"
    | .case d => s!"case {d}"
  let lines := (allTypes env ns).map (fun t =>
      s!"type {t.envName} {t.params.map (·.1)}{if t.isData then s!" data {t.ctors}" else ""}") ++
    (allOps env ns).map fun o => s!"{kind o.kind}: {o.show}"
  logInfo ("\n".intercalate lines.toList)

/--
info: type rec.Int #[]
type rec.Bool #[]
type rec.Seq #[a]
type rec.Fn #[args, ret]
type rec.Box #[a] data #[rec.box, rec.empty]
ctor rec.Box 0: insn rec.box [a] (contents : a) : rec.Box a
ctor rec.Box 1: insn rec.empty [a] : rec.Box a
case rec.Box: terminal insn rec.Box.case [a] (scrutinee : rec.Box a) (^box (_ : a)) (^empty)
decl: insn rec.add (lhs : rec.Int) (rhs : rec.Int) : rec.Int
decl: insn rec.pick [a] (cond : rec.Bool) (x : a) (y : a) : a
decl: insn rec.sum (*xs : rec.Int) : rec.Int
decl: insn rec.div (lhs : rec.Int) (rhs : rec.Int) (^err (_ : rec.Int) (_ : rec.Bool)) : rec.Int
decl: insn rec.loop [a] (&body (i : rec.Int) : rec.Box a) : rec.Seq rec.Int
decl: insn rec.callFn [(as : list) r] (f : rec.Fn as r) (*args : as) : r
decl: insn rec.bind [(cs : list)] (f : rec.Fn [*cs, rec.Int] rec.Bool) (*xs : cs) : rec.Fn [rec.Int] rec.Bool
decl: insn rec.unpack [(ts : list)] (f : rec.Fn ts rec.Int) (^k (*_ : ts)) : rec.Int
decl: terminal insn rec.branch (cond : rec.Bool) (^t) (^f)
decl: insn child.first [a] (xs : rec.Seq a) (^none) : a
-/
#guard_msgs in
run_cmd printRecord `Strata.Dyn.DSLRecordTest.RecChild

-- A child's own record holds only its own declarations.
/--
info: [child.first]
-/
#guard_msgs in
run_cmd do
  let some e := findEntry? (← getEnv) `Strata.Dyn.DSLRecordTest.RecChild | throwError "none"
  logInfo m!"{e.ops.map (·.envName)}"

-- A declaration is found by its Lean name, through the record of its environment.
/--
info: rec.Box: type
rec.box: op
rec.Box.case: op
child.first: op
none
-/
#guard_msgs in
run_cmd do
  let env ← getEnv
  let describe (n : Lean.Name) : String := match findDecl? env n with
    | some (.type _ t) => s!"{t.envName}: type"
    | some (.op _ o) => s!"{o.envName}: op"
    | none => "none"
  logInfo ("\n".intercalate
    ([`Rec.Box, `Rec.Box.box, `Rec.Box.case, `RecChild.first, `Rec.nope].map fun n =>
      describe (`Strata.Dyn.DSLRecordTest ++ n)))

end Strata.Dyn.DSLRecordTest
