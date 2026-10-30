/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
public import StrataDyn.WF
public import StrataPython.Dyn.Env
import StrataDyn.Build
import StrataDyn.Util.LabelMap
-- Matching instruction names needs the environment's representation at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The shape of comprehensions

A comprehension is one `py.listComp`, `py.setComp` or `py.dictComp`.  Its `each` region runs the
first `for` clause, and holds the rest of the comprehension as a chain: a `py.compFor` for a
later `for` clause, a `py.compIf` for the `if`s after a `for`, and at the end one addition,
`py.compAppend`, `py.compAdd` or `py.compStore`, that adds the element to the accumulator the
comprehension's region receives.

Types alone do not keep an accumulator in place: the base's generic operations and block
parameters take any type.  `check` decides the rules a reader of a comprehension relies on:

* S1: the accumulator of an addition is the one of the nearest enclosing comprehension.
* S2: an accumulator is used only as the accumulator of an addition: not as another operand,
  not passed to a block, and not returned.
* S3: a chain region (an `each` region, or a `compIf`'s `then` region) applies exactly one
  continuation, a `compFor`, a `compIf` or an addition, at its top level.  Its blocks form no
  cycle: every transfer between them goes to a later block.  It leaves only by `ret v`, with
  `v` made by `base.ok` or `base.error` in the same block, and the only block that returns
  `ok` is the one holding the continuation.  So each candidate that reaches the continuation
  runs it exactly once.
* S4: a `compIf`'s `cond` region and an addition's `elt`, `key` and `value` regions apply no
  addition, except in a comprehension nested there, to that comprehension's accumulator.
* S5: a `compFor` or `compIf` appears only in a chain region.

A function body, and a region of an operation that is not a comprehension operation, a
`compFor` or a `compIf`, follow the rule of a `cond` region: no addition, `compFor` or `compIf`
in them, except inside a comprehension nested there.

The rules assume a well-formed function: `check` takes a checked `Module`.
-/

namespace StrataPython.Dyn.CompShape

open Strata.Dyn

public section

/-- Where a region sits: in a comprehension's chain, building the accumulator `acc`, or
anywhere else. -/
inductive Place where
  | chain (acc : ValId)
  | expr

private def nm {isig : InsnSig Py.env} (r : InsnRef Py.env isig) : Name := r.name

/-- What an operation is to the rules. -/
private inductive Role where
  /-- `listComp`, `setComp` or `dictComp`. -/
  | comp
  | compFor
  | compIf
  /-- `compAppend`, `compAdd` or `compStore`. -/
  | add
  | other

private def roleOf (n : Name) : Role :=
  if n == nm Py.listComp.ref || n == nm Py.setComp.ref || n == nm Py.dictComp.ref then .comp
  else if n == nm Py.compFor.ref then .compFor
  else if n == nm Py.compIf.ref then .compIf
  else if n == nm Py.compAppend.ref || n == nm Py.compAdd.ref || n == nm Py.compStore.ref then .add
  else .other

/-- Where the `i`-th region of an operation with role `role` sits, the operation being at
`here`.  `params` are the parameters of the region's entry block: a comprehension's first is
its accumulator. -/
private def regionPlace (role : Role) (here : Place) (i : Nat) (params : Array ValId) : Place :=
  match role, here with
  | .comp, _ => match params[0]? with
    | some out => .chain out
    | none => .expr
  | .compFor, .chain acc => .chain acc
  | .compIf, .chain acc => if i == 1 then .chain acc else .expr
  | _, _ => .expr

/-- The operation that defines `v` in `instrs`, if any. -/
private def definer {α : Type} (instrs : List (Instruction Py.env α)) (v : ValId) : Option Name :=
  instrs.findSome? fun
    | .apply _ d r .. => if d.id == v then some r.name else none
    | .const .. => none

/-- How a block leaves its region. -/
private inductive Exit where
  /-- By `ret v`, `v` made by `base.ok` in the block. -/
  | ok
  /-- By `ret v`, `v` made by `base.error` in the block. -/
  | error
  /-- In any other way: another terminator, or a value made elsewhere. -/
  | other
  /-- It does not leave the region. -/
  | stays

/-- What the check finds in a block of a region. -/
private structure BlockFacts where
  label : Label
  /-- Its continuations at the top level. -/
  conts : Nat
  exit : Exit
  /-- The blocks its transfers name, the region's exit excluded. -/
  targets : List Label
  /-- Whether one of its instructions transfers out of the region. -/
  instrExit : Bool

private def okName : Name := (Base.Except.ok.ref : InsnRef Py.env _).name
private def errorName : Name := (Base.Except.error.ref : InsnRef Py.env _).name
private def jumpName : Name := (Base.jump.ref : InsnRef Py.env _).name

/-- How a block with instructions `instrs` leaves its region, its terminator applying the
operation `term` with successors `succs`. -/
private def exitOf {α : Type} (instrs : List (Instruction Py.env α)) (term : Name)
    (succs : List Target.Raw) : Exit :=
  if !(succs.any (·.label == Label.exit)) then .stays
  else match succs with
    | [⟨t, #[v]⟩] =>
      if t != Label.exit || term != jumpName then .other
      else match definer instrs v with
        | some n => if n == okName then .ok else if n == errorName then .error else .other
        | none => .other
    | _ => .other

variable {α : Type} (fn : String)

/-- A failure, naming the function and the rule. -/
private def fail {β : Type} (rule msg : String) : Except String β :=
  .error s!"in {fn}: {msg} ({rule})"

/-- An accumulator among `vs`, if any. -/
private def accIn (accs : List ValId) (vs : List ValId) : Option ValId :=
  vs.find? (accs.contains ·)

/-- S3 for the chain region `region`, from the facts of its blocks, in order. -/
private def checkChain (region : String) (facts : List BlockFacts) : Except String Unit := do
  -- Each block's position, the first one for a repeated label.
  let positions : LabelMap Nat := facts.zipIdx.foldl (init := ∅) fun m (f, i) =>
    m.update f.label fun | some j => j | none => i
  for (f, i) in facts.zipIdx do
    if f.instrExit then
      fail fn "S3" s!"an instruction of {region} leaves the region"
    for t in f.targets do
      match positions.find? t with
      | some j => if j ≤ i then
          fail fn "S3" s!"{region} transfers back to {Strata.Dyn.Build.nameText t.name}"
      | none => pure ()
  let conts := facts.foldl (· + ·.conts) 0
  if conts != 1 then
    fail fn "S3" s!"{region} applies {conts} continuations, not one"
  if facts.any fun f => match f.exit with | .other => true | _ => false then
    fail fn "S3" s!"{region} leaves other than by returning ok or error"
  if facts.any fun f => match f.exit with | .ok => f.conts == 0 | _ => false then
    fail fn "S3" s!"{region} returns ok without its continuation"
  if !(facts.any fun f => match f.exit with | .ok => f.conts == 1 | _ => false) then
    fail fn "S3" s!"the block holding the continuation of {region} does not return ok"

mutual

/-- Check an instruction at `here`, with `accs` the accumulators in scope.  Returns the number
of continuations it is (zero or one). -/
private def checkInstr (accs : List ValId) (here : Place) :
    Instruction Py.env α → Except String Nat
  | .const .. => pure 0
  | .apply _ _ r _ args succs ⟨regions⟩ => do
    let role := roleOf r.name
    let op := Strata.Dyn.Build.nameText r.name
    -- S1, S2 and S4: where accumulators may appear among the operands.
    let rest ← match role, args.toList, here with
      | .add, out :: rest, .chain acc =>
        if out != acc then
          fail fn "S1" s!"{op} adds to an accumulator that is not its comprehension's"
        else pure rest
      | .add, _, _ => fail fn "S4" s!"{op} adds outside a comprehension's chain"
      | _, vs, _ => pure vs
    if (accIn accs rest).isSome then
      fail fn "S2" s!"{op} takes an accumulator as an operand"
    if (accIn accs (succs.toList.flatMap (·.args.toList))).isSome then
      fail fn "S2" s!"{op} passes an accumulator to a block"
    -- S5: clauses only in a chain.
    match role, here with
    | .compFor, .expr | .compIf, .expr =>
      fail fn "S5" s!"{op} outside a comprehension's chain"
    | _, _ => pure ()
    checkRegions accs role op here 0 regions
    return match role with
      | .compFor | .compIf | .add => 1
      | _ => 0

/-- `checkInstr` of each, summing the continuations. -/
private def checkInstrs (accs : List ValId) (here : Place) :
    List (Instruction Py.env α) → Except String Nat
  | [] => pure 0
  | i :: is => return (← checkInstr accs here i) + (← checkInstrs accs here is)

/-- Check the regions of the operation `op`, with role `role`, at `here`, the first one being
its `i`-th. -/
private def checkRegions (accs : List ValId) (role : Role) (op : String) (here : Place)
    (i : Nat) : List (Region Py.env α) → Except String Unit
  | [] => pure ()
  | ⟨blocks⟩ :: rs => do
    let params := match blocks[0]? with
      | some b => b.params.map (·.id)
      | none => #[]
    let place := regionPlace role here i params
    let accs := match place, role with
      | .chain out, .comp => out :: accs
      | _, _ => accs
    let facts ← checkBlocks accs place blocks.toList
    if let .chain _ := place then
      let entry := match blocks[0]? with
        | some b => Strata.Dyn.Build.nameText b.label.name
        | none => "?"
      checkChain fn s!"the region {entry} of {op}" facts
    checkRegions accs role op here (i + 1) rs

/-- Check blocks at `here`, giving the facts of each. -/
private def checkBlocks (accs : List ValId) (here : Place) :
    List (Block Py.env α) → Except String (List BlockFacts)
  | [] => pure []
  | ⟨label, _, ⟨instrs⟩, .apply _ tr _ targs tsuccs ⟨tregions⟩, _⟩ :: bs => do
    let conts ← checkInstrs accs here instrs
    if (accIn accs (targs.toList ++ tsuccs.toList.flatMap (·.args.toList))).isSome then
      fail fn "S2" "a block passes or returns an accumulator"
    checkRegions accs .other (Strata.Dyn.Build.nameText tr.name) here 0 tregions
    let instrSuccs := instrs.flatMap (·.succs.toList)
    let targets := (instrSuccs ++ tsuccs.toList).map (·.label) |>.filter (· != Label.exit)
    let facts : BlockFacts :=
      { label, conts, exit := exitOf instrs tr.name tsuccs.toList, targets,
        instrExit := instrSuccs.any (·.label == Label.exit) }
    return facts :: (← checkBlocks accs here bs)

end

/-- Check the comprehensions of the blocks of the function named `name`. -/
private def checkBody (name : Name) (blocks : Array (Block Py.env α)) : Except String Unit :=
  discard <| checkBlocks (Strata.Dyn.Build.nameText name) [] .expr blocks.toList

/-- Check the comprehensions of a checked function. -/
def checkFunc (func : {fn : Func Py.env α // fn.WF}) : Except String Unit :=
  checkBody func.1.name func.1.blocks

/-- Check the comprehensions of every function of `m`, failing at the first that breaks a
rule. -/
def check (m : Module Py.env α) : Except String Unit :=
  m.raw.funcs.toList.forM fun f => checkBody f.name f.blocks

end

end StrataPython.Dyn.CompShape
