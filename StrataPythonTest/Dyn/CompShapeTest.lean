/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataPython.Dyn.Build
public import StrataPython.Dyn.CompShape
import StrataDyn.Env.WF
-- The builder, the checker and the shape check run as compiled code below.
meta import StrataDyn.WF
meta import StrataPython.Dyn.Build
meta import StrataPython.Dyn.CompShape
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The shape of comprehensions

`CompShape.check` on functions built with `PyBuild`: one accepted function per comprehension
operation, a comprehension nested in an element, and one rejected function for each rule and
for each way of breaking S3.
-/

namespace StrataPython.Dyn.CompShapeTest

open Strata.Dyn

open StrataPython.Dyn.PyBuild

/-! Some functions below break a rule in a way that the typed builder does not express, such as
leaving a region from a block that the builder does not close.  They build their blocks and
transfers with the untyped layer, `Build.Raw`, through these. -/

private def rawLabel (base : String) : PyM Unit Label :=
  monadLift (Build.Raw.freshLabel (env := Py.env) (α := Unit) base)

private def rawStart (l : Label) (ps : Array (ValDecl Py.env) := #[]) : PyM Unit Unit :=
  monadLift (Build.Raw.startBlock (env := Py.env) (α := Unit) l ps)

private def rawStartWith (l : Label) (name : Name) : PyM Unit ValId :=
  monadLift (Build.Raw.startBlockWith (env := Py.env) (α := Unit) l name Py.Value)

private def rawJump (k : Target.Raw) : PyM Unit Unit :=
  monadLift (Build.Raw.jump (env := Py.env) (α := Unit) k)

private def rawBranch (c : ValId) (t f : Target.Raw) : PyM Unit Unit :=
  monadLift (Build.Raw.branch (env := Py.env) (α := Unit) c t f)

private def rawRet (v : ValId) : PyM Unit Unit :=
  monadLift (Build.Raw.ret (env := Py.env) (α := Unit) v)

/-- What `CompShape.check` says of the function `body` builds, with parameters `xs` and `ys`:
`ok`, the rule it breaks, or that the function is not well formed. -/
private def shape (body : Vector ValId 2 → PyM Unit Unit) : String :=
  match buildFunc (Py.pn "f") #["xs", "ys"] () body with
  | .error e => if e.misuses.isEmpty then "not well formed" else s!"misuses: {e.misuses}"
  | .ok fn =>
    match CompShape.checkFunc fn with
    | .ok () => "ok"
    | .error msg => msg

/-! ## Accepted -/

/-- `[x for x in xs if x]`. -/
private def listIf (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x =>
    compIf (fun t f => do branch (← truthy x) t f)
      (compAppend out (pure x))
  emitReturn r

/-- info: "ok" -/
#guard_msgs in
#eval shape listIf

/-- `{x for x in xs for y in ys}`. -/
private def setFor (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← setComp args[0] fun out x => compFor args[1] fun _ => compAdd out (pure x)
  emitReturn r

/-- info: "ok" -/
#guard_msgs in
#eval shape setFor

/-- `{x: y for x in xs for y in ys}`. -/
private def dictFor (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← dictComp args[0] fun out x => compFor args[1] fun y => compStore out (pure x) (pure y)
  emitReturn r

/-- info: "ok" -/
#guard_msgs in
#eval shape dictFor

/-- `[[y for y in ys] for x in xs]`: a comprehension nested in an element adds to its own
accumulator (S4's exception). -/
private def nested (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out _ =>
    compAppend out (listComp args[1] fun out' y => compAppend out' (pure y))
  emitReturn r

/-- info: "ok" -/
#guard_msgs in
#eval shape nested

/-- `[x for x in xs for y in ys if y]`: a `compIf` in a `compFor`. -/
private def ifInFor (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x =>
    compFor args[1] fun y =>
      compIf (fun t f => do branch (← truthy y) t f)
        (compAppend out (pure x))
  emitReturn r

/-- info: "ok" -/
#guard_msgs in
#eval shape ifInFor

/-- `[y for x in xs for y in [z for z in x]]`: a comprehension in a chain region, before its
continuation. -/
private def compInChain (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let inner ← listComp x fun out' z => compAppend out' (pure z)
    compFor inner fun y => compAppend out (pure y)
  emitReturn r

/-- info: "ok" -/
#guard_msgs in
#eval shape compInChain

/-! ## Rejected -/

/-- S1: the inner comprehension adds to the outer one's accumulator. -/
private def outerAcc (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out _ =>
    compAppend out (listComp args[1] fun _ y => compAppend out (pure y))
  emitReturn r

/-- info: "in py.f: py.compAppend adds to an accumulator that is not its comprehension's (S1)" -/
#guard_msgs in
#eval shape outerAcc

/-- S2: the accumulator is passed to `base.ok`. -/
private def accEscapes (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let _ ← Build.emitApply (env := Py.env) (α := Unit) (stem "leak")
      (Py.raising Py.ListAcc) Base.Except.ok.ref #[out]
    compAppend out (pure x)
  emitReturn r

/-- info: "in py.f: base.ok takes an accumulator as an operand (S2)" -/
#guard_msgs in
#eval shape accEscapes

/-- S3: two additions in one region. -/
private def twoAdds (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    compAppend out (pure x)
    compAppend out (pure x)
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp applies 2 continuations, not one (S3)" -/
#guard_msgs in
#eval shape twoAdds

/-- S3: a hidden filter: one path returns `ok` without the addition. -/
private def hiddenFilter (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let keep ← rawLabel "keep"
    let skip ← rawLabel "skip"
    rawBranch (← truthy x) (Build.Raw.goto keep) (Build.Raw.goto skip)
    rawStart skip
    let u ← Build.emitApply (env := Py.env) (α := Unit) (stem "unit") Base.Unit
      Base.Unit.unit.ref #[]
    let ok ← Build.emitApply (env := Py.env) (α := Unit) (stem "ok")
      (Py.raising Base.Unit) Base.Except.ok.ref #[u]
    rawRet ok
    rawStart keep
    compAppend out (pure x)
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp returns ok without its continuation (S3)" -/
#guard_msgs in
#eval shape hiddenFilter

/-- S3: a region with no continuation. -/
private def noAdd (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun _ _ => pure ()
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp applies 0 continuations, not one (S3)" -/
#guard_msgs in
#eval shape noAdd

/-- S3: a region that exits with a value its own block does not make: here the `ok` the entry
made, returned from the next block. -/
private def foreignExit (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let u ← Build.emitApply (env := Py.env) (α := Unit) (stem "unit") Base.Unit
      Base.Unit.unit.ref #[]
    let ok ← Build.emitApply (env := Py.env) (α := Unit) (stem "ok")
      (Py.raising Base.Unit) Base.Except.ok.ref #[u]
    let next ← rawLabel "next"
    rawJump (Build.Raw.goto next)
    rawStart next
    compAppend out (pure x)
    rawRet ok
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp leaves other than by returning ok or error (S3)" -/
#guard_msgs in
#eval shape foreignExit

/-- S3: the block holding the addition raises instead of returning `ok`. -/
private def addThenRaise (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    compAppend out (pure x)
    jump (← raiseTo x)
  emitReturn r

/-- info: "in py.f: the block holding the continuation of the region each.0 of py.listComp does not return ok (S3)" -/
#guard_msgs in
#eval shape addThenRaise

/-- S3: a cycle through the continuation's handler: a failing `compFor` would run again and
add its first elements a second time. -/
private def retryFor (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out _ => do
    let l ← freshLabel [] "L"
    let h ← freshLabel [Py.Value] "H"
    jump l.goto
    let _ ← startBlockWith h (stem "exc")
    jump l.goto
    startBlock l
    withHandler h (compFor args[1] fun y => compAppend out (pure y))
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp transfers back to H.0 (S3)" -/
#guard_msgs in
#eval shape retryFor

/-- S3: a cycle after the addition: each failure of the test appends the element again. -/
private def retryAfterAdd (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let l ← freshLabel [] "L"
    let h ← freshLabel [Py.Value] "H"
    jump l.goto
    let _ ← startBlockWith h (stem "exc")
    jump l.goto
    startBlock l
    compAppend out (pure x)
    let _ ← withHandler h (truthy x)
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp transfers back to H.0 (S3)" -/
#guard_msgs in
#eval shape retryAfterAdd

/-- S3: a hidden filter through a `branch` whose two successors leave the region. -/
private def twoExits (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let keep ← rawLabel "keep"
    let skip ← rawLabel "skip"
    rawBranch (← truthy x) (Build.Raw.goto keep) (Build.Raw.goto skip)
    rawStart skip
    let u ← Build.emitApply (env := Py.env) (α := Unit) (stem "unit") Base.Unit
      Base.Unit.unit.ref #[]
    let e ← Build.emitApply (env := Py.env) (α := Unit) (stem "err")
      (Py.raising Base.Unit) Base.Except.error.ref #[x]
    let ok ← Build.emitApply (env := Py.env) (α := Unit) (stem "ok")
      (Py.raising Base.Unit) Base.Except.ok.ref #[u]
    let t ← emitConst (stem "t") (.bool true)
    rawBranch t ⟨Label.exit, #[e]⟩ ⟨Label.exit, #[ok]⟩
    rawStart keep
    compAppend out (pure x)
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp leaves other than by returning ok or error (S3)" -/
#guard_msgs in
#eval shape twoExits

/-- S3: a hidden filter through a case whose `ok` successor leaves the region with its
payload, passing no value itself. -/
private def caseExit (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let keep ← rawLabel "keep"
    let skip ← rawLabel "skip"
    rawBranch (← truthy x) (Build.Raw.goto keep) (Build.Raw.goto skip)
    rawStart skip
    let u ← Build.emitApply (env := Py.env) (α := Unit) (stem "unit") Base.Unit
      Base.Unit.unit.ref #[]
    let ok ← Build.emitApply (env := Py.env) (α := Unit) (stem "ok")
      (Py.raising Base.Unit) Base.Except.ok.ref #[u]
    let rr ← Build.emitApply (env := Py.env) (α := Unit) (stem "rr")
      (Py.raising (Py.raising Base.Unit)) Base.Except.ok.ref #[ok]
    let dead ← rawLabel "dead"
    monadLift (Build.terminate (env := Py.env) (α := Unit) Base.Except.case.ref #[rr]
      #[⟨Label.exit, #[]⟩, Build.Raw.goto dead])
    let _ ← rawStartWith dead (stem "e")
    unreachable
    rawStart keep
    compAppend out (pure x)
  emitReturn r

/-- info: "in py.f: the region each.0 of py.listComp leaves other than by returning ok or error (S3)" -/
#guard_msgs in
#eval shape caseExit

/-- S2: the accumulator passed to a block. -/
private def accToBlock (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let l ← rawLabel "L"
    rawJump (Build.Raw.goto l #[out])
    let o ← Build.freshVal (env := Py.env) (α := Unit) (stem "o") Py.ListAcc
    rawStart l #[o]
    compAppend out (pure x)
  emitReturn r

/-- info: "in py.f: a block passes or returns an accumulator (S2)" -/
#guard_msgs in
#eval shape accToBlock

/-- S2: the accumulator pre-bound as an argument of a failure's handler. -/
private def accToHandler (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let h ← freshLabel [Py.ListAcc, Py.Value] "H"
    let _ ← withHandlerTo (h.goto.bind (Val.ofId Py.ListAcc out)) (truthy x)
    compAppend out (pure x)
    let u ← Build.emitApply (env := Py.env) (α := Unit) (stem "unit") Base.Unit
      Base.Unit.unit.ref #[]
    let ok ← Build.emitApply (env := Py.env) (α := Unit) (stem "ok")
      (Py.raising Base.Unit) Base.Except.ok.ref #[u]
    rawRet ok
    let o ← Build.freshVal (env := Py.env) (α := Unit) (stem "o") Py.ListAcc
    let e ← Build.freshVal (env := Py.env) (α := Unit) (stem "e") Py.Value
    rawStart h.label #[o, e]
    jump (← raiseTo e.id)
  emitReturn r

/-- info: "in py.f: py.truthy passes an accumulator to a block (S2)" -/
#guard_msgs in
#eval shape accToHandler

/-- S4: an addition in an `elt` region. -/
private def addInElt (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x =>
    compAppend out (do compAppend out (pure x); pure x)
  emitReturn r

/-- info: "in py.f: py.compAppend adds outside a comprehension's chain (S4)" -/
#guard_msgs in
#eval shape addInElt

/-- S4: an addition in a `key` region, and one in a `value` region. -/
private def addInKey (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← dictComp args[0] fun out x =>
    compStore out (do compStore out (pure x) (pure x); pure x) (pure x)
  emitReturn r

/-- info: "in py.f: py.compStore adds outside a comprehension's chain (S4)" -/
#guard_msgs in
#eval shape addInKey

private def addInValue (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← dictComp args[0] fun out x =>
    compStore out (pure x) (do compStore out (pure x) (pure x); pure x)
  emitReturn r

/-- info: "in py.f: py.compStore adds outside a comprehension's chain (S4)" -/
#guard_msgs in
#eval shape addInValue

/-- S5: a `compFor` in an `elt` region. -/
private def forInElt (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x =>
    compAppend out (do compFor args[1] fun _ => pure (); pure x)
  emitReturn r

/-- info: "in py.f: py.compFor outside a comprehension's chain (S5)" -/
#guard_msgs in
#eval shape forInElt

/-- S4: an addition in a `cond` region. -/
private def addInCond (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x =>
    compIf (fun t _ => do compAppend out (pure x); jump t)
      (compAppend out (pure x))
  emitReturn r

/-- info: "in py.f: py.compAppend adds outside a comprehension's chain (S4)" -/
#guard_msgs in
#eval shape addInCond

/-- S5: a `compIf` outside any comprehension. -/
private def strayIf (_ : Vector ValId 2) : PyM Unit Unit := do
  compIf (fun t _ => jump t) (pure ())
  emitReturnNone

/-- info: "in py.f: py.compIf outside a comprehension's chain (S5)" -/
#guard_msgs in
#eval shape strayIf

/-- The type check already rejects an accumulator where a list is expected. -/
private def listAppendAcc (args : Vector ValId 2) : PyM Unit Unit := do
  let r ← listComp args[0] fun out x => do
    let _ ← emitEffect (.str .base "append") Py.listAppend.ref #[out, x]
    compAppend out (pure x)
  emitReturn r

/-- info: "not well formed" -/
#guard_msgs in
#eval shape listAppendAcc

/-! ## A module

`check` runs over every function of a checked module, and names the first that breaks a
rule. -/

/-- What `CompShape.check` says of the module of the functions `bodies` build, named `f0`,
`f1`, … -/
private def moduleShape (bodies : Array (Vector ValId 2 → PyM Unit Unit)) : String :=
  let fs := bodies.mapIdx fun i body => buildFunc (Py.pn s!"f{i}") #["xs", "ys"] () body
  match fs.mapM id with
  | .error _ => "not built"
  | .ok fs => match Module.ofChecked (Py.pn "m") fs () with
    | .error _ => "not well formed"
    | .ok m => match CompShape.check m with
      | .ok () => "ok"
      | .error msg => msg

/-- info: "ok" -/
#guard_msgs in
#eval moduleShape #[listIf, dictFor]

/-- info: "in py.f1: the region each.0 of py.listComp applies 2 continuations, not one (S3)" -/
#guard_msgs in
#eval moduleShape #[listIf, twoAdds]

end StrataPython.Dyn.CompShapeTest
