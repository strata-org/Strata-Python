/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Dialect
public import StrataDyn.Examples.While.Env
public import StrataDyn.Build
-- Building instructions evaluates the environment representation at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Lowering While to Dyn

`lower` turns a While program, the AST that `#strata_gen` generates from the dialect, into a
checked module over `While.env`, emitting each function with `Dyn.Build`.  It type-checks as it goes,
and fails on an unknown name, a redeclared name, a type mismatch, a call with the wrong
arguments, or a construct a region does not allow.

* **Variables** are SSA values, not cells.  A block with one predecessor, and the join after a
  `case`, read the variables where they begin directly, as values of the blocks that dominate
  them.  A join after `if`, a loop header and a `catch` handler take every variable in scope as
  a parameter, and each edge into one passes the variables' current values.
* **Blocks** may come in any order: `Func.WF` and linking compute each body's dominator
  tree.  A handler that nothing raises to, which no edge would reach, is checked and then
  dropped.
* **Functions** that may raise, by a `raise`, `/`, `%`, a region operation or a call of one
  that may raise, return `base.Except Int T`; the others return their `T`.  `raise e` returns
  `error e`, and a raising operation's `^err` leaves to a block that does.  A call is
  `base.callCode` on the callee's typed code pointer, at its `Func.codeType`, and the call of a
  function that may raise is followed by `base.Except.case`, whose `^error` goes to the handler
  in effect: the innermost `catch`, the enclosing region's, or the function's own.  `T` may be a
  cell, which then travels in the `ok`, and the case's payload.
* **Cells**: `ref e` is `base.refNew`, `*r` `base.refGet` and `*r := e` `base.refSet`, at
  `base.Ref Int` or `base.Ref IntList`.  A `Cell` is `while.cellNew`, `cellGet` and `cellSet`,
  whose rules make, read and write cells of the machine's heap.
* **Regions**: `region while` and `region if` lower each body to a region of the operation,
  which reads the variables in scope but cannot assign them.  A body region yields a
  `while.Flow`: `next` when it ends, or `raise e` from its `raised` block, the handler in effect
  inside it.  A condition region yields a `Bool` and has no handler.
-/

namespace Strata.Dyn.While

open Strata.Dyn.While.Ast
open StrataDDM (SourceRange)

@[expose] public section

/-- The environment While lowers to. -/
abbrev E : Env Unit := While.env

/-- A While type, without its annotation. -/
inductive VTy where
  | int | bool | unit | list | ref | listRef | cell
  deriving Repr, DecidableEq, Inhabited

/-- The type a type expression denotes. -/
def Ast.Ty.vty {α : Type} : Ast.Ty α → VTy
  | .tyInt _ => .int
  | .tyBool _ => .bool
  | .tyUnit _ => .unit
  | .tyList _ => .list
  | .tyRef _ => .ref
  | .tyListRef _ => .listRef
  | .tyCell _ => .cell

/-- The type as While writes it. -/
def VTy.name : VTy → String
  | .int => "Int"
  | .bool => "Bool"
  | .unit => "Unit"
  | .list => "IntList"
  | .ref => "Ref"
  | .listRef => "ListRef"
  | .cell => "Cell"

/-- The Dyn type a While type lowers to. -/
def VTy.ty : VTy → TypeExpr E
  | .int => Base.Int
  | .bool => Base.Bool
  | .unit => Base.Unit
  | .list => While.IntList
  | .ref => Base.Ref Base.Int
  | .listRef => Base.Ref While.IntList
  | .cell => While.Cell

/-- `while.Flow`. -/
def flowT : TypeExpr E := While.Flow

/-- `base.Except Int t`. -/
def exceptT (t : TypeExpr E) : TypeExpr E := Base.Except Base.Int t

/-- A name of one component. -/
def nm (s : String) : Name := .str .base s

/-! ## What may raise

A function may raise if its body contains a `raise`, `/`, `%`, a region operation, or a call of
a function that may raise.  `scan` collects the first four and the callees; `mayRaise` closes
the callees. -/

/-- What a piece of code shows about raising: whether it raises itself, and what it calls. -/
structure Scan where
  raises : Bool := false
  calls : List String := []

instance : Append Scan := ⟨fun a b => ⟨a.raises || b.raises, a.calls ++ b.calls⟩⟩

/-- Code that raises. -/
def Scan.raising : Scan := { raises := true }

mutual

def scanExp : Exp SourceRange → Scan
  | .div _ a b | .mod _ a b => Scan.raising ++ scanExp a ++ scanExp b
  | .add _ a b | .sub _ a b | .mul _ a b | .pow _ a b | .lt _ a b | .le _ a b | .gt _ a b
  | .ge _ a b | .eq _ a b | .ne _ a b | .and _ a b | .or _ a b | .cons _ a b =>
    scanExp a ++ scanExp b
  | .paren _ a | .neg _ a | .not _ a | .mkRef _ a | .deref _ a | .mkCell _ a | .pick _ a =>
    scanExp a
  | .case _ e n _ _ c => scanExp e ++ scanExp n ++ scanExp c
  | .call _ ⟨_, f⟩ ⟨_, ⟨args⟩⟩ => { calls := [f] } ++ scanExps args
  | .int .. | .boolTrue _ | .boolFalse _ | .unit _ | .nil _ | .var .. | .tick _ => {}

def scanExps : List (Exp SourceRange) → Scan
  | [] => {}
  | e :: es => scanExp e ++ scanExps es

def scanStmt : Stmt SourceRange → Scan
  | .decl _ _ _ e | .assign _ _ e | .ret _ e | .expr _ e | .print _ e => scanExp e
  | .store _ r e => scanExp r ++ scanExp e
  | .ite _ c t ⟨_, none⟩ => scanExp c ++ scanBody t
  | .ite _ c t ⟨_, some (.elseBody _ e)⟩ => scanExp c ++ scanBody t ++ scanBody e
  | .while _ c b => scanExp c ++ scanBody b
  | .regionWhile _ c b => Scan.raising ++ scanExp c ++ scanBody b
  | .regionIte _ c t ⟨_, none⟩ => Scan.raising ++ scanExp c ++ scanBody t
  | .regionIte _ c t ⟨_, some (.elseBody _ e)⟩ =>
    Scan.raising ++ scanExp c ++ scanBody t ++ scanBody e
  | .block _ b => scanBody b
  | .raise _ e => Scan.raising ++ scanExp e
  | .try _ b _ h => scanBody b ++ scanBody h

def scanStmts : List (Stmt SourceRange) → Scan
  | [] => {}
  | s :: ss => scanStmt s ++ scanStmts ss

def scanBody : Body SourceRange → Scan
  | .body _ ⟨_, ⟨ss⟩⟩ => scanStmts ss

end

/-- A function's name, parameters and return type. -/
def Ast.Command.sig : Command SourceRange → String × List (String × VTy) × VTy
  | .func _ ⟨_, name⟩ ⟨_, ps⟩ ret _ =>
    (name, ps.toList.map (fun | .param _ ⟨_, x⟩ t => (x, t.vty)), ret.vty)

/-- The function's body. -/
def Ast.Command.body : Command SourceRange → Body SourceRange
  | .func _ _ _ _ b => b

/-- The functions that may raise, among `scans`, each function's name and scan: those that
raise themselves, then, `n` times, those that call one of them. -/
def mayRaise (scans : List (String × Scan)) : Nat → List String
  | 0 => scans.filterMap fun (f, s) => if s.raises then some f else none
  | n + 1 =>
    let r := mayRaise scans n
    scans.filterMap fun (f, s) => if s.raises || s.calls.any r.contains then some f else none

/-! ## The lowering state -/

/-- A function's signature, and whether it may raise. -/
structure FunSig where
  name : String
  params : List VTy
  ret : VTy
  raises : Bool

/-- What a call of the function returns: `ret`, in a `base.Except` if it may raise. -/
def FunSig.retTy (f : FunSig) : TypeExpr E := if f.raises then exceptT f.ret.ty else f.ret.ty

/-- The type of a code pointer to the function, its `Func.codeType`. -/
def FunSig.codeType (f : FunSig) : TypeExpr E :=
  Base.Fn (f.params.map VTy.ty) f.retTy

/-- Where a raise goes. -/
inductive Handler where
  /-- Nothing may raise: a region's condition, or a function that cannot raise. -/
  | none
  /-- Out of the function: return `error e`, from block `label` for an operation's `^err`. -/
  | propagate (label : Label)
  /-- Out of a body region: yield `raise e`, from block `label` for an operation's `^err`. -/
  | yield (label : Label)
  /-- To a `catch`'s block `label`, which takes the variables `vars` and then the raised
  integer. -/
  | catch (label : Label) (vars : List String)

/-- What lowering a function reads. -/
structure LCtx where
  sigs : List FunSig
  /-- The function's own signature. -/
  self : FunSig

/-- The lowering state of one function, beside the builder's. -/
structure LState where
  /-- The variables in scope, innermost first: name, type, current value. -/
  vars : List (String × VTy × ValId) := []
  handler : Handler
  /-- The variables a region in progress reads but cannot assign. -/
  readOnly : List String := []
  /-- Whether a region is in progress, which cannot `return`. -/
  inRegion : Bool := false
  /-- The handler blocks some edge goes to. -/
  used : List Label := []

/-- Emitting one function's code. -/
abbrev BM := BuildM E Unit

/-- Lowering one function. -/
abbrev M := ReaderT LCtx (StateT LState (ExceptT String BM))

/-- Run a builder action. -/
def build {β : Type} (m : BM β) : M β := liftM m

/-- The errors the builder has recorded. -/
def buildErrors : M (Array String) := build do return (← get).misuses

/-- Fail with the first error the builder recorded beyond the first `n`. -/
def checkBuild (n : Nat) : M Unit := do
  if let some e := (← buildErrors)[n]? then throw e

/-! ## Values and blocks -/

def lookupVar (x : String) : M (VTy × ValId) := do
  match (← get).vars.find? (·.1 == x) with
  | some (_, t, v) => return (t, v)
  | none => throw s!"unknown variable {x}"

def bindVar (x : String) (t : VTy) (v : ValId) : M Unit :=
  modify fun s => { s with vars := (x, t, v) :: s.vars }

def setVar (x : String) (v : ValId) : M Unit := do
  if (← get).readOnly.contains x then
    throw s!"{x} is assigned inside a region, which reads it but cannot assign it; use a cell"
  modify fun s =>
    { s with vars := s.vars.map fun (y, t, w) => if y == x then (y, t, v) else (y, t, w) }

/-- The current values of the variables `xs`. -/
def values (xs : List String) : M (Array ValId) := do
  let s ← get
  return (xs.filterMap fun x => (s.vars.find? (·.1 == x)).map (·.2.2)).toArray

/-- The names of the variables of `scope`, outermost first, as a block takes them. -/
def varNames (scope : List (String × VTy × ValId)) : List String := scope.reverse.map (·.1)

/-- Open block `l` with a fresh parameter for each variable of `scope`, then one more if
`extra` names it, and make those parameters the variables' values.  The last parameter's id, if
`extra` names one. -/
def openWithVars (l : Label) (scope : List (String × VTy × ValId))
    (extra : Option (String × VTy) := none) : M (Option ValId) := do
  let mut ps := #[]
  let mut vars := []
  for (x, t, _) in scope.reverse do
    let p ← build (Build.freshVal (nm x) t.ty)
    ps := ps.push p
    vars := (x, t, p.id) :: vars
  let e ← extra.mapM fun (x, t) => build (Build.freshVal (nm x) t.ty)
  build (Build.startBlock l (ps ++ e.toArray))
  modify fun s => { s with vars }
  return e.map (·.id)

/-- End the open block with a jump to `l`, passing the variables of `scope`. -/
def jumpWith (l : Label) (scope : List (String × VTy × ValId)) : M Unit := do
  build (Build.jump (Build.goto l (← values (varNames scope))))

/-- Keep only the variables of `outer`, at their current values. -/
def restoreScope (outer : List (String × VTy × ValId)) : M Unit :=
  modify fun s => { s with vars := s.vars.filter fun (x, _, _) => outer.any (·.1 == x) }

/-- Run `act` in its own scope: its declarations end with it. -/
def inScope (act : M Bool) : M Bool := do
  let outer := (← get).vars
  let t ← act
  restoreScope outer
  return t

def expect (want got : VTy) (what : String) : M Unit :=
  if want == got then pure () else throw s!"{what}: expected {want.name}, got {got.name}"

/-- `%t = r args succs regions`, a value of `type`, checking the builder's errors after it.
The type arguments are inferred from the operands' types and `type` when the builder runs. -/
def app {isig : InsnSig E} (stem : String) (type : TypeExpr E) (r : InsnRef E isig)
    (args : Array ValId) (succs : Array Target.Raw := #[])
    (regions : Array (BM (Dyn.Region E Unit)) := #[]) : M ValId := do
  let n := (← buildErrors).size
  let v ← build (Build.emitApply (nm stem) type r args succs regions (typeArgs := .infer))
  checkBuild n
  return v

def const (c : Const) : M ValId := build (Build.emitConst (nm "k") c)

/-- The `^err` successor of a raising operation: the handler in effect. -/
def errSite : M Target.Raw := do
  match (← get).handler with
  | .none => throw "the condition of a region while cannot raise"
  | .propagate l | .yield l =>
    modify fun s => { s with used := l :: s.used }
    return Build.goto l
  | .catch l vars =>
    modify fun s => { s with used := l :: s.used }
    return Build.goto l (← values vars)

/-- Leave the function with `v`, as `ok v` if it may raise. -/
def retValue (v : ValId) : M Unit := do
  let self := (← read).self
  if self.raises then
    build (Build.ret (← app "ok" self.retTy Base.Except.ok.ref #[v]))
  else build (Build.ret v)

/-- Raise `v`, an `Int`, to the handler in effect, ending the open block. -/
def raiseValue (v : ValId) : M Unit := do
  match (← get).handler with
  | .none => throw "the condition of a region while cannot raise"
  | .propagate _ =>
    let self := (← read).self
    build (Build.ret (← app "error" self.retTy Base.Except.error.ref #[v]))
  | .yield _ => build (Build.ret (← app "flow" flowT While.Flow.raise.ref #[v]))
  | .catch l vars =>
    modify fun s => { s with used := l :: s.used }
    build (Build.jump (Build.goto l ((← values vars).push v)))

/-- A binary operator. -/
inductive BinOp where
  | add | sub | mul | div | mod | pow | lt | le | gt | ge | eq | ne | and | or
  deriving DecidableEq

/-- The operands' and the result's types of `op`. -/
def BinOp.types : BinOp → VTy × VTy
  | .add | .sub | .mul | .div | .mod | .pow => (.int, .int)
  | .lt | .le | .gt | .ge | .eq | .ne => (.int, .bool)
  | .and | .or => (.bool, .bool)

/-- Apply binary operator `op` to lowered operands.  `a > b` is `b < a`, and `a >= b` is
`b <= a`. -/
def binApp (op : BinOp) (a b : ValId × VTy) : M (ValId × VTy) := do
  let (va, ta) := a
  let (vb, tb) := b
  let (arg, res) := op.types
  expect arg ta "left operand"
  expect arg tb "right operand"
  let x := #[va, vb]
  let r := res.ty
  let v ← match op with
    | .add => app "t" r While.add.ref x
    | .sub => app "t" r While.sub.ref x
    | .mul => app "t" r While.mul.ref x
    | .div => app "t" r While.div.ref x #[← errSite]
    | .mod => app "t" r While.mod.ref x #[← errSite]
    | .pow => app "t" r While.pow.ref x
    | .lt => app "t" r While.lt.ref x
    | .le => app "t" r While.le.ref x
    | .gt => app "t" r While.lt.ref #[vb, va]
    | .ge => app "t" r While.le.ref #[vb, va]
    | .eq => app "t" r While.eq.ref x
    | .ne => app "t" r While.ne.ref x
    | .and => app "t" r While.and_.ref x
    | .or => app "t" r While.or_.ref x
  return (v, res)

/-! ## Expressions -/

/-- The cell type holding values of `t`, if any, and the cell's `new`. -/
def newCell (t : VTy) (v : ValId) : M (ValId × VTy) :=
  match t with
  | .int => return (← app "cell" (VTy.ty .ref) Base.refNew.ref #[v], .ref)
  | .list => return (← app "cell" (VTy.ty .listRef) Base.refNew.ref #[v], .listRef)
  | _ => throw s!"ref: no cell holds a {t.name}"

/-- The contents of cell `c`, of type `t`. -/
def getCell (t : VTy) (c : ValId) : M (ValId × VTy) :=
  match t with
  | .ref => return (← app "t" Base.Int Base.refGet.ref #[c], .int)
  | .listRef => return (← app "t" While.IntList Base.refGet.ref #[c], .list)
  | .cell => return (← app "t" Base.Int While.cellGet.ref #[c], .int)
  | _ => throw s!"*: expected a cell, got {t.name}"

/-- Store `v`, of type `tv`, in cell `c`, of type `tc`. -/
def setCell (tc : VTy) (c : ValId) (tv : VTy) (v : ValId) : M Unit := do
  let unitT := VTy.ty .unit
  match tc with
  | .ref =>
    expect .int tv "contents of a cell"
    let _ ← app "u" unitT Base.refSet.ref #[c, v]
  | .listRef =>
    expect .list tv "contents of a cell"
    let _ ← app "u" unitT Base.refSet.ref #[c, v]
  | .cell =>
    expect .int tv "contents of a cell"
    let _ ← app "u" unitT While.cellSet.ref #[c, v]
  | _ => throw s!"*: expected a cell, got {tc.name}"

/-- Call `f` on `args`, after the checks. -/
def callFun (f : FunSig) (args : Array ValId) : M ValId := do
  let fv ← build (Build.emitFunc (nm f.name) (ty := f.codeType))
  let r ← app "r" f.retTy Base.callCode.ref (#[fv] ++ args)
  if !f.raises then return r
  let ok ← build (Build.freshLabel "ok")
  let site ← errSite
  let n := (← buildErrors).size
  build (Build.terminate Base.Except.case.ref #[r] #[Build.goto ok, site])
  checkBuild n
  build (Build.startBlockWith ok (nm "x") f.ret.ty)

mutual

def lowerExpr : Exp SourceRange → M (ValId × VTy)
  | .int _ ⟨_, n⟩ => return (← const (.int n), .int)
  | .boolTrue _ => return (← const (.bool true), .bool)
  | .boolFalse _ => return (← const (.bool false), .bool)
  | .unit _ => return (← const .unit, .unit)
  | .var _ ⟨_, x⟩ => do let (t, v) ← lookupVar x; return (v, t)
  | .paren _ e => lowerExpr e
  | .add _ a b => do binApp .add (← lowerExpr a) (← lowerExpr b)
  | .sub _ a b => do binApp .sub (← lowerExpr a) (← lowerExpr b)
  | .mul _ a b => do binApp .mul (← lowerExpr a) (← lowerExpr b)
  | .div _ a b => do binApp .div (← lowerExpr a) (← lowerExpr b)
  | .mod _ a b => do binApp .mod (← lowerExpr a) (← lowerExpr b)
  | .pow _ a b => do binApp .pow (← lowerExpr a) (← lowerExpr b)
  | .lt _ a b => do binApp .lt (← lowerExpr a) (← lowerExpr b)
  | .le _ a b => do binApp .le (← lowerExpr a) (← lowerExpr b)
  | .gt _ a b => do binApp .gt (← lowerExpr a) (← lowerExpr b)
  | .ge _ a b => do binApp .ge (← lowerExpr a) (← lowerExpr b)
  | .eq _ a b => do binApp .eq (← lowerExpr a) (← lowerExpr b)
  | .ne _ a b => do binApp .ne (← lowerExpr a) (← lowerExpr b)
  | .and _ a b => do binApp .and (← lowerExpr a) (← lowerExpr b)
  | .or _ a b => do binApp .or (← lowerExpr a) (← lowerExpr b)
  | .neg _ a => do
    let (v, t) ← lowerExpr a
    expect .int t "operand of -"
    return (← app "t" Base.Int While.neg.ref #[v], .int)
  | .not _ a => do
    let (v, t) ← lowerExpr a
    expect .bool t "operand of !"
    return (← app "t" Base.Bool While.not_.ref #[v], .bool)
  | .mkRef _ a => do
    let (v, t) ← lowerExpr a
    newCell t v
  | .deref _ a => do
    let (v, t) ← lowerExpr a
    getCell t v
  | .mkCell _ a => do
    let (v, t) ← lowerExpr a
    expect .int t "contents of a world cell"
    return (← app "cell" While.Cell While.cellNew.ref #[v], .cell)
  | .nil _ => return (← app "l" While.IntList While.IntList.nil.ref #[], .list)
  | .tick _ => return (← app "t" Base.Int While.tick.ref #[], .int)
  | .pick _ e => do
    let (v, t) ← lowerExpr e
    expect .int t "pick's bound"
    return (← app "t" Base.Int While.pick.ref #[v], .int)
  | .cons _ h t => do
    let (vh, th) ← lowerExpr h
    let (vt, tt) ← lowerExpr t
    expect .int th "head of ::"
    expect .list tt "tail of ::"
    return (← app "l" While.IntList While.IntList.cons.ref #[vh, vt], .list)
  | .case _ e onNil ⟨_, h⟩ ⟨_, t⟩ onCons => do
    let (v, te) ← lowerExpr e
    expect .list te "scrutinee of case"
    let outer := (← get).vars
    let nilL ← build (Build.freshLabel "nil")
    let consL ← build (Build.freshLabel "cons")
    let joinL ← build (Build.freshLabel "join")
    let n := (← buildErrors).size
    build (Build.terminate While.IntList.case.ref #[v] #[Build.goto nilL, Build.goto consL])
    checkBuild n
    build (Build.startBlock nilL)
    let (rn, tn) ← lowerExpr onNil
    build (Build.jump (Build.goto joinL #[rn]))
    let ph ← build (Build.freshVal (nm h) Base.Int)
    let pt ← build (Build.freshVal (nm t) While.IntList)
    build (Build.startBlock consL #[ph, pt])
    if (← get).vars.any (fun (y, _) => y == h || y == t) || h == t then
      throw s!"case: {h} or {t} is already declared"
    bindVar h .int ph.id
    bindVar t .list pt.id
    let (rc, tc) ← lowerExpr onCons
    expect tn tc "branches of case"
    build (Build.jump (Build.goto joinL #[rc]))
    modify fun s => { s with vars := outer }
    return (← build (Build.startBlockWith joinL (nm "r") tn.ty), tn)
  | .call _ ⟨_, f⟩ ⟨_, ⟨args⟩⟩ => do
    let vs ← lowerArgs args
    let some sig := (← read).sigs.find? (·.name == f) | throw s!"unknown function {f}"
    unless sig.params.length == vs.length do throw s!"{f} takes {sig.params.length} arguments"
    for (p, (_, t)) in sig.params.zip vs do expect p t s!"argument of {f}"
    return (← callFun sig (vs.map (·.1)).toArray, sig.ret)

def lowerArgs : List (Exp SourceRange) → M (List (ValId × VTy))
  | [] => return []
  | e :: es => do
    let v ← lowerExpr e
    return v :: (← lowerArgs es)

end

/-! ## Regions -/

/-- A region of an operation, yielding a value of `ret`, whose code `body` lowers from its entry
block: it returns the value to yield, or none if the code is terminated.  With `raises`, the
handler in effect inside it yields `while.Flow.raise e`; otherwise nothing in it may raise.  The
region reads the variables in scope and cannot assign them. -/
def region (raises : Bool) (body : M (Option ValId)) : M (BM (Dyn.Region E Unit)) := do
  let ctx ← read
  let s ← get
  let inner : LState := { s with readOnly := s.vars.map (·.1), inRegion := true,
                                 handler := .none, used := [] }
  return Build.region #[] do
    let raised ← Build.freshLabel "raised"
    let act : M Unit := do
      if raises then modify fun s => { s with handler := .yield raised }
      if let some v ← body then build (Build.ret v)
      if (← get).used.contains raised then
        let e ← build (Build.startBlockWith raised (nm "e") Base.Int)
        build (Build.ret (← app "flow" flowT While.Flow.raise.ref #[e]))
    match ← ((act.run ctx).run inner).run with
    | .ok _ => pure ()
    | .error msg =>
      Build.error msg
      if (← get).body.label.isSome then Build.unreachable

/-- A body region: `body`, then `while.Flow.next` if it ends. -/
def bodyRegion (body : M Bool) : M (BM (Dyn.Region E Unit)) :=
  region true do
    if ← inScope body then return none
    return some (← app "next" flowT While.Flow.next.ref #[])

/-! ## Statements -/

mutual

/-- Lower a statement list.  Returns whether the open block was terminated. -/
def lowerStmts : List (Stmt SourceRange) → M Bool
  | [] => return false
  | s :: ss => do
    if ← lowerStmt s then return true
    lowerStmts ss

/-- Lower a body's statements, in the current scope. -/
def lowerBody : Body SourceRange → M Bool
  | .body _ ⟨_, ⟨ss⟩⟩ => lowerStmts ss

/-- Lower an `else` branch, if any. -/
def lowerElse : Option (Else SourceRange) → M Bool
  | some (.elseBody _ b) => lowerBody b
  | none => pure false

def lowerStmt : Stmt SourceRange → M Bool
  | .decl _ ⟨_, x⟩ t e => do
    if (← get).vars.any (·.1 == x) then throw s!"{x} is already declared"
    let (v, te) ← lowerExpr e
    expect t.vty te s!"initializer of {x}"
    bindVar x t.vty v
    return false
  | .assign _ ⟨_, x⟩ e => do
    let (t, _) ← lookupVar x
    let (v, te) ← lowerExpr e
    expect t te s!"assignment to {x}"
    setVar x v
    return false
  | .store _ r e => do
    let (vr, tr) ← lowerExpr r
    let (ve, te) ← lowerExpr e
    setCell tr vr te ve
    return false
  | .ite _ c th ⟨_, el⟩ => do
    let (vc, tc) ← lowerExpr c
    expect .bool tc "condition of if"
    let outer := (← get).vars
    let thenL ← build (Build.freshLabel "then")
    let elseL ← build (Build.freshLabel "else")
    let joinL ← build (Build.freshLabel "join")
    build (Build.branch vc (Build.goto thenL) (Build.goto elseL))
    build (Build.startBlock thenL)
    let t₁ ← inScope (lowerBody th)
    unless t₁ do jumpWith joinL outer
    modify fun s => { s with vars := outer }
    build (Build.startBlock elseL)
    let t₂ ← inScope (lowerElse el)
    unless t₂ do jumpWith joinL outer
    if t₁ && t₂ then return true
    let _ ← openWithVars joinL outer
    return false
  | .while _ c body => do
    let outer := (← get).vars
    let headL ← build (Build.freshLabel "head")
    let bodyL ← build (Build.freshLabel "body")
    let exitL ← build (Build.freshLabel "exit")
    jumpWith headL outer
    let _ ← openWithVars headL outer
    let atHead := (← get).vars
    let (vc, tc) ← lowerExpr c
    expect .bool tc "condition of while"
    build (Build.branch vc (Build.goto bodyL) (Build.goto exitL))
    let afterCond := (← get).vars
    build (Build.startBlock bodyL)
    let t ← inScope (lowerBody body)
    unless t do jumpWith headL atHead
    build (Build.startBlock exitL)
    modify fun s => { s with vars := afterCond }
    return false
  | .regionWhile _ c body => do
    let cond ← region false do
      let (v, t) ← lowerExpr c
      expect .bool t "condition of region while"
      return some v
    let bodyR ← bodyRegion (lowerBody body)
    let _ ← app "u" (VTy.ty .unit) While.loop.ref #[] #[← errSite] #[cond, bodyR]
    return false
  | .regionIte _ c th ⟨_, el⟩ => do
    let (vc, tc) ← lowerExpr c
    expect .bool tc "condition of region if"
    let thenR ← bodyRegion (lowerBody th)
    let elseR ← bodyRegion (lowerElse el)
    let _ ← app "u" (VTy.ty .unit) While.«if».ref #[vc] #[← errSite] #[thenR, elseR]
    return false
  | .block _ b => inScope (lowerBody b)
  | .ret _ e => do
    if (← get).inRegion then throw "a region cannot return"
    let (v, t) ← lowerExpr e
    expect (← read).self.ret t "return value"
    retValue v
    return true
  | .raise _ e => do
    let (v, t) ← lowerExpr e
    expect .int t "raised value"
    raiseValue v
    return true
  | .try _ body ⟨_, x⟩ handler => do
    let outer := (← get).vars
    if outer.any (·.1 == x) then throw s!"{x} is already declared"
    let handlerL ← build (Build.freshLabel "catch")
    let joinL ← build (Build.freshLabel "join")
    let saved := (← get).handler
    modify fun s => { s with handler := .catch handlerL (varNames outer) }
    let t₁ ← inScope (lowerBody body)
    unless t₁ do jumpWith joinL outer
    modify fun s => { s with handler := saved, vars := outer }
    let handle : M Bool := do
      let some e ← openWithVars handlerL outer (some (x, .int))
        | throw "catch: no parameter for the raised value"
      bindVar x .int e
      let t₂ ← inScope (lowerBody handler)
      unless t₂ do jumpWith joinL outer
      return t₂
    let t₂ ← if (← get).used.contains handlerL then handle else do
      -- Nothing raises to the handler, so no edge reaches it: check it, in a region that is
      -- dropped, and emit nothing.
      let ctx ← read
      let s ← get
      let n := (← buildErrors).size
      let _ ← build (Build.region #[] do
        Build.unreachable
        match ← (((do let _ ← handle) : M Unit).run ctx |>.run s).run with
        | .ok _ => pure ()
        | .error msg =>
          Build.error msg
          if (← get).body.label.isSome then Build.unreachable)
      checkBuild n
      pure true
    modify fun s => { s with vars := outer }
    if t₁ && t₂ then return true
    let _ ← openWithVars joinL outer
    return false
  | .expr _ e => do
    let _ ← lowerExpr e
    return false
  | .print _ e => do
    let (v, t) ← lowerExpr e
    expect .int t "printed value"
    let _ ← app "u" (VTy.ty .unit) While.print.ref #[v]
    return false

end

/-! ## Functions and programs -/

/-- Lower one function. -/
def lowerFun (sigs : List FunSig) (self : FunSig) (f : Command SourceRange) :
    Except String {fn : Func E Unit // fn.WF} :=
  let (_, params, _) := f.sig
  let built := Build.run (nm self.name) self.retTy () do
    let ps ← params.toArray.mapM fun (x, t) => Build.freshVal (nm x) t.ty
    let _ ← Build.startFreshBlock ps "entry"
    let raiseL ← Build.freshLabel "raise"
    let s : LState := { handler := if self.raises then .propagate raiseL else .none }
    let act : M Unit := do
      for (x, t) in params, p in ps do
        if (← get).vars.any (·.1 == x) then throw s!"{x} is already declared"
        bindVar x t p.id
      let t ← lowerBody f.body
      unless t do
        if self.ret == .unit then retValue (← const .unit)
        else build Build.unreachable
      if (← get).used.contains raiseL then
        let e ← build (Build.startBlockWith raiseL (nm "e") Base.Int)
        raiseValue e
    ((act.run { sigs, self }).run s).run
  match built with
  | .ok (fn, .ok _) => .ok fn
  | .ok (_, .error e) => .error e
  | .error fail => match fail.value with
    | .error e => .error e
    | .ok _ => .error (fail.misuses[0]?.getD (toString fail))

/-- Lower each function, with the signatures `sigs`. -/
def lowerFuns (sigs : List FunSig) :
    List (Command SourceRange) → Except String (List {fn : Func E Unit // fn.WF})
  | [] => .ok []
  | f :: fs => do
    let (name, _, _) := f.sig
    let some self := sigs.find? (·.name == name) | .error s!"{name}: no signature"
    let g ← (lowerFun sigs self f).mapError (s!"{name}: " ++ ·)
    return g :: (← lowerFuns sigs fs)

/-- Lower a program to a module named `main`. -/
def lower (p : Program) : Except String (Module E Unit) := do
  let fs := p.toList
  let raising := mayRaise (fs.map fun f => (f.sig.1, scanBody f.body)) fs.length
  let sigs := fs.map fun f =>
    let (name, ps, ret) := f.sig
    { name, params := ps.map (·.2), ret, raises := raising.contains name : FunSig }
  (Module.ofChecked (nm "main") (← lowerFuns sigs fs).toArray ()).mapError fun ns =>
    s!"not well formed: {ns.toList.map Build.nameText}"

end

end Strata.Dyn.While
