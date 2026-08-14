/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.Specs.ToLaurel

meta section

/-! # SpecExpr → Laurel lowering tests

Direct unit tests for `StrataPython.Specs.ToLaurel.specExprToLaurel`, covering
the arithmetic (`PAdd`/`PSub`/…), comparison (`pcmp`), boolean (`and`/`or`), and
literal-boxing (`from_int`/`from_bool`/`from_None`) arms that previously had no
direct lowering test, plus an exhaustive check of `pcmpPreludeName`.
-/

namespace StrataPython.Specs.ToLaurel.SpecExprLoweringTest

open StrataPython
open StrataPython.Specs
open StrataPython.Specs.ToLaurel
open StrataPython.Laurel (SomeTypedStmtExpr)
open Strata
open Strata.Laurel

/-! ## Harness -/

def loc : SourceRange := default

/-- Identifiers referenced by test expressions, all typed `Any`. -/
def argTypes : Std.HashMap String HighType :=
  .ofList [("x", StrataPython.Laurel.tyAny), ("y", StrataPython.Laurel.tyAny)]

def specCtx : SpecExprContext := { procName := "test", argTypes }

def laurelCtx : ToLaurelContext := { filepath := "test.py", modulePrefix := "" }

/-- Lower a `SpecExpr` in `ctx` and return the resulting top-level `StmtExpr`
    plus the number of reported errors (0 means the lowering succeeded). -/
private def lowerIn (ctx : SpecExprContext) (e : SpecExpr) : StmtExpr × Nat :=
  let act := specExprToLaurel e unknownSource ctx laurelCtx
  let (res, st) := act.run {}
  (res.2.stmt.val, st.errors.size)

/-- Lower a `SpecExpr` in the default all-`Any` context. -/
def lower (e : SpecExpr) : StmtExpr × Nat := lowerIn specCtx e

/-- Describe the head node of a lowered `StmtExpr`: the callee name of a
    `StaticCall`, otherwise the constructor name. Operators are `StaticCall`s to
    their built-in wrapper, so a boolean operator's head reads as `$and`/`$or`. -/
def headName : StmtExpr → String
  | .StaticCall callee _ => callee.text
  | other                => other.constructorName

/-- Number of arguments passed to a head `StaticCall`. -/
def headArgCount : StmtExpr → Nat
  | .StaticCall _ args  => args.length
  | _                   => 0

/-- Render the *full concrete structure* of a lowered `StmtExpr` — constructor,
    local-variable names, and call arguments in order — so a test can pin the
    exact term rather than just its top-level shape. Only covers the node kinds
    reached by these lowering tests; anything else falls back to the constructor
    name. -/
private partial def describeStmt : StmtExpr → String
  | .Var (.Local id)      => s!"Var(Local {id.text})"
  | .StaticCall callee as =>
      s!"StaticCall({callee.text}, [{", ".intercalate (as.map fun a => describeStmt a.val)}])"
  | .Old inner            => s!"Old({describeStmt inner.val})"
  | other                 => other.constructorName

def expectHead (name : String) (e : SpecExpr) : IO Unit := do
  let (stmt, errs) := lower e
  unless errs == 0 do
    throw <| IO.userError s!"{name}: lowering reported {errs} error(s)"
  unless headName stmt == name do
    throw <| IO.userError s!"expected head '{name}', got '{headName stmt}'"

/-- Sample `Any`-typed operands. -/
def x : SpecExpr := .var "x" loc
def y : SpecExpr := .var "y" loc

/-! ## pcmpPreludeName is the single source of prelude comparison names -/

#guard pcmpPreludeName .lt    == "PLt"
#guard pcmpPreludeName .le    == "PLe"
#guard pcmpPreludeName .gt    == "PGt"
#guard pcmpPreludeName .ge    == "PGe"
#guard pcmpPreludeName .eq    == "PEq"
#guard pcmpPreludeName .ne    == "PNEq"
#guard pcmpPreludeName .isIn  == "PIn"
#guard pcmpPreludeName .notIn == "PNotIn"

/-! ## Lowering checks -/

def arithmeticTests : IO Unit := do
  expectHead "PAdd"      (.add x y loc)
  expectHead "PSub"      (.sub x y loc)
  expectHead "PMul"      (.mul x y loc)
  expectHead "PFloorDiv" (.floorDiv x y loc)
  expectHead "PMod"      (.mod x y loc)
  expectHead "PPow"      (.pow x y loc)
  -- Unary minus lowers to a single-operand `PNeg`.
  let (negStmt, negErrs) := lower (.neg x loc)
  unless negErrs == 0 do throw <| IO.userError s!"neg: {negErrs} error(s)"
  unless headName negStmt == "PNeg" do
    throw <| IO.userError s!"neg: expected PNeg, got {headName negStmt}"
  unless headArgCount negStmt == 1 do
    throw <| IO.userError s!"neg: expected 1 operand, got {headArgCount negStmt}"

/-- `.pcmp op l r` lowers to `Any_to_bool(StaticCall (pcmpPreludeName op) [l, r])`. -/
def pcmpTests : IO Unit := do
  for op in [PCmpOp.lt, .le, .gt, .ge, .eq, .ne, .isIn, .notIn] do
    let (stmt, errs) := lower (.pcmp op x y loc)
    unless errs == 0 do throw <| IO.userError s!"pcmp {op.tag}: {errs} error(s)"
    match stmt with
    | .StaticCall outer [inner] =>
      unless outer.text == "Any_to_bool" do
        throw <| IO.userError s!"pcmp {op.tag}: expected outer Any_to_bool, got {outer.text}"
      unless headName inner.val == pcmpPreludeName op do
        throw <| IO.userError
          s!"pcmp {op.tag}: expected inner {pcmpPreludeName op}, got {headName inner.val}"
    | _ =>
      throw <| IO.userError s!"pcmp {op.tag}: expected Any_to_bool(StaticCall ..), got {headName stmt}"

/-- `.intGe`/`.intLe` lower to `Any_to_bool(StaticCall "PGe"/"PLe" [l, r])`.
    Unlike `pcmp`, these arms hard-code `PGe`/`PLe` rather than going through
    `pcmpPreludeName`, so they are a distinct lowering path worth pinning. -/
def intBoundTests : IO Unit := do
  for (label, inner, e) in
      [("intGe", "PGe", SpecExpr.intGe x (.intLit 3 loc) loc),
       ("intLe", "PLe", SpecExpr.intLe x (.intLit 3 loc) loc)] do
    let (stmt, errs) := lower e
    unless errs == 0 do throw <| IO.userError s!"{label}: lowering reported {errs} error(s)"
    match stmt with
    | .StaticCall outer [arg] =>
      unless outer.text == "Any_to_bool" do
        throw <| IO.userError s!"{label}: expected outer Any_to_bool, got {outer.text}"
      unless headName arg.val == inner do
        throw <| IO.userError s!"{label}: expected inner {inner}, got {headName arg.val}"
    | _ =>
      throw <| IO.userError s!"{label}: expected Any_to_bool(StaticCall ..), got {headName stmt}"

/-- An unsupported expression reports at least one error (the `errors` counter
    actually moves). `.floatLit` hits the `Float literals not yet supported` arm. -/
def errorPathTests : IO Unit := do
  let (_, errs) := lower (.floatLit "1.5" loc)
  unless errs ≥ 1 do
    throw <| IO.userError s!"floatLit: expected ≥ 1 reported error, got {errs}"

/-- `.and`/`.or` lower to a call to the boolean wrapper `$and`/`$or` of their
    (boolean) operands. Operands here are `pcmp` comparisons, which are
    `Bool`-typed. -/
def expectBoolOp (label : String) (op : Operation) (e : SpecExpr) : IO Unit := do
  let (stmt, errs) := lower e
  unless errs == 0 do throw <| IO.userError s!"{label}: lowering reported {errs} error(s)"
  unless headName stmt == op.procName do
    throw <| IO.userError s!"{label}: expected a call to {op.procName}, got {headName stmt}"

def boolTests : IO Unit := do
  let cmp := SpecExpr.pcmp .lt x y loc
  expectBoolOp "and" .And (.and cmp cmp loc)
  expectBoolOp "or"  .Or  (.or cmp cmp loc)

/-- Boolean operators over `Any`-typed operands (a bare bool param lowers to
    `Any`, not `TBool`). `asBool` must coerce each operand via `Any_to_bool`
    rather than reporting a type error and dropping the assertion. -/
def boolAnyOperandTests : IO Unit := do
  -- Binary operators: both operands wrapped in `Any_to_bool`.
  for (label, op, e) in
      [("and", Operation.And, SpecExpr.and x y loc),
       ("or",  .Or,           .or x y loc),
       ("implies", .Implies,  .implies x y loc)] do
    let (stmt, errs) := lower e
    unless errs == 0 do throw <| IO.userError s!"{label} (Any operands): {errs} error(s)"
    match stmt with
    | .StaticCall actual [l, r] =>
      unless actual.text == op.procName do
        throw <| IO.userError s!"{label}: expected a call to {op.procName}, got {actual.text}"
      unless headName l.val == "Any_to_bool" && headName r.val == "Any_to_bool" do
        throw <| IO.userError
          s!"{label}: expected Any_to_bool operands, got {headName l.val} / {headName r.val}"
    | _ => throw <| IO.userError s!"{label}: expected {op.procName}(l, r), got {headName stmt}"
  -- Unary `not` over an `Any` operand: `$not(Any_to_bool(x))`.
  let (notStmt, notErrs) := lower (.not x loc)
  unless notErrs == 0 do throw <| IO.userError s!"not (Any operand): {notErrs} error(s)"
  match notStmt with
  | .StaticCall actual [arg] =>
    unless actual.text == Operation.Not.procName do
      throw <| IO.userError
        s!"not: expected a call to {Operation.Not.procName}, got {actual.text}"
    unless headName arg.val == "Any_to_bool" do
      throw <| IO.userError s!"not: expected Any_to_bool operand, got {headName arg.val}"
  | _ =>
    throw <| IO.userError
      s!"not: expected {Operation.Not.procName}(arg), got {headName notStmt}"

/-- Literal boxing: each scalar literal becomes its `from_*` prelude call. -/
def literalTests : IO Unit := do
  expectHead "from_int"  (.intLit 7 loc)
  expectHead "from_bool" (.boolLit true loc)
  expectHead "from_None" (.noneLit loc)

/-- `asAny` boxing reached indirectly: an arithmetic operand that is an int/bool
    literal is boxed via `from_int`/`from_bool` before being passed to `PAdd`. -/
def asAnyBoxingTests : IO Unit := do
  let (stmt, errs) := lower (.add (.intLit 1 loc) (.boolLit true loc) loc)
  unless errs == 0 do throw <| IO.userError s!"asAny add: {errs} error(s)"
  match stmt with
  | .StaticCall callee [l, r] =>
    unless callee.text == "PAdd" do
      throw <| IO.userError s!"asAny add: expected PAdd, got {callee.text}"
    unless headName l.val == "from_int" do
      throw <| IO.userError s!"asAny add: expected left from_int, got {headName l.val}"
    unless headName r.val == "from_bool" do
      throw <| IO.userError s!"asAny add: expected right from_bool, got {headName r.val}"
  | _ => throw <| IO.userError s!"asAny add: expected PAdd(.., ..), got {headName stmt}"

/-- A `.UserDefined` operand that is *not* `Any` is a type error in both
    coercion positions. `asAny` and `asBool` each match `.UserDefined id` and
    then test `id.text == "Any"`, so a non-`Any` user-defined type takes the
    error arm rather than being coerced — the operand is still returned, so the
    surrounding expression keeps its shape and only the error count moves. -/
def nonAnyUserDefinedTests : IO Unit := do
  let customCtx : SpecExprContext :=
    { procName := "test"
      argTypes := .ofList [("z", HighType.UserDefined (mkId "SomeType"))] }
  let z : SpecExpr := .var "z" loc
  -- `asAny`: an arithmetic operand must be `Any`-typed.
  let (addStmt, addErrs) := lowerIn customCtx (.add z z loc)
  unless addErrs == 2 do
    throw <| IO.userError s!"asAny (SomeType operand): expected 2 errors, got {addErrs}"
  unless headName addStmt == "PAdd" do
    throw <| IO.userError s!"asAny (SomeType operand): expected PAdd, got {headName addStmt}"
  -- `asBool`: a boolean-operator operand must be `TBool` or `Any`.
  let (andStmt, andErrs) := lowerIn customCtx (.and z z loc)
  unless andErrs == 2 do
    throw <| IO.userError s!"asBool (SomeType operand): expected 2 errors, got {andErrs}"
  -- Operators are `StaticCall`s to the `$`-prefixed built-in wrappers, so the
  -- head's callee name is what identifies the operator.
  match andStmt with
  | .StaticCall callee _ =>
    unless callee.text == Operation.And.procName do
      throw <| IO.userError
        s!"asBool (SomeType operand): expected a call to {Operation.And.procName}, got {callee.text}"
  | _ =>
    throw <| IO.userError
      s!"asBool (SomeType operand): expected a StaticCall, got {headName andStmt}"

/-- `SpecExpr.old` wraps its argument in Laurel's `Old(…)`. A bare variable
    wraps to `Old(Var)`; a compound inner expression is lowered recursively and
    the whole result sits under the `Old` wrapper (e.g. `old(x + y)` becomes
    `Old(PAdd(x, y))`, not `PAdd(Old(x), Old(y))`).

    Both cases pin the *full concrete term* via `describeStmt` — variable names
    and operand order included — so a renamed variable or swapped operands would
    fail the check, not just a wrong top-level constructor. -/
private def oldTests : IO Unit := do
  -- Bare variable: the inner term is exactly the local `x`, wrapped in `Old`.
  let (stmt, errs) := lower (.old x loc)
  unless errs == 0 do throw <| IO.userError s!"old: {errs} error(s)"
  let bare := describeStmt stmt
  unless bare == "Old(Var(Local x))" do
    throw <| IO.userError s!"old: expected Old(Var(Local x)), got {bare}"
  -- Compound inner expression: the binary op is lowered under the `Old` wrapper,
  -- preserving the callee (`PAdd`) and both operands in order (`x` then `y`).
  let (compound, cErrs) := lower (.old (.add x y loc) loc)
  unless cErrs == 0 do throw <| IO.userError s!"old(compound): {cErrs} error(s)"
  let comp := describeStmt compound
  unless comp == "Old(StaticCall(PAdd, [Var(Local x), Var(Local y)]))" do
    throw <| IO.userError
      s!"old(compound): expected Old(StaticCall(PAdd, [Var(Local x), Var(Local y)])), got {comp}"

def allTests : IO Unit := do
  arithmeticTests
  pcmpTests
  intBoundTests
  errorPathTests
  boolTests
  boolAnyOperandTests
  literalTests
  asAnyBoxingTests
  nonAnyUserDefinedTests
  oldTests

#guard_msgs in
#eval allTests

end StrataPython.Specs.ToLaurel.SpecExprLoweringTest
end
