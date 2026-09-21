/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.Specs.ToLaurel
meta import StrataPython.PySpecPipeline
meta import StrataLaurel.Implementation.FilterPrelude
meta import Plausible

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
  | .LiteralInt v         => s!"LiteralInt({v})"
  | .LiteralBool v        => s!"LiteralBool({v})"
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
/-! ## Module ghosts lower to `$static` field references -/

private def ghostModuleName : ModuleName := ModuleName.ofString! "m"

private def ghostDecl (name : String) (init : Option SpecExpr := none) : Signature :=
  .ghostDecl { name, type := some (.ident loc .builtinsInt), init, loc }

/-- The exact term `init=0` lowers to: the boxed prelude call, not a `Hole`. -/
private def intZeroInit : String := "StaticCall(from_int, [LiteralInt(0)])"

/-- Concrete term of a field's initializer, or an error if it has none. -/
private def initShape (what : String) (field : Laurel.Field) : IO String := do
  let some init := field.initializer
    | throw <| IO.userError s!"{what} has no initializer"
  return describeStmt init.val

/-- `ghostFieldName` escapes each component (`_` → `_u`, `.` → `_d`) and joins
    them with `$`, under the front end's `py$` generated namespace. Pinned
    literally (module `m`, ghost `g`) so a change to the encoding fails here
    instead of silently renaming every emitted ghost field. -/
private def ghostFieldNameInM : String := "py$ghost_m$g"

/-- A `functionDecl` skeleton for one ghost-module test procedure; only the
    contract fields vary per test. -/
private def ghostModuleFn (pres : Array SpecExpr := #[]) (admits : Array SpecExpr := #[])
    (mods : Array SpecExpr := #[]) (args : Array Arg := #[]) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name := "f"
    args := { args, kwonly := #[], kwargs := none }
    returnType := .ident loc .builtinsInt
    isOverload := false
    preconditions := pres.map ({ formula := ·, message := #[] })
    postconditions := #[]
    admittedPostconditions := admits
    modifies := mods
    ghosts := #[] }

/-- Lower one ghost `g` plus a procedure whose precondition is `body`. -/
private def lowerModuleWithGhost (body : SpecExpr) (args : Array Arg := #[])
    : Laurel.Program × Array Pipeline.PipelineMessage :=
  let r := signaturesToLaurel "m.py"
    #[ghostDecl "g" (some (.intLit 0 loc)), ghostModuleFn (pres := #[body]) (args := args)]
    ghostModuleName
  (r.program, r.errors)

private def hasKind (errs : Array Pipeline.PipelineMessage) (category : String) : Bool :=
  errs.any fun e => e.message.kind.category == category

/-- Like `lowerModuleWithGhost` but with `@admit` and optional `@modifies`. -/
private def lowerModuleWithGhostAdmit (admits : Array SpecExpr) (args : Array Arg := #[])
    (mods : Array SpecExpr := #[])
    : Laurel.Program × Array Pipeline.PipelineMessage :=
  let r := signaturesToLaurel "m.py"
    #[ghostDecl "g" (some (.intLit 0 loc)),
      ghostModuleFn (admits := admits) (mods := mods) (args := args)]
    ghostModuleName
  (r.program, r.errors)

/-- The emitted procedure `f` of a lowered module. -/
private def procF (pgm : Laurel.Program) : IO Procedure := do
  let some proc := pgm.staticProcedures.find? (·.name.text.endsWith "f")
    | throw <| IO.userError "procedure 'f' not emitted"
  return proc

/-- A model is bodiless: its contract lives entirely in its spec. -/
private def procFIsBodiless (pgm : Laurel.Program) : IO Unit := do
  let proc ← procF pgm
  if proc.body.implementation.isSome then
    throw <| IO.userError "procedure 'f' carries an implementation; models must be bodiless"

/-- `f`'s declared global effects and free postconditions, by summary. -/
private def procFSpec (pgm : Laurel.Program)
    : IO (List String × List String × List (String × String)) := do
  procFIsBodiless pgm
  let proc ← procF pgm
  let posts ← proc.body.postconditions.mapM fun c => do
    unless c.mode == .Assume do
      throw <| IO.userError s!"postcondition '{c.summary.getD "?"}' is not free (assume-only)"
    return (c.summary.getD "<none>", describeStmt c.condition.val)
  return (proc.readsGlobals.map (·.text), proc.writesGlobals.map (·.text), posts)

/-- `OLD` over a ghost is legal exactly when `@modifies` writes it. -/
private def ghostOldAdmitPostconditionTest : IO Unit := do
  let intArg : Arg := { name := "x", type := .ident loc .builtinsInt }
  let gField := ghostFieldNameInM
  let ghostRef := "Var(Local $static." ++ gField ++ ")"
  let lowered (body : SpecExpr) (args : Array Arg) (mods : Array SpecExpr := #[]) := do
    let (pgm, errs) := lowerModuleWithGhostAdmit #[body] args mods
    let spec ← procFSpec pgm
    return (spec, errs)
  let oldG : SpecExpr := .intGe (.var "g" loc) (.old (.var "g" loc) loc) loc
  -- OLD(ghost) with @modifies: declared as written, and the admit is free.
  let ((reads, writes, posts), dErrs) ← lowered oldG #[] #[.var "g" loc]
  unless dErrs.isEmpty do
    throw <| IO.userError s!"modified-ghost OLD reported {dErrs.size} error(s)"
  unless writes == [gField] && reads == [] do
    throw <| IO.userError s!"expected writes=[{gField}] reads=[], got writes={writes} reads={reads}"
  -- Declared type, admit, return type, in that order.
  let expected := [
    ("declared type of module ghost 'g'", "StaticCall(Any..isfrom_int, [" ++ ghostRef ++ "])"),
    ("admitted postcondition of 'm_f'",
      "StaticCall(Any_to_bool, [StaticCall(PGe, [" ++ ghostRef ++ ", Old(" ++ ghostRef ++ ")])])"),
    ("return type of 'm_f'", "StaticCall(Any..isfrom_int, [Var(Local result)])")]
  unless posts == expected do
    throw <| IO.userError s!"postconditions: expected {expected}, got {posts}"
  -- OLD(ghost) without @modifies: rejected, and the admit is not emitted.
  let ((_, uWrites, uPosts), uErrs) ← lowered oldG #[]
  unless hasKind uErrs "ghostOldWithoutModifies" do
    throw <| IO.userError "OLD over an unwritten ghost was not rejected"
  unless uWrites == [] do
    throw <| IO.userError s!"rejected OLD(ghost) still declared writes={uWrites}"
  if uPosts.any (fun (s, _) => s == "admitted postcondition of 'm_f'") then
    throw <| IO.userError "rejected OLD(ghost) still emitted its admitted postcondition"
  -- A parameter shadowing the ghost: reported, and no ghost effect is declared,
  -- because the contract's `g` is the parameter.
  let gParam : Arg := { name := "g", type := .ident loc .builtinsInt }
  let ((sReads, sWrites, sPosts), sErrs) ← lowered oldG #[gParam]
  if hasKind sErrs "ghostOldWithoutModifies" then
    throw <| IO.userError "shadowed-param OLD was misdiagnosed as unwritten-ghost OLD"
  unless hasKind sErrs "ghostShadowedByParam" do
    throw <| IO.userError "expected the shadowing error"
  unless sReads == [] && sWrites == [] do
    throw <| IO.userError
      s!"a shadowed ghost must declare no effect, got reads={sReads} writes={sWrites}"
  -- The admit is over the parameter, so no ghost reference appears in it.
  let expectedShadowed :=
    ["StaticCall(Any_to_bool, [StaticCall(PGe, [Var(Local g), Old(Var(Local g))])])",
     "StaticCall(Any..isfrom_int, [Var(Local result)])"]
  unless sPosts.map Prod.snd == expectedShadowed do
    throw <| IO.userError
      s!"shadowed-param postconditions: expected {expectedShadowed}, got {sPosts.map Prod.snd}"
  -- OLD over a parameter: no ghost involvement at all.
  let ((pReads, pWrites, _), pErrs) ← lowered (.intGe (.var "x" loc) (.old (.var "x" loc) loc) loc) #[intArg]
  unless pErrs.isEmpty do
    throw <| IO.userError s!"OLD(param) reported {pErrs.size} error(s)"
  unless pReads == [] && pWrites == [] do
    throw <| IO.userError s!"OLD(param) declared a ghost effect: reads={pReads} writes={pWrites}"
  -- The ghost appears OUTSIDE the OLD: a read, not a write, and accepted.
  let ((gReads, gWrites, _), gErrs) ← lowered
    (.intGe (.var "g" loc) (.old (.var "x" loc) loc) loc) #[intArg]
  unless gErrs.isEmpty do
    throw <| IO.userError s!"ghost-outside-OLD reported {gErrs.size} error(s)"
  unless gReads == [gField] && gWrites == [] do
    throw <| IO.userError
      s!"ghost outside OLD: expected reads=[{gField}] writes=[], got reads={gReads} writes={gWrites}"

/-- One ghost emits exactly one mutable, initialized static field. -/
private def ghostFieldEmittedTest : IO Unit := do
  let (pgm, errs) := lowerModuleWithGhost (.intGe (.var "g" loc) (.intLit 0 loc) loc)
  unless errs.isEmpty do
    throw <| IO.userError s!"lowering reported {errs.size} error(s)"
  let some field := pgm.staticFields.head?
    | throw <| IO.userError "no static field emitted for the module ghost"
  unless pgm.staticFields.length == 1 do
    throw <| IO.userError s!"expected 1 static field, got {pgm.staticFields.length}"
  unless field.isMutable do
    throw <| IO.userError "module ghost field is not mutable"
  unless field.name.text == ghostFieldNameInM do
    throw <| IO.userError
      s!"expected ghost field name '{ghostFieldNameInM}', got '{field.name.text}'"
  -- `init=0` must survive as the boxed literal, not a `Hole`.
  let shape ← initShape "module ghost field" field
  unless shape == intZeroInit do
    throw <| IO.userError
      s!"expected module ghost initializer {intZeroInit}, got {shape}"

/-- The same contract lowers with the ghost declared and fails without it. -/
private def ghostReferenceResolvesTest : IO Unit := do
  let body : SpecExpr := .intGe (.var "g" loc) (.intLit 0 loc) loc
  let (pgm, errs) := lowerModuleWithGhost body
  unless errs.isEmpty do
    throw <| IO.userError
      s!"contract referencing the module ghost reported {errs.size} error(s)"
  -- The reference resolved to the ghost's static field, not some fallback.
  let proc ← procF pgm
  let pres := proc.preconditions.map fun c => describeStmt c.condition.val
  let expectedPre := "StaticCall(Any_to_bool, [StaticCall(PGe, [Var(Local $static." ++
    ghostFieldNameInM ++ "), StaticCall(from_int, [LiteralInt(0)])])])"
  unless pres == [expectedPre] do
    throw <| IO.userError
      s!"lowered precondition: expected [{expectedPre}], got {pres}"
  let fn : Signature := .functionDecl {
    loc, nameLoc := loc, name := "f"
    args := { args := #[], kwonly := #[], kwargs := none }
    returnType := .ident loc .builtinsInt
    isOverload := false
    preconditions := #[{ formula := body, message := #[] }]
    postconditions := #[]
    admittedPostconditions := #[]
    modifies := #[]
    ghosts := #[] }
  let without := signaturesToLaurel "m.py" #[fn] ghostModuleName
  unless hasKind without.errors "typeError" do
    throw <| IO.userError
      "reference to 'g' with no ghost declared did not report a typeError; the \
       test cannot distinguish ghost resolution from an unrelated fallback"

/-- Omitting `init=` yields a nondeterministic initializer. -/
private def ghostNondeterministicDefaultTest : IO Unit := do
  let r := signaturesToLaurel "m.py" #[ghostDecl "g"] ghostModuleName
  unless r.errors.isEmpty do
    throw <| IO.userError s!"lowering reported {r.errors.size} error(s)"
  let some field := r.program.staticFields.head?
    | throw <| IO.userError "no static field emitted for the module ghost"
  match field.initializer with
  | some init =>
    match init.val with
    | .Hole deterministic _ =>
      if deterministic then
        throw <| IO.userError "ghost default initializer is deterministic"
    | _ => throw <| IO.userError "ghost default initializer is not a hole"
  | none => throw <| IO.userError "ghost default has no initializer"

/-- Numeric tower: an `int` literal initializes a `float` ghost. -/
private def ghostInitNumericWideningTest : IO Unit := do
  let r := signaturesToLaurel "m.py"
    #[.ghostDecl { name := "g", type := some (.ident loc .builtinsFloat),
                   init := some (.intLit 0 loc), loc }]
    ghostModuleName
  unless r.errors.isEmpty do
    throw <| IO.userError
      s!"int initializer for a float-typed ghost was rejected: \
         {r.errors.size} error(s)"
  unless r.program.staticFields.length == 1 do
    throw <| IO.userError
      s!"expected 1 static field for the float ghost, got {r.program.staticFields.length}"
  let some field := r.program.staticFields.head?
    | throw <| IO.userError "no static field emitted for the float-typed ghost"
  unless field.isMutable do
    throw <| IO.userError "float ghost field is not mutable"
  unless field.name.text == ghostFieldNameInM do
    throw <| IO.userError
      s!"expected ghost field name '{ghostFieldNameInM}', got '{field.name.text}'"
  -- Widening accepts the `int` literal without rewriting it: still `from_int(0)`.
  let shape ← initShape "float ghost field" field
  unless shape == intZeroInit do
    throw <| IO.userError
      s!"expected widened ghost initializer {intZeroInit}, got {shape}"

/-- Numeric tower coverage: `bool` widens to `int` and `float`, a union accepts
    a matching scalar atom, and `float` does not narrow to `int`. -/
private def ghostInitWideningCoverageTest : IO Unit := do
  let accepted (label : String) (tp : SpecType) (init : SpecExpr)
      (expectedInit : String) : IO Unit := do
    let r := signaturesToLaurel "m.py"
      #[.ghostDecl { name := "g", type := some tp, init := some init, loc }]
      ghostModuleName
    unless r.errors.isEmpty do
      throw <| IO.userError s!"{label}: rejected with {r.errors.size} error(s)"
    let some field := r.program.staticFields.head?
      | throw <| IO.userError s!"{label}: no static field emitted"
    let shape ← initShape label field
    unless shape == expectedInit do
      throw <| IO.userError s!"{label}: expected initializer {expectedInit}, got {shape}"
  let boolTrueInit := "StaticCall(from_bool, [LiteralBool(true)])"
  accepted "bool init for int ghost" (.ident loc .builtinsInt) (.boolLit true loc)
    boolTrueInit
  accepted "bool init for float ghost" (.ident loc .builtinsFloat) (.boolLit true loc)
    boolTrueInit
  accepted "int init for Optional[int] ghost"
    (SpecType.union loc (.ident loc .builtinsInt) (.noneType loc)) (.intLit 0 loc)
    intZeroInit
  accepted "None init for Optional[int] ghost"
    (SpecType.union loc (.ident loc .builtinsInt) (.noneType loc)) (.noneLit loc)
    "StaticCall(from_None, [])"
  let narrowed := signaturesToLaurel "m.py"
    #[.ghostDecl { name := "g", type := some (.ident loc .builtinsInt),
                   init := some (.floatLit "0.5" loc), loc }]
    ghostModuleName
  unless hasKind narrowed.errors "ghostInitializerError" do
    throw <| IO.userError "float initializer for an int-typed ghost was accepted"
  -- A composite boolean initializer exercises the bool-typed branch.
  accepted "comparison init for bool ghost" (.ident loc .builtinsBool)
    (.intGe (.intLit 0 loc) (.intLit 0 loc) loc)
    "StaticCall(from_bool, [StaticCall(Any_to_bool, [StaticCall(PGe, \
     [StaticCall(from_int, [LiteralInt(0)]), StaticCall(from_int, [LiteralInt(0)])])])])"

/-- An unknown identifier is still an error despite ghost lookup. -/
private def unknownIdentifierStillErrorsTest : IO Unit := do
  let (_, errs) := lowerModuleWithGhost (.intGe (.var "nope" loc) (.intLit 0 loc) loc)
  unless hasKind errs "typeError" do
    throw <| IO.userError
      "unknown identifier did not report a typeError; ghost lookup swallowed it \
       or the failure came from an unrelated branch"

/-- A same-named parameter shadows the ghost; the shadowing is reported. -/
private def ghostShadowedByParamTest : IO Unit := do
  let param : Arg := { name := "g", type := .ident loc .builtinsInt }
  let (_, errs) := lowerModuleWithGhost (.intGe (.var "g" loc) (.intLit 0 loc) loc) #[param]
  unless hasKind errs "ghostShadowedByParam" do
    throw <| IO.userError
      "parameter shadowing a module ghost was not reported"

/-- In the map model a TypedDict `**kwargs` field is not a parameter: a bare
    mention of its name in a contract reads the same-named module ghost, and
    only the kwargs dict name itself shadows. -/
private def ghostKwargsFieldReadsGhostTest : IO Unit := do
  let kwargs := some ("kw",
    SpecType.typedDict loc #["g"] #[SpecType.ident loc .builtinsInt] #[true])
  let fn (pre : SpecExpr) : Signature :=
    .functionDecl {
      loc, nameLoc := loc, name := "f"
      args := { args := #[], kwonly := #[], kwargs }
      returnType := .ident loc .builtinsInt
      isOverload := false
      preconditions := #[{ formula := pre, message := #[] }]
      postconditions := #[]
      admittedPostconditions := #[]
      modifies := #[]
      ghosts := #[] }
  let lower (pre : SpecExpr) :=
    signaturesToLaurel "m.py" #[ghostDecl "g" (some (.intLit 0 loc)), fn pre] ghostModuleName
  let mentioned := lower (.intGe (.var "g" loc) (.intLit 0 loc) loc)
  if hasKind mentioned.errors "ghostShadowedByParam" then
    throw <| IO.userError
      "kwargs field is not a parameter in the map model; it must not shadow the ghost"
  unless mentioned.errors.isEmpty do
    throw <| IO.userError
      s!"ghost read through a kwargs-field name reported {mentioned.errors.size} error(s)"
  let (reads, _, _) ← procFSpec mentioned.program
  unless reads == [ghostFieldNameInM] do
    throw <| IO.userError s!"expected reads=[{ghostFieldNameInM}], got {reads}"
  let unmentioned := lower (.intGe (.intLit 1 loc) (.intLit 0 loc) loc)
  unless unmentioned.errors.isEmpty do
    throw <| IO.userError
      s!"unmentioned kwargs-field collision reported {unmentioned.errors.size} error(s)"
  let (reads, writes, _) ← procFSpec unmentioned.program
  unless reads == [] && writes == [] do
    throw <| IO.userError
      s!"kwargs-shadowed ghost declared effects: reads={reads} writes={writes}"

/-- A method receiver shadows a same-named ghost: reported, and no effect. -/
private def ghostShadowedByReceiverTest : IO Unit := do
  let selfArg : Arg := { name := "self", type := .ident loc .typingAny }
  let method : FunctionDecl := {
    loc, nameLoc := loc, name := "bump"
    args := { args := #[selfArg], kwonly := #[], kwargs := none }
    returnType := .ident loc .builtinsInt
    isOverload := false
    preconditions := #[]
    postconditions := #[]
    admittedPostconditions := #[.intGe (.var "self" loc) (.old (.var "self" loc) loc) loc]
    modifies := #[.var "self" loc]
    ghosts := #[] }
  let r := signaturesToLaurel "m.py"
    #[.ghostDecl { name := "self", type := some (.ident loc .builtinsInt),
                   init := some (.intLit 0 loc), loc },
      .classDef { loc, name := "C", methods := #[method] }]
    ghostModuleName
  unless hasKind r.errors "ghostShadowedByParam" do
    throw <| IO.userError "ghost shadowed by the method receiver was not reported"
  let some proc := r.program.staticProcedures.find? (·.name.text.endsWith "bump")
    | throw <| IO.userError "method procedure not emitted"
  unless proc.readsGlobals.isEmpty && proc.writesGlobals.isEmpty do
    throw <| IO.userError "receiver-shadowed ghost declared a global effect"

/-- A parameter colliding with a ghost the contract never mentions is accepted. -/
private def ghostShadowedByUnusedParamTest : IO Unit := do
  let param : Arg := { name := "g", type := .ident loc .builtinsInt }
  let constantContract := .intGe (.intLit 1 loc) (.intLit 0 loc) loc
  let (pgm, errs) := lowerModuleWithGhost constantContract #[param]
  let (reads, writes, _) ← procFSpec pgm
  unless errs.isEmpty do
    throw <| IO.userError
      s!"unused shadowing parameter reported {errs.size} error(s)"
  unless reads == [] && writes == [] do
    throw <| IO.userError
      s!"unused shadowing parameter declared effects: reads={reads} writes={writes}"

/-- Declared effects and type postconditions follow declaration order. -/
private def ghostEffectsFollowDeclarationOrderTest : IO Unit := do
  let names := #["zulu", "alpha", "mike"]
  let admit := .and
    (.intGe (.var "zulu" loc) (.var "alpha" loc) loc)
    (.intGe (.var "alpha" loc) (.var "mike" loc) loc) loc
  -- Reads only: every ghost is mentioned, none is written.
  let r := signaturesToLaurel "m.py"
    ((names.map ghostDecl).push (ghostModuleFn (admits := #[admit])))
    ghostModuleName
  unless r.errors.isEmpty do
    throw <| IO.userError s!"ordered ghost lowering reported {r.errors.size} error(s)"
  let (reads, writes, posts) ← procFSpec r.program
  let expectedReads := names.toList.map (ghostFieldName "m" ·)
  unless reads == expectedReads && writes == [] do
    throw <| IO.userError
      s!"expected reads={expectedReads} writes=[], got reads={reads} writes={writes}"
  let ghostTypeSummaries (posts : List (String × String)) : List String :=
    posts.map Prod.fst |>.filter (·.startsWith "declared type of module ghost")
  let summaryOf (names : List String) : List String :=
    names.map (s!"declared type of module ghost '{·}'")
  unless ghostTypeSummaries posts == summaryOf names.toList do
    throw <| IO.userError
      s!"ghost type postcondition order: expected {summaryOf names.toList}, \
         got {ghostTypeSummaries posts}"
  -- Decorator order reversed; declaration order must win.
  let rw := signaturesToLaurel "m.py"
    ((names.map ghostDecl).push
      (ghostModuleFn (admits := #[admit]) (mods := #[.var "mike" loc, .var "zulu" loc])))
    ghostModuleName
  unless rw.errors.isEmpty do
    throw <| IO.userError s!"mixed-effect lowering reported {rw.errors.size} error(s)"
  let (rwReads, rwWrites, rwPosts) ← procFSpec rw.program
  unless rwWrites == [ghostFieldName "m" "zulu", ghostFieldName "m" "mike"] do
    throw <| IO.userError s!"writes not in declaration order: {rwWrites}"
  unless rwReads == [ghostFieldName "m" "alpha"] do
    throw <| IO.userError s!"expected reads=[alpha], got {rwReads}"
  unless ghostTypeSummaries rwPosts == summaryOf ["zulu", "alpha", "mike"] do
    throw <| IO.userError
      s!"mixed type postcondition order: expected [zulu, alpha, mike], \
         got {ghostTypeSummaries rwPosts}"
  -- A middle ghost written: declaration order must still win.
  let mid := signaturesToLaurel "m.py"
    ((names.map ghostDecl).push
      (ghostModuleFn (admits := #[admit]) (mods := #[.var "alpha" loc])))
    ghostModuleName
  unless mid.errors.isEmpty do
    throw <| IO.userError s!"middle-write lowering reported {mid.errors.size} error(s)"
  let (midReads, midWrites, midPosts) ← procFSpec mid.program
  unless midWrites == [ghostFieldName "m" "alpha"] do
    throw <| IO.userError s!"expected writes=[alpha], got {midWrites}"
  unless midReads == [ghostFieldName "m" "zulu", ghostFieldName "m" "mike"] do
    throw <| IO.userError s!"expected reads=[zulu, mike], got {midReads}"
  unless ghostTypeSummaries midPosts == summaryOf names.toList do
    throw <| IO.userError
      s!"middle-write type postcondition order: expected {names.toList}, \
         got {ghostTypeSummaries midPosts}"

/-- The first DECLARED unwritten ghost is named, not the first mentioned. -/
private def ghostOldErrorNamesFirstDeclarationTest : IO Unit := do
  let relative (name : String) : SpecExpr :=
    .intGe (.var name loc) (.old (.var name loc) loc) loc
  let admit := .and (relative "alpha") (relative "zulu") loc
  let r := signaturesToLaurel "m.py"
    #[ghostDecl "zulu", ghostDecl "alpha", ghostModuleFn (admits := #[admit])]
    ghostModuleName
  let some err := r.errors.find? (·.message.kind.category == "ghostOldWithoutModifies")
    | throw <| IO.userError "missing OLD over unwritten ghost error"
  unless err.message.message.contains "module ghost 'zulu'" do
    throw <| IO.userError s!"nondeterministic OLD offender: {err.message.message}"

/-- Ghost field names are module-qualified: no cross-module collisions. -/
private def ghostFieldNamesAreModuleQualifiedTest : IO Unit := do
  let nameIn (m : String) : Option String :=
    let r := signaturesToLaurel "m.py" #[ghostDecl "g" (some (.intLit 0 loc))]
      (ModuleName.ofString! m)
    r.program.staticFields.head?.map (·.name.text)
  let some a := nameIn "modA" | throw <| IO.userError "modA emitted no ghost field"
  let some b := nameIn "modB" | throw <| IO.userError "modB emitted no ghost field"
  -- Pin the encoding itself, not just distinctness.
  unless a == "py$ghost_modA$g" do
    throw <| IO.userError s!"unexpected ghost field name for modA: '{a}'"
  unless b == "py$ghost_modB$g" do
    throw <| IO.userError s!"unexpected ghost field name for modB: '{b}'"
  unless a != b do
    throw <| IO.userError s!"ghost fields from different modules collide: '{a}'"

/-! Boundary: empty components must not collide through separator shifting. -/
#guard ghostFieldName "" "x" != ghostFieldName "x" ""
#guard ghostFieldName "n" "" != ghostFieldName "" "n"
#guard ghostFieldName "a" "b_c" != ghostFieldName "a_b" "c"
#guard encodeGeneratedComponent "" == ""
#guard encodeGeneratedComponent "a" == "a"
-- A dotted module and an underscored one must not converge.
#guard encodeGeneratedComponent "a.b" != encodeGeneratedComponent "a_b"
-- The separator cannot be forged from inside a component.
#guard ghostFieldName "a" "under" != ghostFieldName "a_nder" ""
-- Not even by a literal `$` in a (non-Python) component.
#guard encodeGeneratedComponent "a$b" == "a_sb"
#guard ghostFieldName "m$a" "b" != ghostFieldName "m" "a$b"
#guard ghostFieldName "servicelib.GhostOld" "allocated"
       == "py$ghost_servicelib_dGhostOld$allocated"

/-! Property: the encoding is injective (random search, not a proof). -/
#guard_msgs in
#eval Plausible.Testable.check (cfg := { quiet := true }) <|
  ∀ (a b : String), a ≠ b → encodeGeneratedComponent a ≠ encodeGeneratedComponent b

#guard_msgs in
#eval Plausible.Testable.check (cfg := { quiet := true }) <|
  ∀ (m₁ n₁ m₂ n₂ : String), (m₁, n₁) ≠ (m₂, n₂) → ghostFieldName m₁ n₁ ≠ ghostFieldName m₂ n₂

/-- A type-mismatched initializer (`None` for an int ghost) is rejected. -/
private def ghostInitializerTypeMismatchTest : IO Unit := do
  let r := signaturesToLaurel "m.py"
    #[.ghostDecl { name := "g", type := some (.ident loc .builtinsInt),
                   init := some (.noneLit loc), loc }]
    ghostModuleName
  unless hasKind r.errors "ghostInitializerError" do
    throw <| IO.userError
      "None initializer for an int-typed module ghost was accepted"
  -- A compound initializer has no statically guaranteed runtime type.
  let compound := signaturesToLaurel "m.py"
    #[.ghostDecl { name := "g", type := some (.ident loc .builtinsInt),
                   init := some (.add (.intLit 0 loc) (.intLit 1 loc) loc), loc }]
    ghostModuleName
  unless hasKind compound.errors "ghostInitializerError" do
    throw <| IO.userError "compound ghost initializer was accepted"
  let some field := r.program.staticFields.head?
    | throw <| IO.userError
        "rejected initializer left the module ghost without a backing field"
  -- The fallback initializer is a nondeterministic hole, not a lowered value.
  match field.initializer with
  | some init =>
    match init.val with
    | .Hole deterministic _ =>
      if deterministic then
        throw <| IO.userError "fallback initializer after rejection is deterministic"
    | _ => throw <| IO.userError "fallback initializer after type mismatch is not a hole"
  | none => throw <| IO.userError "fallback field has no initializer"

/-- Ghost fields must survive `filterPrelude` on the user side. -/
private def ghostSurvivesFilterPreludeTest : IO Unit := do
  let r := signaturesToLaurel "m.py" #[ghostDecl "g" (some (.intLit 0 loc))] ghostModuleName
  unless r.program.staticFields.length == 1 do
    throw <| IO.userError "expected one ghost field to route through the pipeline"
  let ghostFields := r.program.staticFields
  let preludeForFilter := { r.program with staticFields := [] }
  let user : Strata.Laurel.Program :=
    { staticProcedures := [], staticFields := ghostFields, types := [], constants := [] }
  match Strata.Laurel.filterPrelude preludeForFilter user with
  | .error e =>
    throw <| IO.userError s!"filterPrelude rejected a ghost-bearing program: {e}"
  | .ok filtered =>
    -- Assert on the combined program through the production combinator.
    let combined := combinePySpecLaurel filtered user
    unless combined.staticFields.length == 1 do
      throw <| IO.userError "ghost field lost while filtering the prelude"
    unless combined.staticFields.head?.map (·.name.text) == ghostFields.head?.map (·.name.text) do
      throw <| IO.userError "combined program carries a different field than the ghost"
    let some combinedField := combined.staticFields.head?
      | throw <| IO.userError "combined program lost the ghost field"
    let combinedInit ← initShape "combined ghost field" combinedField
    unless combinedInit == intZeroInit do
      throw <| IO.userError
        s!"ghost initializer lost during filterPrelude; got {combinedInit}"

/-- Duplicate `@modifies` clauses declare a single `writes`. -/
private def ghostDuplicateModifiesTest : IO Unit := do
  let gField := ghostFieldNameInM
  let effects (mods : Array SpecExpr) : IO (List String × List String) := do
    let (pgm, errs) := lowerModuleWithGhostAdmit
      #[.intGe (.var "g" loc) (.intLit 0 loc) loc] #[] (mods := mods)
    unless errs.isEmpty do
      throw <| IO.userError s!"lowering reported {errs.size} error(s)"
    let (reads, writes, _) ← procFSpec pgm
    return (reads, writes)
  let (baseReads, baseWrites) ← effects #[]
  unless baseReads == [gField] && baseWrites == [] do
    throw <| IO.userError
      s!"unmodified ghost: expected reads=[{gField}] writes=[], got {baseReads} / {baseWrites}"
  let (onceReads, onceWrites) ← effects #[.var "g" loc]
  unless onceReads == [] && onceWrites == [gField] do
    throw <| IO.userError
      s!"single @modifies: expected reads=[] writes=[{gField}], got {onceReads} / {onceWrites}"
  let (twiceReads, twiceWrites) ← effects #[.var "g" loc, .var "g" loc]
  unless twiceReads == [] && twiceWrites == [gField] do
    throw <| IO.userError
      s!"duplicate @modifies: expected one writes entry, got {twiceReads} / {twiceWrites}"

private def ghostTests : IO Unit := do
  ghostSurvivesFilterPreludeTest
  ghostFieldEmittedTest
  ghostReferenceResolvesTest
  ghostNondeterministicDefaultTest
  ghostInitNumericWideningTest
  ghostInitWideningCoverageTest
  unknownIdentifierStillErrorsTest
  ghostShadowedByParamTest
  ghostShadowedByReceiverTest
  ghostShadowedByUnusedParamTest
  ghostKwargsFieldReadsGhostTest
  ghostEffectsFollowDeclarationOrderTest
  ghostOldErrorNamesFirstDeclarationTest
  ghostFieldNamesAreModuleQualifiedTest
  ghostInitializerTypeMismatchTest
  ghostDuplicateModifiesTest
  ghostOldAdmitPostconditionTest

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
  ghostTests

#guard_msgs in
#eval allTests

end StrataPython.Specs.ToLaurel.SpecExprLoweringTest
end
