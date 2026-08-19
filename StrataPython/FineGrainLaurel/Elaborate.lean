/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.HeapParameterizationConstants
public import Strata.Languages.Laurel.CoreDefinitionsForLaurel

/-!
# Pass 3: Elaboration

"Pass 3" is the third stage of the v2 Python->Core pipeline: Pass 1 = Resolution
(`Resolution.lean`, name/scope resolution), Pass 2 = Translation
(`Translation.lean`, Python AST -> Laurel), Pass 3 = Elaboration (this file). The
stage is pipeline-ordinal, not Laurel-specific — a non-Python Laurel front end
would reuse this same pass.

Elaboration transforms Laurel programs (impure CBV, effects implicit) into
Laurel programs where effects are explicit via calling conventions. The
theoretical foundation is **Fine-Grain Call-By-Value** (FGCBV) with graded
effects and bidirectional typing.

## Why FGCBV?

In plain CBV, every expression can have effects. You cannot tell by looking
at `f(x, g(y))` whether `g(y)` allocates, throws, or is pure. This matters
for verification because the calling convention depends on it: a pure call
returns a value directly; an effectful call returns through output parameters
(heap, error status).

FGCBV separates **values** (pure, duplicable) from **producers** (effectful,
sequenced). A producer must be explicitly sequenced — this makes the
elaborator syntax-directed. At every point, the structure of the term tells
you whether you are looking at a value or a producer.

## Bidirectional Typing

The elaborator has three mutually recursive functions:

- `synthValue`: value synthesis — literals, variables, pure calls, field access
- `checkValue`: value checking — synthesize then coerce (the ONE place subsumption lives)
- `checkProducer`: producer checking — if, while, assign, block, exit, assert, etc.

Values synthesize their types bottom-up. Producers are checked against an
ambient grade and output type top-down. The mode discipline guarantees
deterministic choices at every point.

## Graded Effects

Each producer carries a grade from `{pure, proc, err, heap, heapErr}`. The
grade determines the calling convention (extra heap parameters, error outputs).
Grade inference proceeds by coinduction over the call graph: try each grade
from `pure` upward, the first that succeeds is the procedure's grade.

## Two Passes

1. **Grade inference** (coinductive fixpoint): for each user procedure, find
   the minimal grade at which elaboration succeeds.
2. **Term production**: elaborate each procedure at its inferred grade,
   project the FGCBV term back to Laurel statements.

## Direction: an extrinsic effect system for Laurel

Today this elaborator is driven by the Python frontend and threads Python's
exceptions (the `err` grade / `maybe_except` outputs). The intended direction
is to generalize it into an **extrinsic effect system and checker for Laurel
itself** — one that also covers *native* Laurel exceptions, not only the
Python-sourced ones. "Extrinsic" meaning the grade discipline is inferred and
checked over ordinary Laurel rather than requiring effect annotations in the
surface syntax.

This is the same design space as the `EliminateExceptions` / `Result<Val, Err>`
lowering. Both give exceptions an explicit channel; the graded-effect approach
here additionally classifies which procedures can throw (and which need heap
parameters) so the calling convention is derived rather than uniform. Once this
covers native Laurel exceptions, a new frontend should not have to choose between
two mechanisms — the effect system becomes the single Laurel-level account of
effects, and per-frontend exception threading (like Python's) is just its first
client.

The Python front end (StrataPythonFrontEnd, via `PySpecPipeline`) is the only
consumer of this pass — it is the sole caller of `fullElaborate`, `Grade`, and
`gradeFromSignature`. It therefore lives in the StrataPythonFrontEnd package,
beside its only caller and where it can be tested end-to-end against Python
inputs. If the pass grows to cover native Laurel exceptions and gains consumers
beyond Python, it can move into the Strata package then, with its own tests.

## Surface syntax the FGCBV IR is intended to have

`FGLValue`/`FGLProducer` below are the hand-written IR the elaborator operates on.
For reference, the surface syntax that IR corresponds to — a fine-grain
call-by-value grammar with explicit polarity, splitting terms into a `Value`
category (inert, duplicable) and a `Producer` category (effectful, sequenced):

- **Types**: `int`, `bool`, `real`, `float64`, `string`, `Core <name>`,
  `Map <k> <v>`, and composite names.
- **Values** (no effects): literals (int/bool/decimal/string); variables;
  arithmetic `+ - * / %`; comparisons `== != < <= > >=`; logical `& | !`;
  negation; field access `obj#field`; parentheses; and the `Any`-injection
  coercions `from_int`/`from_str`/`from_bool`/`from_float`/`from_Composite`/
  `from_ListAny`/`from_DictStrAny`/`from_None`.
- **Producers** (effectful, must be sequenced): `return v`; pure call
  `f(args)`; `let x: T = <producer|value> in body`; assignment `t := v`;
  `var x: T := v`; `if c then .. else ..`; `assert`/`assume`; `while (c)
  <invariants> body`; heap allocation `let r: T = new C in body`;
  error-handling call `let [r: T, e: E] = f(args) in body`; sequencing `;`;
  block `{ .. }`; `exit <label>` and labeled `block <label> { .. }` for
  break/continue.
- **Declarations**: `procedure` (params, `returns(..)`, `requires`/`ensures`
  with optional `summary`, `modifies`, optional body or `external`) and
  `composite` (optional `extends`, mutable/immutable fields, procedures).

This is documentation only: the elaborator constructs `FGLValue`/`FGLProducer`
directly and does not parse or serialize this grammar.
-/

namespace Strata.FineGrainLaurel
open Strata.Laurel
open StrataDDM  -- for `Decimal` (used by FGLValue.litDecimal), as LaurelAST does
public section

/-! ## Internal Types

Elaboration builds its own environment from `Laurel.Program` declarations.
Ideally call sites would carry callee signatures directly (no lookup needed),
but the Laurel AST uses string-named `StaticCall` nodes. -/

/-- Elaboration's internal function signature (built from Laurel.Procedure declarations). -/
structure FuncSig where
  /-- Procedure name (string, matching StaticCall callee names). -/
  name : String
  /-- Input parameters as (name, type) pairs. -/
  params : List (String × HighType)
  /-- Return type (first non-error output). -/
  returnType : HighType

instance : Inhabited FuncSig where
  default := { name := "", params := [], returnType := .UserDefined { text := "Any" } }

/-- What a name resolves to in Elaboration's type environment. -/
inductive NameInfo where
  /-- A callable procedure with its signature. -/
  | function (sig : FuncSig)
  /-- A variable binding with its type. -/
  | variable (ty : HighType)

instance : Inhabited NameInfo where
  default := .variable (.UserDefined { text := "Any" })

/-- The typing environment: maps names to their info and class names to field lists. -/
structure ElabTypeEnv where
  /-- All known names (procedures, variables, datatype constructors). -/
  names : Std.HashMap String NameInfo := {}
  /-- Class fields: class name -> list of (field name, field type). -/
  classFields : Std.HashMap String (List (String × HighType)) := {}
  deriving Inhabited

/-- Builds the type environment from a Laurel program's declarations. Scans all
    procedures (user + runtime) for signatures, all types for class fields. -/
def buildElabEnvFromProgram (program : Laurel.Program) (runtime : Laurel.Program := default) : ElabTypeEnv := Id.run do
  let mut names : Std.HashMap String NameInfo := {}
  let mut classFields : Std.HashMap String (List (String × HighType)) := {}
  for proc in program.staticProcedures ++ runtime.staticProcedures do
    let params := proc.inputs.map fun p => (p.name.text, p.type.val)
    let retTy := match proc.outputs.head? with
      | some o => o.type.val | none => HighType.TVoid
    names := names.insert proc.name.text (.function { name := proc.name.text, params, returnType := retTy })
  for td in program.types ++ runtime.types do
    match td with
    | .Composite ct =>
      let fields := ct.fields.map fun f => (f.name.text, f.type.val)
      classFields := classFields.insert ct.name.text fields
      -- Register the class as a callable constructor: CircularBuffer(args) → CircularBuffer
      let retTy := HighType.UserDefined { text := ct.name.text, uniqueId := none }
      names := names.insert ct.name.text (.function { name := ct.name.text, params := [], returnType := retTy })
    | .Datatype dt =>
      for ctor in dt.constructors do
        let ctorParams := ctor.args.map fun p => (p.name.text, p.type.val)
        let retTy := HighType.UserDefined { text := dt.name.text, uniqueId := none }
        names := names.insert ctor.name.text (.function { name := ctor.name.text, params := ctorParams, returnType := retTy })
    | .Constrained _ => pure ()
    | .Alias _ => pure ()
    | .Opaque _ => pure ()
  { names, classFields }

def mkLaurel (md : Option FileRange) (e : StmtExpr) : StmtExprMd :=
  { val := e, source := md.getD .unknown }
def mkHighTypeMd (md : Option FileRange) (ty : HighType) : HighTypeMd :=
  { val := ty, source := md.getD .unknown }

/-! ## The Grade Monoid

Grades classify which effects a producer performs. The monoid structure
ensures compositionality: sequencing two producers joins their grades.
The left residual `d \ e` ("what grade remains for the continuation after
a call at grade `d` within ambient grade `e`") drives grade inference —
if `d \ e` is undefined (d > e), elaboration fails and the grade is
pushed upward. -/

/-- The effect grade lattice: pure < proc < {err, heap} < heapErr. -/
inductive Grade where
  /-- No effects. Value-level `staticCall`, no extra params. -/
  | pure
  /-- Effectful but no error or heap. Outputs: `[result]`. -/
  | proc
  /-- May throw. Outputs: `[result, maybe_except]`. -/
  | err
  /-- Reads/writes heap. Inputs: `[$heap]`. Outputs: `[$heap, result]`. -/
  | heap
  /-- Heap + error. Inputs: `[$heap]`. Outputs: `[$heap, result, maybe_except]`. -/
  | heapErr
  deriving Inhabited, BEq, Repr

/-- Join (least upper bound) of two grades. Sequencing two producers joins their grades. -/
def Grade.join : Grade → Grade → Grade
  | .pure, e => e | e, .pure => e
  | .proc, .proc => .proc
  | .proc, .err => .err | .err, .proc => .err
  | .proc, .heap => .heap | .heap, .proc => .heap
  | .proc, .heapErr => .heapErr | .heapErr, .proc => .heapErr
  | .err, .err => .err
  | .err, .heap => .heapErr | .heap, .err => .heapErr
  | .err, .heapErr => .heapErr | .heapErr, .err => .heapErr
  | .heap, .heap => .heap
  | .heap, .heapErr => .heapErr | .heapErr, .heap => .heapErr
  | .heapErr, .heapErr => .heapErr

/-- Left residual: `d\e` = grade for the continuation after a call at grade `d`
    within ambient grade `e`. Returns `none` if `d > e` (elaboration fails).

    Satisfies the residuation law for an idempotent semilattice:
    `d ⊔ x ≤ e` iff `x ≤ d\e`. Since `⊔` is idempotent (join),
    the largest `x` with `d ⊔ x ≤ e` is `e` itself (when `d ≤ e`).
    So `d\e = e` whenever `d ≤ e`, and undefined otherwise.
```
d\e = e    if d ≤ e
d\e = ⊥    otherwise
```
-/
def Grade.leftResidual : Grade → Grade → Option Grade
  | .pure, e => some e
  | .proc, e => if e == .pure then none else some e
  | .err, e => match e with | .err | .heapErr => some e | _ => none
  | .heap, e => match e with | .heap | .heapErr => some e | _ => none
  | .heapErr, .heapErr => some .heapErr
  | _, _ => none

/-! ## Type Erasure

Elaboration operates on `LowType` — the erased version of `HighType`.
User-defined types erase to `Composite` (they live on the heap). The
subtyping/coercion system operates on `LowType` values. -/

/-- The erased type system. User-defined types become `Composite` (heap-allocated).
    Subsumption and coercion operate on `LowType` values. -/
inductive LowType where
  /-- Machine integer. -/
  | TInt
  /-- Boolean. -/
  | TBool
  /-- String. -/
  | TString
  /-- 64-bit float. -/
  | TFloat64
  /-- Unit/void. -/
  | TVoid
  /-- Named core type (Any, Error, Heap, Composite, ListAny, DictStrAny, etc.). -/
  | TCore (name : String)
  /-- A user-defined class, name preserved. The class name is kept distinct (rather than
      collapsed to `Composite`) so a `var self : C` declaration round-trips back to
      `.UserDefined "C"`; the Laurel resolver resolves `self.field` via the receiver's
      static `.UserDefined` type, which collapsing to `Composite` would lose. -/
  | TUser (name : String)
  deriving Inhabited, Repr, BEq

/-- Type erasure: HighType -> LowType. Primitives map directly, user-defined classes
    keep their name (`.TUser`), unknown/complex types become Any. -/
def eraseType : HighType → LowType
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid
  | .UserDefined id => match id.text with
    | "Any" => .TCore "Any" | "Error" => .TCore "Error"
    | "ListAny" => .TCore "ListAny" | "DictStrAny" => .TCore "DictStrAny"
    | "OptionInt" => .TCore "OptionInt"
    | "Box" => .TCore "Box" | "Field" => .TCore "Field" | "TypeTag" => .TCore "TypeTag"
    | _ => .TUser id.text
  | .TReal => .TCore "real"
  | .TSet _ | .TMap _ _ | .Applied _ _ | .Intersection _ | .Unknown
  | .TVar _ | .TBv _ | .MultiValuedExpr _ => .TCore "Any"

/-- Inverse of erasure (partial): lifts a LowType back to HighType for env extension. -/
def liftType : LowType → HighType
  | .TUser name => .UserDefined { text := name, uniqueId := none }
  | .TInt => .TInt | .TBool => .TBool | .TString => .TString
  | .TFloat64 => .TFloat64 | .TVoid => .TVoid | .TCore n => .UserDefined { text := n, uniqueId := none }

/-! ## FGL Terms

The intermediate representation between Laurel input and Laurel output.
Values are pure (can appear in any context). Producers are effectful
(must be sequenced). Every constructor carries source metadata so
provenance is preserved through elaboration. -/

abbrev Md := Option FileRange

/-- A pure value in the FGCBV intermediate term. Can appear in any context.
    Every constructor carries source metadata for provenance. -/
inductive FGLValue where
  /-- Integer literal. -/
  | litInt (md : Md) (n : Int)
  /-- Boolean literal. -/
  | litBool (md : Md) (b : Bool)
  /-- String literal. -/
  | litString (md : Md) (s : String)
  /-- Decimal/real literal (Python float). -/
  | litDecimal (md : Md) (d : Decimal)
  /-- Variable reference. -/
  | var (md : Md) (name : String)
  /-- Coercion: int → Any. -/
  | fromInt (md : Md) (inner : FGLValue)
  /-- Coercion: string → Any. -/
  | fromStr (md : Md) (inner : FGLValue)
  /-- Coercion: bool → Any. -/
  | fromBool (md : Md) (inner : FGLValue)
  /-- Coercion: float → Any. -/
  | fromFloat (md : Md) (inner : FGLValue)
  /-- Coercion: Composite → Any. -/
  | fromComposite (md : Md) (inner : FGLValue)
  /-- Coercion: ListAny → Any. -/
  | fromListAny (md : Md) (inner : FGLValue)
  /-- Coercion: DictStrAny → Any. -/
  | fromDictStrAny (md : Md) (inner : FGLValue)
  /-- Coercion: None → Any. -/
  | fromNone (md : Md)
  /-- Field access (pre-heap-resolution). -/
  | fieldAccess (md : Md) (obj : FGLValue) (field : String)
  /-- Pure function call. -/
  | staticCall (md : Md) (name : String) (args : List FGLValue)
  /-- Object creation (pre-heap-resolution). heapParameterizationPass allocates. -/
  | new (md : Md) (className : String)
  deriving Inhabited

def FGLValue.getMd : FGLValue → Md
  | .litInt md _ | .litBool md _ | .litString md _ | .litDecimal md _ | .var md _
  | .fromInt md _ | .fromStr md _ | .fromBool md _ | .fromFloat md _
  | .fromComposite md _ | .fromListAny md _ | .fromDictStrAny md _ | .fromNone md
  | .fieldAccess md _ _ | .staticCall md _ _ | .new md _ => md

/-- An effectful producer in the FGCBV intermediate term. Must be sequenced.
    Each form carries a continuation (`body`/`after`) — the CPS structure
    makes projection to Laurel statements trivial. -/
inductive FGLProducer where
  /-- Return a value (terminal — no continuation). -/
  | produce (md : Md) (v : FGLValue)
  /-- Assign to an existing variable, then continue. RHS is a producer whose
      resolved value is assigned to target. -/
  | assign (md : Md) (target : FGLValue) (val : FGLProducer) (body : FGLProducer)
  /-- Declare a local variable, then continue in extended scope. Init is a
      producer whose resolved value initializes the variable. -/
  | varDecl (md : Md) (name : String) (ty : LowType) (init : FGLProducer) (body : FGLProducer)
  /-- Conditional: check condition, branch, then continue after. -/
  | ifThenElse (md : Md) (cond : FGLValue) (thn : FGLProducer) (els : FGLProducer) (after : FGLProducer)
  /-- Loop: check condition, iterate body, then continue after. -/
  | whileLoop (md : Md) (cond : FGLValue) (body : FGLProducer) (after : FGLProducer)
  /-- Assert condition holds, then continue. Optional summary names the obligation. -/
  | assert (md : Md) (cond : FGLValue) (body : FGLProducer) (summary : Option String := none)
  /-- Assume condition holds, then continue. -/
  | assume (md : Md) (cond : FGLValue) (body : FGLProducer)
  /-- Effectful call: bind outputs, then continue in extended scope. -/
  | procedureCall (md : Md) (callee : String) (args : List FGLValue)
      (outputs : List (String × LowType)) (body : FGLProducer)
  /-- Exit to enclosing labeled block (non-returning). -/
  | exit (md : Md) (label : String)
  /-- Labeled block: body may exit to label, then continue after. -/
  | labeledBlock (md : Md) (label : String) (body : FGLProducer) (after : FGLProducer)
  /-- Empty continuation (end of block). -/
  | skip
  deriving Inhabited

-- ═══════════════════════════════════════════════════════════════════════════════
-- Monad
-- ═══════════════════════════════════════════════════════════════════════════════

/-- Reader environment for elaboration. Carries the type environment, program,
    runtime, inferred grades, and current procedure's input list (for hole args). -/
structure ElabEnv where
  /-- The typing context (names + class fields). -/
  typeEnv : ElabTypeEnv
  /-- The user program being elaborated. -/
  program : Laurel.Program
  /-- The runtime prelude (builtins, data structure operations). -/
  runtime : Laurel.Program := default
  /-- Inferred grades for all procedures. -/
  procGrades : Std.HashMap String Grade := {}
  /-- Current procedure's input params (used as hole arguments). -/
  procInputs : List (String × HighType) := []

/-- Mutable state for elaboration: fresh name counter and hole collector. -/
structure ElabState where
  /-- Counter for generating fresh variable names. -/
  freshCounter : Nat := 0
  /-- Hole functions used (emitted as opaque procedure declarations in output). -/
  usedHoles : List (String × Bool × HighType) := []

abbrev ElabM := ReaderT ElabEnv (StateT ElabState (Except String))

private def freshVar (pfx : String := "tmp") : ElabM String := do
  let s ← get; set { s with freshCounter := s.freshCounter + 1 }; pure s!"{pfx}${s.freshCounter}"


/-- A procedure is functional (pure, callable as a `StaticCall`) when its body is a
    transparent expression or an uninterpreted opaque stub (opaque with no imperative
    implementation). An opaque body WITH an implementation is a real procedure, not
    functional. -/
def procIsFunctional (proc : Laurel.Procedure) : Bool :=
  match proc.body with
  | .Transparent _ => true
  | .Opaque _ none _ => true
  | _ => false

/-- Reads a runtime procedure's grade structurally from its signature: does it
    have a Heap input? An Error output? The combination determines the grade.
    User procedure grades are inferred by coinduction, not read from signature.

    `mayThrow` names runtime procedures that encode exceptions inside an `Any`
    return rather than a declared `Error` output — they carry no `Error`-typed
    output, so `hasError` alone would grade them `.pure`/`.proc` and emit no
    exception obligation at their call sites. The set is supplied by the frontend
    (Python passes `AnyMaybeExceptionList`), keeping this pass frontend-agnostic. -/
def gradeFromSignature (mayThrow : Std.HashSet String) (proc : Laurel.Procedure) : Grade :=
  -- Exceptions-only principle: heap is owned by heapParameterizationPass, so
  -- a runtime proc that takes a Heap input is just `.proc` (or `.err` if it can also throw).
  let hasError := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
  if hasError || mayThrow.contains proc.name.text then .err
  else if procIsFunctional proc then .pure else .proc

-- ═══════════════════════════════════════════════════════════════════════════════
-- Env helpers
-- ═══════════════════════════════════════════════════════════════════════════════

def lookupEnv (name : String) : ElabM NameInfo := do
  match (← read).typeEnv.names[name]? with | some info => pure info | none => throw s!"lookupEnv: {name} not in env"
def extendEnv (name : String) (ty : HighType) (action : ElabM α) : ElabM α :=
  withReader (fun env => { env with typeEnv := { env.typeEnv with names := env.typeEnv.names.insert name (.variable ty) } }) action
def lookupFuncSig (name : String) : ElabM FuncSig := do
  match (← read).typeEnv.names[name]? with | some (.function sig) => pure sig | _ => throw s!"lookupFuncSig: {name} not a function"

/-! ## HOAS Smart Constructors

These construct effectful call nodes using higher-order abstract syntax:
the continuation is a Lean function from fresh output variables to the
body producer. This ensures output variables are always correctly scoped
(extended in the environment before the body is elaborated). -/

def mkEffectfulCall (md : Md) (callee : String) (args : List FGLValue)
    (outputSpecs : List (String × HighType))
    (body : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  let mut names : List String := []
  let mut lowOutputs : List (String × LowType) := []
  for (pfx, ty) in outputSpecs do
    let n ← freshVar pfx
    names := names ++ [n]
    lowOutputs := lowOutputs ++ [(n, eraseType ty)]
  let vars := names.map (FGLValue.var md)
  let cont ← names.zip (outputSpecs.map (·.2)) |>.foldr
    (fun (n, ty) acc => extendEnv n ty acc) (body vars)
  pure (.procedureCall md callee args lowOutputs cont)

/-- Subgrading witness: `d ≤ e ↦ (pre, outs)`. Constructs a `procedureCall`
    with the correct calling convention based on grade.
```
d ≤ e ↦ (args_prepended, outputs_declared, resultIdx)

pure:     ([], [], —)                                  — value-level, no procedureCall
proc:     ([], [result:B], 0)
err:      ([], [result:B, except:Error], 0)
heap:     ([heap_var], [heap:Heap, result:B], 1)
heapErr:  ([heap_var], [heap:Heap, result:B, except:Error], 1)
```
-/
def mkGradedCall (md : Md) (callee : String) (args : List FGLValue)
    (declaredOutputs : List (String × HighType))
    (body : FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  mkEffectfulCall md callee args declaredOutputs fun outs => do
    let resultVar := outs[0]?
    match resultVar with
    | some rv => body rv
    | none => body (.fromNone md)

/-! ## The Translation ⟦·⟧ : Laurel → GFGL

Three functions: synthValue (⟦·⟧⇒ᵥ), checkValue (⟦·⟧⇐ᵥ), checkProducer (⟦·⟧⇐ₚ).
Entry point is checkProducer — every Laurel derivation maps to a GFGL producer.
synthValue/checkValue are internal helpers for building value sub-terms.
Producer synthesis (⟦·⟧⇒ₚ) is applied by inversion inside the call clause. -/

/-- Fetch the declared outputs of a proc from the runtime or user program. -/
private def lookupProcDeclaredOutputs (callee : String) : ElabM (List (String × HighType)) := do
  let env ← read
  let findProc (procs : List Laurel.Procedure) : Option Laurel.Procedure :=
    procs.find? (fun p => p.name.text == callee)
  match findProc env.runtime.staticProcedures with
  | some proc => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
  | none => match findProc env.program.staticProcedures with
    | some proc => pure (proc.outputs.map fun o => (o.name.text, o.type.val))
    | none => throw s!"lookupProcDeclaredOutputs: callee '{callee}' not found"

/-- Rewrite declared outputs for a given inferred grade: strip any existing Error
    output and re-add it for err/heapErr grades. Heap is owned by the downstream
    `heapParameterizationPass` — no `$heap` output is emitted here. -/
private def rewriteOutputsForGrade (declaredOutputs : List (String × HighType)) (g : Grade) : List (String × HighType) :=
  let resultOutputs := declaredOutputs.filter fun (_, ty) => eraseType ty != .TCore "Error"
  match g with
  | .err | .heapErr => resultOutputs ++ [("maybe_except", .UserDefined { text := "Error" })]
  | _ => resultOutputs

/-- Look up a proc's outputs rewritten for its inferred grade. -/
partial def lookupProcOutputs (callee : String) : ElabM (List (String × HighType)) := do
  let g := (← read).procGrades[callee]?.getD .pure
  let declared ← lookupProcDeclaredOutputs callee
  pure (rewriteOutputsForGrade declared g)

-- ═══════════════════════════════════════════════════════════════════════════════
-- The Translation ⟦·⟧ : Laurel → GFGL
--
-- Three functions: synthValue (⟦·⟧⇒ᵥ), checkValue (⟦·⟧⇐ᵥ), checkProducer (⟦·⟧⇐ₚ)
-- Entry point is checkProducer. synthValue/checkValue are internal helpers.
-- Producer synthesis (⟦·⟧⇒ₚ) is applied by inversion inside the call clause.
-- ═══════════════════════════════════════════════════════════════════════════════

mutual

/-- ⟦·⟧⇒ᵥ (literal):
```
D :: Γ ⊢ n : int   [lit]

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ litInt n ⇒ TInt   [litInt]
```
(analogous for bool, string)
-/
partial def synthValueLiteral (md : Md) (expr : StmtExpr) : Option (FGLValue × HighType) :=
  match expr with
  | .LiteralInt n => some (.litInt md n, .TInt)
  | .LiteralBool b => some (.litBool md b, .TBool)
  | .LiteralString s => some (.litString md s, .TString)
  | .LiteralDecimal d => some (.litDecimal md d, .TReal)
  | _ => none

/-- ⟦·⟧⇒ᵥ (variable):
```
D :: Γ ⊢ x : A   [var, (x:A) ∈ Γ]

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ var x ⇒ ⟦A⟧   [var, (x:⟦A⟧) ∈ ⟦Γ⟧]
```
-/
partial def synthValueVar (md : Md) (id : Identifier) : ElabM (FGLValue × HighType) := do
  match (← lookupEnv id.text) with
  | .variable ty => pure (.var md id.text, ty)
  | _ => throw "synthValueVar: not a .variable"

/-- ⟦·⟧⇒ᵥ (field access):
```
D :: Γ ⊢ obj.f : T   [fieldSelect]
└─ D_obj :: Γ ⊢ obj : C

    ↦    precondition: ($heap : Heap) ∈ ⟦Γ⟧

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall unbox_T [functionCall readField [$heap, V_obj, $field.C.f]] ⇒ ⟦T⟧   [functionCall]
└─ ⟦Γ⟧ ⊢ functionCall readField [$heap, V_obj, $field.C.f] ⇐ Box   [subsumption]
   ├─ ⟦Γ⟧ ⊢ functionCall readField [$heap, V_obj, $field.C.f] ⇒ Box   [functionCall]
   │  ├─ ⟦Γ⟧ ⊢ $heap ⇐ Heap   [subsumption]
   │  │  ├─ ⟦Γ⟧ ⊢ $heap ⇒ Heap   [var]
   │  │  └─ Heap ≤ Heap ↦ id
   │  ├─ ⟦D_obj⟧⇐ᵥ :: ⟦Γ⟧ ⊢ V_obj ⇐ Composite   [subsumption]
   │  │  ├─ ⟦D_obj⟧⇒ᵥ :: ⟦Γ⟧ ⊢ V_obj ⇒ Composite   (since ⟦C⟧ = Composite for user-defined C)
   │  │  └─ Composite ≤ Composite ↦ id
   │  └─ ⟦Γ⟧ ⊢ functionCall $field.C.f [] ⇐ Field   [subsumption]
   │     ├─ ⟦Γ⟧ ⊢ functionCall $field.C.f [] ⇒ Field   [functionCall]
   │     └─ Field ≤ Field ↦ id
   └─ Box ≤ Box ↦ id
```
-/
partial def synthValueFieldSelect (md : Md) (obj : StmtExprMd) (field : Identifier) : ElabM (FGLValue × HighType) := do
  let (ov, objTy) ← synthValue obj
  -- Synth rule for field access:  e ⇒ &{… l : A_l …}  ⊢  e.l ⇒ A_l ;  e ⇒ Any ⊢ e.l ⇒ Any.
  -- We trust the user's field annotations (the frontend's contract) and let the coercion
  -- mechanism reconcile A_l with whatever the use-site demands. The bare `.fieldAccess` is
  -- lowered by heapParameterizationPass to `Box..<A_l>Val!(readField …)`, which unboxes to
  -- exactly A_l — so synthesizing A_l here is faithful, not optimistic. `Any` is the genuine
  -- FALLTHROUGH: only when the receiver's type isn't a known composite (e.g. `self`/`Any`).
  let fieldTy ←
    match objTy with
    | .UserDefined cls =>
      match ← (do match (← read).typeEnv.classFields[cls.text]? with
                  | some fields => pure (fields.find? (fun (n, _) => n == field.text))
                  | none => pure none) with
      | some (_, ty) => pure ty
      | none => pure (.UserDefined { text := "Any" })
    | _ => pure (.UserDefined { text := "Any" })
  pure (.fieldAccess md ov field.text, fieldTy)

/-- ⟦·⟧⇒ᵥ (pure call):
```
D :: Γ ⊢ f(e₁,…,eₙ) : B   [call, f : (Aᵢ) → B & pure]
└─ D_i :: Γ ⊢ eᵢ : Aᵢ  (for each i)

    ↦

⟦D⟧⇒ᵥ :: ⟦Γ⟧ ⊢ functionCall f [V₁,…,Vₙ] ⇒ ⟦B⟧   [functionCall]
└─ ⟦D_i⟧⇐ᵥ :: ⟦Γ⟧ ⊢ Vᵢ ⇐ ⟦Aᵢ⟧  (for each i)   [subsumption]
   ├─ ⟦D_i⟧⇒ᵥ :: ⟦Γ⟧ ⊢ Vᵢ ⇒ Bᵢ   (Bᵢ discovered by recursive synthValue)
   └─ Bᵢ ≤ ⟦Aᵢ⟧ ↦ cᵢ
```
-/
partial def synthValueStaticCall (md : Md) (callee : Identifier) (args : List StmtExprMd) : ElabM (FGLValue × HighType) := do
  -- A name carrying a function signature but no explicit procedure grade is pure:
  -- datatype constructors (from_None, from_int, ...) and pure runtime functions
  -- live in typeEnv.names but not in procGrades. Default to pure, as elaborateCall
  -- and lookupProcOutputs do; only a name graded above pure is rejected here.
  -- In value position the callee is used purely: its result value is what matters, not its
  -- effect grade. A runtime op graded `.err`/`.proc` (e.g. `PAdd`, `Any_get!`) carries that grade
  -- only for statement-position exception/heap threading; called inside a pure value (a contract,
  -- or an argument of a pure call) it denotes its value and is elaborated as pure. Heap-graded
  -- callees are still rejected — a value context cannot thread the heap.
  let g := (← read).procGrades[callee.text]?.getD .pure
  unless g == .pure || g == .proc || g == .err do
    throw s!"synthValueStaticCall: value-position call of heap-effecting callee (grade {repr g})"
  let sig : FuncSig := match (← read).typeEnv.names[callee.text]? with
    | some (.function s) => s
    | _ => { name := callee.text, params := [], returnType := HighType.Unknown }
  let checkedArgs ← checkArgValues args sig.params
  pure (.staticCall md callee.text checkedArgs, sig.returnType)

/-- ⟦·⟧⇒ᵥ: Value synthesis. Dispatches to clause helpers. -/
partial def synthValue (expr : StmtExprMd) : ElabM (FGLValue × HighType) := do
  let md := expr.source
  match expr.val with
  | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ =>
    match synthValueLiteral md expr.val with
    | some r => pure r
    | none => throw "synthValueLiteral: unsupported literal form"
  | .Var (.Local id) => synthValueVar md id
  | .Var (.Field obj field) => synthValueFieldSelect md obj field
  | .StaticCall callee args => synthValueStaticCall md callee args
  | _ => throw "synthValue: unsupported value form"

/-- Helper: check a list of arguments as values against parameter types. -/
partial def checkArgValues (args : List StmtExprMd) (params : List (String × HighType)) : ElabM (List FGLValue) := do
  match args, params with
  | [], _ => pure []
  | arg :: rest, (_, pty) :: prest => do
    let v ← checkValue arg pty
    let vs ← checkArgValues rest prest
    pure (v :: vs)
  | _ :: _, [] => throw "bindArgs(value): more args than params"

/-- ⟦·⟧⇐ᵥ: Value checking. Synthesizes then applies subtyping coercion.
```
⟦D⟧⇐ᵥ (deterministic hole) :: ⟦Γ⟧ ⊢ functionCall hole_N [input₁,...,inputₖ] ⇐ ⟦A⟧   [functionCall]
└─ (hole_N : (⟦T₁⟧,...,⟦Tₖ⟧) → ⟦A⟧ & pure) ∈ ⟦Γ⟧
```
-/
partial def checkValue (expr : StmtExprMd) (expected : HighType) : ElabM FGLValue := do
  let md := expr.source
  match expr.val with
  | .Hole _ _ =>
    -- A hole in pure value position (a contract, or an argument of a pure call)
    -- denotes a deterministic uninterpreted function of the procedure's inputs:
    -- nondeterminism is meaningless in a pure value, so even a hole Translation
    -- marked nondeterministic (e.g. an unresolved `re.search(...)` inside a
    -- `requires`) is elaborated here as the deterministic `hole_N(inputs)`. This
    -- keeps the contract well-typed; the caller obligation is sound but
    -- uninterpretable (verification stays inconclusive, never unsound).
    let hv ← freshVar "hole"
    let args := (← read).procInputs.map fun (name, _) => FGLValue.var md name
    modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, true, expected)] }
    pure (.staticCall md hv args)
  | _ =>
    let (val, _actual) ← synthValue expr
    pure val

/-- ⟦·⟧⇐ₚ*: Check a list of statements as a producer (list extension). -/
partial def checkProducers (stmts : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match stmts with
  | [] => pure .skip
  | stmt :: rest => checkProducer stmt rest retTy grade

/-- ⟦·⟧⇐ₚ (if):
```
D :: Γ ⊢ (if c then t else f); k : A   [if]
├─ D_c :: Γ ⊢ c : bool
├─ D_t :: Γ ⊢ t : A
├─ D_f :: Γ ⊢ f : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (ifThenElse x_c M_t M_f M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ ifThenElse x_c M_t M_f M_k ⇐ ⟦A⟧ & d   [ifThenElse]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   ├─ ⟦D_t⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_t ⇐ ⟦A⟧ & d
   ├─ ⟦D_f⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_f ⇐ ⟦A⟧ & d
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerIf (md : Md) (cond thn : StmtExprMd) (els : Option StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  let body ← extendEnv x_c .TBool do
    let M_t ← checkProducer thn [] retTy grade
    let M_f ← match els with
      | some e => checkProducer e [] retTy grade
      | none => pure .skip
    let M_k ← checkProducers rest retTy grade
    pure (.ifThenElse md (.var md x_c) M_t M_f M_k)
  pure (.varDecl md x_c .TBool M_c body)

/-- ⟦·⟧⇐ₚ (while):
```
D :: Γ ⊢ (while c do body); k : A   [while]
├─ D_c :: Γ ⊢ c : bool
├─ D_b :: Γ ⊢ body : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (whileLoop x_c M_b' M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d          (initial guard evaluation)
└─ ⟦Γ⟧, x_c:bool ⊢ whileLoop x_c M_b' M_k ⇐ ⟦A⟧ & d   [whileLoop]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   ├─ ⟦D_b ; (x_c := c)⟧⇐ₚ :: ⟦Γ⟧, x_c:bool ⊢ M_b' ⇐ ⟦A⟧ & d
   │     where M_b' = ⟦body ; (x_c := c)⟧  — the guard is RE-EVALUATED at the end of
   │     each iteration, so the loop tests a fresh value, not a frozen one. The
   │     re-evaluation is threaded by appending the source-level assignment `x_c := c`
   │     to `body`'s statement block before elaboration (so M_b' is a single derivation
   │     over the extended body, sharing the body's sequencing). This is REQUIRED for
   │     soundness: with a frozen `x_c`, downstream loop-elimination (which havocs
   │     loop-modified vars) lets the verifier prove post-loop facts the loop should
   │     not establish.
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerWhile (md : Md) (cond loopBody : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  -- The condition must be RE-EVALUATED every iteration. We bind it to `x_c` before the
  -- loop AND re-assign `x_c := cond` at the END of the loop body, so the next guard test
  -- sees the updated value. A frozen `x_c` is unsound: the guard never changes, and after
  -- LoopElim havoc the verifier can prove post-loop facts the loop should havoc. We keep
  -- the value-bound form (the elaborator needs a value guard) but refresh it in the body.
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  -- Append `x_c := cond` to the END of the loop body (at the Laurel level) so it elaborates
  -- with the body's natural sequencing and refreshes the guard each iteration. `loopBody`
  -- is a Block; we extend its statement list with the reassignment.
  -- IMPORTANT: when the body is a block labelled with the loop's continue label, `continue`
  -- lowers to `Exit lbl`, which exits THAT labelled block. So the reassignment must sit
  -- AFTER the labelled block, not inside it — otherwise `continue` jumps past the refresh and
  -- the next guard test reads a stale `x_c`. Keep the label on the original body and wrap the
  -- reassignment in an outer unlabelled block so `Exit lbl` still reaches it.
  let reassign : StmtExprMd := mkLaurel md (.Assign [⟨.Local { text := x_c }, md.getD .unknown⟩] cond)
  let loopBody' : StmtExprMd := match loopBody.val with
    | .Block stmts (some lbl) =>
      mkLaurel md (.Block [mkLaurel md (.Block stmts (some lbl)), reassign] none)
    | .Block stmts none => mkLaurel md (.Block (stmts ++ [reassign]) none)
    | _ => mkLaurel md (.Block [loopBody, reassign] none)
  let body ← extendEnv x_c .TBool do
    let M_b ← checkProducer loopBody' [] retTy grade
    let M_k ← checkProducers rest retTy grade
    pure (.whileLoop md (.var md x_c) M_b M_k)
  pure (.varDecl md x_c .TBool M_c body)

/-- ⟦·⟧⇐ₚ (varDecl):
```
D :: Γ ⊢ (var x:T := e); k : A   [varDecl]
├─ D_e :: Γ ⊢ e : T
└─ D_k :: Γ, x:T ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x ⟦T⟧ M_e M_k ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_e⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_e ⇐ ⟦T⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x:⟦T⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerVarDecl (md : Md) (nameId : Identifier) (typeMd : HighTypeMd)
    (initOpt : Option StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_e ← match initOpt with
    | some init => checkProducer init [] typeMd.val grade
    | none => do
      let v ← checkValue (mkLaurel md (.Hole true none)) typeMd.val
      pure (.produce md v)
  let body ← extendEnv nameId.text typeMd.val do
    checkProducers rest retTy grade
  pure (.varDecl md nameId.text (eraseType typeMd.val) M_e body)

/-- ⟦·⟧⇐ₚ (assert):
```
D :: Γ ⊢ (assert c); k : A   [assert]
├─ D_c :: Γ ⊢ c : bool
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (assert x_c M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ assert x_c M_k ⇐ ⟦A⟧ & d   [assert]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerAssert (md : Md) (cond : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  let body ← extendEnv x_c .TBool do
    let M_k ← checkProducers rest retTy grade
    pure (.assert md (.var md x_c) M_k)
  pure (.varDecl md x_c .TBool M_c body)

/-- ⟦·⟧⇐ₚ (assume):
```
D :: Γ ⊢ (assume c); k : A   [assume]
├─ D_c :: Γ ⊢ c : bool
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_c bool M_c (assume x_c M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_c⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_c ⇐ bool & d
└─ ⟦Γ⟧, x_c:bool ⊢ assume x_c M_k ⇐ ⟦A⟧ & d   [assume]
   ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇐ bool   [subsumption]
   │  ├─ ⟦Γ⟧, x_c:bool ⊢ x_c ⇒ bool   [var]
   │  └─ bool ≤ bool ↦ id
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_c:bool ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkProducerAssume (md : Md) (cond : StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M_c ← checkProducer cond [] .TBool grade
  let x_c ← freshVar "cond"
  let body ← extendEnv x_c .TBool do
    let M_k ← checkProducers rest retTy grade
    pure (.assume md (.var md x_c) M_k)
  pure (.varDecl md x_c .TBool M_c body)

partial def elaborateCall (md : Md) (callee : Identifier) (args : List StmtExprMd)
    (grade : Grade) (body : FGLValue → Grade → ElabM FGLProducer) : ElabM FGLProducer := do
  let callGrade := (← read).procGrades[callee.text]?.getD .pure
  let some residual := Grade.leftResidual callGrade grade
    | throw s!"elaborateCall: leftResidual none (callGrade vs ambient)"
  let sig ← lookupFuncSig callee.text
  -- Runtime `function` procs (isFunctional=true) are called as StaticCalls regardless of
  -- their grade. Their exceptions are encoded as values (returning `exception(...)` inside
  -- `Any`), not as a Laurel `Error` output. Only user procs and runtime `procedure`s get the
  -- full procedureCall calling convention.
  let env ← read
  let isFunctionalRuntime : Bool :=
    match env.runtime.staticProcedures.find? (fun p => p.name.text == callee.text) with
    | some rp => procIsFunctional rp
    | none => false
  bindArgs md args sig.params grade fun boundVars => do
    if isFunctionalRuntime || callGrade == .pure then
      let rv := FGLValue.staticCall md callee.text boundVars
      body rv residual
    else
      let declaredOutputs ← lookupProcOutputs callee.text
      mkGradedCall md callee.text boundVars declaredOutputs fun rv =>
        body rv residual

/-- ⟦·⟧⇐ₚ (bare call, discards return value):
```
D :: Γ ⊢ g(e₁,…,eₙ); k : A   [call]
├─ (g : (A₁,...,Aₙ) → B) ∈ Γ
├─ Dᵢ :: Γ ⊢ eᵢ : Aᵢ  (for each i)
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x₁ ⟦A₁⟧ M₁ (...(varDecl xₙ ⟦Aₙ⟧ Mₙ (procedureCall g (pre ++ [x₁,...,xₙ]) outs M_k))) ⇐ ⟦A⟧ & d
├─ ⟦D₁⟧⇐ₚ :: ⟦Γ⟧ ⊢ M₁ ⇐ ⟦A₁⟧ & d
├─ ...   [varDecl]
├─ ⟦Dₙ⟧⇐ₚ :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ₋₁:⟦Aₙ₋₁⟧ ⊢ Mₙ ⇐ ⟦Aₙ⟧ & d
└─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ procedureCall g (pre ++ [x₁,...,xₙ]) outs M_k ⇐ ⟦A⟧ & d   [producerSubsumption]
   ├─ (g : (⟦A₁⟧,...,⟦Aₙ⟧) → ⟦B⟧ & d') ∈ ⟦Γ⟧
   ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇐ ⟦Aᵢ⟧   [subsumption]
   │  ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇒ ⟦Aᵢ⟧   [var]
   │  └─ ⟦Aᵢ⟧ ≤ ⟦Aᵢ⟧ ↦ id
   ├─ d' ≤ d ↦ (pre, outs)
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ M_k ⇐ ⟦A⟧ & (d'\d)
```
-/
partial def checkProducerStaticCall (md : Md) (callee : Identifier) (args : List StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  elaborateCall md callee args grade fun rv residual => do
    -- A bare call to a value-encoded-exception proc (e.g. a subscript write whose
    -- root is not an lvalue) must still raise `assert !Any..isexception(rv)`.
    withValueExceptionCheck md callee.text rv do
      match rest with
      | [] =>
        let _sig ← lookupFuncSig callee.text
        pure (.produce md rv)
      | _ => checkProducers rest retTy residual

/-- ⟦·⟧⇐ₚ (block):
```
D :: Γ ⊢ {body}_l; k : A   [block]
├─ D_b :: Γ, l ⊢ body : A
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ labeledBlock l M_b M_k ⇐ ⟦A⟧ & d   [labeledBlock]
├─ ⟦D_b⟧⇐ₚ :: ⟦Γ⟧, l ⊢ M_b ⇐ ⟦A⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
Unlabeled blocks are flattened into the enclosing scope.
-/
partial def checkProducerBlock (md : Md) (stmts : List StmtExprMd) (label : Option String)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  match label with
  | some l =>
    let M_b ← checkProducers stmts retTy grade
    let M_k ← checkProducers rest retTy grade
    pure (.labeledBlock md l M_b M_k)
  | none => checkProducers (stmts ++ rest) retTy grade

/-- ⟦·⟧⇐ₚ: Producer checking. Entry point of the translation.
    Dispatches on statement form to clause helpers. -/
partial def checkProducer (stmt : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let md := stmt.source
  match stmt.val with
  | .IfThenElse cond thn els => checkProducerIf md cond thn els rest retTy grade
  | .While cond _invs _dec loopBody _postTest => checkProducerWhile md cond loopBody rest retTy grade
  | .Exit target => pure (.exit md target)
  | .Var (.Declare ⟨nameId, typeMd⟩) => checkProducerVarDecl md nameId (typeMd.getD default) none rest retTy grade
  | .Assert cond _summary => checkProducerAssert md cond rest retTy grade
  | .Assume cond => checkProducerAssume md cond rest retTy grade
  | .Assign targets value => match targets with
    | [target] => checkAssign target value rest retTy grade
    | _ => throw "checkProducer: multi-target Assign unsupported"
  | .StaticCall callee args => checkProducerStaticCall md callee args rest retTy grade
  | .Block stmts label => checkProducerBlock md stmts label rest retTy grade
  | .New classId =>
    -- A constructor `.New` in PRODUCER position (e.g. the then-branch of a ternary
    -- assigned to a field). Emit the bare `.new` value (heapParameterizationPass allocates
    -- it), as `checkAssignNew` and the field-write `.New` branch do. Valid only as a
    -- TERMINAL producer (rest empty) — same shape as the value catch-all below.
    match rest with
    | [] => pure (.produce md (.new md classId.text))
    | _ => throw "checkProducer: bare .New with non-empty continuation"
  | .Hole deterministic _ => do
    let hv ← freshVar "havoc"
    modify fun s => { s with usedHoles := s.usedHoles ++ [(hv, deterministic, retTy)] }
    -- A deterministic hole is a pure function of the procedure's inputs, so it is
    -- declared with those inputs (see emission below) and must be applied to them
    -- here — same as the value-judgment `.Hole` case. A nondeterministic hole
    -- (havoc) is declared with no inputs and called with none.
    let env ← read
    let args := if deterministic then env.procInputs.map (fun (name, _) => FGLValue.var md name) else []
    let declaredOutputs := [("result", retTy)]
    mkGradedCall md hv args declaredOutputs fun rv => do
      let M_k ← checkProducers rest retTy grade
      match rest with
      | [] => pure (.produce md rv)
      | _ => pure M_k
  | _ => do
    let v ← checkValue stmt retTy
    match rest with
    | [] => pure (.produce md v)
    | _ => throw "checkProducer: non-final value statement"

/-- Bind a list of arguments as producers via nested varDecls.
    Each arg is checked as a producer, bound to a fresh var, and the
    continuation receives the list of bound values. -/
partial def bindArgs (md : Md) (args : List StmtExprMd) (params : List (String × HighType))
    (grade : Grade) (cont : List FGLValue → ElabM FGLProducer) : ElabM FGLProducer := do
  match args, params with
  | [], _ => cont []
  | arg :: restArgs, (_, pty) :: restParams => do
    let M_arg ← checkProducer arg [] pty grade
    let x_arg ← freshVar "arg"
    let body ← extendEnv x_arg pty do
      bindArgs md restArgs restParams grade fun restVars =>
        cont (.var md x_arg :: restVars)
    pure (.varDecl md x_arg (eraseType pty) M_arg body)
  | _ :: _, [] => throw "bindArgs: more args than params"

/-- ⟦·⟧⇐ₚ (field write):
```
D :: Γ ⊢ (obj.f := v); k : A   [fieldWrite]
├─ D_obj :: Γ ⊢ obj : C   (C discovered by synthesis on obj)
├─ fieldType(C, f) = T
├─ D_v :: Γ ⊢ v : T
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x_obj ⟦C⟧ M_obj (varDecl x_v ⟦T⟧ M_v (varDecl h' Heap M_update M_k)) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D_obj⟧⇐ₚ :: ⟦Γ⟧ ⊢ M_obj ⇐ ⟦C⟧ & d
└─ ⟦Γ⟧, x_obj:⟦C⟧ ⊢ varDecl x_v ⟦T⟧ M_v (varDecl h' Heap M_update M_k) ⇐ ⟦A⟧ & d   [varDecl]
   ├─ ⟦D_v⟧⇐ₚ :: ⟦Γ⟧, x_obj ⊢ M_v ⇐ ⟦T⟧ & d
   └─ ⟦Γ⟧, x_obj, x_v ⊢ varDecl h' Heap M_update M_k ⇐ ⟦A⟧ & d   [varDecl]
      ├─ ⟦Γ⟧, x_obj, x_v ⊢ produce (functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]]) ⇐ Heap & d   [produce]
      │  └─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]] ⇐ Heap   [subsumption]
      │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall updateField [$heap, x_obj, $field.C.f, functionCall box_T [x_v]] ⇒ Heap   [functionCall]
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ $heap ⇐ Heap   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ $heap ⇒ Heap   [var]
      │     │  │  └─ Heap ≤ Heap ↦ id
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_obj ⇐ Composite   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_obj ⇒ Composite   [var]
      │     │  │  └─ Composite ≤ Composite ↦ id
      │     │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall $field.C.f [] ⇐ Field   [subsumption]
      │     │  │  ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall $field.C.f [] ⇒ Field   [functionCall]
      │     │  │  └─ Field ≤ Field ↦ id
      │     │  └─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall box_T [x_v] ⇐ Box   [subsumption]
      │     │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ functionCall box_T [x_v] ⇒ Box   [functionCall]
      │     │     │  └─ ⟦Γ⟧, x_obj, x_v ⊢ x_v ⇐ ⟦T⟧   [subsumption]
      │     │     │     ├─ ⟦Γ⟧, x_obj, x_v ⊢ x_v ⇒ ⟦T⟧   [var]
      │     │     │     └─ ⟦T⟧ ≤ ⟦T⟧ ↦ id
      │     │     └─ Box ≤ Box ↦ id
      │     └─ Heap ≤ Heap ↦ id
      └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x_obj, x_v, h':Heap ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignFieldWrite (md : Md) (obj : StmtExprMd) (field : Identifier)
    (value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  -- Write rule for field access:  Γ ⊢ e.l := v ; k  with  v ⇐ A_l  (the DECLARED field
  -- type). We check the RHS against `A_l` so the coercion mechanism inserts the right
  -- boxing — we trust the user's annotation and let coercion handle impedance. `A_l` is
  -- looked up from the receiver's composite type; `Any` is the genuine fallthrough when
  -- the receiver isn't a known composite (e.g. `self`/dynamic).
  -- The heap is threaded by heapParameterizationPass, which consumes a BARE field-write
  -- `.Assign [.Field obj f] rhs` and rewrites it into `updateField($heap, obj, $field.C.f,
  -- box_<A_l>(rhs))`. We emit it DIRECTLY as `.assign (.fieldAccess obj f) rhs` — no
  -- intermediate fresh temp (a `val$N` temp would collide with a same-named field/param,
  -- e.g. `self.val = val`, so the write is emitted as a single `self#val := val`).
  let (ov, objTy) ← synthValue obj
  let fieldTy ←
    match objTy with
    | .UserDefined cls =>
      match ← (do match (← read).typeEnv.classFields[cls.text]? with
                  | some fields => pure (fields.find? (fun (n, _) => n == field.text))
                  | none => pure none) with
      | some (_, ty) => pure ty
      | none => pure (.UserDefined { text := "Any" })
    | _ => pure (.UserDefined { text := "Any" })
  -- RHS `.New classId` (a constructor in field-write position, e.g. `self.field = C(...)`).
  -- `checkProducer` has no `.New` arm (only `.Local`-target Assign special-cases it via
  -- `checkAssignNew`), so a bare `.New` here would fall to `synthValue .New => failure`. Emit
  -- the bare `.new` value DIRECTLY (as `checkAssignNew` does for local targets) — the
  -- heapParameterizationPass consumes the bare `.new` node and heap-allocates it.
  match value.val with
  | .New classId =>
    let M_k ← checkProducers rest retTy grade
    pure (.assign md (.fieldAccess md ov field.text) (.produce md (.new md classId.text)) M_k)
  | _ =>
    let M_v ← checkProducer value [] fieldTy grade
    let M_k ← checkProducers rest retTy grade
    pure (.assign md (.fieldAccess md ov field.text) M_v M_k)

/-- Dispatches on LHS to get assignee, then on RHS form. -/
partial def checkAssign (target : VariableMd) (value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let md := target.source
  match target.val with
  | .Field obj field => checkAssignFieldWrite md obj field value rest retTy grade
  -- A `.Declare` target is a local-variable declaration with an initializer
  -- (`var x : T := value`); route it to `checkProducerVarDecl` with the initializer.
  | .Declare ⟨nameId, typeMd⟩ => checkProducerVarDecl md nameId (typeMd.getD default) (some value) rest retTy grade
  | .Local id =>
    let .variable targetTy := (← lookupEnv id.text) | throw s!"checkAssign: target {id.text} not bound as a variable"
    match value.val with
    | .StaticCall callee args => checkAssignStaticCall md id.text targetTy callee args rest retTy grade
    | .New classId => checkAssignNew md id.text targetTy classId rest retTy grade
    | _ => checkAssignVar md id.text targetTy value rest retTy grade

/-- ⟦·⟧⇐ₚ (assign, generic RHS):
```
D :: Γ ⊢ (x := e); k : A   [assign]
├─ D_e :: Γ ⊢ e : Γ(x)
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ assign x M M_k ⇐ ⟦A⟧ & d   [assign]
├─ ⟦D_e⟧⇐ₚ :: ⟦Γ⟧ ⊢ M ⇐ ⟦Γ(x)⟧ & d
└─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧ ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignVar (md : Md) (targetName : String) (targetTy : HighType)
    (value : StmtExprMd) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let M ← checkProducer value [] targetTy grade
  let M_k ← checkProducers rest retTy grade
  pure (.assign md (.var md targetName) M M_k)

/-- ⟦·⟧⇐ₚ (assign + call):
```
D :: Γ ⊢ (x := f(e₁,...,eₙ)); k : A   [assign]
├─ D_e :: Γ ⊢ f(e₁,...,eₙ) : Γ(x)   [call]
│  ├─ (f : (A₁,...,Aₙ) → B) ∈ Γ
│  └─ Dᵢ :: Γ ⊢ eᵢ : Aᵢ   (for i = 1,...,n)
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl x₁ ⟦A₁⟧ M₁ (...(varDecl xₙ ⟦Aₙ⟧ Mₙ (procedureCall f (pre ++ [x₁,...,xₙ]) outs (assign x (produce c(rv)) M_k)))) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦D₁⟧⇐ₚ :: ⟦Γ⟧ ⊢ M₁ ⇐ ⟦A₁⟧ & d
├─ ...   [varDecl]
├─ ⟦Dₙ⟧⇐ₚ :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ₋₁:⟦Aₙ₋₁⟧ ⊢ Mₙ ⇐ ⟦Aₙ⟧ & d
└─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ procedureCall f (pre ++ [x₁,...,xₙ]) outs (assign x (produce c(rv)) M_k) ⇐ ⟦A⟧ & d   [producerSubsumption]
   ├─ (f : (⟦A₁⟧,...,⟦Aₙ⟧) → ⟦B⟧ & d') ∈ ⟦Γ⟧
   ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇐ ⟦Aᵢ⟧   [subsumption]
   │  ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧ ⊢ xᵢ ⇒ ⟦Aᵢ⟧   [var]
   │  └─ ⟦Aᵢ⟧ ≤ ⟦Aᵢ⟧ ↦ id
   ├─ d' ≤ d ↦ (pre, outs)   where (rv : ⟦B⟧) ∈ outs
   └─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ assign x (produce c(rv)) M_k ⇐ ⟦A⟧ & (d'\d)   [assign]
      ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ produce c(rv) ⇐ ⟦Γ(x)⟧ & (d'\d)   [produce]
      │  └─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ c(rv) ⇐ ⟦Γ(x)⟧   [subsumption]
      │     ├─ ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ rv ⇒ ⟦B⟧   [var]
      │     └─ ⟦B⟧ ≤ ⟦Γ(x)⟧ ↦ c
      └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, x₁:⟦A₁⟧,...,xₙ:⟦Aₙ⟧, outs ⊢ M_k ⇐ ⟦A⟧ & (d'\d)
```
-/
-- `isValueEncodedExceptionCall` / `withValueExceptionCheck` identify a runtime proc
-- whose exception is encoded inside its returned `Any` (graded `.err` yet transparent,
-- so `elaborateCall` lowers it as a plain value `StaticCall` with no `maybe_except`
-- output) and wrap the continuation with `assert !Any..isexception(rv)` so a
-- possibly-throwing call raises a checkable obligation instead of silently storing the
-- exception into the target. `Any..isexception` returns native `bool`; `$not` negates it.
partial def isValueEncodedExceptionCall (callee : String) : ElabM Bool := do
  let env ← read
  let gradedErr := env.procGrades[callee]? == some .err
  let functionalRuntime :=
    match env.runtime.staticProcedures.find? (fun p => p.name.text == callee) with
    | some rp => procIsFunctional rp
    | none => false
  pure (gradedErr && functionalRuntime)

partial def withValueExceptionCheck (md : Md) (callee : String) (rv : FGLValue)
    (body : ElabM FGLProducer) : ElabM FGLProducer := do
  if ← isValueEncodedExceptionCall callee then
    let isExc := FGLValue.staticCall md "Any..isexception" [rv]
    let notExc := FGLValue.staticCall md "$not" [isExc]
    let x_c ← freshVar "exccheck"
    let inner ← extendEnv x_c .TBool do
      let M_k ← body
      pure (.assert md (.var md x_c) M_k (some s!"Check {callee} exception"))
    pure (.varDecl md x_c .TBool (.produce md notExc) inner)
  else
    body

partial def checkAssignStaticCall (md : Md) (targetName : String) (_targetTy : HighType)
    (callee : Identifier) (args : List StmtExprMd)
    (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  let _sig ← lookupFuncSig callee.text
  elaborateCall md callee args grade fun rv residual => do
    let coerced := rv
    withValueExceptionCheck md callee.text rv do
      let M_k ← checkProducers rest retTy residual
      pure (.assign md (.var md targetName) (.produce md coerced) M_k)

/-- ⟦·⟧⇐ₚ (assign + new):
```
D :: Γ ⊢ (x := new C); k : A   [assign]
├─ D_e :: Γ ⊢ new C : Γ(x)   [new]
│  └─ C is a class ∈ Γ
└─ D_k :: Γ ⊢ k : A

    ↦

⟦D⟧⇐ₚ :: ⟦Γ⟧ ⊢ varDecl h' Heap (produce (functionCall increment [$heap])) (assign x (produce c(functionCall MkComposite [functionCall Heap..nextReference! [$heap], functionCall C_TypeTag []])) M_k) ⇐ ⟦A⟧ & d   [varDecl]
├─ ⟦Γ⟧ ⊢ produce (functionCall increment [$heap]) ⇐ Heap & d   [produce]
│  └─ ⟦Γ⟧ ⊢ functionCall increment [$heap] ⇐ Heap   [subsumption]
│     ├─ ⟦Γ⟧ ⊢ functionCall increment [$heap] ⇒ Heap   [functionCall]
│     │  └─ ⟦Γ⟧ ⊢ $heap ⇐ Heap   [subsumption]
│     │     ├─ ⟦Γ⟧ ⊢ $heap ⇒ Heap   [var]
│     │     └─ Heap ≤ Heap ↦ id
│     └─ Heap ≤ Heap ↦ id
└─ ⟦Γ⟧, h':Heap ⊢ assign x (produce c(functionCall MkComposite [functionCall Heap..nextReference! [$heap], functionCall C_TypeTag []])) M_k ⇐ ⟦A⟧ & d   [assign]
   ├─ ⟦Γ⟧, h':Heap ⊢ produce c(functionCall MkComposite [...]) ⇐ ⟦Γ(x)⟧ & d   [produce]
   │  └─ ⟦Γ⟧, h':Heap ⊢ c(functionCall MkComposite [...]) ⇐ ⟦Γ(x)⟧   [subsumption]
   │     ├─ ⟦Γ⟧, h':Heap ⊢ functionCall MkComposite [functionCall Heap..nextReference! [$heap], functionCall C_TypeTag []] ⇒ Composite   [functionCall]
   │     │  ├─ ⟦Γ⟧, h':Heap ⊢ functionCall Heap..nextReference! [$heap] ⇐ int   [subsumption]
   │     │  │  ├─ ⟦Γ⟧, h':Heap ⊢ functionCall Heap..nextReference! [$heap] ⇒ int   [functionCall]
   │     │  │  │  └─ ⟦Γ⟧, h':Heap ⊢ $heap ⇐ Heap   [subsumption]
   │     │  │  │     ├─ ⟦Γ⟧, h':Heap ⊢ $heap ⇒ Heap   [var]
   │     │  │  │     └─ Heap ≤ Heap ↦ id
   │     │  │  └─ int ≤ int ↦ id
   │     │  └─ ⟦Γ⟧, h':Heap ⊢ functionCall C_TypeTag [] ⇐ TypeTag   [subsumption]
   │     │     ├─ ⟦Γ⟧, h':Heap ⊢ functionCall C_TypeTag [] ⇒ TypeTag   [functionCall]
   │     │     └─ TypeTag ≤ TypeTag ↦ id
   │     └─ Composite ≤ ⟦Γ(x)⟧ ↦ c
   └─ ⟦D_k⟧⇐ₚ* :: ⟦Γ⟧, h':Heap ⊢ M_k ⇐ ⟦A⟧ & d
```
-/
partial def checkAssignNew (md : Md) (targetName : String) (targetTy : HighType)
    (classId : Identifier) (rest : List StmtExprMd) (retTy : HighType) (grade : Grade) : ElabM FGLProducer := do
  -- Exceptions-only: allocation is heapParameterizationPass's job. It consumes a BARE
  -- `.New classId` node and rewrites it into a heap-allocated `MkComposite` with a fresh
  -- reference + threads `$heap`. So here we emit the bare `.new` value and assign it.
  let _ := targetTy
  let M_k ← checkProducers rest retTy grade
  pure (.assign md (.var md targetName) (.produce md (.new md classId.text)) M_k)

end

/-! ## Grade Inference

Grade inference is coinductive over the call graph. For each procedure,
try elaboration at successively higher grades until one succeeds. When a
callee's grade exceeds the trial grade, the left residual is undefined,
elaboration fails (returns `none`), and the next grade is tried. The
finite lattice guarantees convergence. -/

/-- Try elaborating a procedure body at each grade in order. Returns the
    first grade that succeeds, or `heapErr` as fallback. -/
private partial def tryGrades (callee : String) (env : ElabEnv) (body : StmtExprMd)
    (retTy : HighType) (grades : List Grade) : Option Grade :=
  match grades with
  | [] => some .err  -- Exceptions-only: top of the lattice we use is .err
  | g :: rest =>
    let st : ElabState := { freshCounter := 0 }
    let trialEnv := { env with procGrades := env.procGrades.insert callee g }
    match (checkProducer body [] retTy g).run trialEnv |>.run st with
    | .ok _ => some g
    | .error _ => tryGrades callee env body retTy rest

/-! ## Projection (Destination Passing Style)

Projection reverses elaboration: GFGL derivations → Laurel derivations.
Uses a writer monad that accumulates declarations (hoisted to procedure top).

```
⟦D⟧ₓ⁻¹ : (⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d) → ∃e⃗. (Γ, x : A ⊢ e⃗ : TVoid)
```
-/

structure ProjM (α : Type) where
  run : α × List StmtExprMd

instance : Monad ProjM where
  pure a := ⟨(a, [])⟩
  bind ma f := let (a, d1) := ma.run; let (b, d2) := (f a).run; ⟨(b, d1 ++ d2)⟩

private def projDecl (decl : StmtExprMd) : ProjM Unit := ⟨((), [decl])⟩

def projectValue : FGLValue → StmtExprMd
  | .litInt md n => mkLaurel md (.LiteralInt n)
  | .litBool md b => mkLaurel md (.LiteralBool b)
  | .litString md s => mkLaurel md (.LiteralString s)
  | .litDecimal md d => mkLaurel md (.LiteralDecimal d)
  | .var md name => mkLaurel md (.Var (.Local { text := name }))
  | .fromInt md v => mkLaurel md (.StaticCall { text := "from_int" } [projectValue v])
  | .fromStr md v => mkLaurel md (.StaticCall { text := "from_str" } [projectValue v])
  | .fromBool md v => mkLaurel md (.StaticCall { text := "from_bool" } [projectValue v])
  | .fromFloat md v => mkLaurel md (.StaticCall { text := "from_float" } [projectValue v])
  | .fromComposite md v =>
    -- The target IR has no structural `Composite → Any` constructor (from_ClassInstance takes
    -- (classname, attr-dict), a different representation). Use the value-PRESERVING
    -- uninterpreted stub `Any..from_Composite(v)` so the term type-checks (Composite⇒Any)
    -- and stays sound-but-uninterpreted, rather than discarding `v` into an empty
    -- from_ClassInstance("", {}) (which both loses the value and mis-types).
    mkLaurel md (.StaticCall { text := "Any..from_Composite" } [projectValue v])
  | .fromListAny md v => mkLaurel md (.StaticCall { text := "from_ListAny" } [projectValue v])
  | .fromDictStrAny md v => mkLaurel md (.StaticCall { text := "from_DictStrAny" } [projectValue v])
  | .fromNone md => mkLaurel md (.StaticCall { text := "from_None" } [])
  | .fieldAccess md obj f => mkLaurel md (.Var (.Field (projectValue obj) { text := f }))
  | .staticCall md name args => mkLaurel md (.StaticCall { text := name } (args.map projectValue))
  | .new md className => mkLaurel md (.New { text := className })

/-- Project an FGL value used as an assignment destination into a `VariableMd`.
    Assignment/declaration destinations are always variables (`.var`) or, for
    field writes, field selections (`.fieldAccess`). -/
private def projectVarTarget : FGLValue → VariableMd
  | .var md name => ⟨.Local { text := name }, md.getD .unknown⟩
  | .fieldAccess md obj f => ⟨.Field (projectValue obj) { text := f }, md.getD .unknown⟩
  | v => ⟨.Local default, v.getMd.getD .unknown⟩

mutual

/-- Destination-passing projection.
```
⟦·⟧ₓ⁻¹ : (⟦Γ⟧ ⊢ M ⇔ ⟦A⟧ & d) → ∃e⃗. (Γ, x : A ⊢ e⃗ : TVoid)
⟦·⟧⁻¹  : (⟦Γ⟧ ⊢ V ⇔ ⟦A⟧)     → ∃e. (Γ ⊢ e : A)
```
Dispatches to per-constructor helpers. -/
partial def proj (dest : Option VariableMd) : FGLProducer → ProjM (List StmtExprMd)
  | .produce md v => projProduce dest md v
  | .varDecl md name ty init body => projVarDecl dest md name ty init body
  | .assign md target val body => projAssign dest md target val body
  | .ifThenElse md cond thn els after => projIfThenElse dest md cond thn els after
  | .whileLoop md cond body after => projWhileLoop dest md cond body after
  | .procedureCall md callee args outputs body => projProcedureCall dest md callee args outputs body
  | .assert md cond body summary => projAssert dest md cond body summary
  | .assume md cond body => projAssume dest md cond body
  | .labeledBlock md label body after => projLabeledBlock dest md label body after
  | .exit md label => projExit md label
  | .skip => projSkip

/-- projProduce:
```
D :: ⟦Γ⟧ ⊢ produce V ⇐ ⟦A⟧ & d   [produce]
└─ D_V :: ⟦Γ⟧ ⊢ V ⇐ ⟦A⟧

    ↦   (destination x : A present)

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (x := e_V); skip : TVoid   [assign]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : A
└─ Γ ⊢ skip : TVoid   [skip]
```
With no destination (a `TVoid` command — the body, or a control-flow path with
no `x : A` in context), the produced value has nowhere to go and projects to the
empty statement list. -/
partial def projProduce (dest : Option VariableMd) (md : Md) (v : FGLValue) : ProjM (List StmtExprMd) :=
  match dest with
  | some d => pure [mkLaurel md (.Assign [d] (projectValue v))]
  | none => pure []

/-- projVarDecl:
```
D :: ⟦Γ⟧ ⊢ varDecl y T M N ⇐ ⟦A⟧ & d
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ T & d
└─ D_N :: ⟦Γ⟧, y:T ⊢ N ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (var y : T; e⃗_M; e⃗_N) : TVoid   [varDecl]
├─ ⟦D_M⟧ᵧ⁻¹ :: Γ, y : T ⊢ e⃗_M : TVoid
└─ ⟦D_N⟧ₓ⁻¹ :: Γ, x : A, y : T ⊢ e⃗_N : TVoid
```
-/
partial def projVarDecl (dest : Option VariableMd) (md : Md) (name : String) (ty : LowType)
    (init : FGLProducer) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let nameVar : VariableMd := ⟨.Local { text := name }, md.getD .unknown⟩
  let decl := mkLaurel md (.Var (.Declare { name := { text := name }, type := mkHighTypeMd md (liftType ty) }))
  projDecl decl
  let initStmts ← proj (some nameVar) init
  let bodyStmts ← proj dest body
  pure (initStmts ++ bodyStmts)

/-- projAssign:
```
D :: ⟦Γ⟧ ⊢ assign y M K ⇐ ⟦A⟧ & d
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ ⟦Γ(y)⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (e⃗_M; e⃗_K) : TVoid   [assign]
├─ ⟦D_M⟧ᵧ⁻¹ :: Γ, y : Γ(y) ⊢ e⃗_M : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projAssign (dest : Option VariableMd) (_md : Md) (target : FGLValue)
    (val : FGLProducer) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let valStmts ← proj (some (projectVarTarget target)) val
  let bodyStmts ← proj dest body
  pure (valStmts ++ bodyStmts)

/-- projIfThenElse:
```
D :: ⟦Γ⟧ ⊢ ifThenElse V M N K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d
├─ D_N :: ⟦Γ⟧ ⊢ N ⇐ ⟦A⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (if e_V then {e⃗_M} else {e⃗_N}); e⃗_K : TVoid   [if]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
├─ ⟦D_M⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_M : TVoid
├─ ⟦D_N⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_N : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projIfThenElse (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (thn els after : FGLProducer) : ProjM (List StmtExprMd) := do
  let thnStmts ← proj dest thn
  let elsStmts ← proj dest els
  -- The Laurel resolver types BOTH `if` branches and rejects a value branch paired with
  -- an empty (void) branch (incompatible types, e.g. 'int' and 'void'). When one branch
  -- is empty, emit a one-armed `if` (`IfThenElse` takes `elseBranch : Option`); for an
  -- empty THEN, flip the condition so only the else runs.
  let ite : StmtExprMd :=
    match thnStmts.isEmpty, elsStmts.isEmpty with
    | true, true => mkLaurel md (.Block [] none)
    | false, true => mkLaurel md (.IfThenElse (projectValue cond) (mkLaurel md (.Block thnStmts none)) none)
    | true, false =>
      -- Empty THEN: emit only the else under the negated condition. `cond` was checked
      -- at `.TBool`, so it projects to a bool — negate with the boolean `$not` wrapper
      -- (NOT `Any_to_bool(PNot ·)`, which assumes an Any-typed cond and yields an
      -- arrow-type mismatch when cond is already bool, e.g. `if x > 10: pass`).
      let negCond := mkLaurel md (.StaticCall "$not" [projectValue cond])
      mkLaurel md (.IfThenElse negCond (mkLaurel md (.Block elsStmts none)) none)
    | false, false =>
      mkLaurel md (.IfThenElse (projectValue cond) (mkLaurel md (.Block thnStmts none))
        (some (mkLaurel md (.Block elsStmts none))))
  let afterStmts ← proj dest after
  pure ([ite] ++ afterStmts)

/-- projWhileLoop:
```
D :: ⟦Γ⟧ ⊢ whileLoop V M K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
├─ D_M :: ⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (while e_V {e⃗_M}); e⃗_K : TVoid   [while]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
├─ ⟦D_M⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_M : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projWhileLoop (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (body after : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  let bodyBlock := mkLaurel md (.Block bodyStmts none)
  let loop := mkLaurel md (.While (projectValue cond) [] none bodyBlock false)
  let afterStmts ← proj dest after
  pure ([loop] ++ afterStmts)

/-- projProcedureCall:
```
D :: ⟦Γ⟧ ⊢ procedureCall f [Vᵢ] [outⱼ : Tⱼ] K ⇐ ⟦A⟧ & d
├─ D_Vᵢ :: ⟦Γ⟧ ⊢ Vᵢ ⇐ ⟦Aᵢ⟧
└─ D_K :: ⟦Γ⟧, outⱼ:Tⱼ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (var out₁:T₁; ...; var outₙ:Tₙ; (out₁,...,outₙ) := f(e_Vᵢ); e⃗_K) : TVoid   [call]
├─ ⟦D_Vᵢ⟧⁻¹ :: Γ ⊢ e_Vᵢ : Aᵢ
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A, out₁:T₁, ..., outₙ:Tₙ ⊢ e⃗_K : TVoid
```
-/
partial def projProcedureCall (dest : Option VariableMd) (md : Md) (callee : String)
    (args : List FGLValue) (outputs : List (String × LowType)) (body : FGLProducer) : ProjM (List StmtExprMd) := do
  for (n, ty) in outputs do
    projDecl (mkLaurel md (.Var (.Declare { name := { text := n }, type := mkHighTypeMd md (liftType ty) })))
  let targets : List VariableMd := outputs.map fun (n, _) => ⟨.Local { text := n }, md.getD .unknown⟩
  let call := mkLaurel md (.Assign targets (mkLaurel md (.StaticCall { text := callee } (args.map projectValue))))
  let bodyStmts ← proj dest body
  pure ([call] ++ bodyStmts)

/-- projAssert:
```
D :: ⟦Γ⟧ ⊢ assert V K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (assert e_V); e⃗_K : TVoid   [assert]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projAssert (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (body : FGLProducer) (summary : Option String := none) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  pure ([mkLaurel md (.Assert (projectValue cond) summary)] ++ bodyStmts)

/-- projAssume:
```
D :: ⟦Γ⟧ ⊢ assume V K ⇐ ⟦A⟧ & d
├─ D_V :: ⟦Γ⟧ ⊢ V ⇐ bool
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ (assume e_V); e⃗_K : TVoid   [assume]
├─ ⟦D_V⟧⁻¹ :: Γ ⊢ e_V : bool
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projAssume (dest : Option VariableMd) (md : Md) (cond : FGLValue)
    (body : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  pure ([mkLaurel md (.Assume (projectValue cond))] ++ bodyStmts)

/-- projLabeledBlock:
```
D :: ⟦Γ⟧ ⊢ labeledBlock l M K ⇐ ⟦A⟧ & d
├─ D_M :: ⟦Γ⟧, l ⊢ M ⇐ ⟦A⟧ & d
└─ D_K :: ⟦Γ⟧ ⊢ K ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ {e⃗_M}_l; e⃗_K : TVoid   [labeledBlock]
├─ ⟦D_M⟧ₓ⁻¹ :: Γ, x : A, l ⊢ e⃗_M : TVoid
└─ ⟦D_K⟧ₓ⁻¹ :: Γ, x : A ⊢ e⃗_K : TVoid
```
-/
partial def projLabeledBlock (dest : Option VariableMd) (md : Md) (label : String)
    (body after : FGLProducer) : ProjM (List StmtExprMd) := do
  let bodyStmts ← proj dest body
  let bodyBlock := mkLaurel md (.Block bodyStmts (some label))
  let afterStmts ← proj dest after
  pure ([bodyBlock] ++ afterStmts)

/-- projExit:
```
D :: ⟦Γ⟧ ⊢ exit l ⇐ ⟦A⟧ & d

    ↦

⟦D⟧ₓ⁻¹ :: Γ, x : A ⊢ exit l : TVoid   [exit]
└─ l ∈ Γ
```
-/
partial def projExit (md : Md) (label : String) : ProjM (List StmtExprMd) :=
  pure [mkLaurel md (.Exit label)]

/-- projSkip:
```
⟦skip⟧ₓ⁻¹ :: Γ, x : A ⊢ skip : TVoid   [skip]
```
-/
partial def projSkip : ProjM (List StmtExprMd) := pure []

end

/-- Run projection of a procedure body. The body is a command (`TVoid`), so it
    has no destination: its return value reaches `LaurelResult` only through the
    explicit `LaurelResult := e` assignments Translation emits for `return e`, not
    through a tail value. Declarations hoisted to top. -/
def projectProducer (prod : FGLProducer) : List StmtExprMd :=
  let (stmts, decls) := (proj none prod).run
  decls ++ stmts

/-- Run projection, return as a block. -/
def projectBody (md : Md) (prod : FGLProducer) : StmtExprMd :=
  mkLaurel md (.Block (projectProducer prod) none)

/-! ## Entry Point

`fullElaborate` orchestrates both passes. Pass 1 iterates to a fixpoint on
grades. Pass 2 elaborates each procedure at its final grade and projects
back to Laurel. Also emits auxiliary datatypes (TypeTag, Composite, Field,
Box) and hole procedure declarations needed by the output program. -/

/-- Name the top-level constructor of a `StmtExpr`, for elaboration-failure diagnostics. -/
private def stmtKindName (e : StmtExpr) : String :=
  match e with
  | .IfThenElse .. => "IfThenElse" | .Block .. => "Block" | .While .. => "While"
  | .Exit .. => "Exit" | .Return .. => "Return" | .Assign .. => "Assign"
  | .IncrDecr .. => "IncrDecr" | .Var .. => "Var" | .StaticCall .. => "StaticCall"
  | .InstanceCall .. => "InstanceCall" | .New .. => "New" | .Assert .. => "Assert"
  | .Assume .. => "Assume" | .Hole .. => "Hole"
  | .AsType .. => "AsType" | .IsType .. => "IsType" | .ReferenceEquals .. => "ReferenceEquals"
  | .PureFieldUpdate .. => "PureFieldUpdate" | _ => "<other>"

/-- Diagnostic-only: when a proc body (a Block) fails to elaborate, find the first statement index
    `k` where prefix `take k` fails while `take (k-1)` succeeds, and name that statement's
    constructor + source. Pure observability via prefix-bisection; does not change results. -/
private partial def firstFailingStmt (procEnv : ElabEnv) (st : ElabState) (bodyExpr : StmtExprMd)
    (retTy : HighType) (g : Grade) (depth : Nat := 0) : String :=
  match bodyExpr.val with
  | .Block stmts _ =>
    let n := stmts.length
    let prefixOk (k : Nat) : Bool :=
      (match (checkProducers (stmts.take k) retTy g).run procEnv |>.run st with | .ok _ => true | .error _ => false)
    let rec find (k : Nat) : String :=
      if k > n then "<all prefixes elaborate; failure is whole-body/grade-level>"
      else if prefixOk k then find (k + 1)
      else
        match stmts[k - 1]? with
        | some s =>
          let loc := toString (Std.format s.source)
          let gradeProbe : String :=
            let names := [(Grade.pure, "pure"), (Grade.proc, "proc"), (Grade.err, "err"), (Grade.heap, "heap"), (Grade.heapErr, "heapErr")]
            let oks := names.filterMap (fun (gg, nm) =>
              if (match (checkProducer s [] retTy gg).run procEnv |>.run st with | .ok _ => true | .error _ => false) then some nm else none)
            s!" [elaborates-at: {String.intercalate "," oks}]"
          let here := s!"#{k}/{n}: {stmtKindName s.val} at {loc}{gradeProbe}"
          -- If the culprit is itself a nested Block (e.g. a with/try desugar) and we have not
          -- recursed too deep, drill into it to name the innermost failing statement. This uses
          -- the same env/state (an approximation), so it pinpoints the construct kind even though
          -- nested env extensions are not re-threaded.
          match s.val with
          | .Block _ _ =>
            if depth < 6 then s!"{here} -> {firstFailingStmt procEnv st s retTy g (depth+1)}"
            else here
          | .While _ _ _ lb _ =>
            if depth < 6 then s!"{here} (loop body) -> {firstFailingStmt procEnv st lb retTy g (depth+1)}"
            else here
          | .IfThenElse _ thn _ =>
            if depth < 6 then s!"{here} (then) -> {firstFailingStmt procEnv st thn retTy g (depth+1)}"
            else here
          | .Assign _ value =>
            -- Drill into an Assign's RHS: the failure is often in the value producer (e.g. a
            -- ternary whose branch is a constructor block). Name the RHS kind; if it is an
            -- IfThenElse/Block, recurse into it so the innermost failing construct is reported.
            -- Diagnostic-only (same env/state approximation).
            if depth < 6 then
              let rhsKind := stmtKindName value.val
              match value.val with
              | .IfThenElse _ rthn _ => s!"{here} (RHS={rhsKind} then) -> {firstFailingStmt procEnv st rthn retTy g (depth+1)}"
              | .Block _ _ => s!"{here} (RHS Block) -> {firstFailingStmt procEnv st value retTy g (depth+1)}"
              | _ => s!"{here} (RHS={rhsKind})"
            else here
          | _ => here
        | none => "<index out of range>"
    find 1
  | _ => s!"(non-Block {stmtKindName bodyExpr.val})"

/-- Entry point: elaborates a Laurel program. Returns the elaborated program
    and a list of procedure names that failed to elaborate (emitted unchanged). -/
def fullElaborate (program : Laurel.Program) (runtime : Laurel.Program := default) (initialGrades : Std.HashMap String Grade := {}) : Except String (Laurel.Program × List String) := do
  let typeEnv := buildElabEnvFromProgram program runtime
  let baseEnv : ElabEnv := { typeEnv := typeEnv, program := program, runtime := runtime }

  -- PASS 1: Coinductive fixpoint iteration
  let mut knownGrades : Std.HashMap String Grade := initialGrades
  let mut changed := true
  while changed do
    changed := false
    for proc in program.staticProcedures do
      let bodyOpt := match proc.body with
        | .Transparent b => some b
        | .Opaque _ (some impl) _ => some impl
        | _ => none
      match bodyOpt with
      | some bodyExpr =>
        let extEnv := (proc.inputs ++ proc.outputs).foldl
          (fun (e : ElabTypeEnv) p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
        let inputList := proc.inputs.map fun p => (p.name.text, p.type.val)
        let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades, procInputs := inputList }
        -- The body is a command (DPS): checked at TVoid, not the return type. The
        -- return value flows only through explicit `LaurelResult := e` assigns.
        match tryGrades proc.name.text procEnv bodyExpr .TVoid [.pure, .proc, .err] with
        | some g =>
          -- A proc that declares an `Error` output can throw, so its grade is at least `.err`.
          -- Without this join a caller elaborated at `.pure`/`.proc` cannot call it
          -- (leftResidual .err _ = none) and the call is silently dropped. This uses the same
          -- Error-output identity test as PASS 2's `resultOutputs` filter (:1601), so both passes
          -- agree on "can throw": a multi-output non-error helper (e.g. returning `(int, string)`)
          -- is not lifted to `.err`, keeping the emitted arity matched to what callers elaborate.
          let hasErrOut := proc.outputs.any fun o => eraseType o.type.val == .TCore "Error"
          let g := if hasErrOut then Grade.join g .err else g
          if knownGrades[proc.name.text]? != some g then
            knownGrades := knownGrades.insert proc.name.text g
            changed := true
        | none => pure ()
      | none => pure ()

  -- PASS 2: Elaborate each proc with final grades
  let mut procs : List Laurel.Procedure := []
  let mut allHoles : List (String × Bool × List (String × HighType) × HighType) := []
  let mut elabFailures : List String := []
  let mut globalCounter : Nat := 0
  for proc in program.staticProcedures do
    let bodyOpt2 : Option (StmtExprMd × Bool) := match proc.body with
      | .Transparent b => some (b, false)
      | .Opaque _ (some impl) _ => some (impl, true)
      | _ => none
    match bodyOpt2 with
    | some (bodyExpr, isOpaque) =>
      let extEnv := (proc.inputs ++ proc.outputs).foldl
        (fun (e : ElabTypeEnv) p => { e with names := e.names.insert p.name.text (.variable p.type.val) }) typeEnv
      let inputList := proc.inputs.map fun p => (p.name.text, p.type.val)
      let procEnv : ElabEnv := { baseEnv with typeEnv := extEnv, procGrades := knownGrades, procInputs := inputList }
      let g := knownGrades[proc.name.text]?.getD .pure
      -- Elaborate preconditions: a `requires` is a pure value of type bool, not an
      -- effect-sequenced statement, so it elaborates with the value judgment
      -- (checkValue) rather than the producer judgment. checkValue synthesizes the
      -- term and applies subtyping coercions — from_int/from_str on argument
      -- literals (the runtime operators take Any parameters) and Any_to_bool on the
      -- Any-typed result — then projectValue yields the single Core expression.
      -- Holes are collected as for bodies.
      let mut elabPreconditions : List Condition := []
      for pre in proc.preconditions do
        let preSt : ElabState := { freshCounter := globalCounter }
        match (checkValue pre.condition .TBool).run procEnv |>.run preSt with
        | .ok (preVal, preSt') =>
          globalCounter := preSt'.freshCounter
          let newHoles := (preSt'.usedHoles.map fun (name, det, outTy) => (name, det, inputList, outTy)).filter
            (fun (n, _, _, _) => !allHoles.any (fun (n2, _, _, _) => n == n2))
          allHoles := allHoles ++ newHoles
          elabPreconditions := elabPreconditions ++ [{ pre with condition := ⟨(projectValue preVal).val, pre.condition.source⟩ }]
        | .error reason =>
          -- A precondition whose coercions fail to elaborate is recorded into `elabFailures`, which
          -- `pyAnalyzeV2ToCore` surfaces as a fatal diagnostic (same handling as a body-elaboration
          -- failure at :1611). This keeps the `--v2` path from reporting success on a file whose
          -- `requires` was carried through un-coerced and therefore never actually checked.
          elabFailures := elabFailures ++ [s!"{proc.name.text} precondition (REASON={reason})"]
          elabPreconditions := elabPreconditions ++ [pre]
      let proc := { proc with preconditions := elabPreconditions }
      -- Capture `st` AFTER the precondition loop: that loop advances `globalCounter`
      -- (via `preSt'.freshCounter`), so binding `st` earlier would reuse a stale counter
      -- and let body-elaboration fresh names collide with precondition fresh names.
      let st : ElabState := { freshCounter := globalCounter }
      match (checkProducer bodyExpr [] .TVoid g).run procEnv |>.run st with
      | .ok (fgl, st') =>
        globalCounter := st'.freshCounter
        let newHoles := (st'.usedHoles.map fun (name, det, outTy) => (name, det, inputList, outTy)).filter
          (fun (n, _, _, _) => !allHoles.any (fun (n2, _, _, _) => n == n2))
        allHoles := allHoles ++ newHoles
        let projected := projectBody bodyExpr.source fgl
        let md := bodyExpr.source
        let errOutParam : Laurel.Parameter := { name := { text := "maybe_except" }, type := mkHighTypeMd md (.UserDefined { text := "Error" }) }
        let resultOutputs := proc.outputs.filter fun o => eraseType o.type.val != .TCore "Error"
        let mkBody (b : StmtExprMd) : Laurel.Body :=
          if isOpaque then .Opaque [] (some b) [] else .Transparent b
        match g with
        | .err =>
          procs := procs ++ [{ proc with
            outputs := resultOutputs ++ [errOutParam]
            body := mkBody projected }]
        | _ =>
          procs := procs ++ [{ proc with body := mkBody projected }]
      | .error reason =>
        -- On elaboration failure the proc is emitted unchanged (so downstream has a well-formed
        -- program to point at) and the reason is recorded into `elabFailures`. This DOES abort the
        -- `--v2` run, but only through an implicit chain: `pyAnalyzeV2ToCore` maps each entry via
        -- `Message.fromString`, whose kind defaults to `UserError`; the pipeline caller
        -- (`PyAnalyzeLaurel.runPipeline`) then throws on the first message whose `impact.isFatal`,
        -- and `UserError` is fatal. So the file is aborted, not partially verified — but the
        -- soundness rests on that default classification. If `fromMessage`'s default is ever changed
        -- (or these are reclassified non-fatal), an un-elaborated proc could reach the verifier;
        -- keep them fatal, or make callers check `elabFailures` explicitly.
        let detail := firstFailingStmt procEnv st bodyExpr .TVoid g
        elabFailures := elabFailures ++ [s!"{proc.name.text} (grade {repr g}; REASON={reason}; {detail})"]
        procs := procs ++ [proc]
    | none => procs := procs ++ [proc]
  -- Hole procs are emitted because grade inference may introduce them.
  -- Everything else (heap, box types, auxiliary datatypes) is owned by downstream passes.
  let holeProcs := allHoles.map fun (name, deterministic, inputs, outTy) =>
    let params := inputs.map fun (pName, pType) =>
      ({ name := { text := pName }, type := ⟨pType, .unknown⟩ } : Laurel.Parameter)
    let outputParam : Laurel.Parameter := { name := { text := "result" }, type := ⟨outTy, .unknown⟩ }
    { name := { text := name }
      inputs := if deterministic then params else []
      outputs := [outputParam]
      preconditions := []
      decreases := none
      body := .Opaque [] none [] : Laurel.Procedure }
  let result : Laurel.Program :=
    { program with
      staticProcedures := holeProcs ++ procs }
  pure (result, elabFailures)

end
end Strata.FineGrainLaurel

