/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataMantle.WF
public import StrataDDM.AST
public import StrataDDM.Integration.Lean.OfAstM
-- Private: translating a checked IR needs the environment representation at codegen time.
import StrataMantle.Env.WF
import StrataMantle.FloatText
import StrataDDM.Format
import StrataDDM.Ion
import StrataDDM.Integration.Lean -- shake: keep
import Std.Data.HashMap
import Std.Data.HashSet

open StrataDDM

set_option autoImplicit false

/-!
# Printing the IR, through a Strata dialect

The IR prints by translation into the DDM dialect `Mantle`, defined below, which DDM's
formatter lays out.  `StrataMantle/DDMRead.lean` reads the text back.

* `Module.format`: a `Module`, printed, with constants folded by default;
* `Module.Raw.format`, `Func.format`: an unchecked module or one function, printed with the
  given options;
* `PrintOptions.full`: every constant on its own line;
* `ToDDM.nameText`, `ToDDM.valNameText`: a name, and a value's name, as printed.

`toString` prints a `Module` folded and a `Module.Raw` in full.

## The printed form

```
module m {
  func @m.f(%x.0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%x.0 : py.Value):
      %int.0 : py.Value = py.intLit(1)
      %sum.0 : py.Value = py.add(%x.0, %int.0) ^propagate.0()
      %ret.0 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value](%sum.0)
      ret(%ret.0)
    propagate.0(%exc.0 : py.Value):
      %exc.1 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value](%exc.0)
      ret(%exc.1)
  }
}
```

* A value prints as its name, `Func.names` at its id: `%x.0`.  Ids are not printed, so
  renumbering a function changes nothing printed.  Every value is printed with its type where
  it is defined.
* A block prints as its label and parameters.  The entry block's parameters are the
  function's, so they appear twice: on the signature and on the entry.
* An application prints as its operation, then its type arguments in brackets, its operands
  in parentheses, its successors, each `^label(args)`, and its regions, each in braces.  Empty
  brackets and parentheses are left out: `py.noneLit`.  A constructor prints as any
  application does: `base.ok[py.Value, py.Value](%sum.0)`.
* A successor binds only the values the site passes.  The operation supplies the rest: above,
  `py.add` passes the exception to `propagate.0`.
* A terminator is a block's last line, an application without a result:
  `base.Except.case[base.Int, base.Int](%e.0) ^ok.0() ^err.0()`.  The base's control flow
  drops `base.`: `jump ^done.0(%v.0)`, `branch(%c.0) ^some.0() ^none.0()` and `unreachable`.
  A jump to the exit is `ret(%ret.0)`.
* A name prints dotted, as one identifier, escaped whole when a segment needs it:
  `@|m.<module>|`.  A numeric segment prints as its digits: `entry.0`.  A function's name is
  marked `@`, both where it is defined and where a constant names it: `ret(@m.counter)`.
* A literal carries no type tag, and its form fixes its type exactly, with no widening.  An
  integer, `5` or `-1`, is a `base.Int`.  A float always has a decimal point or an exponent,
  `1.0`, `0.0025` or `1e22`, and is the shortest decimal that reads back as it, or `inf`,
  `-inf` or `nan`; it is a `base.Float64`.  A boolean is `true` or `false`, a string `"…"`,
  the unit `unit` and a function pointer `@m.f`.
* An operation's regions follow the rest of its line, each opening with its entry block,
  whose parameters are the region's arguments:

```
%r.0 : base.Int = demo.if[base.Int](%c.0) {
  then.0():
    ret(%x.0)
} {
  else.0():
    ret(%y.0)
}
```

By default each constant a function uses is written at its uses, and its own line is
dropped: `%int.0 : py.Value = py.intLit(1)` rather than `%c.0 : base.Int = const 1` and
`%int.0 : py.Value = py.intLit(%c.0)`.  The folded form is in the same dialect.

Two names do not read back as printed: one whose string segment is empty, all digits or
contains `.`, and one that is a keyword of the dialect as a whole, such as `ret` or `unit`.
-/

namespace Strata.Mantle

namespace DDM

-- Public: the reader parses this dialect and reads its AST.
public section

#dialect
dialect Mantle;

/*
  A hierarchical name, printed dotted as one identifier, escaped whole when it needs to be:
  `py.Value`, `entry.0`, `@|m.<module>|`.  The reader splits it at each `.`, and reads an
  all-digit segment as a numeric one.
*/
category MName;
op name (s : Ident) : MName => s;

category MInt;
op natInt (x : Num) : MInt => x;
op negInt (x : Num) : MInt => "-" x;

/* A float always has a decimal point or an exponent, so it never reads as an integer. */
category MFloat;
op floatPos (d : Decimal) : MFloat => d;
op floatNeg (d : Decimal) : MFloat => "-" d;
op floatInf () : MFloat => "inf";
op floatNegInf () : MFloat => "-" "inf";
op floatNan () : MFloat => "nan";

/* Type expressions.  `#i` is a type variable; a type constructor with no arguments
   prints as its bare name. */
category MType;
op tyVar (i : Num) : MType => "#" i;
op tyPrim (n : MName) : MType => n;
op tyApp (n : MName, args : CommaSepBy MType) : MType => @[prec(0)] n "(" args ")";

/* A function of the module, marked `@` as in LLVM. */
category MFuncName;
op funcName (n : MName) : MFuncName => "@" n:0;

/* A value, by its name: `%x.1`. */
category MVal;
op valName (n : MName) : MVal => "%" n:0;

category MValDecl;
op valDecl (v : MVal, ty : MType) : MValDecl => @[prec(0)] v " : " ty;

/* A literal.  Its form fixes its type: an integer is a `base.Int`, never a `base.Float64`. */
category MConst;
op constUnit () : MConst => "unit";
op constBool (b : Bool) : MConst => b:0;
op constInt (i : MInt) : MConst => i:0;
op constFloat (f : MFloat) : MConst => f:0;
op constStr (s : Str) : MConst => s;
op constFunc (f : MFuncName) : MConst => f;

/* An operand: a value, or a constant written where it is used. */
category MOperand;
op operandVal (v : MVal) : MOperand => v;
op operandConst (c : MConst) : MOperand => c;

/* An operation's operands, in parentheses, absent rather than empty. */
category MOperands;
op operands (args : CommaSepBy MOperand) : MOperands => "(" args ")";

/* A successor of an operation: a block label and the arguments the site binds, marked `^`
   as in MLIR so that it reads apart from the operands before it.  Several follow one
   another. */
category MSucc;
op succ (target : MName, args : CommaSepBy MOperand) : MSucc =>
  @[prec(0)] " ^" target "(" args ")";

/* An operation's type arguments, likewise absent rather than empty. */
category MTypeArgs;
op typeArgs (args : CommaSepBy MType) : MTypeArgs => "[" args "]";

/* A line's newline leads it, inside the `indent` that encloses it, so each line indents at
   its own level. */
/* Declared ahead of their operations: an instruction holds regions, which hold blocks,
   which hold instructions. */
category MBlock;
category MRegion;

category MInsn;
op insnConst (result : MValDecl, c : MConst) : MInsn =>
  @[prec(0)] "\n" result " = const " c;
/* An application: a constructor's as any other operation's. */
op insnApply (result : MValDecl, name : MName, tyArgs : Option MTypeArgs,
              args : Option MOperands, succs : Seq MSucc,
              regions : Seq MRegion) : MInsn =>
  @[prec(0)] "\n" result " = " name tyArgs args succs regions;

category MTerm;
/* A jump to the exit of the enclosing body, passing its arguments. */
op termRet (args : Option MOperands) : MTerm => @[prec(0)] "\n" "ret" args;
/* A terminal operation: an application's line without a result. */
op termApply (name : MName, tyArgs : Option MTypeArgs, args : Option MOperands,
              succs : Seq MSucc, regions : Seq MRegion) : MTerm =>
  @[prec(0)] "\n" name tyArgs args succs regions;

op block (label : MName, params : CommaSepBy MValDecl, instrs : Seq MInsn, term : MTerm)
    : MBlock =>
  @[prec(0)] "\n" label "(" params "):" indent(2, instrs term);

/* A region: its blocks in braces, entry first, so it opens with its arguments. */
op region (blocks : Seq MBlock) : MRegion => @[prec(0)] " {" indent(2, blocks) "\n" "}";

category MFunc;
op func (name : MFuncName, params : CommaSepBy MValDecl, retType : MType, blocks : Seq MBlock)
    : MFunc =>
  @[prec(0)] "\n" "func " name "(" params ") -> " retType " {" indent(2, blocks) "\n" "}";

op moduleDecl (name : MName, funcs : Seq MFunc) : Command =>
  @[prec(0)] "module " name " {" indent(2, funcs) "\n" "}\n";
#end

-- The generated AST binds its annotation type implicitly, so this command needs
-- `autoImplicit`.
set_option autoImplicit true in
#strata_gen Mantle

end

end DDM

/-- How to print. -/
public structure PrintOptions where
  /-- Write each constant a function uses at its uses, instead of on a line of its own. -/
  foldConsts : Bool := true

/-- Print in full: every constant on its own line. -/
public def PrintOptions.full : PrintOptions := { foldConsts := false }

/-! ## The translation

One function per level.  It prints any IR, well formed or not. -/

-- Every node is annotated `.none`: the IR's annotation type has no map to `SourceRange`.

namespace ToDDM

open Strata.Mantle.DDM

/-- A name's text: its segments, dotted.  The root alone is `_`. -/
public def nameText : Name → String
  | .base => "_"
  | .str .base s => s
  | .num .base i => toString i
  | .str pre s => s!"{nameText pre}.{s}"
  | .num pre i => s!"{nameText pre}.{i}"

/-- A name, as one identifier. -/
def name (n : Name) : MName SourceRange := .name .none ⟨.none, nameText n⟩

def int (i : Int) : MInt SourceRange :=
  match i with
  | .ofNat n => .natInt .none ⟨.none, n⟩
  | .negSucc n => .negInt .none ⟨.none, n + 1⟩

/-- A type expression. -/
def type {env : Env Unit} {scope : Nat} (e : TypeExpr env scope) : MType SourceRange :=
  e.fold (fun i => .tyVar .none ⟨.none, i⟩) fun n as =>
    if as.isEmpty then .tyPrim .none (name n) else .tyApp .none (name n) ⟨.none, as⟩

/-- A function's name, marked `@`. -/
def funcName (n : Name) : MFuncName SourceRange := .funcName .none (name n)

/-- A value's name, as printed: `%x.1`. -/
public def valNameText (n : Name) : String := s!"%{nameText n}"

/-- The name `v` prints as: its name, or `?id` if it has none.  Only an ill-formed function
has an unnamed value. -/
def valNameOf (names : Array Name) (v : ValId) : Name :=
  names[v.id]?.getD (.str .base s!"?{v.id}")

def val (names : Array Name) (v : ValId) : MVal SourceRange :=
  .valName .none (name (valNameOf names v))

def valDecl {env : Env Unit} (names : Array Name) (d : ValDecl env) : MValDecl SourceRange :=
  .valDecl .none (val names d.id) (type d.type)

/-- Type arguments, absent when there are none. -/
def typeArgs {env : Env Unit} (as : Array (TypeExpr env 0)) :
    Ann (Option (MTypeArgs SourceRange)) SourceRange :=
  if as.isEmpty then ⟨.none, none⟩
  else ⟨.none, some (.typeArgs .none ⟨.none, as.map type⟩)⟩

/-- A float: the shortest decimal that reads back as it, or `inf`, `-inf` or `nan`.  The
decimal always has a point or an exponent: `1.0`, `0.1`, `1e22`. -/
def float (f : Float) : MFloat SourceRange :=
  match FloatText.shortest f with
  | some d =>
    let v : StrataDDM.Decimal := { mantissa := d.mantissa, exponent := d.exponent }
    if d.neg then .floatNeg .none ⟨.none, v⟩ else .floatPos .none ⟨.none, v⟩
  | none =>
    if f.isNaN then .floatNan .none
    else if f < 0 then .floatNegInf .none else .floatInf .none

def const : Const → MConst SourceRange
  | .unit => .constUnit .none
  | .bool b => .constBool .none ⟨.none, b⟩
  | .int i => .constInt .none (int i)
  | .float f => .constFloat .none (float f)
  | .str s => .constStr .none ⟨.none, s⟩
  | .func target => .constFunc .none (funcName target)

/-! ### Folding constants

With `PrintOptions.foldConsts`, the default, each constant a function uses is written at each
of its uses, as an operand, and its own line is dropped.  A constant it never uses keeps its
line.  An application's result is never folded. -/

/-- The constants to write in place, by value id. -/
abbrev Folded := Std.HashMap Nat Const

/-- What printing a function's body needs: the constants to fold, and the values' names. -/
structure Cx where
  fold : Folded
  names : Array Name

/-- An operand: the constant `v` names, if it is folded, else `v`. -/
def operand (cx : Cx) (v : ValId) : MOperand SourceRange :=
  match cx.fold[v.id]? with
  | some c => .operandConst .none (const c)
  | none => .operandVal .none (val cx.names v)

def operandList (cx : Cx) (vs : Array ValId) :
    Ann (Array (MOperand SourceRange)) SourceRange :=
  ⟨.none, vs.map (operand cx)⟩

/-- An operation's operands, in parentheses, absent when there are none. -/
def operands (cx : Cx) (vs : Array ValId) :
    Ann (Option (MOperands SourceRange)) SourceRange :=
  if vs.isEmpty then ⟨.none, none⟩ else ⟨.none, some (.operands .none (operandList cx vs))⟩

/-- An operation's successors, each `^target(args)`. -/
def succs (cx : Cx) (ks : Array BlockValue) :
    Ann (Array (MSucc SourceRange)) SourceRange :=
  ⟨.none, ks.map fun k => .succ .none (name k.target.name) (operandList cx k.args)⟩

/-- What a function's body defines as constants, by id, and the ids its operands and
successor arguments use, regions included. -/
structure Uses where
  consts : Std.HashMap Nat Const := {}
  used : Std.HashSet Nat := {}

namespace Uses

def use (u : Uses) (vs : Array ValId) : Uses :=
  { u with used := vs.foldl (fun s v => s.insert v.id) u.used }

def useSuccs (u : Uses) (ks : Array BlockValue) : Uses :=
  ks.foldl (fun u k => u.use k.args) u

mutual

def regionList {env : Env Unit} {α : Type} (u : Uses) : List (Region env α) → Uses
  | [] => u
  | ⟨⟨blocks⟩⟩ :: rs => regionList (blockList u blocks) rs

def blockList {env : Env Unit} {α : Type} (u : Uses) : List (Block env α) → Uses
  | [] => u
  | ⟨_, _, ⟨instrs⟩, .apply _ _ _ args ks ⟨regions⟩, _⟩ :: bs =>
    blockList (regionList ((insnList u instrs).use args |>.useSuccs ks) regions) bs

def insnList {env : Env Unit} {α : Type} (u : Uses) : List (Instruction env α) → Uses
  | [] => u
  | .const _ d c :: is => insnList { u with consts := u.consts.insert d.id.id c } is
  | .apply _ _ _ _ args ks ⟨regions⟩ :: is =>
    insnList (regionList (u.use args |>.useSuccs ks) regions) is

end

end Uses

/-- The constants of `blocks` to fold: those used at least once. -/
def folded {env : Env Unit} {α : Type} (blocks : Array (Block env α)) : Folded :=
  let u := Uses.blockList {} blocks.toList
  u.consts.filter fun i _ => u.used.contains i

mutual

/-- A terminator.  The base's control flow prints without its namespace, and a jump to the
exit as `ret`. -/
def term {env : Env Unit} {α : Type} (cx : Cx) : Terminator env α → MTerm SourceRange
  | .apply _ r tyArgs args ks ⟨regions⟩ =>
    let generic (n : Name) :=
      .termApply .none (name n) (typeArgs tyArgs.toArray) (operands cx args) (succs cx ks)
        ⟨.none, ⟨regionList cx regions⟩⟩
    if r.name == bn "jump" then
      match ks with
      | #[k] => if k.target == Label.exit then .termRet .none (operands cx k.args)
        else generic (.str .base "jump")
      | _ => generic (.str .base "jump")
    else if r.name == bn "branch" then generic (.str .base "branch")
    else if r.name == bn "unreachable" then generic (.str .base "unreachable")
    else generic r.name

def insn {env : Env Unit} {α : Type} (cx : Cx) : Instruction env α → MInsn SourceRange
  | .const _ d c => .insnConst .none (valDecl cx.names d) (const c)
  | .apply _ d r tyArgs args ks ⟨regions⟩ =>
    .insnApply .none (valDecl cx.names d) (name r.name) (typeArgs tyArgs.toArray)
      (operands cx args) (succs cx ks) ⟨.none, ⟨regionList cx regions⟩⟩

/-- Instructions, less the folded constants. -/
def insnList {env : Env Unit} {α : Type} (cx : Cx) :
    List (Instruction env α) → List (MInsn SourceRange)
  | [] => []
  | i :: is =>
    if cx.fold.contains i.result.id.id then insnList cx is
    else insn cx i :: insnList cx is

/-- A block, under its label. -/
def block {env : Env Unit} {α : Type} (cx : Cx) : Block env α → MBlock SourceRange
  | ⟨label, params, ⟨instrs⟩, t, _⟩ =>
    .block .none (name label.name) ⟨.none, params.map (valDecl cx.names)⟩
      ⟨.none, ⟨insnList cx instrs⟩⟩ (term cx t)

def blockList {env : Env Unit} {α : Type} (cx : Cx) :
    List (Block env α) → List (MBlock SourceRange)
  | [] => []
  | b :: bs => block cx b :: blockList cx bs

def regionList {env : Env Unit} {α : Type} (cx : Cx) :
    List (Region env α) → List (MRegion SourceRange)
  | [] => []
  | ⟨⟨blocks⟩⟩ :: rs => .region .none ⟨.none, ⟨blockList cx blocks⟩⟩ :: regionList cx rs

end

/-- A function.  Its parameters are the entry block's, so they are read from there. -/
def func {env : Env Unit} {α : Type} (opts : PrintOptions) (fn : Func env α) :
    MFunc SourceRange :=
  let cx : Cx := { fold := if opts.foldConsts then folded fn.blocks else {}, names := fn.names }
  .func .none (funcName fn.name)
    ⟨.none, (fn.blocks[0]?.map (·.params.map (valDecl cx.names))).getD #[]⟩
    (type fn.retType)
    ⟨.none, fn.blocks.map (block cx)⟩

def module {env : Env Unit} [base ⊑ env] {α : Type} (opts : PrintOptions)
    (m : Module.Raw env α) : DDM.Command SourceRange :=
  .moduleDecl .none (name m.name) ⟨.none, m.funcs.map (func opts)⟩

end ToDDM

/-! ## Rendering -/

namespace Print

def context : FormatContext := .ofDialects DDM.Mantle_map

def state : FormatState where
  openDialects := DDM.Mantle_map.toList.foldl (init := {}) fun s d => s.insert d.name

/-- Lay out a DDM term of this dialect. -/
def render (c : DDM.Command SourceRange) : String :=
  (mformat c.toAst context state).format.pretty

end Print

/-- The module, printed with the given options.  Folding a module that is not well formed can
print text that reads back as a different module. -/
public def Module.Raw.format {env : Env Unit} [base ⊑ env] {α : Type} (opts : PrintOptions)
    (m : Module.Raw env α) : String :=
  Print.render (ToDDM.module opts m)

/-- The module, printed in full. -/
public instance {env : Env Unit} [base ⊑ env] {α : Type} : ToString (Module.Raw env α) where
  toString := Module.Raw.format .full

/-- The module, printed, with constants folded by default. -/
public def Module.format {env : Env Unit} [base ⊑ env] {α : Type} (m : Module env α)
    (opts : PrintOptions := {}) : String :=
  m.raw.format opts

/-- The module, printed with constants folded. -/
public instance {env : Env Unit} [base ⊑ env] {α : Type} : ToString (Module env α) where
  toString m := m.format

/-- One function, printed with the given options, as a module with just it in.  Folding a
function that is not well formed can print text that reads back as a different function. -/
public def Func.format {env : Env Unit} {α : Type} (opts : PrintOptions) (fn : Func env α) :
    String :=
  Print.render (.moduleDecl .none (ToDDM.name fn.name) ⟨.none, #[ToDDM.func opts fn]⟩)

end Strata.Mantle
