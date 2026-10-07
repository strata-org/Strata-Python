/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataMantle.IR
public import StrataDDM.AST
-- Private: translating a checked IR needs the environment representation at codegen time.
import StrataMantle.Env.WF
import StrataDDM.Format
import StrataDDM.Ion
import StrataDDM.Integration.Lean -- shake: keep

open StrataDDM

set_option autoImplicit false

/-!
# Printing the IR, through a Strata dialect

The IR is printed by translating it into a DDM dialect and letting DDM's formatter lay it
out.  The dialect below is the surface syntax, and a DDM term goes to and from Ion.  Only the
printing direction is built here.

## What the annotations are

Every node of the generated AST is annotated `.none`: the IR's annotation type `α` has no
map to `SourceRange`.

## The shape it prints

```
module py.f {
  func @py.f(%0 : py.Value) -> base.Except(py.Value, py.Value) {
    entry.0(%0 : py.Value):
      %1 : base.String = const str "y"
      %2 : py.Value = py.undef %1
      %3 : base.Ref(py.Value) = base.refNew[py.Value] %2
      %4 : py.Value = py.add %0 %3 ^propagate.0()
      %5 : base.Except(py.Value, py.Value) = base.ok[py.Value, py.Value] %4
      ret %5
    propagate.0(%6 : py.Value):
      %7 : base.Except(py.Value, py.Value) = base.error[py.Value, py.Value] %6
      ret %7
  }
}
```

Every value is printed with its type, at its definition site.  A function's name is marked
`@`, as in LLVM, both where it is defined and where a constant refers to it:
`%5 : base.Code = const @m.f`.  So a function never reads as an operation of the same
name.  An operation's successors
follow its operands, each marked `^` as in MLIR.  The `err` successor above binds nothing:
the operation supplies the exception, which `propagate.0()` receives.  A constructor is
printed as any application is, with its type arguments: `base.ok[py.Value, py.Value] %4`.

A terminator is printed as the block's last line, an application without a result:
`demo.raise %3 ^handler.0()`, or `base.Except.case[py.Value, py.Value] %4 ^ok.0() ^err.0()`.
The base's control flow drops its namespace: `jump ^bb.1(%2)`, `branch %3 ^bb.1() ^bb.2()`
and `unreachable`.  A jump to the exit is `ret %5`.

A block is named by its label.  The entry block's parameters are the function's, so they
appear twice: on the signature and on the entry.

An operation's regions follow the rest of its line, each in braces and opening with its
entry block, whose parameters are the region's arguments:

```
%4 : base.Int = demo.if[base.Int] %1 {
  then.0():
    ret %2
} {
  else.0():
    ret %3
}
```
-/

namespace Strata.Mantle

namespace DDM

#dialect
dialect Mantle;

/*
  Hierarchical names, printed dotted.  One operation per `Name` constructor, so a name
  survives the round trip: a numeric segment is not a string segment that happens to
  look like a number.
*/
category MName;
op nameIdent (s : Ident) : MName => s;
op nameIdx (i : Num) : MName => i;
op nameDotIdent (pre : MName, s : Ident) : MName => @[prec(60), leftassoc] pre "." s;
op nameDotIdx (pre : MName, i : Num) : MName => @[prec(60), leftassoc] pre "." i;

category MInt;
op natInt (x : Num) : MInt => x;
op negInt (x : Num) : MInt => "-" x;

/* Type expressions.  `#i` is a type variable; a type constructor with no arguments
   prints as its bare name. */
category MType;
op tyVar (i : Num) : MType => "#" i;
op tyPrim (n : MName) : MType => n;
op tyApp (n : MName, args : CommaSepBy MType) : MType => @[prec(0)] n "(" args ")";

/* A function of the module, marked `@` as in LLVM. */
category MFuncName;
op funcName (n : MName) : MFuncName => "@" n:0;

category MVal;
op valId (i : Num) : MVal => "%" i;

category MValDecl;
op valDecl (v : MVal, ty : MType) : MValDecl => @[prec(0)] v " : " ty;

/* A transfer: a block label, and the arguments the site binds. */
category MTransfer;
op transfer (target : MName, args : CommaSepBy MVal) : MTransfer =>
  @[prec(0)] target "(" args ")";

/* A successor of an operation: a transfer, marked `^` as in MLIR so that it reads apart
   from the operands before it.  Several follow one another. */
category MSucc;
op succ (target : MName, args : CommaSepBy MVal) : MSucc =>
  @[prec(0)] " ^" target "(" args ")";

/* An operation's type arguments, likewise absent rather than empty. */
category MTypeArgs;
op typeArgs (args : CommaSepBy MType) : MTypeArgs => "[" args "]";

category MConst;
op constUnit () : MConst => "unit";
op constBool (b : Bool) : MConst => "bool " b;
op constInt (i : MInt) : MConst => "int " i;
op constFloat (s : Str) : MConst => "float " s;
op constStr (s : Str) : MConst => "str " s;
op constFunc (f : MFuncName) : MConst => f;

/*
  Newlines *lead* a line rather than trailing it, and a line's own newline sits inside
  whatever `indent` encloses it.  That is what makes nesting come out right: the newline
  that ends a header belongs to the header's level, and the ones between the items it
  encloses belong to theirs.
*/
/* Declared ahead of their operations: an instruction holds regions, which hold blocks,
   which hold instructions. */
category MBlock;
category MRegion;

category MInsn;
op insnConst (result : MValDecl, c : MConst) : MInsn =>
  @[prec(0)] "\n" result " = const " c;
/* An application: a constructor's as any other operation's. */
op insnApply (result : MValDecl, name : MName, tyArgs : Option MTypeArgs,
              args : SpacePrefixSepBy MVal, succs : Seq MSucc,
              regions : Seq MRegion) : MInsn =>
  @[prec(0)] "\n" result " = " name tyArgs args succs regions;

category MTerm;
/* A jump to the exit of the enclosing body, passing its arguments. */
op termRet (args : SpacePrefixSepBy MVal) : MTerm => @[prec(0)] "\n" "ret" args;
/* A terminal operation: an application's line without a result. */
op termApply (name : MName, tyArgs : Option MTypeArgs, args : SpacePrefixSepBy MVal,
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

end DDM

/-! ## The translation

One function per level.  The IR is already checked, so the translation cannot fail. -/

namespace ToDDM

open Strata.Mantle.DDM

/-- A name, dotted.  The root segment prints bare, so `py.Value` is two segments and not
three. -/
def name : Name → MName SourceRange
  | .base => .nameIdent .none ⟨.none, "_"⟩
  | .str .base s => .nameIdent .none ⟨.none, s⟩
  | .num .base i => .nameIdx .none ⟨.none, i⟩
  | .str pre s => .nameDotIdent .none (name pre) ⟨.none, s⟩
  | .num pre i => .nameDotIdx .none (name pre) ⟨.none, i⟩

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

def val (v : ValId) : MVal SourceRange := .valId .none ⟨.none, v.id⟩

def valDecl {env : Env Unit} (d : ValDecl env) : MValDecl SourceRange :=
  .valDecl .none (val d.id) (type d.type)

def transfer (k : BlockValue) : MTransfer SourceRange :=
  .transfer .none (name k.target.name) ⟨.none, k.args.map val⟩

/-- An operation's successors, each `^target(args)`. -/
def succs (ks : Array BlockValue) : Ann (Array (MSucc SourceRange)) SourceRange :=
  ⟨.none, ks.map fun k => .succ .none (name k.target.name) ⟨.none, k.args.map val⟩⟩

/-- Type arguments, absent when there are none. -/
def typeArgs {env : Env Unit} (as : Array (TypeExpr env 0)) :
    Ann (Option (MTypeArgs SourceRange)) SourceRange :=
  if as.isEmpty then ⟨.none, none⟩
  else ⟨.none, some (.typeArgs .none ⟨.none, as.map type⟩)⟩

/-- The exact decimal expansion of `f`, which every finite binary64 value has: `3.14` prints
as `3.140000000000000124344978758017532527446746826171875`, and `1.5` as `1.5`.  The fraction
has no trailing zeros and at least one digit.  The non-finite values print as `inf`, `-inf`
and `nan`, as Python's `repr` does. -/
def floatDecimal (f : Float) : String :=
  let bits := f.toBits.toNat
  let sign := if bits >>> 63 == 1 then "-" else ""
  let biased := (bits >>> 52) % 2048
  let frac := bits % 2 ^ 52
  if biased == 2047 then
    if frac == 0 then sign ++ "inf" else "nan"
  else
    -- `f` is `m * 2 ^ e`.
    let (m, e) : Nat × Int :=
      if biased == 0 then (frac, -1074) else (frac + 2 ^ 52, (biased : Int) - 1075)
    if 0 ≤ e then sign ++ toString (m * 2 ^ e.toNat) ++ ".0"
    else
      -- `m / 2 ^ k` is `m * 5 ^ k / 10 ^ k`: `k` fraction digits.
      let k := e.natAbs
      let n := m * 5 ^ k
      let rest := Nat.toDigits 10 (n % 10 ^ k)
      let rest := List.replicate (k - rest.length) '0' ++ rest
      let rest := (rest.reverse.dropWhile (· == '0')).reverse
      let rest := if rest.isEmpty then "0" else String.ofList rest
      sign ++ toString (n / 10 ^ k) ++ "." ++ rest

def const : Const → MConst SourceRange
  | .unit => .constUnit .none
  | .bool b => .constBool .none ⟨.none, b⟩
  | .int i => .constInt .none (int i)
  | .float f => .constFloat .none ⟨.none, floatDecimal f⟩
  | .str s => .constStr .none ⟨.none, s⟩
  | .func target => .constFunc .none (funcName target)

mutual

/-- A terminator.  The base's control flow prints without its namespace, and a jump to the
exit as `ret`. -/
def term {env : Env Unit} {α : Type} : Terminator env α → MTerm SourceRange
  | .apply _ r tyArgs args ks ⟨regions⟩ =>
    let generic (n : Name) :=
      .termApply .none (name n) (typeArgs tyArgs.toArray) ⟨.none, args.map val⟩ (succs ks)
        ⟨.none, ⟨regionList regions⟩⟩
    if r.name == bn "jump" then
      match ks with
      | #[k] => if k.target == Label.exit then .termRet .none ⟨.none, k.args.map val⟩
        else generic (.str .base "jump")
      | _ => generic (.str .base "jump")
    else if r.name == bn "branch" then generic (.str .base "branch")
    else if r.name == bn "unreachable" then generic (.str .base "unreachable")
    else generic r.name

def insn {env : Env Unit} {α : Type} : Instruction env α → MInsn SourceRange
  | .const _ d c => .insnConst .none (valDecl d) (const c)
  | .apply _ d r tyArgs args ks ⟨regions⟩ =>
    .insnApply .none (valDecl d) (name r.name) (typeArgs tyArgs.toArray)
      ⟨.none, args.map val⟩ (succs ks) ⟨.none, ⟨regionList regions⟩⟩

def insnList {env : Env Unit} {α : Type} : List (Instruction env α) → List (MInsn SourceRange)
  | [] => []
  | i :: is => insn i :: insnList is

/-- A block, under its label. -/
def block {env : Env Unit} {α : Type} : Block env α → MBlock SourceRange
  | ⟨label, params, ⟨instrs⟩, t, _⟩ =>
    .block .none (name label.name) ⟨.none, params.map valDecl⟩
      ⟨.none, ⟨insnList instrs⟩⟩ (term t)

def blockList {env : Env Unit} {α : Type} : List (Block env α) → List (MBlock SourceRange)
  | [] => []
  | b :: bs => block b :: blockList bs

def regionList {env : Env Unit} {α : Type} : List (Region env α) → List (MRegion SourceRange)
  | [] => []
  | ⟨⟨blocks⟩⟩ :: rs => .region .none ⟨.none, ⟨blockList blocks⟩⟩ :: regionList rs

end

/-- A function.  Its parameters are the entry block's, so they are read from there. -/
def func {env : Env Unit} {α : Type} (fn : Func env α) : MFunc SourceRange :=
  .func .none (funcName fn.name)
    ⟨.none, (fn.blocks[0]?.map (·.params.map valDecl)).getD #[]⟩
    (type fn.retType)
    ⟨.none, fn.blocks.map block⟩

def module {env : Env Unit} [base ⊑ env] {α : Type} (m : Module env α) :
    DDM.Command SourceRange :=
  .moduleDecl .none (name m.name) ⟨.none, m.funcs.map func⟩

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

/-- The module, printed. -/
public def Module.toString {env : Env Unit} [base ⊑ env] {α : Type} (m : Module env α) :
    String :=
  Print.render (ToDDM.module m)

public instance {env : Env Unit} [base ⊑ env] {α : Type} : ToString (Module env α) where
  toString := Module.toString

/-- One function, printed: a module with just it in. -/
public def Func.toString {env : Env Unit} {α : Type} (fn : Func env α) : String :=
  Print.render (.moduleDecl .none (ToDDM.name fn.name) ⟨.none, #[ToDDM.func fn]⟩)

end Strata.Mantle
