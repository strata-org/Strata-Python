/-
Keys for the admitted syntax constructors, ENGINE.md section 3.

The `kindOf` functions below match every constructor of `Syntax.lean`
exhaustively, so a new constructor is a compile error rather than a silently
undispatched node. Until the structural plans exist, `RuleValidate` uses these
keys to count how much of the syntax surface is still dispatched by hand.
-/
import Pylate.Syntax.Nodes

namespace Pylate.RuleDriven

open Pylate

inductive ExprKind
  | const | name | binop | cmp | boolAnd | boolOr | notE | unary | attr
  | subscr | call | listlit | tuplelit | setlit | dictlit | ifexp | fstr
  | listComp | setComp | dictComp | genComp | yieldE | yieldFrom
deriving Repr, DecidableEq, Inhabited, Hashable

inductive TargetKind
  | name | attr | subscript | tuple
deriving Repr, DecidableEq, Inhabited, Hashable

inductive StmtKind
  | assign | annAssign | exprS | ifS | whileS | forS | tryS | ret | brk
  | cont | pass | raiseS | assertS | delS
deriving Repr, DecidableEq, Inhabited, Hashable

inductive AnnKind
  | any | atom | union | generic | literal | required | notRequired | readOnly
deriving Repr, DecidableEq, Inhabited, Hashable

/-- `boolop` splits on its operator because `isAnd` selects which branch
    short-circuits, and a comprehension splits by form because the produced
    collection differs; every other constructor keeps one key with its
    operator carried as data. -/
def ExprKind.of : Expr -> ExprKind
  | .const .. => .const
  | .name .. => .name
  | .binop .. => .binop
  | .cmp .. => .cmp
  | .boolop _ isAnd _ => if isAnd then .boolAnd else .boolOr
  | .notE .. => .notE
  | .unary .. => .unary
  | .attr .. => .attr
  | .subscr .. => .subscr
  | .call .. => .call
  | .listlit .. => .listlit
  | .tuplelit .. => .tuplelit
  | .setlit .. => .setlit
  | .dictlit .. => .dictlit
  | .ifexp .. => .ifexp
  | .fstr .. => .fstr
  | .comp _ kind .. =>
    match kind with
    | .clist => .listComp
    | .cset => .setComp
    | .cdict => .dictComp
    | .cgen => .genComp
  | .yieldE .. => .yieldE
  | .yieldFrom .. => .yieldFrom

def TargetKind.of : Target -> TargetKind
  | .tname .. => .name
  | .tattr .. => .attr
  | .tsub .. => .subscript
  | .ttuple .. => .tuple

def StmtKind.of : Stmt -> StmtKind
  | .assign .. => .assign
  | .annAssign .. => .annAssign
  | .exprS .. => .exprS
  | .ifS .. => .ifS
  | .whileS .. => .whileS
  | .forS .. => .forS
  | .tryS .. => .tryS
  | .ret .. => .ret
  | .brk .. => .brk
  | .cont .. => .cont
  | .pass .. => .pass
  | .raiseS .. => .raiseS
  | .assertS .. => .assertS
  | .delS .. => .delS

def AnnKind.of : Ann -> AnnKind
  | .any => .any
  | .atom .. => .atom
  | .union .. => .union
  | .generic .. => .generic
  | .literal .. => .literal
  | .required .. => .required
  | .notRequired .. => .notRequired
  | .readOnly .. => .readOnly

def ExprKind.render : ExprKind -> String
  | .const => "const" | .name => "name" | .binop => "binop" | .cmp => "cmp"
  | .boolAnd => "boolAnd" | .boolOr => "boolOr" | .notE => "not"
  | .unary => "unary" | .attr => "attr" | .subscr => "subscr"
  | .call => "call" | .listlit => "listlit" | .tuplelit => "tuplelit"
  | .setlit => "setlit" | .dictlit => "dictlit" | .ifexp => "ifexp"
  | .fstr => "fstr" | .listComp => "listComp" | .setComp => "setComp"
  | .dictComp => "dictComp" | .genComp => "genComp" | .yieldE => "yield"
  | .yieldFrom => "yieldFrom"

def TargetKind.render : TargetKind -> String
  | .name => "name" | .attr => "attr" | .subscript => "subscript"
  | .tuple => "tuple"

def StmtKind.render : StmtKind -> String
  | .assign => "assign" | .annAssign => "annAssign" | .exprS => "exprS"
  | .ifS => "if" | .whileS => "while" | .forS => "for" | .tryS => "try"
  | .ret => "return" | .brk => "break" | .cont => "continue"
  | .pass => "pass" | .raiseS => "raise" | .assertS => "assert"
  | .delS => "del"

def AnnKind.render : AnnKind -> String
  | .any => "any" | .atom => "atom" | .union => "union"
  | .generic => "generic" | .literal => "literal" | .required => "required"
  | .notRequired => "notRequired" | .readOnly => "readOnly"

/-- Every admitted syntax key, for the coverage condition. -/
def allExprKinds : List ExprKind :=
  [.const, .name, .binop, .cmp, .boolAnd, .boolOr, .notE, .unary, .attr,
   .subscr, .call, .listlit, .tuplelit, .setlit, .dictlit, .ifexp, .fstr,
   .listComp, .setComp, .dictComp, .genComp, .yieldE, .yieldFrom]

def allTargetKinds : List TargetKind := [.name, .attr, .subscript, .tuple]

def allStmtKinds : List StmtKind :=
  [.assign, .annAssign, .exprS, .ifS, .whileS, .forS, .tryS, .ret, .brk,
   .cont, .pass, .raiseS, .assertS, .delS]

def allAnnKinds : List AnnKind :=
  [.any, .atom, .union, .generic, .literal, .required, .notRequired,
   .readOnly]

end Pylate.RuleDriven
