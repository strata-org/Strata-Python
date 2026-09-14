/-
Core syntax (LEAN_SPEC.md 2.1). Every node carries a `Pos`: the path-based
`NodeId` assigned by `Syntax/Label.lean`, which keys the residual table and the
abstract states, plus the line and column that key obligations and per-line
invariants.
-/
import Pylate.Domains.Value

namespace Pylate

structure Pos where
  id   : NodeId := NodeId.root
  line : Nat := 0
  col  : Nat := 0
deriving Repr, Inhabited, DecidableEq

/-- Which join a node owns.

    A join point needs no identity space of its own: it is named by the node that
    induces it plus which join it is. An `If` owns one `ifMerge`; `While` and
    `For` own `loopHead`, `loopExit`, `breakTarget` and `continueTarget`; a `Try`
    owns a `handlerEntry i` per clause plus `handlerMerge`, `finallyEntry` and
    `finallyMerge`. All of it is derivable from the AST -- no CFG construction and
    no fresh-name generation.

    Naming a join is what lets a claim be attached to it: an obligation like
    "`break` and `continue` from a handler feed the correct loop exits" is about a
    state that only exists at one of these points. -/
inductive JoinKind where
  | ifMerge
  | loopHead
  | loopExit
  | breakTarget
  | continueTarget
  | handlerEntry (clause : Nat)
  | handlerMerge
  | finallyEntry
  | finallyMerge
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

def JoinKind.render : JoinKind → String
  | .ifMerge => "if-merge"
  | .loopHead => "loop-head"
  | .loopExit => "loop-exit"
  | .breakTarget => "break-target"
  | .continueTarget => "continue-target"
  | .handlerEntry i => s!"handler-entry:{i}"
  | .handlerMerge => "handler-merge"
  | .finallyEntry => "finally-entry"
  | .finallyMerge => "finally-merge"

/-- A program point: either a node, or a join that node induces.

    The abstract state is keyed on this rather than on a source line, so distinct
    points have distinct keys. A line does not identify one: all nine
    sub-expressions of `x = d["key"].field1 + y.field2` share a line, as do a
    comprehension's fixpoint rounds and the statement enclosing them. -/
inductive PP where
  | node (id : NodeId)
  | join (owner : NodeId) (kind : JoinKind)
deriving Repr, Inhabited, DecidableEq, BEq, Hashable

def PP.render : PP → String
  | .node id => id.render
  | .join owner kind => s!"{owner.render}@{kind.render}"

/-- The join kind, when the point is one. `none` for a node. -/
def PP.joinKind : PP → Option JoinKind
  | .node _ => none
  | .join _ kind => some kind

/-- The owning node, which is what carries the source position. -/
def PP.owner : PP → NodeId
  | .node id => id
  | .join owner _ => owner

/-- The addressing system used to identify program locations and key abstract
    states.

    An address is a program point plus the call sites that led to it, innermost
    first. The analysis is context-sensitive by inlining, so a point inside a
    function body is reached once per call chain and the node alone does not
    identify it:

        foo -> bar -> x        frames = [call bar in foo, decl foo]
        foo -> qux -> bar -> x frames = [call bar in qux, call qux in foo, decl foo]

    Both have the same `point` -- `x` in `bar` -- and differ only in the frames, so
    they do not collide.

    A call site is identified by its node path, not its line: two calls on one
    line are two frames.

    Extension is a cons at both levels and the digest is folded as frames are
    pushed, so forming an address is O(1) and hashing it is O(1). -/
structure Addr where
  /-- Folded over the frames and the point; compared first. -/
  digest : UInt64
  /-- The node or join within the innermost frame. -/
  point  : PP
  /-- Call sites, innermost first; empty at module level. -/
  frames : List NodeId
deriving Repr, Inhabited, DecidableEq

instance : Hashable Addr where
  hash a := a.digest

/-- `3.2@loop-head < 4.1` is the loop head of node `3.2`, reached through the call
    at node `4.1`. `@` introduces the join kind and ` < ` the call frames, so the
    two cannot be confused. -/
def Addr.render (a : Addr) : String :=
  let here := a.point.render
  if a.frames.isEmpty then here
  else s!"{here} < {" < ".intercalate (a.frames.map NodeId.render)}"

inductive Const
  | cint (n : Int) | cbool (b : Bool) | cfloat (repr : String)
  | cstr (s : String) | cnone
deriving Repr, Inhabited, DecidableEq

/-- The literal a constant denotes, and the value it evaluates to.

    One definition, here beside `Const`, so that every consumer keeps the payload
    `Const` carries. `Plan.lean`, `Analyzer.lean` and `StructuralExpressions.lean`
    all read it, and only the first is on the hot path -- a second copy that
    dropped the literal would go unnoticed. -/
def Const.lit : Const -> Lit
  | .cint n => .lint n
  | .cbool b => .lbool b
  | .cfloat repr => .lfloat repr
  | .cstr s => .lstr s
  | .cnone => .lnone

def constV (c : Const) : AbsVal := litV c.lit

inductive BinOp
  | add | sub | mul | div | floordiv | mod | pow
  | bitOr | bitAnd | bitXor | lshift | rshift
deriving Repr, Inhabited, DecidableEq

/-- The arithmetic unary operators. `not` is not one of them: it goes through
    the truth protocol rather than a numeric slot, so it keeps its own node.
    `invert` is bitwise, so unlike `neg` and `pos` it rejects float and
    complex operands. -/
inductive UnOp
  | neg | pos | invert
deriving Repr, Inhabited, DecidableEq

def UnOp.render : UnOp → String
  | .neg => "-" | .pos => "+" | .invert => "~"

def UnOp.astName : UnOp → String
  | .neg => "USub" | .pos => "UAdd" | .invert => "Invert"

def UnOp.dunder : UnOp → String
  | .neg => "__neg__" | .pos => "__pos__" | .invert => "__invert__"

/-- Whether the operator accepts real and complex operands, or only the
    integral ones a bit pattern is defined for. -/
def UnOp.acceptsInexact : UnOp → Bool
  | .neg | .pos => true
  | .invert => false

def BinOp.render : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
  | .floordiv => "//" | .mod => "%" | .pow => "**"
  | .bitOr => "|" | .bitAnd => "&" | .bitXor => "^"
  | .lshift => "<<" | .rshift => ">>"

def BinOp.astName : BinOp → String
  | .add => "Add" | .sub => "Sub" | .mul => "Mult" | .div => "Div"
  | .floordiv => "FloorDiv" | .mod => "Mod" | .pow => "Pow"
  | .bitOr => "BitOr" | .bitAnd => "BitAnd" | .bitXor => "BitXor"
  | .lshift => "LShift" | .rshift => "RShift"

def BinOp.dunder : BinOp → String
  | .add => "__add__" | .sub => "__sub__" | .mul => "__mul__"
  | .div => "__truediv__" | .floordiv => "__floordiv__"
  | .mod => "__mod__" | .pow => "__pow__"
  | .bitOr => "__or__" | .bitAnd => "__and__" | .bitXor => "__xor__"
  | .lshift => "__lshift__" | .rshift => "__rshift__"

def BinOp.reflectedDunder : BinOp → String
  | .add => "__radd__" | .sub => "__rsub__" | .mul => "__rmul__"
  | .div => "__rtruediv__" | .floordiv => "__rfloordiv__"
  | .mod => "__rmod__" | .pow => "__rpow__"
  | .bitOr => "__ror__" | .bitAnd => "__rand__" | .bitXor => "__rxor__"
  | .lshift => "__rlshift__" | .rshift => "__rrshift__"

inductive CmpOp
  | lt | le | gt | ge | eq | ne | inOp | notInOp | isOp | isNotOp
deriving Repr, Inhabited, DecidableEq

def CmpOp.render : CmpOp → String
  | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .eq => "==" | .ne => "!=" | .inOp => "in" | .notInOp => "not in"
  | .isOp => "is" | .isNotOp => "is not"

def CmpOp.astName : CmpOp → String
  | .lt => "Lt" | .le => "LtE" | .gt => "Gt" | .ge => "GtE"
  | .eq => "Eq" | .ne => "NotEq" | .inOp => "In" | .notInOp => "NotIn"
  | .isOp => "Is" | .isNotOp => "IsNot"

def CmpOp.dunder : CmpOp → String
  | .lt => "__lt__" | .le => "__le__" | .gt => "__gt__" | .ge => "__ge__"
  | .eq => "__eq__" | .ne => "__ne__" | .inOp => "__contains__"
  | .notInOp => "__contains__" | .isOp => "" | .isNotOp => ""

def CmpOp.reflectedDunder : CmpOp → String
  | .lt => "__gt__" | .le => "__ge__" | .gt => "__lt__" | .ge => "__le__"
  | .eq => "__eq__" | .ne => "__ne__" | .inOp => "__contains__"
  | .notInOp => "__contains__" | .isOp => "" | .isNotOp => ""

inductive CompKind | clist | cset | cdict | cgen
deriving Repr, Inhabited, DecidableEq

mutual
inductive Expr
  | const    (p : Pos) (c : Const)
  | name     (p : Pos) (x : String)
  | binop    (p : Pos) (op : BinOp) (l r : Expr)
  | cmp      (p : Pos) (op : CmpOp) (l r : Expr)
  | boolop   (p : Pos) (isAnd : Bool) (vals : List Expr)
  | notE     (p : Pos) (e : Expr)
  | unary    (p : Pos) (op : UnOp) (e : Expr)
  | attr     (p : Pos) (e : Expr) (f : String)
  | subscr   (p : Pos) (e i : Expr)
  | call     (p : Pos) (f : Expr) (args : List Expr)
             (kws : List (String × Expr))
  | listlit  (p : Pos) (es : List Expr)
  | tuplelit (p : Pos) (es : List Expr)
  | setlit   (p : Pos) (es : List Expr)
  | dictlit  (p : Pos) (kvs : List (Expr × Expr))
  | ifexp    (p : Pos) (c t f : Expr)
  | fstr     (p : Pos) (parts : List Expr)
  | comp     (p : Pos) (kind : CompKind) (elt : Expr) (eltVal : Option Expr)
             (var : String) (iter : Expr) (conds : List Expr)
  | yieldE   (p : Pos) (e : Option Expr)
  | yieldFrom (p : Pos) (e : Expr)
deriving Inhabited
end

/-- Source spelling of an expression, for residual prefixes. -/
partial def exprText : Expr → String
  | .const _ c => match c with
    | .cint n => toString n
    | .cbool b => if b then "True" else "False"
    | .cfloat s => s
    | .cstr s => s!"\"{s}\""
    | .cnone => "None"
  | .name _ x => x
  | .binop _ op l r => s!"{exprText l} {op.render} {exprText r}"
  | .cmp _ op l r => s!"{exprText l} {op.render} {exprText r}"
  | .boolop _ isAnd vs =>
    (if isAnd then " and " else " or ").intercalate (vs.map exprText)
  | .notE _ e => s!"not {exprText e}"
  | .unary _ op e => s!"{op.render}{exprText e}"
  | .attr _ e f => s!"{exprText e}.{f}"
  | .subscr _ e i => s!"{exprText e}[{exprText i}]"
  | .call _ f args _ =>
    s!"{exprText f}({", ".intercalate (args.map exprText)})"
  | .listlit _ es => s!"[{", ".intercalate (es.map exprText)}]"
  | .tuplelit _ es => s!"({", ".intercalate (es.map exprText)})"
  | .setlit _ es => "{" ++ ", ".intercalate (es.map exprText) ++ "}"
  | .dictlit _ kvs =>
    "{" ++ ", ".intercalate (kvs.map fun (k, v) =>
      s!"{exprText k}: {exprText v}") ++ "}"
  | .ifexp _ c t f => s!"{exprText t} if {exprText c} else {exprText f}"
  | .fstr _ _ => "f\"...\""
  | .comp _ _ _ _ x it _ => s!"[... for {x} in {exprText it}]"
  | .yieldE _ _ => "yield"
  | .yieldFrom _ e => s!"yield from {exprText e}"

def Expr.pos : Expr → Pos
  | .const p .. | .name p .. | .binop p .. | .cmp p .. | .boolop p ..
  | .notE p .. | .unary p .. | .attr p .. | .subscr p .. | .call p ..
  | .listlit p .. | .tuplelit p .. | .setlit p .. | .dictlit p ..
  | .ifexp p .. | .fstr p .. | .comp p .. | .yieldE p ..
  | .yieldFrom p .. => p

inductive Target
  | tname  (p : Pos) (x : String)
  | tattr  (p : Pos) (e : Expr) (f : String)
  | tsub   (p : Pos) (e i : Expr)
  | ttuple (p : Pos) (elts : List Target)
deriving Inhabited

mutual
inductive Stmt
  | assign    (p : Pos) (tgt : Target) (e : Expr)
  | annAssign (p : Pos) (x : String) (e : Option Expr)
  | exprS     (p : Pos) (e : Expr)
  | ifS       (p : Pos) (c : Expr) (thn els : List Stmt)
  | whileS    (p : Pos) (c : Expr) (body orelse : List Stmt)
  | forS      (p : Pos) (tgt : Target) (iter : Expr)
              (body orelse : List Stmt)
  | tryS      (p : Pos) (body : List Stmt) (handlers : List Handler)
              (orelse fin : List Stmt)
  | ret       (p : Pos) (e : Option Expr)
  | brk       (p : Pos)
  | cont      (p : Pos)
  | pass      (p : Pos)
  | raiseS    (p : Pos) (cls : Option String) (arg : Option Expr)
  | assertS   (p : Pos) (c : Expr)
  | delS      (p : Pos) (tgt : Target)
deriving Inhabited

inductive Handler
  | mk (p : Pos) (cls : Option String) (name : Option String)
       (body : List Stmt)
deriving Inhabited
end

def Stmt.pos : Stmt → Pos
  | .assign p .. | .annAssign p .. | .exprS p .. | .ifS p ..
  | .whileS p .. | .forS p .. | .tryS p .. | .ret p .. | .brk p ..
  | .cont p .. | .pass p .. | .raiseS p .. | .assertS p ..
  | .delS p .. => p

/-- Recursive source-level contracts. Requiredness/read-only wrappers are
    retained until a TypedDict field declaration normalizes them. -/
inductive Ann
  | any
  | atom (name : String)
  | union (members : List Ann)
  | generic (name : String) (args : List Ann) (variadic : Bool := false)
  | literal (values : List Const)
  | required (inner : Ann)
  | notRequired (inner : Ann)
  | readOnly (inner : Ann)
deriving Repr, Inhabited

structure FieldDecl where
  name     : String
  ann      : Option Ann := none
  required : Bool := true
  readOnly : Bool := false
deriving Repr, Inhabited

structure Param where
  name    : String
  ann     : Option Ann := none
  default : Option Expr := none
deriving Inhabited

structure FuncDef where
  p       : Pos
  name    : String
  params  : List Param
  retAnn  : Option Ann := none
  body    : List Stmt
  isGen   : Bool := false
  /-- A declaration with no implementation: the body was `...`. Its declared
      types are the whole specification, so a call is answered from the return
      annotation instead of by analysing a body that is not there.

      Only `...` marks one. `pass` does not: `def f(): pass` is a function that
      returns `None`, and corpus programs depend on that reading. -/
  isStub  : Bool := false
deriving Inhabited

structure ClassDef where
  p           : Pos
  name        : String
  bases       : List String
  fields      : List FieldDecl              -- annotated class/TypedDict fields
  methods     : List FuncDef
  isDataclass : Bool := false
  isTypedDict : Bool := false
  total       : Bool := true
  /-- The names in a `__slots__` declaration, when the class body has one.
      `some []` is `__slots__ = ()`, the form a subclass uses to keep an
      inherited slots layout without adding to it. `none` means the class
      declared none, so CPython gives its instances a `__dict__`. -/
  slots       : Option (List String) := none
deriving Inhabited

inductive ModItem
  | fdef (f : FuncDef)
  | cdef (c : ClassDef)
  | stmt (s : Stmt)
deriving Inhabited

structure Program where
  items : List ModItem
deriving Inhabited

end Pylate
