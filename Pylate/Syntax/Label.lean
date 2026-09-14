/-
Relabel the Strata Python AST from `SourceRange` to Pylate's `Pos`.

`Check.lean` needs a `Pos` -- an id plus a line and column -- at every node it
lowers. The Strata AST carries a `SourceRange`, which is a pair of byte offsets
with no id, and two different nodes can share one range: a bare expression
statement has exactly its expression's extent, so `Expr` and `Call` collide. So
the range cannot serve as identity.

So the AST is relabelled once here. The generated types are generic in their
annotation, so `stmt SourceRange` becomes `stmt Pos` and every later pattern
match reads the `Pos` straight off the node. `Check.lean` needs no counter
threaded through it, which matters because its lowering is an applicative over
accumulated violations rather than a state monad.

A node's id is its path from the root: the sequence of argument indices taken to
reach it (see `NodeId`). Paths are handed *down* the traversal, so these are
plain total functions and an id is a property of where the node sits rather than
of the order a traversal reached it.

An *argument's* annotation is never read -- only the owning node's `Pos` is -- so
wrapped arguments get a placeholder and do not consume a path component.
-/
import Pylate.Syntax.Nodes
import StrataPython.ReadPython

namespace Pylate.Label

open StrataPython
open StrataDDM (SourceRange Ann)

/-- Byte offsets of each line start, to turn a `SourceRange` into a line and
    column. CPython's `col_offset` is a byte offset within the line and
    `SourceRange.start` is a byte offset within the file, so the subtraction is
    exact for any encoding. -/
structure Src where
  lineStarts : Array Nat
deriving Inhabited

def Src.of (text : String) : Src := Id.run do
  let bytes := text.toUTF8
  let mut starts : Array Nat := #[0]
  for i in [0:bytes.size] do
    if bytes[i]! == 10 then
      starts := starts.push (i + 1)
  pure { lineStarts := starts }

/-- The 1-based line and 0-based byte column of a byte offset. -/
def Src.lineCol (s : Src) (offset : Nat) : Nat × Nat := Id.run do
  let mut lo := 0
  let mut hi := s.lineStarts.size
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if s.lineStarts[mid]! <= offset then lo := mid else hi := mid
  pure (lo + 1, offset - s.lineStarts[lo]!)

/-- A `Pos` for a node that has a source position, at path `id`. -/
private def posOf (src : Src) (id : NodeId) (r : SourceRange) : Pos :=
  let (line, col) := src.lineCol r.start.byteIdx
  ⟨id, line, col⟩

/-- A `Pos` for a node CPython gives no position to -- the operator families,
    `expr_context`, `comprehension`, `arguments`, `withitem`, `match_case`.
    CPython attaches no `lineno`/`col_offset` to them, so line and column stay 0
    and `snap`'s `line == 0` skip keeps excluding exactly those nodes. The path is
    still assigned: they are real nodes and a claim can be attached to one. -/
private def posNone (id : NodeId) : Pos := ⟨id, 0, 0⟩

/-- The placeholder annotation for a wrapped argument, which nothing reads. -/
private def noPos : Pos := ⟨NodeId.root, 0, 0⟩

/-- Rewrap an argument with a relabelled payload. -/
private def wrap {β : Type} (v : β) : StrataDDM.Ann β Pos := ⟨noPos, v⟩

/-- Argument indices follow the dialect's declaration order, which is CPython's
    `_field_types` order, so a path is `parent ++ [argIndex]` for a plain argument
    and `parent ++ [argIndex, elementIndex]` for an element of a sequence. -/
private def argAt (path : NodeId) (i : Nat) : NodeId := path.child i

private def itemAt (path : NodeId) (i j : Nat) : NodeId := (path.child i).child j

/-- `Python.int` is a syncat but CPython holds these in plain `int` fields, so
    there is no node there and the path is not extended. -/
private def ofPyInt : StrataPython.int SourceRange → StrataPython.int Pos
  | .IntPos _ v => .IntPos noPos (wrap v.val)
  | .IntNeg _ v => .IntNeg noPos (wrap v.val)

/-- A constant's value is a Python object, not an `ast.AST`, so likewise. -/
private def ofConstant : constant SourceRange → constant Pos
  | .ConNone _ => .ConNone noPos
  | .ConTrue _ => .ConTrue noPos
  | .ConFalse _ => .ConFalse noPos
  | .ConPos _ v => .ConPos noPos (wrap v.val)
  | .ConNeg _ v => .ConNeg noPos (wrap v.val)
  | .ConString _ v => .ConString noPos (wrap v.val)
  | .ConFloat _ v => .ConFloat noPos (wrap v.val)
  | .ConEllipsis _ => .ConEllipsis noPos
  | .ConBytes _ v => .ConBytes noPos (wrap v.val)
  | .ConComplex _ r i => .ConComplex noPos (wrap r.val) (wrap i.val)

mutual

private partial def ofCtx (path : NodeId) : expr_context SourceRange → expr_context Pos
  | .Load _ => .Load (posNone path)
  | .Store _ => .Store (posNone path)
  | .Del _ => .Del (posNone path)

private partial def ofOperator (path : NodeId) (o : operator SourceRange) : operator Pos :=
  let p := posNone path
  match o with
  | .Add _ => .Add p            | .Sub _ => .Sub p
  | .Mult _ => .Mult p          | .MatMult _ => .MatMult p
  | .Div _ => .Div p            | .Mod _ => .Mod p
  | .Pow _ => .Pow p            | .LShift _ => .LShift p
  | .RShift _ => .RShift p      | .BitOr _ => .BitOr p
  | .BitXor _ => .BitXor p      | .BitAnd _ => .BitAnd p
  | .FloorDiv _ => .FloorDiv p

private partial def ofUnaryOp (path : NodeId) (o : unaryop SourceRange) : unaryop Pos :=
  let p := posNone path
  match o with
  | .Invert _ => .Invert p | .Not _ => .Not p
  | .UAdd _ => .UAdd p     | .USub _ => .USub p

private partial def ofBoolOp (path : NodeId) (o : boolop SourceRange) : boolop Pos :=
  let p := posNone path
  match o with | .And _ => .And p | .Or _ => .Or p

private partial def ofCmpOp (path : NodeId) (o : cmpop SourceRange) : cmpop Pos :=
  let p := posNone path
  match o with
  | .Eq _ => .Eq p        | .NotEq _ => .NotEq p
  | .Lt _ => .Lt p        | .LtE _ => .LtE p
  | .Gt _ => .Gt p        | .GtE _ => .GtE p
  | .Is _ => .Is p        | .IsNot _ => .IsNot p
  | .In _ => .In p        | .NotIn _ => .NotIn p

private partial def ofOptExpr (src : Src) (path : NodeId) :
    opt_expr SourceRange → opt_expr Pos
  | .some_expr _ x => .some_expr noPos (ofExpr src path x)
  | .missing_expr _ => .missing_expr noPos

private partial def ofExprs (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (expr SourceRange)) : Array (expr Pos) :=
  xs.zipIdx.map (fun (x, j) => ofExpr src (itemAt path i j) x)

private partial def ofStmts (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (stmt SourceRange)) : Array (stmt Pos) :=
  xs.zipIdx.map (fun (x, j) => ofStmt src (itemAt path i j) x)

private partial def ofOptE (src : Src) (path : NodeId)
    (o : Option (expr SourceRange)) : Option (expr Pos) :=
  o.map (ofExpr src path)

private partial def ofArg (src : Src) (path : NodeId) : arg SourceRange → arg Pos
  | .mk_arg a name annotation typeComment =>
    .mk_arg (posOf src path a) (wrap name.val)
      (wrap (ofOptE src (argAt path 1) annotation.val))
      (wrap (typeComment.val.map (wrap ·.val)))

private partial def ofArgs (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (StrataPython.arg SourceRange)) : Array (StrataPython.arg Pos) :=
  xs.zipIdx.map (fun (x, j) => ofArg src (itemAt path i j) x)

private partial def ofArguments (src : Src) (path : NodeId) :
    arguments SourceRange → arguments Pos
  | .mk_arguments _ posonly args' vararg kwonly kwDefaults kwarg defaults =>
    .mk_arguments (posNone path)
      (wrap (ofArgs src path 0 posonly.val))
      (wrap (ofArgs src path 1 args'.val))
      (wrap (vararg.val.map (ofArg src (argAt path 2))))
      (wrap (ofArgs src path 3 kwonly.val))
      (wrap (kwDefaults.val.zipIdx.map (fun (d, j) =>
        ofOptExpr src (itemAt path 4 j) d)))
      (wrap (kwarg.val.map (ofArg src (argAt path 5))))
      (wrap (ofExprs src path 6 defaults.val))

private partial def ofKeyword (src : Src) (path : NodeId) :
    keyword SourceRange → keyword Pos
  | .mk_keyword a k value =>
    .mk_keyword (posOf src path a) (wrap (k.val.map (wrap ·.val)))
      (ofExpr src (argAt path 1) value)

private partial def ofKeywords (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (keyword SourceRange)) : Array (keyword Pos) :=
  xs.zipIdx.map (fun (x, j) => ofKeyword src (itemAt path i j) x)

private partial def ofAlias (src : Src) (path : NodeId) :
    alias SourceRange → alias Pos
  | .mk_alias a name asname =>
    .mk_alias (posOf src path a) (wrap name.val)
      (wrap (asname.val.map (wrap ·.val)))

private partial def ofWithItem (src : Src) (path : NodeId) :
    withitem SourceRange → withitem Pos
  | .mk_withitem _ ctxExpr optionalVars =>
    .mk_withitem (posNone path) (ofExpr src (argAt path 0) ctxExpr)
      (wrap (ofOptE src (argAt path 1) optionalVars.val))

private partial def ofWithItems (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (withitem SourceRange)) : Array (withitem Pos) :=
  xs.zipIdx.map (fun (x, j) => ofWithItem src (itemAt path i j) x)

private partial def ofComprehension (src : Src) (path : NodeId) :
    comprehension SourceRange → comprehension Pos
  | .mk_comprehension _ target iter ifs isAsync =>
    .mk_comprehension (posNone path) (ofExpr src (argAt path 0) target)
      (ofExpr src (argAt path 1) iter) (wrap (ofExprs src path 2 ifs.val))
      (ofPyInt isAsync)

private partial def ofComprehensions (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (comprehension SourceRange)) : Array (comprehension Pos) :=
  xs.zipIdx.map (fun (x, j) => ofComprehension src (itemAt path i j) x)

private partial def ofHandler (src : Src) (path : NodeId) :
    excepthandler SourceRange → excepthandler Pos
  | .ExceptHandler a ty name body =>
    .ExceptHandler (posOf src path a)
      (wrap (ofOptE src (argAt path 0) ty.val))
      (wrap (name.val.map (wrap ·.val)))
      (wrap (ofStmts src path 2 body.val))

private partial def ofHandlers (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (excepthandler SourceRange)) : Array (excepthandler Pos) :=
  xs.zipIdx.map (fun (x, j) => ofHandler src (itemAt path i j) x)

private partial def ofPattern (src : Src) (path : NodeId) :
    pattern SourceRange → pattern Pos := fun q =>
  match q with
  | .MatchValue a value =>
    .MatchValue (posOf src path a) (ofExpr src (argAt path 0) value)
  | .MatchSingleton a value =>
    .MatchSingleton (posOf src path a) (ofConstant value)
  | .MatchSequence a patterns =>
    .MatchSequence (posOf src path a) (wrap (ofPatterns src path 0 patterns.val))
  | .MatchMapping a keys patterns rest =>
    .MatchMapping (posOf src path a) (wrap (ofExprs src path 0 keys.val))
      (wrap (ofPatterns src path 1 patterns.val))
      (wrap (rest.val.map (wrap ·.val)))
  | .MatchClass a cls patterns kwdAttrs kwdPatterns =>
    .MatchClass (posOf src path a) (ofExpr src (argAt path 0) cls)
      (wrap (ofPatterns src path 1 patterns.val))
      (wrap (kwdAttrs.val.map (wrap ·.val)))
      (wrap (ofPatterns src path 3 kwdPatterns.val))
  | .MatchStar a name =>
    .MatchStar (posOf src path a) (wrap (name.val.map (wrap ·.val)))
  | .MatchAs a pat name =>
    .MatchAs (posOf src path a)
      (wrap (pat.val.map (ofPattern src (argAt path 0))))
      (wrap (name.val.map (wrap ·.val)))
  | .MatchOr a patterns =>
    .MatchOr (posOf src path a) (wrap (ofPatterns src path 0 patterns.val))

private partial def ofPatterns (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (pattern SourceRange)) : Array (pattern Pos) :=
  xs.zipIdx.map (fun (x, j) => ofPattern src (itemAt path i j) x)

private partial def ofMatchCase (src : Src) (path : NodeId) :
    match_case SourceRange → match_case Pos
  | .mk_match_case _ pat guard body =>
    .mk_match_case (posNone path) (ofPattern src (argAt path 0) pat)
      (wrap (ofOptE src (argAt path 1) guard.val))
      (wrap (ofStmts src path 2 body.val))

private partial def ofMatchCases (src : Src) (path : NodeId) (i : Nat)
    (xs : Array (match_case SourceRange)) : Array (match_case Pos) :=
  xs.zipIdx.map (fun (x, j) => ofMatchCase src (itemAt path i j) x)

private partial def ofTypeParam (src : Src) (path : NodeId) :
    type_param SourceRange → type_param Pos := fun t =>
  match t with
  | .TypeVar a name bound default =>
    .TypeVar (posOf src path a) (wrap name.val)
      (wrap (ofOptE src (argAt path 1) bound.val))
      (wrap (ofOptE src (argAt path 2) default.val))
  | .TypeVarTuple a name default =>
    .TypeVarTuple (posOf src path a) (wrap name.val)
      (wrap (ofOptE src (argAt path 1) default.val))
  | .ParamSpec a name default =>
    .ParamSpec (posOf src path a) (wrap name.val)
      (wrap (ofOptE src (argAt path 1) default.val))

private partial def ofTypeParams (src : Src) (path : NodeId) (i : Nat)
    (ts : Array (type_param SourceRange)) : Array (type_param Pos) :=
  ts.zipIdx.map (fun (t, j) => ofTypeParam src (itemAt path i j) t)

private partial def ofExpr (src : Src) (path : NodeId) :
    expr SourceRange → expr Pos := fun e =>
  let p := fun (a : SourceRange) => posOf src path a
  match e with
  | .Constant a value kind =>
    .Constant (p a) (ofConstant value) (wrap (kind.val.map (wrap ·.val)))
  | .Name a ident ctx =>
    .Name (p a) (wrap ident.val) (ofCtx (argAt path 1) ctx)
  | .Attribute a value attr ctx =>
    .Attribute (p a) (ofExpr src (argAt path 0) value) (wrap attr.val)
      (ofCtx (argAt path 2) ctx)
  | .Subscript a value slice ctx =>
    .Subscript (p a) (ofExpr src (argAt path 0) value)
      (ofExpr src (argAt path 1) slice) (ofCtx (argAt path 2) ctx)
  | .Starred a value ctx =>
    .Starred (p a) (ofExpr src (argAt path 0) value) (ofCtx (argAt path 1) ctx)
  | .BinOp a left op right =>
    .BinOp (p a) (ofExpr src (argAt path 0) left) (ofOperator (argAt path 1) op)
      (ofExpr src (argAt path 2) right)
  | .UnaryOp a op operand =>
    .UnaryOp (p a) (ofUnaryOp (argAt path 0) op) (ofExpr src (argAt path 1) operand)
  | .BoolOp a op values =>
    .BoolOp (p a) (ofBoolOp (argAt path 0) op) (wrap (ofExprs src path 1 values.val))
  | .Compare a left ops comparators =>
    .Compare (p a) (ofExpr src (argAt path 0) left)
      (wrap (ops.val.zipIdx.map (fun (o, j) => ofCmpOp (itemAt path 1 j) o)))
      (wrap (ofExprs src path 2 comparators.val))
  | .Call a func args' keywords =>
    .Call (p a) (ofExpr src (argAt path 0) func) (wrap (ofExprs src path 1 args'.val))
      (wrap (ofKeywords src path 2 keywords.val))
  | .IfExp a test body orelse =>
    .IfExp (p a) (ofExpr src (argAt path 0) test) (ofExpr src (argAt path 1) body)
      (ofExpr src (argAt path 2) orelse)
  | .Lambda a args' body =>
    .Lambda (p a) (ofArguments src (argAt path 0) args')
      (ofExpr src (argAt path 1) body)
  | .NamedExpr a target value =>
    .NamedExpr (p a) (ofExpr src (argAt path 0) target)
      (ofExpr src (argAt path 1) value)
  | .List a elts ctx =>
    .List (p a) (wrap (ofExprs src path 0 elts.val)) (ofCtx (argAt path 1) ctx)
  | .Tuple a elts ctx =>
    .Tuple (p a) (wrap (ofExprs src path 0 elts.val)) (ofCtx (argAt path 1) ctx)
  | .Set a elts => .Set (p a) (wrap (ofExprs src path 0 elts.val))
  | .Dict a keys values =>
    .Dict (p a)
      (wrap (keys.val.zipIdx.map (fun (k, j) => ofOptExpr src (itemAt path 0 j) k)))
      (wrap (ofExprs src path 1 values.val))
  | .ListComp a elt gens =>
    .ListComp (p a) (ofExpr src (argAt path 0) elt)
      (wrap (ofComprehensions src path 1 gens.val))
  | .SetComp a elt gens =>
    .SetComp (p a) (ofExpr src (argAt path 0) elt)
      (wrap (ofComprehensions src path 1 gens.val))
  | .GeneratorExp a elt gens =>
    .GeneratorExp (p a) (ofExpr src (argAt path 0) elt)
      (wrap (ofComprehensions src path 1 gens.val))
  | .DictComp a key value gens =>
    .DictComp (p a) (ofExpr src (argAt path 0) key) (ofExpr src (argAt path 1) value)
      (wrap (ofComprehensions src path 2 gens.val))
  | .Slice a lower upper step =>
    .Slice (p a) (wrap (ofOptE src (argAt path 0) lower.val))
      (wrap (ofOptE src (argAt path 1) upper.val))
      (wrap (ofOptE src (argAt path 2) step.val))
  | .JoinedStr a values =>
    .JoinedStr (p a) (wrap (ofExprs src path 0 values.val))
  | .FormattedValue a value conversion formatSpec =>
    .FormattedValue (p a) (ofExpr src (argAt path 0) value) (ofPyInt conversion)
      (wrap (ofOptE src (argAt path 2) formatSpec.val))
  | .TemplateStr a values =>
    .TemplateStr (p a) (wrap (ofExprs src path 0 values.val))
  | .Interpolation a value str conversion formatSpec =>
    .Interpolation (p a) (ofExpr src (argAt path 0) value) (ofConstant str)
      (ofPyInt conversion) (wrap (ofOptE src (argAt path 3) formatSpec.val))
  | .Await a value => .Await (p a) (ofExpr src (argAt path 0) value)
  | .Yield a value => .Yield (p a) (wrap (ofOptE src (argAt path 0) value.val))
  | .YieldFrom a value => .YieldFrom (p a) (ofExpr src (argAt path 0) value)

private partial def ofStmt (src : Src) (path : NodeId) :
    stmt SourceRange → stmt Pos := fun s =>
  let p := fun (a : SourceRange) => posOf src path a
  let tc := fun (o : Option (StrataDDM.Ann String SourceRange)) =>
    wrap (o.map (wrap ·.val))
  match s with
  | .Expr a value => .Expr (p a) (ofExpr src (argAt path 0) value)
  | .Assign a targets value typeComment =>
    .Assign (p a) (wrap (ofExprs src path 0 targets.val))
      (ofExpr src (argAt path 1) value) (tc typeComment.val)
  | .AnnAssign a target annotation value simple =>
    .AnnAssign (p a) (ofExpr src (argAt path 0) target)
      (ofExpr src (argAt path 1) annotation)
      (wrap (ofOptE src (argAt path 2) value.val)) (ofPyInt simple)
  | .AugAssign a target op value =>
    .AugAssign (p a) (ofExpr src (argAt path 0) target)
      (ofOperator (argAt path 1) op) (ofExpr src (argAt path 2) value)
  | .For a target iter body orelse typeComment =>
    .For (p a) (ofExpr src (argAt path 0) target) (ofExpr src (argAt path 1) iter)
      (wrap (ofStmts src path 2 body.val)) (wrap (ofStmts src path 3 orelse.val))
      (tc typeComment.val)
  | .AsyncFor a target iter body orelse typeComment =>
    .AsyncFor (p a) (ofExpr src (argAt path 0) target)
      (ofExpr src (argAt path 1) iter)
      (wrap (ofStmts src path 2 body.val)) (wrap (ofStmts src path 3 orelse.val))
      (tc typeComment.val)
  | .While a test body orelse =>
    .While (p a) (ofExpr src (argAt path 0) test)
      (wrap (ofStmts src path 1 body.val)) (wrap (ofStmts src path 2 orelse.val))
  | .If a test body orelse =>
    .If (p a) (ofExpr src (argAt path 0) test)
      (wrap (ofStmts src path 1 body.val)) (wrap (ofStmts src path 2 orelse.val))
  | .With a items body typeComment =>
    .With (p a) (wrap (ofWithItems src path 0 items.val))
      (wrap (ofStmts src path 1 body.val)) (tc typeComment.val)
  | .AsyncWith a items body typeComment =>
    .AsyncWith (p a) (wrap (ofWithItems src path 0 items.val))
      (wrap (ofStmts src path 1 body.val)) (tc typeComment.val)
  | .Raise a exc cause =>
    .Raise (p a) (wrap (ofOptE src (argAt path 0) exc.val))
      (wrap (ofOptE src (argAt path 1) cause.val))
  | .Try a body handlers orelse finalbody =>
    .Try (p a) (wrap (ofStmts src path 0 body.val))
      (wrap (ofHandlers src path 1 handlers.val))
      (wrap (ofStmts src path 2 orelse.val))
      (wrap (ofStmts src path 3 finalbody.val))
  | .TryStar a body handlers orelse finalbody =>
    .TryStar (p a) (wrap (ofStmts src path 0 body.val))
      (wrap (ofHandlers src path 1 handlers.val))
      (wrap (ofStmts src path 2 orelse.val))
      (wrap (ofStmts src path 3 finalbody.val))
  | .Assert a test msg =>
    .Assert (p a) (ofExpr src (argAt path 0) test)
      (wrap (ofOptE src (argAt path 1) msg.val))
  | .Return a value => .Return (p a) (wrap (ofOptE src (argAt path 0) value.val))
  | .Delete a targets => .Delete (p a) (wrap (ofExprs src path 0 targets.val))
  | .Pass a => .Pass (p a)
  | .Break a => .Break (p a)
  | .Continue a => .Continue (p a)
  | .Global a names => .Global (p a) (wrap (names.val.map (wrap ·.val)))
  | .Nonlocal a names => .Nonlocal (p a) (wrap (names.val.map (wrap ·.val)))
  | .Import a names =>
    .Import (p a)
      (wrap (names.val.zipIdx.map (fun (n, j) => ofAlias src (itemAt path 0 j) n)))
  | .ImportFrom a module names level =>
    .ImportFrom (p a) (wrap (module.val.map (wrap ·.val)))
      (wrap (names.val.zipIdx.map (fun (n, j) => ofAlias src (itemAt path 1 j) n)))
      (wrap (level.val.map ofPyInt))
  | .FunctionDef a name args' body decorators returns typeComment typeParams =>
    .FunctionDef (p a) (wrap name.val) (ofArguments src (argAt path 1) args')
      (wrap (ofStmts src path 2 body.val))
      (wrap (ofExprs src path 3 decorators.val))
      (wrap (ofOptE src (argAt path 4) returns.val))
      (tc typeComment.val) (wrap (ofTypeParams src path 6 typeParams.val))
  | .AsyncFunctionDef a name args' body decorators returns typeComment typeParams =>
    .AsyncFunctionDef (p a) (wrap name.val) (ofArguments src (argAt path 1) args')
      (wrap (ofStmts src path 2 body.val))
      (wrap (ofExprs src path 3 decorators.val))
      (wrap (ofOptE src (argAt path 4) returns.val))
      (tc typeComment.val) (wrap (ofTypeParams src path 6 typeParams.val))
  | .ClassDef a name bases keywords body decorators typeParams =>
    .ClassDef (p a) (wrap name.val) (wrap (ofExprs src path 1 bases.val))
      (wrap (ofKeywords src path 2 keywords.val))
      (wrap (ofStmts src path 3 body.val))
      (wrap (ofExprs src path 4 decorators.val))
      (wrap (ofTypeParams src path 5 typeParams.val))
  | .Match a subject cases =>
    .Match (p a) (ofExpr src (argAt path 0) subject)
      (wrap (ofMatchCases src path 1 cases.val))
  | .TypeAlias a name typeParams value =>
    .TypeAlias (p a) (ofExpr src (argAt path 0) name)
      (wrap (ofTypeParams src path 1 typeParams.val))
      (ofExpr src (argAt path 2) value)

end

/-- Relabel a module body. Each top-level statement is command `i`, so its path is
    `[i]` and the module root is the empty path. -/
def relabel (src : Src) (stmts : Array (stmt SourceRange)) : Array (stmt Pos) :=
  stmts.zipIdx.map (fun (s, i) => ofStmt src (NodeId.root.child i) s)

end Pylate.Label
