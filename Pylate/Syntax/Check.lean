/-
Subset checking and lowering, fused into one Validation-applicative pass.

`Va A` is `Except (Array Violation) A` with an applicative that
accumulates errors on both sides instead of short-circuiting: lowering a
node with three offending children reports all three. The checker
therefore never fail-fasts; `lowerModule` returns either the core program
or the complete violation list.

The input is the **Strata Python AST**, relabelled by `Syntax/Label.lean` so every
annotation is a `Pos`. Matching on its constructors rather than on `_type` strings
is what makes the dispatch total: a construct the subset does not handle is a
missing case the compiler reports, not a string that falls through at runtime.
-/
import Pylate.Syntax.Nodes
import Pylate.Syntax.Label
import Pylate.Syntax.ClassTable

namespace Pylate

/-- The relabelled Strata AST this file lowers. -/
abbrev PyExpr := StrataPython.expr Pos
abbrev PyStmt := StrataPython.stmt Pos
abbrev PyConst := StrataPython.constant Pos
abbrev PyArguments := StrataPython.arguments Pos
abbrev PyHandler := StrataPython.excepthandler Pos

/-- The `Const` a Strata constant denotes.

    The dialect names each constant kind with its own constructor, so the match is
    exhaustive rather than a sequence of type tests. Note the sign is
    **structural**: `-1` arrives as `ConNeg 1` rather than a negation applied to
    `1`.

    `none` is the fail-closed answer for the three outside the subset -- bytes,
    complex and `Ellipsis` -- which the caller reports as `unsupported-node`. -/
def constOf : PyConst → Option Const
  | .ConNone _ => some .cnone
  | .ConTrue _ => some (.cbool true)
  | .ConFalse _ => some (.cbool false)
  | .ConPos _ v => some (.cint (v.val : Int))
  | .ConNeg _ v => some (.cint (-(v.val : Int)))
  | .ConString _ v => some (.cstr v.val)
  | .ConFloat _ v => some (.cfloat v.val)
  | .ConEllipsis _ | .ConBytes _ _ | .ConComplex _ _ _ => none

/-- How a constant reads in a diagnostic, standing in for the old
    `Json.compress` of the value. -/
def constText : PyConst → String
  | .ConNone _ => "None"
  | .ConTrue _ => "True"
  | .ConFalse _ => "False"
  | .ConPos _ v => toString v.val
  | .ConNeg _ v => s!"-{v.val}"
  | .ConString _ v => s!"\"{v.val}\""
  | .ConFloat _ v => v.val
  | .ConEllipsis _ => "Ellipsis"
  | .ConBytes _ _ => "bytes"
  | .ConComplex _ r i => s!"complex({r.val}, {i.val})"

/-- Is this constant the `...` that marks a stub body? -/
def isEllipsis : PyConst → Bool
  | .ConEllipsis _ => true
  | _ => false

structure Violation where
  line   : Nat
  col    : Nat
  node   : NodeId
  rule   : String
  detail : String
deriving Repr, Inhabited

inductive Va (A : Type)
  | ok  (a : A)
  | err (es : Array Violation)
deriving Inhabited

namespace Va

instance : Inhabited (Va A) := ⟨err #[]⟩

def map (f : A → B) : Va A → Va B
  | ok a => ok (f a)
  | err es => err es

/-- The accumulating combination: both sides' violations are kept. -/
def seq' : Va (A → B) → Va A → Va B
  | ok f, ok a => ok (f a)
  | err es, ok _ => err es
  | ok _, err es => err es
  | err es, err es' => err (es ++ es')

instance : Functor Va := { map := fun f v => map f v }
instance : Pure Va := ⟨ok⟩
instance : Seq Va := ⟨fun f a => seq' f (a ())⟩

def map2 (f : A → B → G) (a : Va A) (b : Va B) : Va G :=
  seq' (map f a) b

def map3 (f : A → B → G → D) (a : Va A) (b : Va B) (c : Va G) : Va D :=
  seq' (map2 f a b) c

def map4 (f : A → B → G → D → E) (a : Va A) (b : Va B) (c : Va G)
    (d : Va D) : Va E :=
  seq' (map3 f a b c) d

/-- Run a check for its violations, keep the payload of the second. -/
def also (chk : Va Unit) (v : Va A) : Va A :=
  map2 (fun _ a => a) chk v

def traverse (f : A → Va B) : List A → Va (List B)
  | [] => ok []
  | a :: as => map2 (· :: ·) (f a) (traverse f as)

/-- Over an `Array`, which is how the Strata AST holds a `Seq` argument. -/
def traverseA {A B} (f : A → Va B) (a : Array A) : Va (List B) :=
  traverse f a.toList

/-- Over an `Option`, which is how the Strata AST holds an optional argument. -/
def opt {A B} (f : A → Va B) (o : Option A) : Va (Option B) :=
  match o with
  | none => ok none
  | some a => map some (f a)

end Va

/-- A violation at a node. The position comes off the node itself now: `Label.lean`
    relabels the Strata AST from `SourceRange` to `Pos` before lowering, so the id,
    line and column are all present on the annotation. -/
def viol (p : Pos) (rule detail : String) : Va A :=
  .err #[⟨p.line, p.col, p.id, rule, detail⟩]

def violU (p : Pos) (rule detail : String) : Va Unit :=
  viol p rule detail

def okU : Va Unit := .ok ()

-- ------------------------------------------------------------- contexts

structure Cx where
  inFunc  : Bool := false
  inClass : Bool := false
  /-- The class whose method body is being lowered, when there is one. Only
      `super()` needs it: a zero-argument `super()` is defined relative to the
      class the method is *written in*, which the AST does not record at the
      call. -/
  clsName : Option String := none

-- ----------------------------------------------------------- name lists

/-- Names the analyzer gives builtin semantics; binding them anywhere
    would silently change meaning, so binding is a violation. -/
def reservedNames : List String :=
  ["len", "range", "print", "isinstance", "next", "iter",
   "list", "dict", "set", "tuple", "str", "int", "bool", "float",
   "complex", "object", "dataclass", "TypedDict"] ++ builtinExcs

/-- Dynamic escape hatches from one-step dispatch; any use is rejected. -/
def bannedNames : List String :=
  ["super", "globals", "locals", "eval", "exec", "compile", "getattr",
   "setattr", "hasattr", "delattr", "vars", "__import__", "open",
   "input", "breakpoint", "id", "type", "classmethod", "staticmethod",
   "property", "memoryview"]

def unmodeledScalarConstructors : List String :=
  ["bool", "int", "float", "complex", "object"]

def typingWhitelist : List String :=
  ["TypedDict", "Optional", "List", "Dict", "Set", "Tuple", "Union",
   "Literal", "Annotated", "Required", "NotRequired", "ReadOnly", "Any",
   "Never", "NoReturn"]

def hookMethods : List String :=
  ["__getattr__", "__getattribute__", "__setattr__", "__delattr__",
   "__new__", "__del__", "__init_subclass__", "__set_name__",
   "__mro_entries__", "__class_getitem__"]

def unsupportedInplaceDunders : List String :=
  ["__iadd__", "__isub__", "__imul__", "__itruediv__", "__ifloordiv__",
   "__imod__", "__ipow__", "__imatmul__", "__ior__", "__iand__", "__ixor__",
   "__ilshift__", "__irshift__"]

/-- `MatMult` is the one arithmetic operator with no counterpart, so it is the
    only `none`, and the match being exhaustive is what proves it. -/
def binOpOf : StrataPython.operator Pos → Option BinOp
  | .Add _ => some .add | .Sub _ => some .sub | .Mult _ => some .mul
  | .Div _ => some .div | .FloorDiv _ => some .floordiv
  | .Mod _ => some .mod | .Pow _ => some .pow
  | .BitOr _ => some .bitOr | .BitAnd _ => some .bitAnd
  | .BitXor _ => some .bitXor | .LShift _ => some .lshift
  | .RShift _ => some .rshift
  | .MatMult _ => none

def operatorName : StrataPython.operator Pos → String
  | .Add _ => "Add" | .Sub _ => "Sub" | .Mult _ => "Mult"
  | .MatMult _ => "MatMult" | .Div _ => "Div" | .Mod _ => "Mod"
  | .Pow _ => "Pow" | .LShift _ => "LShift" | .RShift _ => "RShift"
  | .BitOr _ => "BitOr" | .BitXor _ => "BitXor" | .BitAnd _ => "BitAnd"
  | .FloorDiv _ => "FloorDiv"

/-- Every comparison operator is modelled, so this is total. -/
def cmpOpOf : StrataPython.cmpop Pos → Option CmpOp
  | .Lt _ => some .lt | .LtE _ => some .le | .Gt _ => some .gt
  | .GtE _ => some .ge | .Eq _ => some .eq | .NotEq _ => some .ne
  | .In _ => some .inOp | .NotIn _ => some .notInOp
  | .Is _ => some .isOp | .IsNot _ => some .isNotOp

def cmpOpName : StrataPython.cmpop Pos → String
  | .Lt _ => "Lt" | .LtE _ => "LtE" | .Gt _ => "Gt" | .GtE _ => "GtE"
  | .Eq _ => "Eq" | .NotEq _ => "NotEq" | .In _ => "In"
  | .NotIn _ => "NotIn" | .Is _ => "Is" | .IsNot _ => "IsNot"

/-- The constructor name, for diagnostics that name the node kind they reject. -/
def exprName : PyExpr → String
  | .Constant .. => "Constant" | .Name .. => "Name"
  | .Attribute .. => "Attribute" | .Subscript .. => "Subscript"
  | .Starred .. => "Starred" | .BinOp .. => "BinOp"
  | .UnaryOp .. => "UnaryOp" | .BoolOp .. => "BoolOp"
  | .Compare .. => "Compare" | .Call .. => "Call"
  | .IfExp .. => "IfExp" | .Lambda .. => "Lambda"
  | .NamedExpr .. => "NamedExpr" | .List .. => "List"
  | .Tuple .. => "Tuple" | .Set .. => "Set" | .Dict .. => "Dict"
  | .ListComp .. => "ListComp" | .SetComp .. => "SetComp"
  | .GeneratorExp .. => "GeneratorExp" | .DictComp .. => "DictComp"
  | .Slice .. => "Slice" | .JoinedStr .. => "JoinedStr"
  | .FormattedValue .. => "FormattedValue" | .TemplateStr .. => "TemplateStr"
  | .Interpolation .. => "Interpolation" | .Await .. => "Await"
  | .Yield .. => "Yield" | .YieldFrom .. => "YieldFrom"

/-- The `Pos` on any expression, whatever its constructor. -/
def exprPos : PyExpr → Pos
  | .Constant p .. | .Name p .. | .Attribute p .. | .Subscript p ..
  | .Starred p .. | .BinOp p .. | .UnaryOp p .. | .BoolOp p ..
  | .Compare p .. | .Call p .. | .IfExp p .. | .Lambda p ..
  | .NamedExpr p .. | .List p .. | .Tuple p .. | .Set p .. | .Dict p ..
  | .ListComp p .. | .SetComp p .. | .GeneratorExp p .. | .DictComp p ..
  | .Slice p .. | .JoinedStr p .. | .FormattedValue p .. | .TemplateStr p ..
  | .Interpolation p .. | .Await p .. | .Yield p .. | .YieldFrom p .. => p

/-- The `Pos` on any statement. -/
def stmtPos : PyStmt → Pos
  | .Expr p .. | .Assign p .. | .AnnAssign p .. | .AugAssign p ..
  | .For p .. | .AsyncFor p .. | .While p .. | .If p .. | .With p ..
  | .AsyncWith p .. | .Raise p .. | .Try p .. | .TryStar p .. | .Assert p ..
  | .Return p .. | .Delete p .. | .Pass p | .Break p | .Continue p
  | .Global p .. | .Nonlocal p .. | .Import p .. | .ImportFrom p ..
  | .FunctionDef p .. | .AsyncFunctionDef p .. | .ClassDef p .. | .Match p ..
  | .TypeAlias p .. => p

/-- Is this JSON node a `True`, `False` or `None` literal?

    The only operands `is` and `is not` may compare against. Identity is not a
    function of a value in CPython: equal scalars may be one object or two, and
    which depends on interning that is an implementation detail rather than
    language semantics. Within one code object constants are deduplicated, so
    `1000 is 1000` is `True`, while `c = 1000; c is int("1000")` is `False`;
    small ints and some strings are cached, so `5 is int("5")` is `True`.

    Modelling that would mean modelling CPython's constant pool. The analysis
    instead gives immutable scalars no heap location at all, which is sound
    precisely because immutability makes aliasing unobservable for them -- except
    through `is` and `id`. So `id` is a banned builtin, and `is` is confined to
    the three singletons, where identity *is* well defined: there is exactly one
    `True`, one `False` and one `None`, guaranteed by the language rather than by
    an implementation choice.

    `../doc/ALGORITHM_AND_SOUNDNESS.md` has the measurements. -/
def isSingletonLiteral (e : PyExpr) : Bool :=
  match e with
  | .Constant _ v _ =>
    match v with
    | .ConNone _ | .ConTrue _ | .ConFalse _ => true
    | _ => false
  | _ => false

mutual

/-- Does this body contain a `yield`, without descending into a nested function?
    The traversal is explicit now rather than a walk over an untyped tree, so the
    scope boundary is a case rather than a name test. -/
partial def stmtHasYield (s : PyStmt) : Bool :=
  match s with
  | .Expr _ e => exprHasYield e
  | .Assign _ _ v _ => exprHasYield v
  | .AnnAssign _ _ _ v _ => (v.val.map exprHasYield).getD false
  | .AugAssign _ _ _ v => exprHasYield v
  | .Return _ v => (v.val.map exprHasYield).getD false
  | .Assert _ t m => exprHasYield t || (m.val.map exprHasYield).getD false
  | .Raise _ e c =>
    (e.val.map exprHasYield).getD false || (c.val.map exprHasYield).getD false
  | .Delete _ ts => ts.val.any exprHasYield
  | .If _ t b o | .While _ t b o =>
    exprHasYield t || b.val.any stmtHasYield || o.val.any stmtHasYield
  | .For _ _ i b o _ | .AsyncFor _ _ i b o _ =>
    exprHasYield i || b.val.any stmtHasYield || o.val.any stmtHasYield
  | .With _ items b _ | .AsyncWith _ items b _ =>
    items.val.any (fun i => match i with
      | .mk_withitem _ c _ => exprHasYield c) || b.val.any stmtHasYield
  | .Try _ b hs o f | .TryStar _ b hs o f =>
    b.val.any stmtHasYield
      || hs.val.any (fun h => match h with
           | .ExceptHandler _ _ _ hb => hb.val.any stmtHasYield)
      || o.val.any stmtHasYield || f.val.any stmtHasYield
  | .Match _ subj cases =>
    exprHasYield subj
      || cases.val.any (fun c => match c with
           | .mk_match_case _ _ g cb =>
             (g.val.map exprHasYield).getD false || cb.val.any stmtHasYield)
  -- A nested `def`/`class` is its own scope: a `yield` inside one does not make
  -- the enclosing function a generator.
  | .FunctionDef .. | .AsyncFunctionDef .. | .ClassDef .. => false
  | .Pass _ | .Break _ | .Continue _ | .Global .. | .Nonlocal ..
  | .Import .. | .ImportFrom .. | .TypeAlias .. => false

partial def exprHasYield (e : PyExpr) : Bool :=
  match e with
  | .Yield .. | .YieldFrom .. => true
  -- `lambda` opens a scope, so a `yield` inside it belongs to the lambda.
  | .Lambda .. => false
  | .Constant .. | .Name .. => false
  | .Attribute _ v _ _ | .Starred _ v _ | .Await _ v => exprHasYield v
  | .Subscript _ v s _ => exprHasYield v || exprHasYield s
  | .BinOp _ l _ r => exprHasYield l || exprHasYield r
  | .UnaryOp _ _ v => exprHasYield v
  | .BoolOp _ _ vs => vs.val.any exprHasYield
  | .Compare _ l _ cs => exprHasYield l || cs.val.any exprHasYield
  | .Call _ f args kws =>
    exprHasYield f || args.val.any exprHasYield
      || kws.val.any (fun k => match k with
           | .mk_keyword _ _ v => exprHasYield v)
  | .IfExp _ t b o => exprHasYield t || exprHasYield b || exprHasYield o
  | .NamedExpr _ t v => exprHasYield t || exprHasYield v
  | .List _ es _ | .Tuple _ es _ | .Set _ es
  | .JoinedStr _ es | .TemplateStr _ es => es.val.any exprHasYield
  | .Dict _ ks vs =>
    ks.val.any (fun k => match k with
      | .some_expr _ x => exprHasYield x
      | .missing_expr _ => false) || vs.val.any exprHasYield
  | .ListComp _ el gs | .SetComp _ el gs | .GeneratorExp _ el gs =>
    exprHasYield el || gs.val.any (fun g => match g with
      | .mk_comprehension _ _ i ifs _ =>
        exprHasYield i || ifs.val.any exprHasYield)
  | .DictComp _ k v gs =>
    exprHasYield k || exprHasYield v
      || gs.val.any (fun g => match g with
           | .mk_comprehension _ _ i ifs _ =>
             exprHasYield i || ifs.val.any exprHasYield)
  | .Slice _ l u s =>
    (l.val.map exprHasYield).getD false || (u.val.map exprHasYield).getD false
      || (s.val.map exprHasYield).getD false
  | .FormattedValue _ v _ f =>
    exprHasYield v || (f.val.map exprHasYield).getD false
  | .Interpolation _ v _ _ f =>
    exprHasYield v || (f.val.map exprHasYield).getD false

end

partial def annotationName (e : PyExpr) : Option String :=
  match e with
  | .Name _ ident _ => some ident.val
  | .Attribute _ value attr _ => do
    let p ← annotationName value
    pure s!"{p}.{attr.val}"
  | _ => none

def annotationConst (e : PyExpr) : Option Const :=
  match e with
  | .Constant _ v _ => constOf v
  | _ => none

/-- Recursive annotation grammar. Unknown generic heads are preserved so
    admission can reject them explicitly instead of erasing parameters. -/
partial def parseAnn (e : PyExpr) : Ann :=
  match e with
  | .Name _ ident _ =>
    let n := ident.val
    if n == "Any" then .any
    else if n == "None" then .atom "None"
    else .atom n
  | .Attribute .. =>
    match annotationName e with
    | some "typing.Any" => .any
    | some n => .atom n
    | none => .any
  | .Constant _ v _ =>
    match v with
    | .ConNone _ => .atom "None"
    | .ConString _ s => .atom s.val
    | _ => .any
  | .BinOp _ left op right =>
    match op with
    | .BitOr _ => .union [parseAnn left, parseAnn right]
    | _ => .any
  | .Subscript _ value slice _ =>
    let head := (annotationName value).getD ""
    let short := (head.splitOn ".").getLastD head
    let elems := match slice with
      | .Tuple _ elts _ => elts.val.toList
      | other => [other]
    let args := elems.map parseAnn
    match short with
    | "Optional" => .union [args.headD .any, .atom "None"]
    | "Union" => .union args
    | "Required" => .required (args.headD .any)
    | "NotRequired" => .notRequired (args.headD .any)
    | "ReadOnly" => .readOnly (args.headD .any)
    | "Annotated" => args.headD .any
    | "Literal" => .literal (elems.filterMap annotationConst)
    | "List" | "list" => .generic "list" args
    | "Dict" | "dict" => .generic "dict" args
    | "Set" | "set" => .generic "set" args
    | "Tuple" | "tuple" =>
      -- `tuple[T, ...]`: the `...` is the variadic marker, and it is a real
      -- `ConEllipsis` now rather than a JSON object to compare textually.
      let variadic := elems.length == 2 &&
        (match elems[1]! with
         | .Constant _ c _ => isEllipsis c
         | _ => false)
      .generic "tuple" (if variadic then args.take 1 else args) variadic
    | _ => .generic head args
  | _ => .any

partial def normalizeFieldAnn (a : Ann) (required : Bool) :
    Ann × Bool × Bool :=
  match a with
  | .required inner =>
    let (a, _, ro) := normalizeFieldAnn inner true
    (a, true, ro)
  | .notRequired inner =>
    let (a, _, ro) := normalizeFieldAnn inner false
    (a, false, ro)
  | .readOnly inner =>
    let (a, req, _) := normalizeFieldAnn inner required
    (a, req, true)
  | _ => (a, required, false)

-- ------------------------------------------------------------- lowering

mutual

partial def lowerExpr (cx : Cx) (e : PyExpr) : Va Expr :=
  match e with
  | .Constant p v _ =>
    match constOf v with
    | some c => pure (.const p c)
    | none => viol p "unsupported-node"
        s!"constant of unsupported kind: {constText v}"
  | .Name p ident _ =>
    let n := ident.val
    if bannedNames.contains n then
      viol p "banned-builtin" s!"{n} is a dynamic escape hatch from one-step dispatch and is outside the subset"
    else pure (.name p n)
  | .BinOp p left op right =>
    match binOpOf op with
    | some bop =>
      Va.map2 (Expr.binop p bop) (lowerExpr cx left) (lowerExpr cx right)
    | none => Va.also
        (violU p "unsupported-node"
          s!"operator {operatorName op} is outside the subset")
        (Va.map2 (Expr.binop p .add) (lowerExpr cx left) (lowerExpr cx right))
  | .UnaryOp p op operand =>
    match op with
    | .Not _ => Va.map (Expr.notE p) (lowerExpr cx operand)
    | .USub _ => Va.map (Expr.unary p .neg) (lowerExpr cx operand)
    -- `+x` is not the identity: it calls `__pos__`, and on a str or a list it
    -- is a TypeError. Lowering it to its operand erased both.
    | .UAdd _ => Va.map (Expr.unary p .pos) (lowerExpr cx operand)
    | .Invert _ => Va.map (Expr.unary p .invert) (lowerExpr cx operand)
  | .BoolOp p op values =>
    let isAnd := match op with | .And _ => true | .Or _ => false
    Va.map (Expr.boolop p isAnd) (Va.traverseA (lowerExpr cx) values.val)
  | .Compare p left ops comparators =>
    let comps := comparators.val.toList
    let opList := ops.val.toList
    -- chained comparison: conjunction of pairwise comparisons
    let pairs := (left :: comps).zip comps
    let identityChk := fun ((l, r) : PyExpr × PyExpr) (op : StrataPython.cmpop Pos) =>
      match op with
      | .Is _ | .IsNot _ =>
        if isSingletonLiteral l || isSingletonLiteral r then okU
        else violU p "identity-comparison"
          s!"{cmpOpName op} against a non-singleton: identity is only well defined against True, False and None, because equal scalars may be one object or two depending on CPython interning"
      | _ => okU
    let lowerPair := fun ((l, r) : PyExpr × PyExpr) (op : StrataPython.cmpop Pos) =>
      match cmpOpOf op with
      | some cop =>
        Va.also (identityChk (l, r) op) <|
          Va.map2 (Expr.cmp (exprPos r) cop) (lowerExpr cx l) (lowerExpr cx r)
      | none => viol p "unsupported-node" s!"comparison operator {cmpOpName op}"
    match pairs, opList with
    | [(l, r)], [o] =>
      match cmpOpOf o with
      | some cop =>
        Va.also (identityChk (l, r) o) <|
          Va.map2 (Expr.cmp p cop) (lowerExpr cx l) (lowerExpr cx r)
      | none => viol p "unsupported-node" s!"comparison operator {cmpOpName o}"
    | _, _ =>
      if pairs.length == opList.length then
        Va.map (Expr.boolop p true)
          (Va.traverse (fun (pr, o) => lowerPair pr o) (pairs.zip opList))
      else viol p "unsupported-node" "malformed Compare node"
  | .Attribute p value attr _ =>
    Va.map (fun v => Expr.attr p v attr.val) (lowerExpr cx value)
  | .Subscript p value slice _ =>
    match slice with
    | .Slice .. =>
      viol p "unsupported-node" "slice expressions are outside the subset"
    | _ => Va.map2 (Expr.subscr p) (lowerExpr cx value) (lowerExpr cx slice)
  | .Call p func args keywords =>
    -- `super().m(...)` is the one admitted use of `super`. It is recognised here,
    -- before the callee is lowered, because lowering it would hit the `Name`
    -- case and report `banned-builtin`. Every *other* spelling still does: bare
    -- `super`, `s = super()`, `super().x` without a call, and the two-argument
    -- form all reach the callee through an ordinary path and are refused there.
    -- So this carve-out admits exactly the immediate-call shape and nothing else.
    --
    -- The owner is baked in as the synthetic receiver `@super:<Owner>`, the same
    -- `@`-prefixed convention `lowerFuncDef` uses for `@get:f`/`@set:f`. `@` is
    -- not an identifier character, so it cannot collide with a Python name.
    let superShape : Option (String × Pos × Bool) :=
      match func with
      | .Attribute _ inner attr _ =>
        match inner with
        | .Call ip (.Name _ callee _) iargs ikws =>
          if callee.val == "super" then
            some (attr.val, ip, iargs.val.isEmpty && ikws.val.isEmpty)
          else none
        | _ => none
      | _ => none
    let superChk : Va Unit :=
      match superShape with
      | none => okU
      | some (_, ip, zeroArg) =>
        if !zeroArg then
          violU ip "super-form"
            "super(C, self) is outside the subset: the zero-argument form is the only one admitted, because it fixes the owner class lexically"
        else if cx.clsName.isNone then
          violU ip "super-form"
            "super() outside a method body: there is no class for it to be relative to"
        else okU
    let starChk : Va Unit := args.val.foldl (init := okU) fun acc a =>
      match a with
      | .Starred sp .. =>
        Va.also acc (violU sp "starred-arg" "*args at a call site")
      | _ => acc
    let kwChk : Va Unit := keywords.val.foldl (init := okU) fun acc k =>
      match k with
      | .mk_keyword _ arg _ =>
        if arg.val.isNone then
          Va.also acc (violU p "starred-arg" "**kwargs at a call site")
        else acc
    let kws := keywords.val.toList.filterMap (fun k =>
      match k with
      | .mk_keyword _ arg value =>
        match arg.val with
        | some name => some (name.val, value)
        | none => none)
    let calleeVa : Va Expr :=
      match superShape, cx.clsName with
      | some (meth, _, _), some owner =>
        pure (.attr p (.name p s!"@super:{owner}") meth)
      | _, _ => lowerExpr cx func
    Va.also superChk <| Va.also starChk <| Va.also kwChk <|
      Va.map3 (Expr.call p)
        calleeVa
        (Va.traverseA (lowerExpr cx)
          (args.val.filter (fun a => match a with
            | .Starred .. => false
            | _ => true)))
        (Va.traverse
          (fun (nm, v) => Va.map (fun x => (nm, x)) (lowerExpr cx v)) kws)
  | .List p elts _ =>
    Va.map (Expr.listlit p) (Va.traverseA (lowerExpr cx) elts.val)
  | .Tuple p elts _ =>
    Va.map (Expr.tuplelit p) (Va.traverseA (lowerExpr cx) elts.val)
  | .Set p elts =>
    Va.map (Expr.setlit p) (Va.traverseA (lowerExpr cx) elts.val)
  | .Dict p keys values =>
    -- A `**mapping` entry is a `missing_expr` key, which is how CPython's `None`
    -- key arrives.
    let starChk : Va Unit := keys.val.foldl (init := okU) fun acc k =>
      match k with
      | .missing_expr _ =>
        Va.also acc (violU p "starred-arg" "**mapping inside a dict literal")
      | _ => acc
    let pairs := (keys.val.toList.zip values.val.toList).filterMap
      (fun (k, v) => match k with
        | .some_expr _ x => some (x, v)
        | .missing_expr _ => none)
    Va.also starChk <|
      Va.map (Expr.dictlit p)
        (Va.traverse
          (fun (k, v) => Va.map2 (fun a b => (a, b)) (lowerExpr cx k)
            (lowerExpr cx v)) pairs)
  | .IfExp p test body orelse =>
    Va.map3 (Expr.ifexp p) (lowerExpr cx test) (lowerExpr cx body)
      (lowerExpr cx orelse)
  | .JoinedStr p values =>
    Va.map (Expr.fstr p) (Va.traverseA (lowerExpr cx) values.val)
  | .FormattedValue _ value _ _ => lowerExpr cx value
  | .ListComp p elt gens => lowerComp cx p .clist elt none gens
  | .SetComp p elt gens => lowerComp cx p .cset elt none gens
  | .GeneratorExp p elt gens => lowerComp cx p .cgen elt none gens
  | .DictComp p key value gens => lowerComp cx p .cdict key (some value) gens
  | .Yield p _ | .YieldFrom p _ =>
    viol p "unsupported-node"
      "yield in value position: the sent value is not modeled"
  | .Lambda p .. => viol p "lambda" "lambda expressions are outside the subset"
  | .NamedExpr p .. =>
    viol p "walrus" "assignment expressions are outside the subset"
  | .Await p _ => viol p "async-construct" "await is outside the subset"
  | .Starred p .. => viol p "starred-arg" "starred expression"
  -- A bare `Slice` outside a subscript, which the subscript case rejects too.
  | .Slice p .. =>
    viol p "unsupported-node" "slice expressions are outside the subset"
  -- PEP 750 template strings, new in the dialect and not in the subset.
  | .TemplateStr p _ =>
    viol p "unsupported-node" "template strings (PEP 750) are outside the subset"
  | .Interpolation p .. =>
    viol p "unsupported-node"
      "template-string interpolation (PEP 750) is outside the subset"

/-- The four comprehension forms, which differ only in their kind and whether
    they carry a separate value expression. -/
partial def lowerComp (cx : Cx) (p : Pos) (kind : CompKind) (elt : PyExpr)
    (value : Option PyExpr)
    (gens : StrataDDM.Ann (Array (StrataPython.comprehension Pos)) Pos) :
    Va Expr :=
  if gens.val.size != 1 then
    viol p "multi-generator-comprehension"
      s!"comprehension with {gens.val.size} generators; the subset admits one"
  else
    match gens.val[0]! with
    | .mk_comprehension _ target iter ifs isAsync =>
      let asyncChk :=
        match isAsync with
        | .IntPos _ v => if v.val != 0 then
            violU p "async-construct" "async comprehension" else okU
        | .IntNeg _ _ => okU
      match target with
      | .Name tp ident _ =>
        let tn := ident.val
        if reservedNames.contains tn || bannedNames.contains tn then
          viol tp "shadowed-builtin"
            s!"comprehension target {tn} shadows a builtin name"
        else
          Va.also asyncChk <|
            Va.map4 (fun el ev it conds => Expr.comp p kind el ev tn it conds)
              (lowerExpr cx elt)
              (match value with
               | some v => Va.map some (lowerExpr cx v)
               | none => pure none)
              (lowerExpr cx iter)
              (Va.traverseA (lowerExpr cx) ifs.val)
      | _ => viol p "unsupported-node" "comprehension target must be a name"

partial def lowerTarget (cx : Cx) (e : PyExpr) : Va Target :=
  match e with
  | .Name p ident _ =>
    let n := ident.val
    if reservedNames.contains n || bannedNames.contains n then
      viol p "shadowed-builtin" s!"binding {n} shadows a name the analyzer gives builtin semantics"
    else pure (.tname p n)
  | .Attribute p value attr _ =>
    Va.map (fun v => Target.tattr p v attr.val) (lowerExpr cx value)
  | .Subscript p value slice _ =>
    Va.map2 (Target.tsub p) (lowerExpr cx value) (lowerExpr cx slice)
  | .Tuple p elts _ =>
    Va.map (Target.ttuple p) (Va.traverseA (lowerTarget cx) elts.val)
  | .Starred p .. => viol p "starred-arg" "starred assignment target"
  -- Everything else, `[a, b] = xs` included: a list target binds exactly as a
  -- tuple target does, but it is outside the admitted subset.
  | other =>
    viol (exprPos other) "unsupported-node"
      s!"assignment target {exprName other}"

partial def lowerStmt (cx : Cx) (s : PyStmt) : Va (List Stmt) :=
  match s with
  | .Assign p targets value _ =>
    Va.map2 (fun tgts e => tgts.map (fun t => Stmt.assign p t e))
      (Va.traverseA (lowerTarget cx) targets.val)
      (lowerExpr cx value)
  | .AnnAssign p target _ value _ =>
    match target with
    | .Name _ ident _ =>
      Va.map (fun e => [Stmt.annAssign p ident.val e])
        (Va.opt (lowerExpr cx) value.val)
    | other =>
      Va.map2 (fun t e => match e with
          | some e => [Stmt.assign p t e]
          | none => [Stmt.pass p])
        (lowerTarget cx other) (Va.opt (lowerExpr cx) value.val)
  | .AugAssign p .. =>
    viol p "unsupported-node"
      "augmented assignment requires Python's in-place operator protocol"
  | .Expr p value =>
    -- yield is admitted in statement position only: a yield expression's
    -- value is what send() delivers, and send is not modeled
    match value with
    | .Yield yp inner =>
      Va.map (fun e => [Stmt.exprS p (Expr.yieldE yp e)])
        (Va.opt (lowerExpr cx) inner.val)
    | .YieldFrom yp inner =>
      Va.map (fun e => [Stmt.exprS p (Expr.yieldFrom yp e)])
        (lowerExpr cx inner)
    | other => Va.map (fun e => [Stmt.exprS p e]) (lowerExpr cx other)
  | .If p test body orelse =>
    Va.map3 (fun c t e => [Stmt.ifS p c t e])
      (lowerExpr cx test) (lowerBody cx body.val) (lowerBody cx orelse.val)
  | .While p test body orelse =>
    Va.map3 (fun c b o => [Stmt.whileS p c b o])
      (lowerExpr cx test) (lowerBody cx body.val) (lowerBody cx orelse.val)
  | .For p target iter body orelse _ =>
    Va.map4 (fun t i b o => [Stmt.forS p t i b o])
      (lowerTarget cx target) (lowerExpr cx iter)
      (lowerBody cx body.val) (lowerBody cx orelse.val)
  | .Try p body handlers orelse finalbody =>
    Va.map4 (fun b h o f => [Stmt.tryS p b h o f])
      (lowerBody cx body.val)
      (Va.traverseA (lowerHandler cx) handlers.val)
      (lowerBody cx orelse.val) (lowerBody cx finalbody.val)
  | .TryStar p .. => viol p "unsupported-node" "except* is outside the subset"
  | .Return p value =>
    Va.map (fun e => [Stmt.ret p e]) (Va.opt (lowerExpr cx) value.val)
  | .Break p => pure [.brk p]
  | .Continue p => pure [.cont p]
  | .Pass p => pure [.pass p]
  | .Raise p exc cause =>
    if cause.val.isSome then
      viol p "unsupported-node" "raise ... from ... is outside the subset"
    else
      match exc.val with
      | none => pure [.raiseS p none none]
      | some (.Name _ ident _) => pure [.raiseS p (some ident.val) none]
      | some (.Call cp func args keywords) =>
        match func with
        | .Name _ fname _ =>
          if args.val.size > 1 || !keywords.val.isEmpty then
            viol cp "unsupported-node"
              "exception construction in raise admits at most one positional argument and no keywords"
          else
            Va.map (fun a => [Stmt.raiseS p (some fname.val) a])
              (if h : args.val.size > 0
               then Va.map some (lowerExpr cx args.val[0])
               else pure none)
        | _ => viol p "unsupported-node" "raise of a non-name exception"
      | some _ => viol p "unsupported-node" "raise of a non-name exception"
  | .Assert p test _ =>
    Va.map (fun c => [Stmt.assertS p c]) (lowerExpr cx test)
  | .FunctionDef p name _ body _ _ _ _ =>
    -- the nested def is a violation, and its body is still traversed so
    -- one pass reports everything inside it as well
    Va.also
      (violU p "nested-function"
        s!"def {name.val} nested inside a function or statement body: closures are outside the subset")
      (Va.map (fun _ => [Stmt.pass p])
        (lowerBody { cx with inFunc := true } body.val))
  | .AsyncFunctionDef p .. => viol p "async-construct" "async def"
  | .ClassDef p name .. =>
    Va.also
      (violU p "nested-class"
        s!"class {name.val} not at module top level: dynamic class creation is outside the subset")
      (Va.map (fun _ => [Stmt.pass p]) (lowerClassDef s))
  | .ImportFrom p module names _ =>
    let modName := (module.val.map (·.val)).getD ""
    let importedNames := names.val.toList.map (fun a =>
      match a with | .mk_alias _ nm _ => nm.val)
    if importedNames.contains "*" then
      viol p "import-star" s!"from {modName} import *: star imports are outside the subset"
    else if modName == "dataclasses" then
      if importedNames.all (· == "dataclass") then pure [.pass p]
      else viol p "import" "from dataclasses only dataclass is admitted"
    else if modName == "typing" then
      if importedNames.all typingWhitelist.contains then pure [.pass p]
      else viol p "import" s!"from typing only {", ".intercalate typingWhitelist} are admitted"
    else viol p "import" s!"import from {modName}: imports are outside the subset (dataclasses and typing excepted)"
  | .Import p _ => viol p "import" "imports are outside the subset"
  | .Global p _ => viol p "global-stmt" "global is outside the subset"
  | .Nonlocal p _ => viol p "nonlocal-stmt" "nonlocal is outside the subset"
  | .Delete p targets =>
    let lowerDeleteTarget := fun (target : PyExpr) =>
      match target with
      | .Name .. => lowerTarget cx target
      | other =>
        viol (exprPos other) "shape-mutation"
          "del on an attribute or subscript is outside the shape-stable subset"
    Va.map (fun ts => ts.map (Stmt.delS p))
      (Va.traverseA lowerDeleteTarget targets.val)
  | .With p .. | .AsyncWith p .. =>
    viol p "with-stmt" "with is outside the subset"
  | .Match p .. => viol p "match-stmt" "match is outside the subset"
  | .AsyncFor p .. => viol p "async-construct" "async for is outside the subset"
  | .TypeAlias p .. =>
    viol p "unsupported-node" "type aliases (PEP 695) are outside the subset"

partial def lowerHandler (cx : Cx) (h : PyHandler) : Va Handler :=
  match h with
  | .ExceptHandler p ty name body =>
    let clsVa : Va (Option String) :=
      match ty.val with
      | none => pure none
      | some (.Name _ ident _) => pure (some ident.val)
      | some other => viol (exprPos other) "unsupported-node"
          "except clause must name a single exception class"
    let asName := name.val.map (·.val)
    let nmChk : Va Unit := match asName with
      | some n =>
        if reservedNames.contains n || bannedNames.contains n then
          violU p "shadowed-builtin" s!"except ... as {n} shadows a builtin name"
        else okU
      | none => okU
    Va.also nmChk <|
      Va.map2 (fun cls b => Handler.mk p cls asName b)
        clsVa (lowerBody cx body.val)

partial def lowerBody (cx : Cx) (a : Array PyStmt) : Va (List Stmt) :=
  Va.map List.flatten (Va.traverseA (lowerStmt cx) a)

partial def lowerParams (p : Pos) (args : PyArguments) : Va (List Param) := Id.run do
  let .mk_arguments _ posonly positional vararg kwonly _ kwarg defaults := args
  let mut checks := okU
  if vararg.val.isSome then
    checks := Va.also checks (violU p "starred-arg" "*args parameter")
  if kwarg.val.isSome then
    checks := Va.also checks (violU p "starred-arg" "**kwargs parameter")
  if kwonly.val.size != 0 then
    checks := Va.also checks
      (violU p "unsupported-node" "keyword-only parameters")
  let pos := posonly.val ++ positional.val
  let defaults := defaults.val.toList
  for a in pos do
    match a with
    | .mk_arg ap nm _ _ =>
      if reservedNames.contains nm.val || bannedNames.contains nm.val then
        checks := Va.also checks (violU ap "shadowed-builtin"
          s!"parameter {nm.val} shadows a builtin name")
  let names := pos.toList.map (fun a =>
    match a with
    | .mk_arg _ nm annotation _ =>
      (nm.val, annotation.val.map parseAnn))
  -- defaults align with the trailing parameters
  let nDef := defaults.length
  let nPos := names.length
  let defVa : Va (List (Option Expr)) :=
    Va.traverse (fun (d : PyExpr) => Va.map some (lowerExpr {} d)) defaults
  return Va.also checks <| Va.map (fun defs =>
      (names.zipIdx.map (fun ((nm, ann), i) =>
        let d := if i + nDef ≥ nPos then
            defs[i + nDef - nPos]?.getD none
          else none
        Param.mk nm ann d)))
    defVa

/-- Lower a `FunctionDef`. Takes the already-destructured pieces because the two
    callers reach it from different statement constructors. -/
partial def lowerFuncDefParts (cx : Cx) (p : Pos) (fname : String)
    (args : PyArguments) (body : Array PyStmt) (decorators : Array PyExpr)
    (returns : Option PyExpr) (typeParams : Array (StrataPython.type_param Pos))
    (allowProperty : Bool) : Va FuncDef :=
  let decoList := decorators.toList
  let propertyFlavor : Option String :=
    if !allowProperty || decoList.length != 1 then none
    else
      match decoList.head! with
      | .Name _ ident _ =>
        if ident.val == "property" then some s!"@get:{fname}" else none
      | .Attribute _ inner attr _ =>
        if attr.val == "setter" then
          match inner with
          | .Name _ base _ => if base.val == fname then some s!"@set:{fname}" else none
          | _ => none
        else none
      | _ => none
  let decoChk : Va Unit := decorators.zipIdx.foldl (init := okU)
    fun acc (d, i) =>
      let recognized := propertyFlavor.isSome && i == 0
      if recognized then acc else
        Va.also acc (violU (exprPos d) "function-decorator"
          s!"decorator on def {fname}: only @property and @name.setter are admitted on methods")
  let decoChk := if reservedNames.contains fname || bannedNames.contains fname
    then Va.also decoChk (violU p "shadowed-builtin"
      s!"def {fname} shadows a name the analyzer gives builtin semantics")
    else decoChk
  let decoChk := if typeParams.size != 0
    then Va.also decoChk (violU p "unsupported-node"
      s!"type parameters (PEP 695) on def {fname}")
    else decoChk
  let retAnn := returns.map parseAnn
  -- `def f(...) -> T: ...` is a declaration, not code. The `...` is recognised
  -- here rather than lowered as an expression, so `Ellipsis` never has to become
  -- a value with a tag of its own -- and the body is dropped, because there is
  -- nothing in it to analyse.
  let isStub :=
    match body.toList with
    | [.Expr _ (.Constant _ c _)] => isEllipsis c
    | _ => false
  -- A stub is only as good as its contract, so it must have one. Returning
  -- `any` instead would be sound and invisible: every call through it would
  -- silently widen with nothing in the log saying why.
  let stubChk := if isStub && retAnn.isNone
    then Va.also decoChk (violU p "stub-without-return-annotation"
      s!"def {fname} has no body, so its return annotation is its specification and is required")
    else decoChk
  if isStub then
    Va.also stubChk <|
      Va.map (fun params =>
          ({ p := p, name := propertyFlavor.getD fname, params := params,
             retAnn := retAnn, body := [], isGen := false,
             isStub := true } : FuncDef))
        (lowerParams p args)
  else
  Va.also stubChk <|
    Va.map2 (fun params b =>
        FuncDef.mk p (propertyFlavor.getD fname) params retAnn b
          (body.any stmtHasYield) false)
      (lowerParams p args)
      (lowerBody { cx with inFunc := true } body)

partial def lowerFuncDef (cx : Cx) (s : PyStmt)
    (allowProperty : Bool := false) : Va FuncDef :=
  match s with
  | .FunctionDef p name args body decorators returns _ typeParams =>
    lowerFuncDefParts cx p name.val args body.val decorators.val returns.val
      typeParams.val allowProperty
  | other =>
    viol (stmtPos other) "unsupported-node" "expected a function definition"

partial def lowerClassDef (s : PyStmt) : Va ClassDef := Id.run do
  let .ClassDef p nameAnn basesAnn keywordsAnn bodyAnn decoratorsAnn typeParamsAnn := s
    | return viol (stmtPos s) "unsupported-node" "expected a class definition"
  let name := nameAnn.val
  let cx : Cx := { inClass := true, clsName := some name }
  -- decorators: @dataclass alone, and it must be frozen
  let mut isDataclass := false
  let mut checks := okU
  if reservedNames.contains name || bannedNames.contains name then
    checks := Va.also checks (violU p "shadowed-builtin"
      s!"class {name} shadows a name the analyzer gives builtin semantics")
  if typeParamsAnn.val.size != 0 then
    checks := Va.also checks (violU p "unsupported-node"
      s!"type parameters (PEP 695) on class {name}")
  for d in decoratorsAnn.val do
    match d with
    | .Name dp ident _ =>
      if ident.val == "dataclass" then
        checks := Va.also checks (violU dp "unfrozen-dataclass"
          s!"@dataclass on {name} without frozen=True: the generated __eq__ sets __hash__ = None, breaking the hash/eq contract")
        isDataclass := true
      else
        checks := Va.also checks (violU dp "class-decorator"
          s!"decorator @{ident.val} on class {name}")
    | .Call dp f _ kws =>
      let isDataclassCall := match f with
        | .Name _ fid _ => fid.val == "dataclass"
        | _ => false
      if isDataclassCall then
        isDataclass := true
        let frozen := kws.val.any (fun k =>
          match k with
          | .mk_keyword _ arg value =>
            (arg.val.map (·.val)) == some "frozen" &&
              (match value with
               | .Constant _ (.ConTrue _) _ => true
               | _ => false))
        if !frozen then
          checks := Va.also checks (violU dp "unfrozen-dataclass"
            s!"@dataclass(...) on {name} without frozen=True")
        -- any other keyword changes the generated-method semantics the
        -- class table synthesizes (init=False would falsify the
        -- generated __init__; order/eq/unsafe_hash touch the hash/eq
        -- contract), so only frozen is admitted
        for k in kws.val do
          match k with
          | .mk_keyword kp arg _ =>
            let kw := (arg.val.map (·.val)).getD ""
            if kw != "frozen" then
              checks := Va.also checks (violU kp "class-decorator"
                s!"@dataclass keyword {kw} on {name}: only frozen=True is admitted")
      else
        checks := Va.also checks (violU dp "class-decorator"
          s!"computed decorator on class {name}")
    | other =>
      checks := Va.also checks (violU (exprPos other) "class-decorator"
        s!"computed decorator on class {name}")
  -- bases must be static names
  let mut bases : List String := []
  for b in basesAnn.val do
    match b with
    | .Name _ ident _ => bases := bases ++ [ident.val]
    | other =>
      checks := Va.also checks (violU (exprPos other) "non-static-base"
        s!"base of class {name} is not a static name")
  let isTypedDict := bases.contains "TypedDict"
  let mut total := true
  for k in keywordsAnn.val do
    match k with
    | .mk_keyword kp arg value =>
      let kw := (arg.val.map (·.val)).getD ""
      if isTypedDict && kw == "total" then
        match value with
        | .Constant _ (.ConTrue _) _ => total := true
        | .Constant _ (.ConFalse _) _ => total := false
        | _ =>
          checks := Va.also checks (violU kp "metaclass-keyword"
            s!"TypedDict {name} total= must be a literal boolean")
      else
        checks := Va.also checks (violU kp "metaclass-keyword"
          s!"class {name} passes unsupported class keyword {kw}")
  bases := bases.filter (· != "TypedDict")
  -- body
  let mut fields : List FieldDecl := []
  let mut methodVas : List (Va FuncDef) := []
  let mut methodNames : List String := []
  let mut slots : Option (List String) := none
  for item in bodyAnn.val do
    match item with
    | .FunctionDef ip m _ _ _ _ _ _ =>
      let mn := m.val
      if isTypedDict then
        checks := Va.also checks (violU ip "class-body-stmt"
          s!"method {mn} in TypedDict {name}: a TypedDict declares fields only")
      methodNames := methodNames ++ [mn]
      if hookMethods.contains mn then
        checks := Va.also checks (violU ip "hook-override"
          s!"{name}.{mn}: overriding the attribute/creation protocol is outside the subset")
      if unsupportedInplaceDunders.contains mn then
        checks := Va.also checks (violU ip "reflected-dunder"
          s!"{name}.{mn}: in-place operator methods require the augmented-assignment protocol")
      methodVas := methodVas ++ [lowerFuncDef cx item true]
    | .AsyncFunctionDef ip .. =>
      checks := Va.also checks (violU ip "async-construct"
        s!"async method in class {name}")
    | .AnnAssign ip target annotation value _ =>
      match target with
      | .Name _ fieldName _ =>
        if value.val.isSome then
          checks := Va.also checks (violU ip "class-body-stmt"
            s!"field {fieldName.val} carries a default value; class-level defaults are outside the subset")
        let parsed := parseAnn annotation
        let (ann, required, readOnly) :=
          normalizeFieldAnn parsed (if isTypedDict then total else true)
        fields := fields ++ [{
          name := fieldName.val
          ann := some ann
          required
          readOnly
        }]
      | _ =>
        checks := Va.also checks (violU ip "class-body-stmt"
          s!"annotated non-name target in class {name} body")
    | .Pass _ => pure ()
    | .Expr ip value =>
      match value with
      | .Constant .. => pure ()
      | _ =>
        checks := Va.also checks (violU ip "class-body-stmt"
          s!"expression statement in class {name} body")
    -- `__slots__` is the one assignment a class body may carry. It is a
    -- declaration, not class-level state: CPython uses it to give instances a
    -- fixed layout and no `__dict__`, which is the shape invariant this subset
    -- otherwise has to impose by admission. A class that is slots-complete over
    -- its whole MRO therefore has the invariant enforced by the runtime, and
    -- `Objects.lean` uses that to raise `AttributeError` on a store outside the
    -- layout instead of filing an obligation.
    | .Assign ip targets value _ =>
      let soleName :=
        if targets.val.size == 1 then
          match targets.val[0]! with
          | .Name _ ident _ => some ident.val
          | _ => none
        else none
      if soleName == some "__slots__" then
        let elts? : Option (Array PyExpr) := match value with
          | .Tuple _ elts _ => some elts.val
          | .List _ elts _ => some elts.val
          | _ => none
        match elts? with
        | some elts =>
          let names := elts.toList.filterMap (fun e =>
            match e with
            | .Constant _ (.ConString _ str) _ => some str.val
            | _ => none)
          if names.length == elts.size then
            slots := some names
          else
            checks := Va.also checks (violU ip "class-body-stmt"
              s!"__slots__ in class {name} must list string literals only")
        | none =>
          checks := Va.also checks (violU ip "class-body-stmt"
            s!"__slots__ in class {name} must be a tuple or list literal")
      else
        checks := Va.also checks (violU ip "class-body-stmt"
          s!"assignment in class {name} body: class bodies hold methods, annotated fields, __slots__ and docstrings only")
    | other =>
      checks := Va.also checks (violU (stmtPos other) "class-body-stmt"
        s!"statement in class {name} body: class bodies hold methods, annotated fields, and docstrings only")
  -- hash/eq contract: defining one of __eq__/__hash__ requires the other
  let hasEq := methodNames.contains "__eq__"
  let hasHash := methodNames.contains "__hash__"
  if hasEq != hasHash then
    let missing := if hasEq then "__hash__" else "__eq__"
    let present := if hasEq then "__eq__" else "__hash__"
    checks := Va.also checks (violU p "hash-eq-contract"
      s!"class {name} defines {present} without {missing}: instances would break the hash/eq contract at key positions")
  return Va.also checks <|
    Va.map (fun methods =>
        ClassDef.mk p name bases fields methods isDataclass
          isTypedDict total slots)
      (Va.traverse id methodVas)

end

-- ------------------------------------------ handler-target lexical freshness

partial def exprUsesName (wanted : String) : Expr → Bool
  | .name _ name => name == wanted
  | .const .. => false
  | .binop _ _ left right | .cmp _ _ left right =>
    exprUsesName wanted left || exprUsesName wanted right
  | .boolop _ _ values | .listlit _ values | .tuplelit _ values
  | .setlit _ values | .fstr _ values =>
    values.any (exprUsesName wanted)
  | .notE _ value | .unary _ _ value | .attr _ value _
  | .yieldFrom _ value => exprUsesName wanted value
  | .subscr _ value index =>
    exprUsesName wanted value || exprUsesName wanted index
  | .call _ fn args keywords =>
    exprUsesName wanted fn ||
      args.any (exprUsesName wanted) ||
      keywords.any (fun (_, value) => exprUsesName wanted value)
  | .dictlit _ entries =>
    entries.any (fun (key, value) =>
      exprUsesName wanted key || exprUsesName wanted value)
  | .ifexp _ condition yes no =>
    exprUsesName wanted condition ||
      exprUsesName wanted yes ||
      exprUsesName wanted no
  | .comp _ _ element value boundName iter conditions =>
    exprUsesName wanted iter ||
      if boundName == wanted then false
      else
        exprUsesName wanted element ||
          value.any (exprUsesName wanted) ||
          conditions.any (exprUsesName wanted)
  | .yieldE _ value => value.any (exprUsesName wanted)

partial def targetUsesName (wanted : String) : Target → Bool
  | .tname _ name => name == wanted
  | .tattr _ recv _ => exprUsesName wanted recv
  | .tsub _ recv index =>
    exprUsesName wanted recv || exprUsesName wanted index
  | .ttuple _ targets => targets.any (targetUsesName wanted)

mutual

partial def stmtUsesNameOutsideHandler (handlerId : NodeId) (wanted : String) :
    Stmt → Bool
  | .assign _ target value =>
    targetUsesName wanted target || exprUsesName wanted value
  | .annAssign _ name value =>
    name == wanted || value.any (exprUsesName wanted)
  | .exprS _ value | .ret _ (some value) | .assertS _ value =>
    exprUsesName wanted value
  | .ret _ none | .brk _ | .cont _ | .pass _ | .raiseS _ _ none => false
  | .raiseS _ _ (some value) => exprUsesName wanted value
  | .delS _ target => targetUsesName wanted target
  | .ifS _ condition yes no | .whileS _ condition yes no =>
    exprUsesName wanted condition ||
      bodyUsesNameOutsideHandler handlerId wanted yes ||
      bodyUsesNameOutsideHandler handlerId wanted no
  | .forS _ target iter body orelse =>
    targetUsesName wanted target ||
      exprUsesName wanted iter ||
      bodyUsesNameOutsideHandler handlerId wanted body ||
      bodyUsesNameOutsideHandler handlerId wanted orelse
  | .tryS _ body handlers orelse finalbody =>
    bodyUsesNameOutsideHandler handlerId wanted body ||
      handlers.any (fun handler =>
        match handler with
        | .mk pos _ target handlerBody =>
          if pos.id == handlerId then false
          else
            target == some wanted ||
              bodyUsesNameOutsideHandler handlerId wanted handlerBody) ||
      bodyUsesNameOutsideHandler handlerId wanted orelse ||
      bodyUsesNameOutsideHandler handlerId wanted finalbody

partial def bodyUsesNameOutsideHandler (handlerId : NodeId) (wanted : String)
    (body : List Stmt) : Bool :=
  body.any (stmtUsesNameOutsideHandler handlerId wanted)

end

mutual

partial def handlerTargetsStmt : Stmt → List (Pos × String)
  | .ifS _ _ yes no | .whileS _ _ yes no =>
    handlerTargetsBody yes ++ handlerTargetsBody no
  | .forS _ _ _ body orelse =>
    handlerTargetsBody body ++ handlerTargetsBody orelse
  | .tryS _ body handlers orelse finalbody =>
    handlerTargetsBody body ++
      handlers.flatMap (fun handler =>
        match handler with
        | .mk pos _ target handlerBody =>
          (target.map (fun name => [(pos, name)])).getD [] ++
            handlerTargetsBody handlerBody) ++
      handlerTargetsBody orelse ++
      handlerTargetsBody finalbody
  | _ => []

partial def handlerTargetsBody (body : List Stmt) : List (Pos × String) :=
  body.flatMap handlerTargetsStmt

end

def handlerFreshnessViolations (scopeNames : Fset String)
    (body : List Stmt) : List Violation :=
  (handlerTargetsBody body).filterMap (fun (pos, name) =>
    if scopeNames.contains name ||
       bodyUsesNameOutsideHandler pos.id name body then
      some {
        line := pos.line
        col := pos.col
        node := pos.id
        rule := "handler-name-collision"
        detail :=
          s!"except ... as {name} reuses a name elsewhere in the same lexical scope"
      }
    else none)

/-- Names an expression calls directly.

    A `Name` callee gives the function's name; an `Attribute` callee gives the
    method name, which is matched against the unqualified half of a method's
    `Class.method` key. Anything else is a computed callee and contributes
    nothing -- deliberately, since this check only has to catch the cycles it can
    see, with the analyser's re-entry check behind it. -/
partial def exprCalleeNames : Expr -> List String
  | .call _ f args kws =>
    (match f with
     | .name _ x => [x]
     -- A `super()` call contributes no edge. The graph below is keyed on the
     -- short method name, so `super().__init__()` inside `Leaf.__init__` would
     -- otherwise read as `Leaf.__init__` calling itself. It cannot be: `super()`
     -- resolves strictly *after* the owner on a finite MRO, so following super
     -- edges only ever ascends the chain and terminates. A cycle through these
     -- methods has to close on an ordinary call, which still contributes.
     | .attr _ (.name _ receiverName) m =>
       if receiverName.startsWith "@super:" then [] else [m]
     | .attr _ _ m => [m]
     | other => exprCalleeNames other) ++
    (args.flatMap exprCalleeNames) ++ (kws.flatMap (fun kw => exprCalleeNames kw.2))
  | .const _ _ | .name _ _ => []
  | .binop _ _ l r | .cmp _ _ l r | .subscr _ l r => exprCalleeNames l ++ exprCalleeNames r
  | .boolop _ _ vals | .listlit _ vals | .tuplelit _ vals | .setlit _ vals
  | .fstr _ vals => vals.flatMap exprCalleeNames
  | .notE _ e | .unary _ _ e | .attr _ e _ | .yieldFrom _ e => exprCalleeNames e
  | .dictlit _ kvs => kvs.flatMap (fun kv => exprCalleeNames kv.1 ++ exprCalleeNames kv.2)
  | .ifexp _ c a b => exprCalleeNames c ++ exprCalleeNames a ++ exprCalleeNames b
  | .comp _ _ elt eltVal _ iter conds =>
    exprCalleeNames elt ++ (eltVal.map exprCalleeNames |>.getD []) ++
      exprCalleeNames iter ++ (conds.flatMap exprCalleeNames)
  | .yieldE _ e => e.map exprCalleeNames |>.getD []

/-- Names a statement's expressions call directly, by name.

    Only direct calls of a `Name` callee. A call through a variable is invisible
    here, which is why the analyser keeps its own re-entry check as the
    fail-closed backstop rather than trusting this to be complete. -/
partial def calleeNames : Stmt -> List String
  | .exprS _ e => exprCalleeNames e
  | .assign _ _ e => exprCalleeNames e
  | .annAssign _ _ (some e) => exprCalleeNames e
  | .annAssign _ _ none => []
  | .ret _ (some e) => exprCalleeNames e
  | .ret _ none => []
  | .raiseS _ _ (some e) => exprCalleeNames e
  | .raiseS _ _ none => []
  | .assertS _ e => exprCalleeNames e
  | .delS _ _ => []
  | .brk _ | .cont _ | .pass _ => []
  | .ifS _ c yes no =>
    exprCalleeNames c ++ (yes.flatMap calleeNames) ++ (no.flatMap calleeNames)
  | .whileS _ c body orelse =>
    exprCalleeNames c ++ (body.flatMap calleeNames) ++
      (orelse.flatMap calleeNames)
  | .forS _ _ it body orelse =>
    exprCalleeNames it ++ (body.flatMap calleeNames) ++
      (orelse.flatMap calleeNames)
  | .tryS _ body handlers orelse finalbody =>
    (body.flatMap calleeNames) ++
      (handlers.flatMap (fun h => match h with
        | .mk _ _ _ hbody => hbody.flatMap calleeNames)) ++
      (orelse.flatMap calleeNames) ++ (finalbody.flatMap calleeNames)

/-- Direct recursion and mutual recursion are outside the admitted subset.

    Summarising a call whose body is already on the stack requires a contract
    that states the callee's result, the exceptions it may raise, the locations it
    may write, and the values it may write there -- and that the engine checks
    rather than assumes. Without one, the only sound summary is "returns anything,
    raises anything, havocs everything reachable". Anything more optimistic --
    assuming the declared return type, assuming no raise, leaving the heap
    untouched -- is unsound in general; `../doc/RECURSION_CONTRACTS.md` records the
    measurements and what a contract language would have to offer.

    Rejecting is the honest interim: the program is outside what can be analysed
    soundly today, and saying so is better than analysing it wrongly. -/
def programRecursionViolations (program : Program) : List Violation :=
  let functions := program.items.foldl (fun acc item =>
    match item with
    | .fdef fn => acc ++ [(fn.name, fn.p, fn.body)]
    | .cdef cls =>
      acc ++ cls.methods.map (fun m => (s!"{cls.name}.{m.name}", m.p, m.body))
    | .stmt _ => acc) []
  let edges := functions.map (fun (name, _, body) =>
    (name, (body.flatMap calleeNames).eraseDups))
  let names := functions.map (·.1)
  -- Reachability by iteration to a fixed point: `|names|` rounds suffice, since a
  -- path through more than that many distinct functions must repeat one.
  let step := fun (reach : List (String × List String)) =>
    reach.map (fun (from_, tos) =>
      (from_, (tos ++ tos.flatMap (fun t =>
        (reach.find? (·.1 == t)).map (·.2) |>.getD [])).eraseDups))
  let closure := names.foldl (fun acc _ => step acc) edges
  functions.filterMap (fun (name, position, _) =>
    let short := (name.splitOn ".").getLast!
    match closure.find? (·.1 == name) with
    | some (_, reachable) =>
      if reachable.contains name || reachable.contains short then
        some {
          line := position.line, col := position.col, node := position.id,
          rule := "recursive-call",
          detail := s!"{name} is reachable from itself: recursion needs a checked contract for the callee's result, raises and write set, which the subset does not yet have"
        }
      else none
    | none => none)

def programHandlerFreshnessViolations (program : Program) : List Violation :=
  let declarations := program.items.filterMap (fun item => match item with
    | .fdef fn => some fn.name
    | .cdef cls => some cls.name
    | .stmt _ => none)
  let moduleBody := program.items.filterMap (fun item => match item with
    | .stmt stmt => some stmt
    | _ => none)
  let moduleErrors := handlerFreshnessViolations declarations moduleBody
  program.items.foldl (fun errors item =>
    match item with
    | .fdef fn =>
      errors ++ handlerFreshnessViolations (fn.params.map (·.name)) fn.body
    | .cdef cls =>
      cls.methods.foldl (fun errors method =>
        errors ++ handlerFreshnessViolations
          (method.params.map (·.name)) method.body) errors
    | .stmt _ => errors) moduleErrors

-- Numeric conversion protocols and bare object construction are not yet
-- modeled. The builtin type names remain legal in annotations and as the
-- class argument of isinstance(), but not as runtime values or callees.
mutual

partial def scalarValueViolationsExpr (allowClassArg : Bool) :
    Expr → List Violation
  | .name p name =>
    if !allowClassArg && unmodeledScalarConstructors.contains name then
      [{
        line := p.line
        col := p.col
        node := p.id
        rule := "unmodeled-scalar-constructor"
        detail :=
          s!"runtime use of builtin type {name} is not modeled; it is admitted only in annotations and isinstance"
      }]
    else []
  | .const .. => []
  | .binop _ _ left right | .cmp _ _ left right =>
    scalarValueViolationsExpr false left ++
      scalarValueViolationsExpr false right
  | .boolop _ _ values | .listlit _ values | .tuplelit _ values
  | .setlit _ values | .fstr _ values =>
    values.flatMap (scalarValueViolationsExpr false)
  | .notE _ value | .unary _ _ value | .attr _ value _
  | .yieldFrom _ value =>
    scalarValueViolationsExpr false value
  | .subscr _ value index =>
    scalarValueViolationsExpr false value ++
      scalarValueViolationsExpr false index
  | .call _ (.name _ "isinstance") args keywords =>
    let argErrors := args.zipIdx.flatMap (fun (arg, index) =>
      scalarValueViolationsExpr (index == 1) arg)
    argErrors ++ keywords.flatMap (fun (_, value) =>
      scalarValueViolationsExpr false value)
  | .call _ fn args keywords =>
    scalarValueViolationsExpr false fn ++
      args.flatMap (scalarValueViolationsExpr false) ++
      keywords.flatMap (fun (_, value) =>
        scalarValueViolationsExpr false value)
  | .dictlit _ entries =>
    entries.flatMap (fun (key, value) =>
      scalarValueViolationsExpr false key ++
        scalarValueViolationsExpr false value)
  | .ifexp _ condition yes no =>
    scalarValueViolationsExpr false condition ++
      scalarValueViolationsExpr false yes ++
      scalarValueViolationsExpr false no
  | .comp _ _ element value _ iter conditions =>
    scalarValueViolationsExpr false iter ++
      scalarValueViolationsExpr false element ++
      value.toList.flatMap (scalarValueViolationsExpr false) ++
      conditions.flatMap (scalarValueViolationsExpr false)
  | .yieldE _ value =>
    value.toList.flatMap (scalarValueViolationsExpr false)

partial def scalarValueViolationsStmt : Stmt → List Violation
  | .assign _ target value =>
    scalarValueViolationsTarget target ++ scalarValueViolationsExpr false value
  | .annAssign _ _ value =>
    value.toList.flatMap (scalarValueViolationsExpr false)
  | .exprS _ value | .ret _ (some value) | .assertS _ value =>
    scalarValueViolationsExpr false value
  | .ret _ none | .brk _ | .cont _ | .pass _ | .raiseS _ _ none => []
  | .raiseS _ _ (some value) => scalarValueViolationsExpr false value
  | .delS _ target => scalarValueViolationsTarget target
  | .ifS _ condition yes no | .whileS _ condition yes no =>
    scalarValueViolationsExpr false condition ++
      scalarValueViolationsBody yes ++ scalarValueViolationsBody no
  | .forS _ target iter body orelse =>
    scalarValueViolationsTarget target ++
      scalarValueViolationsExpr false iter ++
      scalarValueViolationsBody body ++ scalarValueViolationsBody orelse
  | .tryS _ body handlers orelse finalbody =>
    scalarValueViolationsBody body ++
      handlers.flatMap (fun handler => match handler with
        | .mk _ _ _ handlerBody => scalarValueViolationsBody handlerBody) ++
      scalarValueViolationsBody orelse ++
      scalarValueViolationsBody finalbody

partial def scalarValueViolationsTarget : Target → List Violation
  | .tname .. => []
  | .tattr _ receiver _ => scalarValueViolationsExpr false receiver
  | .tsub _ receiver index =>
    scalarValueViolationsExpr false receiver ++
      scalarValueViolationsExpr false index
  | .ttuple _ targets => targets.flatMap scalarValueViolationsTarget

partial def scalarValueViolationsBody (body : List Stmt) : List Violation :=
  body.flatMap scalarValueViolationsStmt

end

def programScalarValueViolations (program : Program) : List Violation :=
  program.items.flatMap (fun item => match item with
    | .stmt statement => scalarValueViolationsStmt statement
    | .fdef function => scalarValueViolationsBody function.body
    | .cdef cls =>
      cls.methods.flatMap (fun method =>
        scalarValueViolationsBody method.body))

def exceptionClassViolation (classes : ClassTable) (p : Pos)
    (role name : String) : List Violation :=
  if builtinExcs.contains name ||
      (classes.getCls? name).any (·.isExc) then
    []
  else
    [{
      line := p.line
      col := p.col
      node := p.id
      rule := "non-exception-class"
      detail := s!"{role} names {name}, which is not a BaseException subclass"
    }]

mutual

partial def exceptionClassViolationsStmt (classes : ClassTable) :
    Stmt → List Violation
  | .raiseS p (some name) _ =>
    exceptionClassViolation classes p "raise" name
  | .raiseS _ none _ => []
  | .ifS _ _ yes no | .whileS _ _ yes no =>
    exceptionClassViolationsBody classes yes ++
      exceptionClassViolationsBody classes no
  | .forS _ _ _ body orelse =>
    exceptionClassViolationsBody classes body ++
      exceptionClassViolationsBody classes orelse
  | .tryS _ body handlers orelse finalbody =>
    exceptionClassViolationsBody classes body ++
      handlers.flatMap (fun handler => match handler with
        | .mk p exceptionClass _ handlerBody =>
          let classErrors := exceptionClass.toList.flatMap (fun name =>
            exceptionClassViolation classes p "except clause" name)
          classErrors ++
            exceptionClassViolationsBody classes handlerBody) ++
      exceptionClassViolationsBody classes orelse ++
      exceptionClassViolationsBody classes finalbody
  | _ => []

partial def exceptionClassViolationsBody (classes : ClassTable)
    (body : List Stmt) : List Violation :=
  body.flatMap (exceptionClassViolationsStmt classes)

end

def programExceptionClassViolations (classes : ClassTable)
    (program : Program) : List Violation :=
  program.items.flatMap (fun item => match item with
    | .stmt statement => exceptionClassViolationsStmt classes statement
    | .fdef function => exceptionClassViolationsBody classes function.body
    | .cdef cls =>
      cls.methods.flatMap (fun method =>
        exceptionClassViolationsBody classes method.body))

-- ------------------------------------------------------ shape-stable stores

/-- Attributes that name the dispatch machinery rather than a field. A store to
    one of these is refused wherever it appears, `self` included: `__class__`
    retags a live object so `tag(o)` stops being constant, `__bases__` and
    `__mro__` rewrite the resolution order, and `__dict__` replaces the instance
    schema wholesale. -/
def dispatchAttrs : List String :=
  ["__class__", "__dict__", "__bases__", "__mro__", "__slots__"]

/-- Every attribute name a store may legitimately target.

    Two kinds qualify. A **field** of some class layout: `buildClassTable`
    derives a layout from the annotated fields *and* every `self.f` store in the
    class's methods, so a store through `self` names a layout field by
    construction and needs no check at all. And a **property setter**, which
    `lowerFuncDef` records as a method named `@set:f`: a store through one runs
    the setter instead of writing a cell, so it changes no schema.

    A store through a receiver other than `self` cannot be checked against one
    class, because admission does not know the receiver's class -- the analysis
    decides that later. So the check is the weaker union: a name that is neither
    a field nor a setter on *any* admitted class cannot be either on the
    receiver whatever it turns out to be, and the Laurel composite derived from
    the class declaration has nowhere to put it.

    A name that is a field of some *other* class still reaches the analysis and
    files `attr-missing` there. That residue is narrower than the rule and is
    recorded in `../doc/SUBSET_DEFINITION.md`. -/
def storableAttrs (classes : ClassTable) : Fset String :=
  classes.foldl (fun acc entry =>
    let setters := entry.2.ownMethods.filterMap (fun method =>
      if method.1.startsWith "@set:" then some (method.1.drop 5).toString else none)
    Fset.union (Fset.union entry.2.layout setters) acc) []

def shapeStoreViol (p : Pos) (rule detail : String) : List Violation :=
  [{ line := p.line, col := p.col, node := p.id, rule := rule, detail := detail }]

/-- Attribute stores in one assignment target. `inMethod` exempts `self`. -/
partial def shapeStoreTargetViolations (fields : Fset String) (inMethod : Bool) :
    Target → List Violation
  | .tattr p receiver name =>
    let isSelf := inMethod && (match receiver with
      | .name _ "self" => true
      | _ => false)
    if dispatchAttrs.contains name then
      shapeStoreViol p "shape-store"
        s!"store to .{name}: it names the dispatch machinery, not a field, and writing it would change an object's type or an already-derived resolution order at runtime"
    else if isSelf || fields.contains name then []
    else
      shapeStoreViol p "shape-store"
        s!"store to .{name}: no admitted class declares that field or a property setter for it, so it is outside every class layout the encoding derives from a declaration"
  | .ttuple _ elts => elts.flatMap (shapeStoreTargetViolations fields inMethod)
  | _ => []

mutual

partial def shapeStoreViolationsStmt (fields : Fset String) (inMethod : Bool) :
    Stmt → List Violation
  | .assign _ target _ => shapeStoreTargetViolations fields inMethod target
  | .forS _ target _ body orelse =>
    shapeStoreTargetViolations fields inMethod target ++
      shapeStoreViolationsBody fields inMethod body ++
      shapeStoreViolationsBody fields inMethod orelse
  | .ifS _ _ yes no | .whileS _ _ yes no =>
    shapeStoreViolationsBody fields inMethod yes ++
      shapeStoreViolationsBody fields inMethod no
  | .tryS _ body handlers orelse finalbody =>
    shapeStoreViolationsBody fields inMethod body ++
      handlers.flatMap (fun handler => match handler with
        | .mk _ _ _ handlerBody =>
          shapeStoreViolationsBody fields inMethod handlerBody) ++
      shapeStoreViolationsBody fields inMethod orelse ++
      shapeStoreViolationsBody fields inMethod finalbody
  | _ => []

partial def shapeStoreViolationsBody (fields : Fset String) (inMethod : Bool)
    (body : List Stmt) : List Violation :=
  body.flatMap (shapeStoreViolationsStmt fields inMethod)

end

-- ------------------------------------------------------------------ super()

/-- Owners named by a `@super:` receiver anywhere in an expression. -/
partial def superOwnersExpr : Expr → List String
  | .call _ f args kws =>
    (match f with
     | .attr _ (.name _ receiverName) _ =>
       if receiverName.startsWith "@super:" then
         [(receiverName.drop 7).toString]
       else []
     | other => superOwnersExpr other) ++
    (args.flatMap superOwnersExpr) ++ (kws.flatMap (fun kw => superOwnersExpr kw.2))
  | .const _ _ | .name _ _ => []
  | .binop _ _ l r | .cmp _ _ l r | .subscr _ l r =>
    superOwnersExpr l ++ superOwnersExpr r
  | .boolop _ _ vals | .listlit _ vals | .tuplelit _ vals | .setlit _ vals
  | .fstr _ vals => vals.flatMap superOwnersExpr
  | .notE _ e | .unary _ _ e | .attr _ e _ | .yieldFrom _ e => superOwnersExpr e
  | .dictlit _ kvs =>
    kvs.flatMap (fun kv => superOwnersExpr kv.1 ++ superOwnersExpr kv.2)
  | .ifexp _ c a b =>
    superOwnersExpr c ++ superOwnersExpr a ++ superOwnersExpr b
  | .comp _ _ elt eltVal _ iter conds =>
    superOwnersExpr elt ++ (eltVal.map superOwnersExpr |>.getD []) ++
      superOwnersExpr iter ++ (conds.flatMap superOwnersExpr)
  | .yieldE _ e => e.map superOwnersExpr |>.getD []

mutual

partial def superOwnersStmt : Stmt → List String
  | .exprS _ e | .assign _ _ e | .assertS _ e => superOwnersExpr e
  | .annAssign _ _ (some e) | .ret _ (some e) | .raiseS _ _ (some e) =>
    superOwnersExpr e
  | .annAssign _ _ none | .ret _ none | .raiseS _ _ none => []
  | .delS _ _ | .brk _ | .cont _ | .pass _ => []
  | .ifS _ c yes no =>
    superOwnersExpr c ++ superOwnersBody yes ++ superOwnersBody no
  | .whileS _ c body orelse =>
    superOwnersExpr c ++ superOwnersBody body ++ superOwnersBody orelse
  | .forS _ _ it body orelse =>
    superOwnersExpr it ++ superOwnersBody body ++ superOwnersBody orelse
  | .tryS _ body handlers orelse finalbody =>
    superOwnersBody body ++
      (handlers.flatMap (fun h => match h with
        | .mk _ _ _ hbody => superOwnersBody hbody)) ++
      superOwnersBody orelse ++ superOwnersBody finalbody

partial def superOwnersBody (body : List Stmt) : List String :=
  body.flatMap superOwnersStmt

end

/-- The two conditions under which a `super()` call is understood well enough to
    admit. Both were found by measurement after the feature was already working
    on the cases it was written for.

    **The first parameter must be named `self`.** A zero-argument `super()` binds
    CPython's *first positional argument*, but the analysis reads the receiver
    out of the binding named `self`. With `def m(this)` that binding is unbound,
    the dispatch loop finds no arm, and the call returns bottom -- a claim that
    the method has no normal completion. Measured: `Sub().m()` where `m` took
    `this` produced no value at all and filed no obligation, while CPython
    answers 11. A silent bottom is the worst failure available, since it makes
    admitted code unreachable and discharges later obligations for free.

    **The MRO must stay in user code.** `ClassInfo.mro` holds user classes only,
    so nothing follows the owner once the chain enters a builtin base and the
    call resolves to "no next definer". For `class MyErr(ValueError)` with
    `super().__init__("boom")` that surfaced as an `AttributeError` abort where
    CPython succeeds -- sound, because an abort is a refusal rather than a claim,
    but it reports a confusing error for an idiomatic program. Delegating into a
    builtin `__init__` means modelling what that constructor does to the
    instance, which is not modelled, so the honest answer is to refuse the
    program with a rule that says why.

    The check runs over every class that could *be* the receiver, not just the
    class the call is written in: a subclass can splice a builtin into the chain
    between the owner and `object`, as `class Sub(Base, ValueError)` does. -/
def programSuperViolations (classes : ClassTable)
    (program : Program) : List Violation :=
  let classItems := program.items.filterMap (fun item => match item with
    | .cdef cls => some cls
    | _ => none)
  -- (a) per method: `super()` requires `self` as the first parameter.
  let selfErrors := classItems.flatMap (fun cls =>
    cls.methods.flatMap (fun method =>
      if (superOwnersBody method.body).isEmpty then []
      else
        let firstParam := (method.params.head?).map (·.name)
        if firstParam == some "self" then []
        else
          [{ line := method.p.line, col := method.p.col, node := method.p.id,
             rule := "super-form",
             detail := s!"super() in {cls.name}.{method.name}, whose first parameter is {firstParam.getD "absent"} rather than self: the zero-argument form binds the first positional argument, and the analysis reads the receiver from the name self" }]))
  -- (b) per class that could be the receiver: if any class on its MRO delegates,
  -- the whole chain has to be user code terminating at `object`.
  let delegating := classItems.filterMap (fun cls =>
    if (cls.methods.flatMap (fun m => superOwnersBody m.body)).isEmpty then none
    else some cls.name)
  let userNames := classItems.map (·.name)
  let chainErrors := classes.flatMap (fun entry =>
    let ci := entry.2
    if ci.mro.any delegating.contains then
      let foreign := ci.fullMro.filter (fun c =>
        c != "object" && !userNames.contains c)
      if foreign.isEmpty then []
      else
        let position := (classItems.find? (·.name == ci.name)).map (·.p)
        match position with
        | none => []
        | some p =>
          [{ line := p.line, col := p.col, node := p.id,
             rule := "super-builtin-base",
             detail := s!"{ci.name} takes part in super() delegation but its MRO continues into {", ".intercalate foreign}: delegating to a builtin base would mean modelling what that constructor does to the instance, which is not modelled" }]
    else [])
  selfErrors ++ chainErrors

def programShapeStoreViolations (classes : ClassTable)
    (program : Program) : List Violation :=
  let fields := storableAttrs classes
  program.items.flatMap (fun item => match item with
    | .stmt statement => shapeStoreViolationsStmt fields false statement
    | .fdef function => shapeStoreViolationsBody fields false function.body
    | .cdef cls =>
      cls.methods.flatMap (fun method =>
        shapeStoreViolationsBody fields true method.body))

-- ------------------------------------------------- functions and classes

/-- Lower a module body. `readPythonStrata` has already unwrapped `.Module`, so
    the input is the statement array; `Label.relabel` has turned every
    `SourceRange` into a `Pos`. -/
def lowerModule (body : Array PyStmt) : Va Program := Id.run do
  let mut itemVas : List (Va (List ModItem)) := []
  for item in body do
    match item with
    | .FunctionDef .. =>
      itemVas := itemVas ++
        [Va.map (fun f => [ModItem.fdef f]) (lowerFuncDef {} item)]
    | .AsyncFunctionDef p .. =>
      itemVas := itemVas ++ [viol p "async-construct" "async def"]
    | .ClassDef .. =>
      itemVas := itemVas ++
        [Va.map (fun c => [ModItem.cdef c]) (lowerClassDef item)]
    | _ =>
      itemVas := itemVas ++
        [Va.map (fun ss => ss.map ModItem.stmt) (lowerStmt {} item)]
  match Va.map (fun xs => Program.mk xs.flatten) (Va.traverse id itemVas) with
  | .err errors => return .err errors
  | .ok program =>
    let classes := program.items.filterMap (fun item => match item with
      | .cdef cls => some cls
      | _ => none)
    match buildClassTable classes with
    | .ok classTable =>
      let semanticErrors :=
        programRecursionViolations program ++
          programHandlerFreshnessViolations program ++
          programScalarValueViolations program ++
          programExceptionClassViolations classTable program ++
          programShapeStoreViolations classTable program ++
          programSuperViolations classTable program
      if semanticErrors.isEmpty then
        return .ok program
      else
        return .err semanticErrors.toArray
    | .error error =>
      return .err #[{
        line := error.p.line
        col := error.p.col
        node := error.p.id
        rule := error.rule
        detail := error.detail
      }]

end Pylate
