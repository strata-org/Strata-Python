/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.PythonDialect

/-!
# Feature Usage Analysis for Python Programs

Walks a Python DDM AST and collects every constructor encountered,
grouped by syntactic category (statement, expression, constant,
operator, etc.).  The result is a frequency map that can be printed
to stdout to understand which Python features a file uses.
-/

namespace StrataPython.FeatureUsage

open StrataDDM
open StrataPython (stmt expr constant operator unaryop boolop cmpop
                    pattern keyword comprehension withitem match_case
                    excepthandler opt_expr)

/-! ## State -/

/-- What kind of block a scope belongs to. -/
public inductive ScopeKind where
  | module
  | function
  | classBody
  | comprehension
  deriving Inhabited, BEq

/-- A scope on the stack including its kind and the names it binds. -/
public structure Scope where
  kind  : ScopeKind
  names : Std.HashSet String := {}
  deriving Inhabited

/-- Accumulated feature counts and warnings. -/
public structure FeatureState where
  stmtCounts      : Std.HashMap String Nat := {}
  exprCounts      : Std.HashMap String Nat := {}
  constantCounts  : Std.HashMap String Nat := {}
  operatorCounts  : Std.HashMap String Nat := {}
  unaryopCounts   : Std.HashMap String Nat := {}
  boolopCounts    : Std.HashMap String Nat := {}
  cmpopCounts     : Std.HashMap String Nat := {}
  patternCounts   : Std.HashMap String Nat := {}
  unresolvedNames : Std.HashMap String Nat := {}
  decoratorNames  : Std.HashMap String Nat := {}
  warnings        : Array String := #[]
  /-- The enclosing scopes, innermost last. The first is the module. -/
  scopeStack      : Array Scope := #[{ kind := .module }]

abbrev FeatureM := StateM FeatureState

/-- Increment a counter in a HashMap by 1. -/
def bump (get : FeatureState → Std.HashMap String Nat)
    (set : FeatureState → Std.HashMap String Nat → FeatureState)
    (key : String) : FeatureM Unit :=
  modify fun s =>
    let m := get s
    set s (m.insert key (m.getD key 0 + 1))

def bumpStmt       := bump (·.stmtCounts)      (fun s m => { s with stmtCounts      := m })
def bumpExpr       := bump (·.exprCounts)      (fun s m => { s with exprCounts      := m })
def bumpConstant   := bump (·.constantCounts)  (fun s m => { s with constantCounts  := m })
def bumpOperator   := bump (·.operatorCounts)  (fun s m => { s with operatorCounts  := m })
def bumpUnaryop    := bump (·.unaryopCounts)   (fun s m => { s with unaryopCounts   := m })
def bumpBoolop     := bump (·.boolopCounts)    (fun s m => { s with boolopCounts    := m })
def bumpCmpop      := bump (·.cmpopCounts)     (fun s m => { s with cmpopCounts     := m })
def bumpPattern    := bump (·.patternCounts)   (fun s m => { s with patternCounts   := m })
def bumpUnresolved := bump (·.unresolvedNames) (fun s m => { s with unresolvedNames := m })
def bumpDecorator  := bump (·.decoratorNames)  (fun s m => { s with decoratorNames  := m })

def warn (msg : String) : FeatureM Unit :=
  modify fun s => { s with warnings := s.warnings.push msg }

/-! ## Scope tracking for unresolved name analysis -/

/-- Define `name` in the scope at index `i` of the stack. -/
def defineNameAt (i : Nat) (name : String) : FeatureM Unit :=
  modify fun s =>
    { s with scopeStack := s.scopeStack.modify i fun sc => { sc with names := sc.names.insert name } }

/-- Define `name` in the innermost scope. -/
def defineName (name : String) : FeatureM Unit := do
  defineNameAt ((← get).scopeStack.size - 1) name

/-- Define a walrus target `name` in the innermost scope that is not a comprehension. -/
def defineWalrusTarget (name : String) : FeatureM Unit := do
  let stack := (← get).scopeStack
  let i := stack.zipIdx.foldl (init := 0) fun acc (sc, j) =>
    if sc.kind != .comprehension then j else acc
  defineNameAt i name

/-- Define `name` in the module scope (`global name`). -/
def defineGlobal (name : String) : FeatureM Unit :=
  defineNameAt 0 name

/-- Whether `name` is visible: bound in the innermost scope, or in an enclosing scope that is
not a class body. -/
def isNameDefined (name : String) : FeatureM Bool := do
  let stack := (← get).scopeStack
  let n := stack.size
  return (stack.zipIdx.any fun (sc, i) =>
    (i + 1 == n || sc.kind != .classBody) && sc.names.contains name)

/-- Enter a scope of kind `kind`. -/
def pushScope (kind : ScopeKind) : FeatureM Unit :=
  modify fun s => { s with scopeStack := s.scopeStack.push { kind } }

/-- Leave the innermost scope. -/
def popScope : FeatureM Unit :=
  modify fun s => { s with scopeStack := s.scopeStack.pop }

/-- Extract a human-readable name from a decorator expression. -/
def decoratorName (d : expr SourceRange) : Option String :=
  match d with
  | .Name _ ⟨_, name⟩ _ => some name
  | .Attribute _ _ ⟨_, attr⟩ _ => some attr
  | .Call _ f _ _ =>
    match f with
    | .Name _ ⟨_, name⟩ _ => some name
    | .Attribute _ _ ⟨_, attr⟩ _ => some attr
    | _ => none
  | _ => none

/-- Record the names of the decorators in a decorator list. -/
def recordDecoratorNames (decorators : Array (expr SourceRange)) : FeatureM Unit :=
  for d in decorators do
    match decoratorName d with
    | some name => bumpDecorator name
    | none => warn s!"Unrecognized decorator expression"

/-- The names an assignment target binds: a name, or every name in a tuple, list or starred
target. -/
def extractNames (e : expr SourceRange) : Array String :=
  match e with
  | .Name _ ⟨_, name⟩ _ => #[name]
  | .Tuple _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | .List _ ⟨_, elts⟩ _ => elts.flatMap extractNames
  | .Starred _ value _ => extractNames value
  | _ => #[]

/-- Define the names an assignment target binds. -/
def defineTarget (e : expr SourceRange) : FeatureM Unit :=
  (extractNames e).forM defineName

/-- The name an import alias binds: its `as` name, else the first component of the module
name (`os` for `import os.path`). -/
def aliasBinding (a : alias SourceRange) : String :=
  a.asname.getD ((a.name.splitOn ".").headD a.name)

/-- Extract parameter names from an arguments node and define them in current scope. -/
def defineParams (args : arguments SourceRange) : FeatureM Unit :=
  match args with
  | .mk_arguments _ posonlyargs posargs vararg kwonlyargs _ kwarg _ => do
    -- positional-only args
    for a in posonlyargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ _ _ => defineName name
    -- regular positional args
    for a in posargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ _ _ => defineName name
    -- *args
    match vararg.val with
    | some (.mk_arg _ ⟨_, name⟩ _ _) => defineName name
    | none => pure ()
    -- keyword-only args
    for a in kwonlyargs.val do
      match a with
      | .mk_arg _ ⟨_, name⟩ _ _ => defineName name
    -- **kwargs
    match kwarg.val with
    | some (.mk_arg _ ⟨_, name⟩ _ _) => defineName name
    | none => pure ()

/-- Define the names a statement list binds by definition, assignment, `for` and `with`
targets, imports and `except … as`, including those in nested blocks but not in nested
function or class bodies. Lets a scope's code refer to names bound later in it. -/
partial def preCollectDefined (stmts : Array (stmt SourceRange)) : FeatureM Unit :=
  for s in stmts do
    match s with
    | .FunctionDef _ ⟨_, name⟩ _ _ _ _ _ _ => defineName name
    | .AsyncFunctionDef _ ⟨_, name⟩ _ _ _ _ _ _ => defineName name
    | .ClassDef _ ⟨_, name⟩ _ _ _ _ _ => defineName name
    | .Assign _ ⟨_, targets⟩ _ _ => targets.forM defineTarget
    | .AnnAssign _ target _ _ _ => defineTarget target
    | .AugAssign _ target _ _ => defineTarget target
    | .For _ target _ ⟨_, body⟩ ⟨_, orelse⟩ _ | .AsyncFor _ target _ ⟨_, body⟩ ⟨_, orelse⟩ _ =>
      defineTarget target
      preCollectDefined body
      preCollectDefined orelse
    | .While _ _ ⟨_, body⟩ ⟨_, orelse⟩ | .If _ _ ⟨_, body⟩ ⟨_, orelse⟩ =>
      preCollectDefined body
      preCollectDefined orelse
    | .Import _ ⟨_, aliases⟩ | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
      aliases.forM (defineName ∘ aliasBinding)
    | .With _ ⟨_, items⟩ ⟨_, body⟩ _ | .AsyncWith _ ⟨_, items⟩ ⟨_, body⟩ _ =>
      for item in items do
        match item with
        | .mk_withitem _ _ ⟨_, optVars⟩ => optVars.forM defineTarget
      preCollectDefined body
    | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩
    | .TryStar _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
      preCollectDefined body
      for h in handlers do
        match h with
        | .ExceptHandler _ _ errname ⟨_, hBody⟩ =>
          errname.val.forM fun ⟨_, name⟩ => defineName name
          preCollectDefined hBody
      preCollectDefined orelse
      preCollectDefined finalbody
    | .Match _ _ ⟨_, cases⟩ =>
      for c in cases do
        match c with
        | .mk_match_case _ _ _ ⟨_, cBody⟩ => preCollectDefined cBody
    | _ => pure ()

/-! ## Leaf visitors -/

def visitConstant (c : constant SourceRange) : FeatureM Unit :=
  match c with
  | .ConTrue ..    => bumpConstant "ConTrue"
  | .ConFalse ..   => bumpConstant "ConFalse"
  | .ConPos ..     => bumpConstant "ConPos"
  | .ConNeg ..     => bumpConstant "ConNeg"
  | .ConString ..  => bumpConstant "ConString"
  | .ConFloat ..   => bumpConstant "ConFloat"
  | .ConComplex .. => bumpConstant "ConComplex"
  | .ConNone ..    => bumpConstant "ConNone"
  | .ConEllipsis ..=> bumpConstant "ConEllipsis"
  | .ConBytes ..   => bumpConstant "ConBytes"

def visitOperator (op : operator SourceRange) : FeatureM Unit :=
  match op with
  | .Add ..      => bumpOperator "Add"
  | .Sub ..      => bumpOperator "Sub"
  | .Mult ..     => bumpOperator "Mult"
  | .Div ..      => bumpOperator "Div"
  | .FloorDiv .. => bumpOperator "FloorDiv"
  | .Mod ..      => bumpOperator "Mod"
  | .Pow ..      => bumpOperator "Pow"
  | .LShift ..   => bumpOperator "LShift"
  | .RShift ..   => bumpOperator "RShift"
  | .BitOr ..    => bumpOperator "BitOr"
  | .BitXor ..   => bumpOperator "BitXor"
  | .BitAnd ..   => bumpOperator "BitAnd"
  | .MatMult ..  => bumpOperator "MatMult"

def visitUnaryOp (op : unaryop SourceRange) : FeatureM Unit :=
  match op with
  | .Invert .. => bumpUnaryop "Invert"
  | .Not ..    => bumpUnaryop "Not"
  | .UAdd ..   => bumpUnaryop "UAdd"
  | .USub ..   => bumpUnaryop "USub"

def visitBoolOp (op : boolop SourceRange) : FeatureM Unit :=
  match op with
  | .And .. => bumpBoolop "And"
  | .Or ..  => bumpBoolop "Or"

def visitCmpOp (op : cmpop SourceRange) : FeatureM Unit :=
  match op with
  | .Eq ..    => bumpCmpop "Eq"
  | .NotEq .. => bumpCmpop "NotEq"
  | .Lt ..    => bumpCmpop "Lt"
  | .LtE ..   => bumpCmpop "LtE"
  | .Gt ..    => bumpCmpop "Gt"
  | .GtE ..   => bumpCmpop "GtE"
  | .Is ..    => bumpCmpop "Is"
  | .IsNot .. => bumpCmpop "IsNot"
  | .In ..    => bumpCmpop "In"
  | .NotIn .. => bumpCmpop "NotIn"

/-! ## Expression visitor -/

partial def visitExpr (e : expr SourceRange) : FeatureM Unit := do
  match e with
  | .BoolOp _ op ⟨_, values⟩ =>
    bumpExpr "BoolOp"
    visitBoolOp op
    values.forM visitExpr
  | .NamedExpr _ target value =>
    bumpExpr "NamedExpr"
    visitExpr value
    (extractNames target).forM defineWalrusTarget
    visitExpr target
  | .BinOp _ left op right =>
    bumpExpr "BinOp"
    visitOperator op
    visitExpr left
    visitExpr right
  | .UnaryOp _ op operand =>
    bumpExpr "UnaryOp"
    visitUnaryOp op
    visitExpr operand
  | .Lambda _ args body =>
    bumpExpr "Lambda"
    visitDefaults args
    pushScope .function
    defineParams args
    visitExpr body
    popScope
  | .IfExp _ test body orelse =>
    bumpExpr "IfExp"
    visitExpr test
    visitExpr body
    visitExpr orelse
  | .Dict _ ⟨_, keys⟩ ⟨_, values⟩ =>
    bumpExpr "Dict"
    for k in keys do
      match k with
      | .some_expr _ ke => visitExpr ke
      | _ => pure ()
    values.forM visitExpr
  | .Set _ ⟨_, elts⟩ =>
    bumpExpr "Set"
    elts.forM visitExpr
  | .ListComp _ elt ⟨_, gens⟩ =>
    bumpExpr "ListComp"
    visitComprehensions gens (visitExpr elt)
  | .SetComp _ elt ⟨_, gens⟩ =>
    bumpExpr "SetComp"
    visitComprehensions gens (visitExpr elt)
  | .DictComp _ key value ⟨_, gens⟩ =>
    bumpExpr "DictComp"
    visitComprehensions gens do
      visitExpr key
      visitExpr value
  | .GeneratorExp _ elt ⟨_, gens⟩ =>
    bumpExpr "GeneratorExp"
    visitComprehensions gens (visitExpr elt)
  | .Await _ value =>
    bumpExpr "Await"
    visitExpr value
  | .Yield _ ⟨_, value⟩ =>
    bumpExpr "Yield"
    value.forM visitExpr
  | .YieldFrom _ value =>
    bumpExpr "YieldFrom"
    visitExpr value
  | .Compare _ left ⟨_, ops⟩ ⟨_, comparators⟩ =>
    bumpExpr "Compare"
    visitExpr left
    ops.forM visitCmpOp
    comparators.forM visitExpr
  | .Call _ f ⟨_, args⟩ ⟨_, kwargs⟩ =>
    bumpExpr "Call"
    visitExpr f
    args.forM visitExpr
    kwargs.forM fun kw => visitKeyword kw
  | .FormattedValue _ value _ ⟨_, fmtSpec⟩ =>
    bumpExpr "FormattedValue"
    visitExpr value
    fmtSpec.forM visitExpr
  | .Interpolation _ value _ _ ⟨_, fmtSpec⟩ =>
    bumpExpr "Interpolation"
    visitExpr value
    fmtSpec.forM visitExpr
  | .JoinedStr _ ⟨_, values⟩ =>
    bumpExpr "JoinedStr"
    values.forM visitExpr
  | .TemplateStr _ ⟨_, values⟩ =>
    bumpExpr "TemplateStr"
    values.forM visitExpr
  | .Constant _ c _ =>
    bumpExpr "Constant"
    visitConstant c
  | .Attribute _ value _ _ =>
    bumpExpr "Attribute"
    visitExpr value
  | .Subscript _ value slice _ =>
    bumpExpr "Subscript"
    visitExpr value
    visitExpr slice
  | .Starred _ value _ =>
    bumpExpr "Starred"
    visitExpr value
  | .Name _ ⟨_, name⟩ (.Load _) =>
    bumpExpr "Name"
    let defined ← isNameDefined name
    if !defined then
      bumpUnresolved name
  | .Name _ ⟨_, _⟩ _ =>
    bumpExpr "Name"
  | .List _ ⟨_, elts⟩ _ =>
    bumpExpr "List"
    elts.forM visitExpr
  | .Tuple _ ⟨_, elts⟩ _ =>
    bumpExpr "Tuple"
    elts.forM visitExpr
  | .Slice _ ⟨_, lower⟩ ⟨_, upper⟩ ⟨_, step⟩ =>
    bumpExpr "Slice"
    lower.forM visitExpr
    upper.forM visitExpr
    step.forM visitExpr
where
  /-- Visit a comprehension's generators and then `body`. The enclosing scope evaluates the
  first iterable; the rest, the targets, the conditions and `body` are in a new scope that
  binds every target name. -/
  visitComprehensions (gens : Array (comprehension SourceRange)) (body : FeatureM Unit) :
      FeatureM Unit := do
    if let some (.mk_comprehension _ _ iter _ _ : comprehension SourceRange) := gens[0]? then
      visitExpr iter
    pushScope .comprehension
    for (g, i) in gens.zipIdx do
      let .mk_comprehension _ target iter ⟨_, ifs⟩ _ := g
      if i > 0 then visitExpr iter
      defineTarget target
      visitExpr target
      ifs.forM visitExpr
    body
    popScope
  /-- Visit the defaults of `args`, which the enclosing scope evaluates. -/
  visitDefaults (args : arguments SourceRange) : FeatureM Unit := do
    match args with
    | .mk_arguments _ _ _ _ _ ⟨_, kwDefaults⟩ _ ⟨_, defaults⟩ =>
      defaults.forM visitExpr
      for d in kwDefaults do
        match d with
        | .some_expr _ d => visitExpr d
        | _ => pure ()
  visitKeyword (kw : keyword SourceRange) : FeatureM Unit := do
    match kw with
    | .mk_keyword _ _ value => visitExpr value

/-! ## Pattern visitor -/

partial def visitPattern (p : pattern SourceRange) : FeatureM Unit := do
  match p with
  | .MatchValue _ value =>
    bumpPattern "MatchValue"
    visitExpr value
  | .MatchSingleton _ c =>
    bumpPattern "MatchSingleton"
    visitConstant c
  | .MatchSequence _ ⟨_, pats⟩ =>
    bumpPattern "MatchSequence"
    pats.forM visitPattern
  | .MatchMapping _ ⟨_, keys⟩ ⟨_, pats⟩ ⟨_, rest⟩ =>
    bumpPattern "MatchMapping"
    keys.forM visitExpr
    pats.forM visitPattern
    rest.forM fun ⟨_, name⟩ => defineName name
  | .MatchClass _ cls ⟨_, pats⟩ ⟨_, _kwAttrs⟩ ⟨_, kwPats⟩ =>
    bumpPattern "MatchClass"
    visitExpr cls
    pats.forM visitPattern
    kwPats.forM visitPattern
  | .MatchStar _ ⟨_, name⟩ =>
    bumpPattern "MatchStar"
    name.forM fun ⟨_, name⟩ => defineName name
  | .MatchAs _ ⟨_, pat⟩ ⟨_, name⟩ =>
    bumpPattern "MatchAs"
    pat.forM visitPattern
    name.forM fun ⟨_, name⟩ => defineName name
  | .MatchOr _ ⟨_, pats⟩ =>
    bumpPattern "MatchOr"
    pats.forM visitPattern

/-! ## Statement visitor -/

/-- Record the decorators' names and visit their expressions. -/
def visitDecorators (decorators : Array (expr SourceRange)) : FeatureM Unit := do
  recordDecoratorNames decorators
  decorators.forM visitExpr

partial def visitStmt (s : stmt SourceRange) : FeatureM Unit := do
  match s with
  | .FunctionDef _ ⟨_, name⟩ args ⟨_, body⟩ ⟨_, decorators⟩ _ _ _ =>
    bumpStmt "FunctionDef"
    defineName name
    visitDecorators decorators
    visitExpr.visitDefaults args
    -- Enter new scope with params, pre-collect body definitions
    pushScope .function
    defineParams args
    preCollectDefined body
    body.forM visitStmt
    popScope
  | .AsyncFunctionDef _ ⟨_, name⟩ args ⟨_, body⟩ ⟨_, decorators⟩ _ _ _ =>
    bumpStmt "AsyncFunctionDef"
    defineName name
    visitDecorators decorators
    visitExpr.visitDefaults args
    pushScope .function
    defineParams args
    preCollectDefined body
    body.forM visitStmt
    popScope
  | .ClassDef _ ⟨_, name⟩ ⟨_, bases⟩ ⟨_, keywords⟩ ⟨_, body⟩ ⟨_, decorators⟩ _ =>
    bumpStmt "ClassDef"
    defineName name
    visitDecorators decorators
    bases.forM visitExpr
    keywords.forM visitExpr.visitKeyword
    pushScope .classBody
    preCollectDefined body
    body.forM visitStmt
    popScope
  | .Return _ ⟨_, value⟩ =>
    bumpStmt "Return"
    value.forM visitExpr
  | .Delete _ ⟨_, targets⟩ =>
    bumpStmt "Delete"
    targets.forM visitExpr
  | .Assign _ ⟨_, targets⟩ value _ =>
    bumpStmt "Assign"
    targets.forM defineTarget
    targets.forM visitExpr
    visitExpr value
  | .AugAssign _ target op value =>
    bumpStmt "AugAssign"
    defineTarget target
    visitExpr target
    visitOperator op
    visitExpr value
  | .AnnAssign _ target _ ⟨_, value⟩ _ =>
    bumpStmt "AnnAssign"
    defineTarget target
    visitExpr target
    value.forM visitExpr
  | .For _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    bumpStmt "For"
    defineTarget target
    visitExpr target
    visitExpr iter
    body.forM visitStmt
    orelse.forM visitStmt
  | .AsyncFor _ target iter ⟨_, body⟩ ⟨_, orelse⟩ _ =>
    bumpStmt "AsyncFor"
    defineTarget target
    visitExpr target
    visitExpr iter
    body.forM visitStmt
    orelse.forM visitStmt
  | .While _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
    bumpStmt "While"
    visitExpr test
    body.forM visitStmt
    orelse.forM visitStmt
  | .If _ test ⟨_, body⟩ ⟨_, orelse⟩ =>
    bumpStmt "If"
    visitExpr test
    body.forM visitStmt
    orelse.forM visitStmt
  | .With _ ⟨_, items⟩ ⟨_, body⟩ _ =>
    bumpStmt "With"
    for item in items do
      match item with
      | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
        visitExpr ctxExpr
        match optVars with
        | some e =>
          defineTarget e
          visitExpr e
        | none => pure ()
    body.forM visitStmt
  | .AsyncWith _ ⟨_, items⟩ ⟨_, body⟩ _ =>
    bumpStmt "AsyncWith"
    for item in items do
      match item with
      | .mk_withitem _ ctxExpr ⟨_, optVars⟩ =>
        visitExpr ctxExpr
        match optVars with
        | some e =>
          defineTarget e
          visitExpr e
        | none => pure ()
    body.forM visitStmt
  | .Raise _ ⟨_, exc⟩ ⟨_, cause⟩ =>
    bumpStmt "Raise"
    exc.forM visitExpr
    cause.forM visitExpr
  | .Try _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
    bumpStmt "Try"
    body.forM visitStmt
    for h in handlers do
      match h with
      | .ExceptHandler _ ⟨_, exType⟩ errname ⟨_, hBody⟩ =>
        exType.forM visitExpr
        -- Define the handler variable (e.g., `as e`)
        match errname.val with
        | some ⟨_, name⟩ => defineName name
        | none => pure ()
        hBody.forM visitStmt
    orelse.forM visitStmt
    finalbody.forM visitStmt
  | .TryStar _ ⟨_, body⟩ ⟨_, handlers⟩ ⟨_, orelse⟩ ⟨_, finalbody⟩ =>
    bumpStmt "TryStar"
    body.forM visitStmt
    for h in handlers do
      match h with
      | .ExceptHandler _ ⟨_, exType⟩ errname ⟨_, hBody⟩ =>
        exType.forM visitExpr
        match errname.val with
        | some ⟨_, name⟩ => defineName name
        | none => pure ()
        hBody.forM visitStmt
    orelse.forM visitStmt
    finalbody.forM visitStmt
  | .Assert _ test ⟨_, msg⟩ =>
    bumpStmt "Assert"
    visitExpr test
    msg.forM visitExpr
  | .Import _ ⟨_, aliases⟩ =>
    bumpStmt "Import"
    aliases.forM (defineName ∘ aliasBinding)
  | .ImportFrom _ _ ⟨_, aliases⟩ _ =>
    bumpStmt "ImportFrom"
    aliases.forM (defineName ∘ aliasBinding)
  | .Global _ ⟨_, names⟩ =>
    bumpStmt "Global"
    names.forM fun ⟨_, name⟩ => defineGlobal name
  | .Nonlocal .. =>
    bumpStmt "Nonlocal"
  | .Expr _ value =>
    bumpStmt "Expr"
    visitExpr value
  | .Pass .. =>
    bumpStmt "Pass"
  | .Break .. =>
    bumpStmt "Break"
  | .Continue .. =>
    bumpStmt "Continue"
  | .Match _ subject ⟨_, cases⟩ =>
    bumpStmt "Match"
    visitExpr subject
    for c in cases do
      match c with
      | .mk_match_case _ pat ⟨_, guard⟩ ⟨_, cBody⟩ =>
        visitPattern pat
        guard.forM visitExpr
        cBody.forM visitStmt
  | .TypeAlias _ _ _ value =>
    bumpStmt "TypeAlias"
    visitExpr value

/-! ## Entry point and formatting -/

/-- Run the feature analysis over an array of top-level statements. -/
public def analyzeFeatures (stmts : Array (stmt SourceRange)) : FeatureState :=
  let action : FeatureM Unit := do
    -- Pre-collect module-level names so forward references resolve
    preCollectDefined stmts
    stmts.forM visitStmt
  (action |>.run {}).2

/-- Format a HashMap as sorted lines of "  Name: Count". -/
def formatCounts (m : Std.HashMap String Nat) : String :=
  let entries := m.toList.mergeSort (·.1 < ·.1)
  entries.foldl (init := "") fun acc (k, v) =>
    acc ++ s!"  {k}: {v}\n"

/-- Format the full feature report. -/
public def formatReport (s : FeatureState) : String :=
  let sections := #[
    ("Statement Features", s.stmtCounts),
    ("Expression Features", s.exprCounts),
    ("Constant Features", s.constantCounts),
    ("Operator Features", s.operatorCounts),
    ("UnaryOp Features", s.unaryopCounts),
    ("BoolOp Features", s.boolopCounts),
    ("CmpOp Features", s.cmpopCounts),
    ("Pattern Features", s.patternCounts),
    ("Unresolved Names", s.unresolvedNames),
    ("Decorator Names", s.decoratorNames)
  ]
  let body := sections.foldl (init := "") fun acc (title, counts) =>
    if counts.isEmpty then acc
    else acc ++ s!"=== {title} ===\n{formatCounts counts}\n"
  let warnSection := if s.warnings.isEmpty then ""
    else "=== Warnings ===\n" ++
      s.warnings.foldl (init := "") fun acc w => acc ++ s!"  {w}\n"
  body ++ warnSection

end StrataPython.FeatureUsage
