/-
Structural plans for syntax nodes, ENGINE.md section 3.

Each plan states one node's semantics as data: which children it evaluates, in
what order, and what it does with their results. The engine supplies the
recursion through `evalSubterm`, so ordering and abandon-on-exception come from
`executeChildren` rather than from a hand-written `match` arm per node -- which
is the whole point of the section. A rule here is checked by `compileRules` like
any other: reading a child before evaluating it does not compile.

Nodes are added here one at a time and their hand-written arm retired as each
lands, so `RuleValidate`'s `unkeyed-syntax` count is the honest measure of what
is still dispatched by hand. Nodes whose semantics are evaluation order plus an
operation are the ones that belong here; the families ENGINE.md section 3 lists as
engine code stay engine code.
-/
import Pylate.RuleLang.Compile

namespace Pylate.RuleDriven.Syntax

open Pylate
open Pylate.RuleDriven

/-- The frame a syntax node is executed in: its children in source order, plus
    the operator or name it carries. -/
def frameOf (subterms : List Subterm)
    (attributes : List (String × Attr) := []) : Frame :=
  { subterms, attributes }

private def exprRule (kind : ExprKind) (body : Plan) : Rule :=
  { key := .expr kind, callable := { signature := {}, body } }

private def stmtRule (kind : StmtKind) (body : Plan) : Rule :=
  { key := .stmt kind, callable := { signature := {}, body } }

/-- `binop` -- both operands in order, then the shared ordered binary planner.
    The operator rides in the frame, so one plan serves all twelve. -/
def binopPlan : Plan :=
  .evalChild 0 <| .evalChild 1 <|
    .invoke { operation := .binaryOfAttr "op"
              arguments := [.read (.evaluated 0), .read (.evaluated 1)] }
      (.normal (.read (.local 0)))

/-- `subscr` -- receiver then index, then the item-read protocol. -/
def subscriptPlan : Plan :=
  .evalChild 0 <| .evalChild 1 <|
    .invoke { operation := .itemReadAt none none
              receiver := some (.read (.evaluated 0))
              arguments := [.read (.evaluated 1)] }
      (.normal (.read (.local 0)))

/-- `boolAnd` -- short-circuiting as data: the left operand's falsy partition is
    the result, and only its truthy partition evaluates the right. -/
def boolAndPlan : Plan :=
  .refineBranch 0
    (.evalChild 1 (.normal (.read (.evaluated 1))))
    (.normal (.read (.evaluated 0)))

/-- `boolOr` -- the dual. -/
def boolOrPlan : Plan :=
  .refineBranch 0
    (.normal (.read (.evaluated 0)))
    (.evalChild 1 (.normal (.read (.evaluated 1))))

/-- `ifexp` -- the condition's truth partitions select which branch is
    evaluated, and each partition carries its own refinement.

    Note `.evaluated` indexes *evaluation order*, not subterm position: on the
    falsy path child 2 is the second thing evaluated, so both branches read
    index 1. The rule compiler catches getting this wrong -- it rejected
    `.evaluated 2` here, because only two children are evaluated on either
    path. -/
def conditionalPlan : Plan :=
  .refineBranch 0
    (.evalChild 1 (.normal (.read (.evaluated 1))))
    (.evalChild 2 (.normal (.read (.evaluated 1))))

/-- `listlit` -- every element in order, then allocate with the element summary
    from the join.

    The size is stated as the child count rather than as mere non-emptiness: a
    list literal keeps every element, so `[1, 2]` has exactly two, and that is
    what lets `xs[0]` avoid a bounds obligation. The empty case needs no marker
    because allocation already records `exact 0`. `setLiteralPlan` below cannot
    do this -- `{1, 1}` has one element, not two. -/
def listLiteralPlan : Plan :=
  .evalChildren 0 <|
    .allocate .list [(.elem, .joinEvaluated)] <|
      .mutate (.sizeOfChildren (.read (.local 0)) .list)
        (.normal (.read (.local 0)))

def setLiteralPlan : Plan :=
  .evalChildren 0 <|
    .allocate .set [(.elem, .joinEvaluated)] <|
      .branch .anyEvaluated
        (.mutate (.emptiness (.read (.local 0)) .set .nonempty)
          (.normal (.read (.local 0))))
        (.normal (.read (.local 0)))

/-- `unary` -- one operand, then the operator from the frame. As with `binop`,
    one plan serves `-`, `+` and `~`. -/
def unaryPlan : Plan :=
  .evalChild 0 <|
    .invoke { operation := .unaryOfAttr "op"
              arguments := [.read (.evaluated 0)] }
      (.normal (.read (.local 0)))

/-- `fstr` -- every part in order, and the result is a string whatever they
    were. The conversion and format-spec protocols are not modelled here, which
    is the same gap the hand-written arm had. -/
def formatStringPlan : Plan :=
  .evalChildren 0 (.normal .str)

/-- `not` -- the truth protocol decides, and both partitions produce a bool. -/
def notPlan : Plan :=
  .refineBranch 0 (.normal .bool) (.normal .bool)

-- ------------------------------------------------------------- statements

/-- `pass` -- no children, no effect. -/
def passPlan : Plan := .normal .none

/-- `break` and `continue` -- the completions `Plan` gained for exactly this. -/
def breakPlan : Plan := .breakLoop
def continuePlan : Plan := .continueLoop

/-- An expression statement evaluates for effect and discards the value. -/
def expressionStatementPlan : Plan :=
  .evalChild 0 (.normal .none)

/-- `if` -- the condition refined syntactically, so each body runs on a state
    narrowed by the test rather than the joined one. -/
def ifPlan : Plan :=
  .refineBranch 0 (.evalBody 1 (.normal .none)) (.evalBody 2 (.normal .none))

/-- `assert` -- the same refinement, the falsy side raising, and the obligation
    the hand-written transfer recorded stated as an effect. -/
def assertPlan : Plan :=
  .obligate "assert" "asserted condition holds" <|
    .refineBranch 0 (.normal .none)
      (.raise (RaiseSpec.machine "AssertionError"))

/-- `assign` -- the value first, then the binding. A failing right-hand side
    performs no binding, which `evalChild` gives without the rule saying so. -/
def assignPlan : Plan :=
  .evalChild 1 (.bindTarget 0 (.read (.evaluated 0)) (.normal .none))

/-- `return` -- one plan for both shapes. `evalChildren` over an empty child list
    evaluates nothing, so `anyEvaluated` distinguishes `return e` from a bare
    `return` without needing two rules for one key. -/
def returnPlan : Plan :=
  .evalChildren 0 <|
    .branch .anyEvaluated
      (.returnWith (.read (.evaluated 0)))
      (.returnWith .none)

/-- `del` -- the target's binding is removed; no value is involved. -/
def deletePlan : Plan :=
  .deleteTarget 0 (.normal .none)

/-- `x: T = e` -- the same as an assignment to the name, and a bare `x: T` with
    no value binds nothing. One plan covers both, as with `return`. -/
def annotatedAssignPlan : Plan :=
  .evalChildren 1 <|
    .branch .anyEvaluated
      (.bindTarget 0 (.read (.evaluated 0)) (.normal .none))
      (.normal .none)

/-- `cmp` -- both operands, then the operator's own operation. `in` and `not in`
    resolve to the membership protocol and everything else to comparison, decided
    by `Operation.resolve` from the operator rather than by a branch in the plan,
    because the operator is already frame data. -/
def comparePlan : Plan :=
  .evalChild 0 <| .evalChild 1 <|
    .invoke { operation := .compareOfAttr "op"
              arguments := [.read (.evaluated 0), .read (.evaluated 1)] }
      (.normal (.read (.local 0)))

/-- `const` -- no children and no operation: the value is the node's own data. -/
def constantPlan : Plan := .normal (.constantOf "value")

/-- `tuplelit` -- every element in order, then a positional slot each. Slots are
    what make `pair[1]` a proven-in-bounds read rather than an element-summary
    read with an IndexError. -/
def tupleLiteralPlan : Plan :=
  .evalChildren 0 (.allocateSlots .tuple (.normal (.read (.local 0))))

/-- `dictlit` -- keys and values in source order, even children keys and odd ones
    values, then a mapping allocation that also gives each literal key its own
    cell. -/
def dictLiteralPlan : Plan :=
  .evalChildren 0 (.allocateMapping .dict (.normal (.read (.local 0))))

/-- `attr` -- the receiver, then the attribute protocol. The field name is frame
    data, so one plan serves every attribute. -/
def attributePlan : Plan :=
  .evalChild 0 <|
    .invoke { operation := .attributeReadOfAttr "field"
              receiver := some (.read (.evaluated 0)) }
      (.normal (.read (.local 0)))

/-- `name` -- the read, with whatever unbound partitions the engine finds. -/
def namePlan : Plan :=
  .readName "name" (.normal (.read (.local 0)))

-- -------------------------------------------------------------- targets

/-- A target is executed with the value being bound in `Frame.receiver`, which is
    what lets these four plans name it without an argument convention. -/
private def targetRule (kind : TargetKind) (body : Plan) : Rule :=
  { key := .target kind, callable := { signature := {}, body } }

/-- `x = v` -- the name binding. -/
def nameTargetPlan : Plan :=
  .storeName "name" (.read .receiver) (.normal (.read .receiver))

/-- `o.f = v` -- the receiver is evaluated, then the attribute protocol stores. -/
def attributeTargetPlan : Plan :=
  .evalChild 0 <|
    .invoke { operation := .attributeWriteOfAttr "field"
              receiver := some (.read (.evaluated 0))
              arguments := [.read .receiver] }
      (.normal (.read .receiver))

/-- `o[i] = v` -- receiver then index in source order, then the item protocol. A
    failing receiver or index performs no store, which `evalChild` gives. -/
def subscriptTargetPlan : Plan :=
  .evalChild 0 <| .evalChild 1 <|
    .invoke { operation := .itemWriteAt none none
              receiver := some (.read (.evaluated 0))
              arguments := [.read (.evaluated 1), .read .receiver] }
      (.normal (.read .receiver))

/-- `a, b = v` -- each nested target takes the element summary of the value. -/
def tupleTargetPlan : Plan :=
  .bindEach 0 (.elements .receiver) (.normal (.read .receiver))

def targetRules : List Rule :=
  [ targetRule .name nameTargetPlan,
    targetRule .attr attributeTargetPlan,
    targetRule .subscript subscriptTargetPlan,
    targetRule .tuple tupleTargetPlan ]

/-- A literal subscript index, as frame data. A string literal proves which
    per-key cell a store writes and a read consults; a non-negative integer proves
    a tuple read in bounds. Both belong on the plan rather than inside a
    dispatcher, so the plan fully describes its node. -/
def literalAttrs : Expr -> List (String × Attr)
  | .const _ (.cstr key) => [("literalKey", .name key)]
  | .const _ (.cint value) =>
    if value >= 0 then [("literalIndex", .index value.toNat)] else []
  | _ => []

/-- The children of a target, in source order, with the value being bound
    supplied separately as the frame's receiver. -/
def targetFramesOf : Target -> Option Frame
  | .tname _ name => some (frameOf [] [("name", .name name)])
  | .tattr _ receiver field =>
    some (frameOf [.expr receiver] [("field", .name field)])
  | .tsub _ receiver index =>
    some (frameOf [.expr receiver, .expr index] (literalAttrs index))
  | .ttuple _ targets => some (frameOf (targets.map .target))

/-- A target's own position, which `Syntax.lean` does not expose. -/
def targetPos : Target -> Pos
  | .tname p _ | .tattr p _ _ | .tsub p _ _ | .ttuple p _ => p

def routedTargetKinds : List TargetKind :=
  targetRules.filterMap fun rule =>
    match rule.key with | .target kind => some kind | _ => none

-- --------------------------------------------------- declared engine bodies

/-- Section 1.6 keeps six constructors in the generic interpreter: loop and
    comprehension fixpoints, `try`/`except`/`finally`, and the generator forms.
    Those are algorithms *over* plans, not plans.

    They are keyed anyway, with `engine` as the body. That is the point of the
    escape hatch: every constructor has exactly one entry, so the coverage
    condition stays satisfiable, and the number of engine bodies becomes a
    tracked inventory figure that must not grow. An omitted rule is invisible; a
    declared engine body is not. The dispatcher sees `engine` and defers to the
    hand-written transfer, which is what the body says it will do. -/
def engineExprRules : List Rule :=
  [ -- `call` is the last unkeyed node and the most significant one, so the
    -- reason is worth stating precisely rather than counting it away.
    --
    -- `evalCall` dispatches on its *callee's syntactic shape*: `.attr` is a
    -- method call, `.name` is a function or class call, anything else is a
    -- computed callee. A plan names children positionally, not by constructor,
    -- so no frame describes that branch. On top of it sits keyword and argument
    -- binding, which is `Signature.bind` -- machinery a syntax plan would only
    -- re-invoke.
    --
    -- What this does *not* mean: call semantics are not hand-written. They are
    -- the 105 compiled builtin rules plus user-function inlining, all rule data
    -- already. What stays engine code is the plumbing from a call node to a
    -- rule: evaluate the callee, the arguments, the keywords, in Python's order,
    -- then resolve. Routing it needs a condition on a subterm's constructor, and
    -- each branch would still hand off to the resolver, so the plan would state
    -- the evaluation order and nothing else. That order is already established
    -- once by `executeChildren`.
    exprRule .call (.engine "callResolution"),
    exprRule .listComp (.engine "comprehension"),
    exprRule .setComp (.engine "comprehension"),
    exprRule .dictComp (.engine "comprehension"),
    exprRule .genComp (.engine "comprehension"),
    exprRule .yieldE (.engine "yield"),
    exprRule .yieldFrom (.engine "yieldFrom") ]

/-- The annotation grammar is keyed with engine bodies, and the reason is not
    convenience.

    An annotation is not evaluated. It is consumed by five separate analyses --
    `annTags`, `assumeAnn`, `annEntailed`, `annEntailedDeep` and
    `materializeAnn` -- each of which matches the grammar and produces a tag set,
    a boolean, or a materialised value. `Plan` describes a flow: children
    evaluated in order, operations invoked, completions produced. It has no
    vocabulary for "the tag set this form denotes" or "does this value entail this
    form", so a plan per form would either be one `engine` escape wearing a
    costume or eight plans per analysis, forty in total, none of which says
    anything the function did not.

    Keying them anyway is what the declared escape hatch is for (ENGINE.md
    section 3, "What has to stay hard-coded"): eight declared
    engine bodies are eight inventory items whose count must not grow, where eight
    omissions would be invisible. Doing this properly needs a second rule language
    over the annotation grammar, which is a different project from section 1. -/
private def annRule (kind : AnnKind) (body : Plan) : Rule :=
  { key := .ann kind, callable := { signature := {}, body } }

def engineAnnRules : List Rule :=
  allAnnKinds.map fun kind => annRule kind (.engine "annotationAnalyses")

def engineAnnKinds : List AnnKind :=
  engineAnnRules.filterMap fun rule =>
    match rule.key with | .ann kind => some kind | _ => none

def engineStmtRules : List Rule :=
  [ -- `raise` joins the escape list with its own reason: the bare form
    -- re-raises whatever the enclosing handler is handling, which is engine
    -- state rather than node data, so no frame can describe it.
    stmtRule .raiseS (.engine "raiseOrReRaise"),
    stmtRule .whileS (.engine "whileFixpoint"),
    stmtRule .forS (.engine "forFixpoint"),
    stmtRule .tryS (.engine "tryExceptFinally") ]

/-- The plans that are routed. Keeping this list separate from the rule set
    makes the count of routed nodes a fact rather than a claim. -/
def syntaxRules : List Rule :=
  [ exprRule .binop binopPlan,
    exprRule .subscr subscriptPlan,
    exprRule .boolAnd boolAndPlan,
    exprRule .boolOr boolOrPlan,
    exprRule .ifexp conditionalPlan,
    exprRule .listlit listLiteralPlan,
    exprRule .setlit setLiteralPlan,
    exprRule .notE notPlan,
    exprRule .unary unaryPlan,
    exprRule .fstr formatStringPlan,
    stmtRule .pass passPlan,
    stmtRule .brk breakPlan,
    stmtRule .cont continuePlan,
    stmtRule .exprS expressionStatementPlan,
    stmtRule .ifS ifPlan,
    stmtRule .assertS assertPlan,
    stmtRule .assign assignPlan,
    stmtRule .ret returnPlan,
    stmtRule .delS deletePlan,
    stmtRule .annAssign annotatedAssignPlan,
    exprRule .cmp comparePlan,
    exprRule .const constantPlan,
    exprRule .tuplelit tupleLiteralPlan,
    exprRule .dictlit dictLiteralPlan,
    exprRule .name namePlan,
    exprRule .attr attributePlan ]

/-- The node's children in source order and the non-value data it carries. The
    plan names children positionally, so this order is the interface between the
    syntax and its rule. -/
def framesOf : Expr -> Option Frame
  | .binop _ op left right =>
    some (frameOf [.expr left, .expr right] [("op", .binOp op)])
  | .subscr _ receiver index =>
    some (frameOf [.expr receiver, .expr index] (literalAttrs index))
  | .boolop _ _ [left, right] =>
    some (frameOf [.expr left, .expr right])
  | .ifexp _ condition yes no =>
    some (frameOf [.expr condition, .expr yes, .expr no])
  | .listlit _ values | .setlit _ values =>
    some (frameOf (values.map .expr))
  | .notE _ value => some (frameOf [.expr value])
  | .unary _ op value => some (frameOf [.expr value] [("op", .unOp op)])
  | .fstr _ parts => some (frameOf (parts.map .expr))
  | .cmp _ op left right =>
    some (frameOf [.expr left, .expr right] [("op", .cmpOp op)])
  | .const _ value => some (frameOf [] [("value", .constant value)])
  | .tuplelit _ values => some (frameOf (values.map .expr))
  -- Key then value per item, so the plan's even/odd reading is source order.
  | .dictlit _ items =>
    some (frameOf (items.flatMap fun (key, value) => [.expr key, .expr value]))
  | .name _ x => some (frameOf [] [("name", .name x)])
  | .attr _ receiver field =>
    some (frameOf [.expr receiver] [("field", .name field)])
  | _ => none

/-- The syntax table as a rule set. `Tests/RuleSyntaxPlan.lean` runs
    `compileRules` over it and fails on any rule error, so an invalid plan is a
    failing gate rather than a silently missing one. The callable sets prove the
    same property with `native_decide`; that tactic segfaults on this set, so the
    check is a suite here instead of a theorem, which is a weaker guarantee and
    is recorded as such. -/
def syntaxRuleSet : RuleSet :=
  { rules := syntaxRules ++ targetRules ++ engineExprRules ++ engineStmtRules
      ++ engineAnnRules }

/-- The keys whose body is a declared engine escape. Reported separately from the
    unkeyed ones, because "dispatched by hand and declared so" is a different
    fact from "not keyed at all". -/
def engineExprKinds : List ExprKind :=
  engineExprRules.filterMap fun rule =>
    match rule.key with | .expr kind => some kind | _ => none

def engineStmtKinds : List StmtKind :=
  engineStmtRules.filterMap fun rule =>
    match rule.key with | .stmt kind => some kind | _ => none

/-- `none` when a rule failed to compile, so a caller cannot proceed on a
    partially populated table.

    This one keeps its validation, unlike the builtin sets. They have
    `native_decide` theorems proving they compile at build time; the syntax set is
    large enough that `native_decide` segfaults on it, so this check is the only
    thing standing between a malformed plan and a silently degraded table. It was
    briefly replaced with `buildTable` while chasing startup cost, and measured no
    faster -- a real fail-closed property for nothing. -/
def compiledSyntaxRules? : Option CompiledRules :=
  (compileRules syntaxRuleSet).toOption

/-- The keys the table covers, for the validator's `unkeyed-syntax` condition. -/
def routedExprKinds : List ExprKind :=
  syntaxRules.filterMap fun rule =>
    match rule.key with
    | .expr kind => some kind
    | _ => none

def routedStmtKinds : List StmtKind :=
  syntaxRules.filterMap fun rule =>
    match rule.key with
    | .stmt kind => some kind
    | _ => none

/-- A statement's children. Only the forms whose children are expressions are
    here: a body or an assignment target is not an expression, and the effects
    that would evaluate them do not exist yet. -/
def stmtFramesOf : Stmt -> Option Frame
  | .pass _ | .brk _ | .cont _ => some (frameOf [])
  | .exprS _ value => some (frameOf [.expr value])
  | .ifS _ condition thenBody elseBody =>
    some (frameOf [.expr condition, .body thenBody, .body elseBody])
  | .assertS _ condition => some (frameOf [.expr condition])
  -- The target is child 0 and the value child 1, so the plan evaluates child 1
  -- first: that ordering is Python's, and stating it here rather than in the
  -- plan keeps the frame in source order.
  | .assign _ target value => some (frameOf [.target target, .expr value])
  | .ret _ value =>
    some (frameOf (match value with | some e => [.expr e] | none => []))
  | .delS _ target => some (frameOf [.target target])
  -- The annotated form names its target rather than carrying a `Target` node, so
  -- the frame synthesises one. Child 0 is the target and child 1 the value when
  -- there is one, which keeps the shape identical to a plain assignment.
  | .annAssign position name value =>
    some (frameOf (.target (.tname position name) ::
      (match value with | some e => [.expr e] | none => [])))
  | _ => none

end Pylate.RuleDriven.Syntax
