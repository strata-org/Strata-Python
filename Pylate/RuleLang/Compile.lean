/-
Static validation and indexing for plans.
-/
import Pylate.RuleLang.Plan
import Pylate.Syntax.Kinds

namespace Pylate.RuleDriven

open Pylate

inductive RuleKey
  | method (receiver : Tag) (name : String)
  | function (name : String)
  /-- A syntax node kind. One key per admitted constructor, with the operator
      carried as frame data rather than split across keys, so `x + y` and
      `x * y` share the `binop` plan. -/
  | expr (kind : ExprKind)
  | target (kind : TargetKind)
  | stmt (kind : StmtKind)
  | ann (kind : AnnKind)
deriving Repr, Inhabited, DecidableEq, Hashable

def RuleKey.render : RuleKey -> String
  | .method receiver name => s!"{receiver.render}.{name}"
  | .function name => name
  | .expr kind => s!"expr:{kind.render}"
  | .target kind => s!"target:{kind.render}"
  | .stmt kind => s!"stmt:{kind.render}"
  | .ann kind => s!"ann:{kind.render}"

/-- An expression or statement rule reads its children through `.evaluated` and
    has no receiver. A *target* rule does have one: a target is a store, and the
    value being bound travels in the receiver slot, which is what lets the four
    target plans name it without inventing an argument convention. -/
def RuleKey.hasReceiver : RuleKey -> Bool
  | .method .. | .target .. => true
  | .function .. | .expr .. | .stmt .. | .ann .. => false

def RuleKey.isSyntax : RuleKey -> Bool
  | .expr .. | .target .. | .stmt .. | .ann .. => true
  | .method .. | .function .. => false

structure Rule where
  key      : RuleKey
  callable : CallableRule
deriving Repr, Inhabited

structure RuleSet where
  rules : List Rule := []
deriving Repr, Inhabited

structure RuleError where
  rule   : String
  detail : String
deriving Repr, Inhabited

/-- The compiled rule database, keyed.

    `entries` was a list and `find?` scanned it, so every dispatch -- every method
    call and every syntax node -- walked a few hundred entries comparing
    `RuleKey`s structurally, which means comparing method-name strings. That is a
    constant per-site tax, which is why it never showed up as superlinear growth;
    it was simply on every site. -/
structure CompiledRules where
  table : Std.HashMap RuleKey CallableRule := {}
deriving Inhabited

def CompiledRules.find? (rules : CompiledRules) (key : RuleKey) :
    Option CallableRule :=
  rules.table[key]?

/-- The rules as a list, for the validator and the inventory conditions. Sorted by
    rendered key, because a hash map has no order and those conditions' output is
    compared. -/
def CompiledRules.entries (rules : CompiledRules) :
    List (RuleKey × CallableRule) :=
  rules.table.toList.mergeSort (fun a b => a.1.render < b.1.render)

/-- `evaluated` is how many children the plan has evaluated at this point.
    `evalChildren` sets it to `allSubterms`, meaning every remaining child, which
    the checker cannot count because it is a property of the node rather than of
    the rule. -/
def allSubterms : Nat := 1000000

def refErrors (signature : Signature) (hasReceiver : Bool)
    (depth : Nat) (evaluated : Nat := 0) : ValueRef -> List String
  | .receiver =>
    if hasReceiver then [] else ["function rule reads a receiver"]
  | .parameter name =>
    if signature.parameters.any (·.name == name) then []
    else [s!"unknown parameter '{name}'"]
  | .argument index =>
    let positional := signature.parameters.filter (·.kind != .keywordOnly)
    if index < positional.length || signature.varPos then []
    else [s!"positional argument {index} is outside the signature"]
  | .keyword name =>
    if signature.parameters.any (·.name == name) || signature.varKw then []
    else [s!"keyword '{name}' is outside the signature"]
  | .local index =>
    if index < depth then [] else [s!"local {index} is not in scope"]
  | .evaluated index =>
    if index < evaluated then []
    else [s!"child {index} is read before it is evaluated"]

partial def valueErrors (signature : Signature) (hasReceiver : Bool)
    (depth : Nat) (evaluated : Nat := 0) : ValueExpr -> List String
  | .bottom | .none | .bool | .int | .str | .bytes | .any | .notImplemented
  | .argumentElements => []
  | .joinEvaluated =>
    if evaluated > 0 then []
    else ["joins evaluated children before any child is evaluated"]
  | .constantOf _ => []
  | .read source | .elements source =>
    refErrors signature hasReceiver depth evaluated source
  | .join left right =>
    valueErrors signature hasReceiver depth evaluated left ++
    valueErrors signature hasReceiver depth evaluated right
  | .without value _ | .restrict value _ =>
    valueErrors signature hasReceiver depth evaluated value

def conditionErrors (signature : Signature) (hasReceiver : Bool)
    (depth : Nat) (evaluated : Nat) : Condition -> List String
  | .hasTag source _ =>
    refErrors signature hasReceiver depth evaluated source
  | .hashable value | .definitelyNonempty value
  | .definitelyEmpty value =>
    valueErrors signature hasReceiver depth evaluated value
  | .supplied name =>
    if signature.parameters.any (·.name == name) then []
    else [s!"condition names unknown parameter '{name}'"]
  | .anyEvaluated =>
    if evaluated > 0 then []
    else ["condition tests evaluated children before any child is evaluated"]
  | .field attrName _ =>
    -- The attribute has to be one the node actually carries, or the predicate
    -- silently reads as false and the rule takes its other branch forever.
    if hasReceiver then []
    else [s!"field condition on '{attrName}' needs a receiver to resolve against"]

def raiseErrors (signature : Signature) (hasReceiver : Bool)
    (depth : Nat) (evaluated : Nat) (spec : RaiseSpec) : List String :=
  (if spec.classes.isEmpty && spec.classesOf.isNone then
    ["raise has no exception class"] else []) ++
  (match spec.classesOf with
   | none => []
   | some source => refErrors signature hasReceiver depth evaluated source) ++
  match spec.value with
  | none => []
  | some value => valueErrors signature hasReceiver depth evaluated value

def mutationErrors (signature : Signature) (hasReceiver : Bool)
    (depth : Nat) (evaluated : Nat) : Mutation -> List String
  | .grow target cls cell value =>
    (if cell.validFor cls then [] else
      [s!"cell {cell.render} is invalid for {cls.render}"]) ++
    valueErrors signature hasReceiver depth evaluated target ++
    valueErrors signature hasReceiver depth evaluated value
  | .emptiness target _ _ =>
    valueErrors signature hasReceiver depth evaluated target
  | .sizeOfChildren target _ =>
    valueErrors signature hasReceiver depth evaluated target
  | .clear target cls cell =>
    (if cell.validFor cls then [] else
      [s!"cell {cell.render} is invalid for {cls.render}"]) ++
    valueErrors signature hasReceiver depth evaluated target
  | .bind _ value => valueErrors signature hasReceiver depth evaluated value
  | .unbind _ => []

def invocationErrors (signature : Signature) (hasReceiver : Bool)
    (depth : Nat) (evaluated : Nat) (call : Invocation) : List String :=
  (match call.receiver with
    | none => []
    | some receiver => valueErrors signature hasReceiver depth evaluated receiver) ++
  call.arguments.flatMap (valueErrors signature hasReceiver depth evaluated) ++
  call.keywords.flatMap fun (_, value) =>
    valueErrors signature hasReceiver depth evaluated value

partial def planErrors (signature : Signature) (hasReceiver : Bool)
    (depth : Nat) (evaluated : Nat := 0) : Plan -> List String
  | .normal .bottom => ["normal completion returns bottom; use stop"]
  | .normal value => valueErrors signature hasReceiver depth evaluated value
  | .stop => []
  | .raise spec => raiseErrors signature hasReceiver depth evaluated spec
  | .bind first next =>
    planErrors signature hasReceiver depth evaluated first ++
    planErrors signature hasReceiver (depth + 1) evaluated next
  | .mutate effect next =>
    mutationErrors signature hasReceiver depth evaluated effect ++
    planErrors signature hasReceiver depth evaluated next
  | .letValue value next =>
    valueErrors signature hasReceiver depth evaluated value ++
    planErrors signature hasReceiver (depth + 1) evaluated next
  | .allocate cls initializers next =>
    initializers.flatMap (fun (cell, value) =>
      (if cell.validFor cls then [] else
        [s!"cell {cell.render} is invalid for {cls.render}"]) ++
      valueErrors signature hasReceiver depth evaluated value) ++
    planErrors signature hasReceiver (depth + 1) evaluated next
  | .require condition failure next =>
    conditionErrors signature hasReceiver depth evaluated condition ++
    raiseErrors signature hasReceiver depth evaluated failure ++
    planErrors signature hasReceiver depth evaluated next
  | .branch condition yes no =>
    conditionErrors signature hasReceiver depth evaluated condition ++
    planErrors signature hasReceiver depth evaluated yes ++
    planErrors signature hasReceiver depth evaluated no
  | .truthBranch source truthy falsy =>
    refErrors signature hasReceiver depth evaluated source ++
    planErrors signature hasReceiver depth evaluated truthy ++
    planErrors signature hasReceiver depth evaluated falsy
  | .alternatives [] => ["empty alternatives; use stop"]
  | .alternatives plans =>
    plans.flatMap (planErrors signature hasReceiver depth)
  | .invoke call next =>
    invocationErrors signature hasReceiver depth evaluated call ++
    planErrors signature hasReceiver (depth + 1) evaluated next
  | .protocolChain candidates fallback =>
    candidates.flatMap (planErrors signature hasReceiver depth evaluated) ++
    planErrors signature hasReceiver depth evaluated fallback
  | .evalChild _ next =>
    planErrors signature hasReceiver depth (evaluated + 1) next
  | .evalChildren _ next =>
    -- Every remaining child is evaluated; how many that is depends on the node
    -- rather than the rule, so any index is in scope afterwards.
    planErrors signature hasReceiver depth allSubterms next
  | .engine _ => []
  | .returnWith value => valueErrors signature hasReceiver depth evaluated value
  | .breakLoop | .continueLoop => []
  | .obligate _ _ next => planErrors signature hasReceiver depth evaluated next
  | .evalBody _ next =>
    -- A body produces completions, not a value, so nothing is evaluated.
    planErrors signature hasReceiver depth evaluated next
  | .allocateSlots _ next | .allocateMapping _ next =>
    -- Both push the fresh object as a local.
    planErrors signature hasReceiver (depth + 1) evaluated next
  | .readName _ next => planErrors signature hasReceiver (depth + 1) evaluated next
  | .storeName _ value next =>
    valueErrors signature hasReceiver depth evaluated value ++
    planErrors signature hasReceiver depth evaluated next
  | .bindEach _ value next =>
    valueErrors signature hasReceiver depth evaluated value ++
    planErrors signature hasReceiver depth evaluated next
  | .deleteTarget _ next => planErrors signature hasReceiver depth evaluated next
  | .bindTarget _ value next =>
    valueErrors signature hasReceiver depth evaluated value ++
    planErrors signature hasReceiver depth evaluated next
  | .refineBranch _ truthy falsy =>
    -- The refined child is evaluated before either side runs, so both see it.
    planErrors signature hasReceiver depth (evaluated + 1) truthy ++
    planErrors signature hasReceiver depth (evaluated + 1) falsy

/-- The table alone, with no validation.

    `compileRules` fuses construction with checking, so going through it would
    re-run `planErrors` over every rule in every process -- about 25ms, against
    roughly 5ms of actual analysis for a small file -- to re-derive what the
    `native_decide` theorems beside each rule set already prove at *build* time.

    Validation therefore stays in `compileRules`, which those theorems and the
    `RuleValidate` suite call, and a production analysis reads the table. -/
def buildTable (source : RuleSet) : CompiledRules :=
  ⟨source.rules.foldl (init := ({} : Std.HashMap RuleKey CallableRule))
    (fun table rule => table.insert rule.key rule.callable)⟩

def compileRules (source : RuleSet) :
    Except (Array RuleError) CompiledRules := Id.run do
  let mut errors : Array RuleError := #[]
  let mut entries : Std.HashMap RuleKey CallableRule := {}
  for rule in source.rules do
    let label := rule.key.render
    if entries.contains rule.key then
      errors := errors.push ⟨label, "duplicate rule"⟩
    else
      let details :=
        rule.callable.signature.errors ++
        planErrors rule.callable.signature rule.key.hasReceiver 0 0
          rule.callable.body
      if details.isEmpty then
        entries := entries.insert rule.key rule.callable
      else
        for detail in details do
          errors := errors.push ⟨label, detail⟩
  if errors.isEmpty then .ok ⟨entries⟩ else .error errors

end Pylate.RuleDriven
