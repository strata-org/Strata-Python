/-
Static validation of a compiled rule set. The conditions and what each one
buys are in ENGINE.md section 3, "What is a table, and what a table buys".

Every condition is reported by name with the rules that fail it, so an unmet
obligation is visible rather than implicit. Conditions the rule language
enforces structurally are reported as such instead of being silently assumed.
-/
import Pylate.Rules.Builtins
import Pylate.Rules.SyntaxPlans

namespace Pylate.RuleDriven.Validate

open Pylate

structure Finding where
  condition : String
  rule      : String
  detail    : String
deriving Repr, Inhabited

structure Report where
  findings   : List Finding := []
  structural : List String := []
deriving Repr, Inhabited

private def internalRaises : Plan -> List String
  | .raise spec =>
    if spec.kind == .internal then spec.classes else []
  | .normal _ | .stop => []
  | .bind first next => internalRaises first ++ internalRaises next
  | .letValue _ next => internalRaises next
  | .mutate _ next => internalRaises next
  | .allocate _ _ next => internalRaises next
  | .require _ failure next =>
    (if failure.kind == .internal then failure.classes else []) ++
      internalRaises next
  | .branch _ yes no => internalRaises yes ++ internalRaises no
  | .truthBranch _ truthy falsy =>
    internalRaises truthy ++ internalRaises falsy
  | .alternatives plans => plans.flatMap internalRaises
  | .invoke _ next => internalRaises next
  | .protocolChain candidates fallback =>
    candidates.flatMap internalRaises ++ internalRaises fallback
  | .evalChild _ next | .evalChildren _ next => internalRaises next
  | .returnWith _ | .breakLoop | .continueLoop => []
  | .obligate _ _ next => internalRaises next
  | .evalBody _ next => internalRaises next
  | .bindTarget _ _ next => internalRaises next
  | .deleteTarget _ next => internalRaises next
  | .allocateSlots _ next | .allocateMapping _ next => internalRaises next
  | .readName _ next => internalRaises next
  | .storeName _ _ next | .bindEach _ _ next => internalRaises next
  | .refineBranch _ truthy falsy => internalRaises truthy ++ internalRaises falsy
  | .engine _ => []

private def raiseClasses : Plan -> List String
  | .raise spec => spec.classes
  | .normal _ | .stop => []
  | .bind first next => raiseClasses first ++ raiseClasses next
  | .letValue _ next => raiseClasses next
  | .mutate _ next => raiseClasses next
  | .allocate _ _ next => raiseClasses next
  | .require _ failure next => failure.classes ++ raiseClasses next
  | .branch _ yes no => raiseClasses yes ++ raiseClasses no
  | .truthBranch _ truthy falsy => raiseClasses truthy ++ raiseClasses falsy
  | .alternatives plans => plans.flatMap raiseClasses
  | .invoke _ next => raiseClasses next
  | .protocolChain candidates fallback =>
    candidates.flatMap raiseClasses ++ raiseClasses fallback
  | .evalChild _ next | .evalChildren _ next => raiseClasses next
  | .returnWith _ | .breakLoop | .continueLoop => []
  | .obligate _ _ next => raiseClasses next
  | .evalBody _ next => raiseClasses next
  | .bindTarget _ _ next => raiseClasses next
  | .deleteTarget _ next => raiseClasses next
  | .allocateSlots _ next | .allocateMapping _ next => raiseClasses next
  | .readName _ next => raiseClasses next
  | .storeName _ _ next | .bindEach _ _ next => raiseClasses next
  | .refineBranch _ truthy falsy => raiseClasses truthy ++ raiseClasses falsy
  | .engine _ => []

private def mutations : Plan -> List Mutation
  | .mutate effect next => effect :: mutations next
  | .normal _ | .stop | .raise _ => []
  | .bind first next => mutations first ++ mutations next
  | .letValue _ next => mutations next
  | .allocate _ _ next => mutations next
  | .require _ _ next => mutations next
  | .branch _ yes no => mutations yes ++ mutations no
  | .truthBranch _ truthy falsy => mutations truthy ++ mutations falsy
  | .alternatives plans => plans.flatMap mutations
  | .invoke _ next => mutations next
  | .protocolChain candidates fallback =>
    candidates.flatMap mutations ++ mutations fallback
  | .evalChild _ next | .evalChildren _ next => mutations next
  | .returnWith _ | .breakLoop | .continueLoop => []
  | .obligate _ _ next => mutations next
  | .evalBody _ next => mutations next
  | .bindTarget _ _ next => mutations next
  | .deleteTarget _ next => mutations next
  | .allocateSlots _ next | .allocateMapping _ next => mutations next
  | .readName _ next => mutations next
  | .storeName _ _ next | .bindEach _ _ next => mutations next
  | .refineBranch _ truthy falsy => mutations truthy ++ mutations falsy
  | .engine _ => []

/-- Condition 1: every admitted builtin method and function has exactly one
    rule, and every rule names an admitted operation. -/
private def inventoryFindings (rules : CompiledRules) : List Finding :=
  let methodTags : List Tag :=
    [.tlist, .tdict, .tset, .ttuple, .trange, .tstr, .tgen]
  let missingMethods := methodTags.flatMap fun tag =>
    (knownMethods tag).filterMap fun name =>
      if (rules.find? (.method tag name)).isSome then none
      else some ⟨"inventory", s!"{tag.render}.{name}", "admitted method has no rule"⟩
  -- `bytes` is reachable through `str.encode` but its method surface is not
  -- modeled: reported as its own condition so the gap is counted rather than
  -- hidden behind the widening fallback.
  let unmodeledSurface := (knownMethods .tbytes).filterMap fun name =>
    if (rules.find? (.method .tbytes name)).isSome then none
    else some ⟨"unmodeled-surface", s!"bytes.{name}",
      "reachable operation widens its result under an external-havoc obligation"⟩
  let missingFunctions := builtinFuncs.filterMap fun name =>
    if (rules.find? (.function name)).isSome then none
    else some ⟨"inventory", name, "admitted builtin function has no rule"⟩
  missingMethods ++ unmodeledSurface ++ missingFunctions

/-- Condition 2: every parameter carries a semantic contract, or the rule
    declares that it is unrestricted. -/
private def contractFindings (rules : CompiledRules) : List Finding :=
  rules.entries.flatMap fun (key, rule) =>
    rule.signature.parameters.filterMap fun parameter =>
      if (rule.contracts.any (·.1 == parameter.name)) then none
      else some ⟨"argument-contract", key.render,
        s!"parameter '{parameter.name}' has no declared contract"⟩

/-- Condition 5: every raised class exists in the exception hierarchy. -/
private def raiseFindings (rules : CompiledRules) : List Finding :=
  rules.entries.flatMap fun (key, rule) =>
    ((raiseClasses rule.body).eraseDups.filterMap fun cls =>
      if builtinExcs.contains cls then none
      else some ⟨"raised-class", key.render,
        s!"{cls} is not in the compiled exception hierarchy"⟩)

/-- Conditions 7 and 8: a rule may not write the legacy non-emptiness marker;
    emptiness travels in the domain component, which the mutation kernel and
    allocation update. -/
private def emptinessFindings (rules : CompiledRules) : List Finding :=
  rules.entries.flatMap fun (key, rule) =>
    (mutations rule.body).filterMap fun effect =>
      match effect with
      | .grow _ _ cell _ | .clear _ _ cell =>
        if !cell.canReach .nonempty then none else
        some ⟨"emptiness-transfer", key.render,
          "writes the legacy nonempty cell instead of the emptiness component"⟩
      | _ => none

/-- ENGINE.md section 2: a store through a selector its target class
    cannot hold reads back as bottom rather than failing, so `CellSelector`
    carries `validFor` and every rule-data store is checked against it here.
    `RuleCompile` checks the same relation when it compiles a store; this
    condition covers the compiled set as a whole, so a rule that reaches the
    database by another route is still checked. -/
private def cellValidityFindings (rules : CompiledRules) : List Finding :=
  rules.entries.flatMap fun (key, rule) =>
    (mutations rule.body).filterMap fun effect =>
      match effect with
      | .grow _ cls cell _ =>
        if cell.validFor cls then none
        else some ⟨"cell-validity", key.render,
          s!"grows {cell.render} on {cls.render}, which cannot hold it"⟩
      | .clear _ cls cell =>
        if cell.validFor cls then none
        else some ⟨"cell-validity", key.render,
          s!"clears {cell.render} on {cls.render}, which cannot hold it"⟩
      | _ => none

/-- An internal signal is raised and consumed inside one transfer, so it can
    never be an outcome of a rule: a rule's raise is its outcome. -/
private def internalOutcomeFindings (rules : CompiledRules) : List Finding :=
  rules.entries.flatMap fun (key, rule) =>
    (internalRaises rule.body).eraseDups.map fun cls =>
      ⟨"internal-escapes", key.render,
        s!"{cls} is raised with internal provenance but is a rule outcome"⟩

/-- Every dunder-dispatched protocol has a declared chain.

    Being data is not the same as being under coverage: `truthChain` and
    `membershipChain` were data while nothing asserted that a *new* protocol would
    have to be declared rather than nested into a transfer by hand. -/
private def dunderChainFindings : List Finding :=
  undeclaredDunderChains.map fun protocol =>
    ⟨"dunder-chain-coverage", protocol.render,
      "protocol has no declared chain, so its dispatch order is sequenced by hand"⟩

/-- The hand-written transfers, listed with their reasons.

    Reported rather than blocking: these are decisions, not defects. The count is
    what matters -- it is the figure the goal's definition of done names, and it
    must not grow without an argument appearing in `transferEngineBodies`. -/
private def transferEngineFindings : List Finding :=
  transferEngineBodies.map fun (name, reason) =>
    ⟨"transfer-engine-body", name, reason⟩

/-- Every (tag, operation) pair has a builtin-outcome row.

    A row that neither admits a normal completion nor raises anything claims the
    operation does nothing at all, which is not an outcome. The rows are
    exhaustive `match`es so this holds by construction; asserting it here means a
    change to the table's shape cannot quietly reintroduce a fall-through, which
    is the defect the table replaced. -/
private def builtinOutcomeFindings : List Finding :=
  missingBuiltinOutcomes.map fun (tag, operation) =>
    ⟨"builtin-outcome-coverage", s!"{tag.render}",
      s!"no outcome for {operation.render} on {tag.render}: the row claims \
         neither a completion nor a raise"⟩

/-- Every (operation, test) pair an operation can encounter has a policy row.

    This is the condition the table exists for. A missing row is not a missing
    message -- `shapeObligation` returns `none`, the `if let` takes no branch, and
    the operation *silently permits* what it should have flagged. That is the
    same failure as a `match` fall-through asserting the wrong outcome, so it is
    caught here at load rather than discovered by a program that happens to hit
    it. -/
private def shapePolicyFindings : List Finding :=
  missingShapePolicies.map fun (operation, test) =>
    ⟨"shape-policy-coverage", s!"{operation.render}",
      s!"no shape policy for {operation.render} against {repr test}, so the \
         operation permits it silently"⟩

/-- Every admitted syntax constructor should have exactly one structural plan
    (ENGINE.md section 3, "Rules and plans"). The kinds are
    derived from `Syntax.lean` exhaustively, so the count cannot drift as
    constructors are added, and a kind drops off it exactly when a plan for it
    enters `Syntax.syntaxRules` -- the number is read from the table rather than
    maintained by hand. -/
private def syntaxFindings : List Finding :=
  (allExprKinds.filter (fun kind =>
      !Syntax.routedExprKinds.contains kind
        && !Syntax.engineExprKinds.contains kind)
    |>.map fun kind =>
      ⟨"unkeyed-syntax", s!"expr.{kind.render}", "dispatched by hand"⟩) ++
  (Syntax.engineExprKinds.map fun kind =>
    ⟨"engine-body", s!"expr.{kind.render}",
      "keyed with a declared engine escape, ENGINE.md section 3"⟩) ++
  (Syntax.engineStmtKinds.map fun kind =>
    ⟨"engine-body", s!"stmt.{kind.render}",
      "keyed with a declared engine escape, ENGINE.md section 3"⟩) ++
  (allTargetKinds.filter (fun kind => !Syntax.routedTargetKinds.contains kind)
    |>.map fun kind =>
      ⟨"unkeyed-syntax", s!"target.{kind.render}", "dispatched by hand"⟩) ++
  (allStmtKinds.filter (fun kind =>
      !Syntax.routedStmtKinds.contains kind
        && !Syntax.engineStmtKinds.contains kind)
    |>.map fun kind =>
      ⟨"unkeyed-syntax", s!"stmt.{kind.render}", "dispatched by hand"⟩) ++
  (allAnnKinds.filter (fun kind => !Syntax.engineAnnKinds.contains kind)
    |>.map fun kind =>
      ⟨"unkeyed-syntax", s!"ann.{kind.render}", "dispatched by hand"⟩) ++
  (Syntax.engineAnnKinds.map fun kind =>
    ⟨"engine-body", s!"ann.{kind.render}",
      "keyed with a declared engine escape: five analyses over the grammar, none of them a flow"⟩)

/-- Condition 12: opaque rules are not a completed semantics. -/
private def opaqueFindings (rules : CompiledRules) : List Finding :=
  rules.entries.filterMap fun (key, rule) =>
    if rule.isOpaque then
      some ⟨"opaque-forbidden", key.render,
        "rule is opaque: valid only in an exploration configuration"⟩
    else none

/-- Conditions the rule language enforces by construction rather than by
    inspection, recorded so the report states why they are not listed. -/
private def structuralConditions : List String :=
  [ "sequenced-effects: the contract prelude runs before the rule body, and \
     a contract without a normal partition suppresses it",
    "failure-outcome: machine raises are produced by executeRaise, which \
     records the raised class and its raise-point state",
    "mutation-discipline: every non-fresh mutation goes through the update \
     kernel, which applies strong or weak targets",
    "hook-state: protocol services return native Flow, so each hook keeps \
     its normal and per-exception post-state",
    "any-fallback: the `any` partition of every contract adds both its \
     normal and its exceptional alternatives",
    "typeddict-write: TypedDict writes go through the dictionary rules, \
     which check declared key, mutability, presence and value annotation" ]

def report (rules : CompiledRules) : Report :=
  { findings :=
      inventoryFindings rules ++ contractFindings rules ++
      raiseFindings rules ++ emptinessFindings rules ++
      cellValidityFindings rules ++
      internalOutcomeFindings rules ++ opaqueFindings rules ++ syntaxFindings ++
      shapePolicyFindings ++ builtinOutcomeFindings ++ transferEngineFindings ++
      dunderChainFindings
    structural := structuralConditions }

def Report.byCondition (report : Report) : List (String × Nat) :=
  report.findings.foldl (fun counts finding =>
    match counts.find? (·.1 == finding.condition) with
    | some _ => counts.map fun (condition, count) =>
        if condition == finding.condition then (condition, count + 1)
        else (condition, count)
    | none => counts ++ [(finding.condition, 1)]) []

/-- Findings that must be empty for a verdict-producing configuration. -/
def Report.blocking (report : Report) : List Finding :=
  report.findings.filter fun finding =>
    finding.condition == "inventory" || finding.condition == "raised-class" ||
      finding.condition == "emptiness-transfer" ||
      finding.condition == "internal-escapes" ||
      finding.condition == "cell-validity"

end Pylate.RuleDriven.Validate
