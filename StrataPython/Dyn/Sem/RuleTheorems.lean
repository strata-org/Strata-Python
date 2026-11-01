/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public meta import StrataDyn.Exec.Table
public import StrataPython.Dyn.Sem.RuleOKProps

set_option autoImplicit false

/-!
# `#py_rule_theorems`

`#py_rule_theorems T for E (effects := eff) (tags := tags) (accounts := A)` states and proves, for
each instruction of the environment `E` that has a rule outside a pure function, three theorems:
* `T.implOK.<instruction>`: the rule satisfies every spec that has the laws (`ImplOK`);
* `T.ok.<instruction>`: its implementation in the table `T` stays within the effect
  `eff "<instruction>"` (`ImplWithin`);
* `T.cert.<instruction>`, only when the accounts are given: the certificate of it at the
  accounts `A` (`Model.OpCertified`, at every position of the table).  `ImplOK.cert` builds it,
  and is stated at Python's table and accounts, so only `PySem` can be given accounts, and they must be `pyAccounts`.

The last two come from the first, which the command proves by taking the rule apart: a rule that
runs a `PyM` computation through `runRule`, `runTotal`, `runRuleFree`, `runTotalFree` or
`runRuleIf`, at an effect no higher than the declared one, is proved by their lemmas.  A rule with
its own lemmas `T.okOf.<instruction>` and `T.certOf.<instruction>` is proved by them.  Any other
rule fails the build.
-/

namespace StrataPython.Dyn.Sem

open Lean Elab Command Term Meta
open Strata.Dyn Strata.Dyn.Exec

public meta section

syntax (name := pyRuleTheorems) "#py_rule_theorems " ident " for " ident
  " (" &"effects" " := " term ")" " (" &"tags" " := " term ")"
  (" (" &"accounts" " := " term ")")? : command

/-- A doc comment with the text `s`. -/
private def mkDoc (s : String) : TSyntax ``Lean.Parser.Command.docComment :=
  ⟨Syntax.node .none ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom s!" {s} -/"]⟩

elab_rules : command
  | `(#py_rule_theorems $tbl for $envId (effects := $eff) (tags := $tags) $[(accounts := $acc?)]?) => do
    let entry ← resolveEnv envId
    let env ← getEnv
    let opsC ← liftCoreM <| resolveGlobalConstNoOverload (mkIdentFrom tbl (tbl.getId ++ `ops))
    let tblNs := opsC.getPrefix
    for o in entry.ops do
      unless o.kind matches .decl do continue
      let some r := findSemRule? env o.fullName | continue
      if r.pure then continue
      let implId := mkIdent (tbl.getId ++ `impl ++ o.envName)
      let implOKId := mkIdent (tbl.getId ++ `implOK ++ o.envName)
      let okId := mkIdent (tbl.getId ++ `ok ++ o.envName)
      let certId := mkIdent (tbl.getId ++ `cert ++ o.envName)
      let ownOk := mkIdent (tbl.getId ++ `okOf ++ o.envName)
      let ownCert := mkIdent (tbl.getId ++ `certOf ++ o.envName)
      let modelId := mkIdent (tbl.getId ++ `model)
      let nameLit := Syntax.mkStrLit (toString o.envName)
      let hasOwn := env.contains (tblNs ++ `okOf ++ o.envName)
      let interpId := mkIdent (tbl.getId ++ `interp)
      -- The model's lemma, which the table's module defines before it runs the command, and the
      -- core's lemmas about accounts.
      let certId' := mkIdent `StrataPython.Dyn.Sem.ImplOK.cert
      let exitNil := mkIdent `Strata.Dyn.Exec.Accounts.exitOK_nil
      let exitCons := mkIdent `Strata.Dyn.Exec.Accounts.exitOK_cons
      let argsNil := mkIdent `Strata.Dyn.Exec.Accounts.argsOK_nil
      let argsCons := mkIdent `Strata.Dyn.Exec.Accounts.argsOK_cons
      let okDoc := mkDoc s!"The rule of `{o.envName}` stays within its declared effect."
      let certDoc := mkDoc s!"The rule of `{o.envName}` reaches only the cells and closures it is \
        given: the certificate of it, at every position of the table."
      let cmds ← if hasOwn then
        let okCmd ← `(command| $okDoc:docComment theorem $okId : ImplWithin $interpId ($eff $nameLit)
            $implId := $ownOk)
        match acc? with
        | some acc => pure #[okCmd, ← `(command| $certDoc:docComment theorem $certId :
            ∀ k, ($modelId).OpCertified $acc k $implId := $ownCert)]
        | none => pure #[okCmd]
      else
        let implDoc := mkDoc s!"The rule of `{o.envName}` satisfies every spec that has the laws, \
          and stays within its declared effect."
        let base := #[← `(command| $implDoc:docComment theorem $implOKId : ImplOK $interpId $tags
            ($eff $nameLit) $implId := by
          intro σ _ _
          letI : Decode σ := ⟨$interpId σ⟩
          intro V hc hX Q hQ
          repeat intro
          first
            | exact RuleOK.lift (of_decide_eq_true rfl) (runRule_ok _ _ hc Q hQ hX _)
            | exact RuleOK.lift (of_decide_eq_true rfl) (runTotal_ok _ _ _ hc Q hQ)
            | exact RuleOK.lift (of_decide_eq_true rfl) (runRuleFree_ok _ _ hc Q hQ hX _)
            | exact RuleOK.lift (of_decide_eq_true rfl) (runTotalFree_ok _ _ _ hc Q hQ)
            | exact RuleOK.lift (of_decide_eq_true rfl) (runRuleIf_ok _ _ _ _ hc Q hQ hX _)),
          ← `(command| $okDoc:docComment theorem $okId : ImplWithin $interpId ($eff $nameLit)
            $implId := ImplOK.within $implOKId)]
        match acc? with
        | none => pure base
        | some acc => pure <| base.push (← `(command| $certDoc:docComment theorem $certId :
            ∀ k, ($modelId).OpCertified $acc k $implId :=
            $certId' $implOKId (by intro _ G _; first | trivial | exact Typing.allValid_nil G)
              (by
                intro _ G
                repeat' first
                  | exact $exitNil $acc G
                  | exact $argsNil $acc G
                  | apply $exitCons $acc G
                  | apply $argsCons $acc G
                  | (intro _; rfl))))
      let msgs := (← get).messages
      withoutModifyingEnv do
        for cmd in cmds do
          elabCommand (← `(command| set_option Elab.async false in $cmd))
      let errors (m : MessageLog) := (m.toList.filter (·.severity == .error)).length
      let failed := errors (← get).messages > errors msgs
      modify fun st => { st with messages := msgs }
      if failed then
        logErrorAt tbl m!"#py_rule_theorems: the rule of {o.envName} is not a `runRule`, \
          `runTotal`, `runRuleFree`, `runTotalFree` or `runRuleIf` wrapper at an effect no higher \
          than its declared one whose results and exits hold no ref, and has no lemmas \
          {tblNs ++ `okOf ++ o.envName} and {tblNs ++ `certOf ++ o.envName}"
      else
        for cmd in cmds do
          elabCommand cmd

/-- `py_op_cert` closes a goal `M.OpCertified A k T.impl.<op>` by the command's certificate
`T.cert.<op>`, when the command made one. -/
elab "py_op_cert" : tactic => Tactic.withMainContext do
  let t ← instantiateMVars (← Tactic.getMainTarget)
  let some o := t.getAppArgs.back? | throwError "py_op_cert: not an operation's certificate"
  let some n := o.getAppFn.constName? | throwError "py_op_cert: the operation is not a constant"
  let comps := n.components.map fun c => if c == `impl then `cert else c
  let c := comps.foldl (fun acc x => acc ++ x) Name.anonymous
  unless (← getEnv).contains c do throwError "py_op_cert: no certificate {c}"
  Tactic.evalTactic (← `(tactic| exact $(mkIdent c) _))

end

end StrataPython.Dyn.Sem
