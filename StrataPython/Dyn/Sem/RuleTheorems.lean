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

/-- The first constant of `forbidden` that `e` names, or a projection in `projs` (a structure and a
field index) that it makes, other than as the head of an operand of the constructor `mk` of a
language's class, itself or by `inferInstance` (a table's instance of the class at the world, which
hands the part to the rule); that operand's arguments are walked. -/
partial def findForbidden (mk : Lean.Name) (forbidden : Array Lean.Name) (projs : Array (Lean.Name × Nat))
    (e : Expr) : Option Lean.Name :=
  let go := findForbidden mk forbidden projs
  match e with
  | .const c _ => if forbidden.contains c then some c else none
  | .app .. =>
    if e.getAppFn.constName? == some mk then
      e.getAppArgs.findSome? fun a =>
        -- The part's instance itself, or `inferInstance` of it.
        let inst := if a.isAppOf ``inferInstance then a.getAppArgs.back? else some a
        -- The instance's own arguments (its types and instances) are walked too.
        match inst with
        | some i => if i.getAppFn.constName?.any forbidden.contains then i.getAppArgs.findSome? go else go a
        | none => go a
    else go e.getAppFn <|> e.getAppArgs.findSome? go
  | .lam _ t b _ | .forallE _ t b _ => go t <|> go b
  | .letE _ t v b _ => go t <|> go v <|> go b
  | .proj s i b => if projs.contains (s, i) then some (s ++ `proj) else go b
  | .mdata _ b => go b
  | _ => none

/-- The libraries of this package, whose definitions `#py_part_writers` walks. -/
def partWritersRoots : List Lean.Name :=
  [`StrataDyn, `StrataDynTest, `StrataPython, `StrataPythonTest, `StrataPythonTestExtra, `Pylate,
    `PylateTests]

/-- `#py_part_writers T (lang := L) (forbidden := [c₁, …]) (trusted := [t₁, …])` fails unless no
definition that the operations of the table `T` reach names a forbidden constant (a guarded part's
instance, the class field that hands it to a rule, or the world's constructor) outside the trusted
names, other than as an operand of `L.mk`, the table's instance of the language's class.  A forbidden
field also forbids the other ways to take it out of its structure: the structure's `casesOn`, `rec`
and `recOn` (which a `match` or a pattern compiles to), and a raw projection of that field.  The
walk starts at `T.ops`, takes every definition of a module of this package (`partWritersRoots`),
private and auxiliary ones included, and never enters a trusted name.  It fails at a definition of
this package whose code proofs don't see (an `opaque`, `partial` or `noncomputable` definition, or
one with `@[implemented_by]` or `@[extern]`) and at an axiom of this package that isn't a proof, so that a write can't
hide in one.  Theorems and the definitions of other packages are not walked: they can't name the
world. -/
syntax (name := pyPartWriters) "#py_part_writers " ident " (" &"lang" " := " ident ")"
  " (" &"forbidden" " := " "[" ident,* "]" ")" " (" &"trusted" " := " "[" ident,* "]" ")" : command

elab_rules : command
  | `(#py_part_writers $tbl (lang := $lang) (forbidden := [$fs,*]) (trusted := [$ts,*])) => do
    let res (i : Ident) : CommandElabM Lean.Name := liftCoreM <| realizeGlobalConstNoOverload i
    let mk := (← res lang) ++ `mk
    let mut forbidden ← fs.getElems.mapM res
    let trusted ← ts.getElems.mapM res
    let ops ← res (mkIdentFrom tbl (tbl.getId.eraseMacroScopes ++ `ops))
    let env ← getEnv
    -- A forbidden field: its structure's eliminators, and its raw projection.
    let mut projs : Array (Lean.Name × Nat) := #[]
    for f in forbidden do
      if let some info := env.getProjectionFnInfo? f then
        let s := info.ctorName.getPrefix
        projs := projs.push (s, info.i)
        for elim in [`casesOn, `rec, `recOn] do
          if env.contains (s ++ elim) then forbidden := forbidden.push (s ++ elim)
    let ours (n : Lean.Name) : Bool := match env.getModuleIdxFor? n with
      | some i => partWritersRoots.contains (env.header.moduleNames[i.toNat]!).getRoot
      | none => true
    let mut parent : Lean.NameMap Lean.Name := {}
    let mut seen : Lean.NameSet := {}
    let mut todo : Array Lean.Name := #[ops]
    let pathTo (parent : Lean.NameMap Lean.Name) (n : Lean.Name) : String := Id.run do
      let mut path := [n]
      let mut cur := n
      for _ in [0:parent.size] do
        match parent.find? cur with
        | some p => path := p :: path; cur := p
        | none => break
      return " → ".intercalate (path.map toString)
    while h : todo.size > 0 do
      let n := todo[todo.size - 1]
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      if trusted.contains n then continue
      if (Lean.Compiler.getImplementedBy? env n).isSome || Lean.isExtern env n ||
          Lean.isNoncomputable env n then
        throwError m!"#py_part_writers: {.ofConstName ops} reaches {.ofConstName n} ({pathTo parent n}), \
          whose compiled code is other code than its definition, or which has none"
      match env.find? n with
      | some (.defnInfo d) =>
        if let some c := findForbidden mk forbidden projs d.value then
          throwError m!"#py_part_writers: {.ofConstName ops} reaches {.ofConstName n} ({pathTo parent n}), \
            which names {.ofConstName c} outside the trusted primitives"
        for c in d.value.getUsedConstants do
          if ours c && !seen.contains c then
            unless parent.contains c do parent := parent.insert c n
            todo := todo.push c
      | some (.opaqueInfo _) =>
        throwError m!"#py_part_writers: {.ofConstName ops} reaches {.ofConstName n} ({pathTo parent n}), \
          an opaque or partial definition whose code proofs don't see"
      | some (.axiomInfo a) =>
        -- An imported proof whose body isn't exposed is an axiom too; only data counts.
        if ours n && !(← liftTermElabM (Meta.isProp a.type)) then
          throwError m!"#py_part_writers: {.ofConstName ops} reaches {.ofConstName n} ({pathTo parent n}), \
            an axiom of this package"
      | _ => pure ()

end

end StrataPython.Dyn.Sem
