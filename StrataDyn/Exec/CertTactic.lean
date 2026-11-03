/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Tactic
public meta import StrataDyn.Exec.Rules
public import StrataDyn.Exec.CertModel

set_option autoImplicit false

/-!
# `dyn_cert`: proving a table's certificates

`dyn_cert` proves that an operation of a table is certified (`Model.OpCertified`), or that a
wrapper is `ImplOK`.  It unfolds the wrapper, the rule and its helpers, then takes the goal
apart with `Spec.Sat`'s lemmas (`sat_bind` through a `do` block, `sat_vis` at each request,
`sat_ite` at a branch) and the machine spec's definitions, splitting each `match` and each
`Bool`, until what is left are validity facts about the operands, which the accounts'
definitions decide.

It unfolds:

* the table's wrappers: constants `S.impl.…`, `S.rule.…` and `S.again.…` of a table `S`;
* the registered rules (`@[dyn_sem]`) and every definition in a rule's namespace, so the rules'
  helpers and the world's parts' instances;
* the fields of the languages' classes (`@[dyn_lang]`), which the wrappers build;
* the handles the rules use, from `Exec/Sem.lean`.

`dyn_cert [h₁, …]` adds the simp lemmas `hᵢ`: the definitions of the table's accounts, and any
lemma a rule's certificate needs.  When the recipe leaves a goal, the tactic fails and shows
it: the request, result, exit or world that the recipe could not show valid.

The tactic builds its simp set once and works through the goals one at a time: on each it
introduces the binders, splits the conjunctions among its hypotheses and cases a `Bool` that an
`if` tests, then simplifies the goal and its hypotheses.  When simp makes no progress it cases a
`Bool` or `Option`, splits a `match` or `if`, or splits a conjunction.  It unfolds the rules
and the definitions among the `hᵢ` by reduction, not by their equation lemmas: an account at
a known tag is computed, where the equation lemma of its catch-all case would leave simp side
conditions to discharge.

`#dyn_certs S A [h₁, …]` proves each operation's certificate as its own theorem, `cert.op`, and
assembles them into `cert.ops : S.model.OpsCertified A 0 S.ops.toList`.
-/

namespace Strata.Dyn.Exec

open Lean Elab Tactic Meta

public meta section

/-- The definitions `dyn_cert` unfolds where they occur. -/
private def certUnfoldable (env : Environment) (c : Lean.Name) : Bool := Id.run do
  let some info := env.find? c | return false
  unless info matches .defnInfo _ do return false
  -- a table's definition: a wrapper, a tag or an instance, but not the table itself
  let comps := c.componentsRev
  for i in [1:comps.length + 1] do
    let pre := (comps.drop i).foldr (fun s n => n ++ s) Lean.Name.anonymous
    if env.contains (pre ++ `table) then
      return ![`table, `model, `ops, `index, `typeIndex, `interp, `H, `W, `decode, `w0,
        `typeNames].any (c == pre ++ ·)
  -- a rule, or a definition beside one
  let sems := (semExt.getState env).entries
  let pre := c.getPrefix
  if sems.foldl (init := false) fun b _ r => b || r.decl.getPrefix == pre then return true
  -- a field of a language's class
  if (langExt.getState env).contains pre then return true
  -- an instance of the execution DSL's: the tags of a type constructor's applications and of a
  -- signature
  if isInstanceCore env c && (`Strata.Dyn.Exec).isPrefixOf c then return true
  return false

/-- The `certUnfoldable` constants among `roots`, and those that their definitions name,
transitively. -/
private def certUnfoldClosure (env : Environment) (seen : Std.HashSet Lean.Name)
    (roots : Array Lean.Name) : Std.HashSet Lean.Name := Id.run do
  let mut seen := seen
  let mut todo := roots
  while h : todo.size > 0 do
    let c := todo[todo.size - 1]
    todo := todo.pop
    if seen.contains c || !certUnfoldable env c then continue
    seen := seen.insert c
    if let some v := (env.find? c).bind (·.value?) then
      todo := todo ++ v.getUsedConstants
  return seen

/-- Unfold an application of definition `c` and reduce its `match`es, when its structural
recursion reduces: so an account of a known tag is computed rather than rewritten by the equation
lemmas of its catch-all case, whose side conditions simp would have to discharge. -/
private def certReduce (c : Lean.Name) : Simp.DSimproc := fun e => do
  unless e.isAppOf c do return .continue
  let n ← forallTelescopeReducing (← inferType e) fun xs _ => pure xs.size
  if n == 0 then
    let some e₁ ← withDefault (unfoldDefinition? e) | return .continue
    return .visit (← whnfCore e₁)
  -- a partial application, such as a `flatMap`'s function: reduce its eta-expansion's body
  forallBoundedTelescope (← inferType e) n fun xs _ => do
    let some e₁ ← withDefault (unfoldDefinition? (mkAppN e xs)) | return .continue
    return .visit (← mkLambdaFVars xs (← whnfCore e₁))

/-- Unfold definition `c`: by `certReduce`, added to `s`, or by its equation lemmas, added to
`thms`, if `c` is irreducible, as a definition by well-founded recursion is, or if simp's index
sees through it, as it does through a reducible one. -/
private def certUnfoldAdd (s : Simprocs × SimpTheorems) (c : Lean.Name) :
    MetaM (Simprocs × SimpTheorems) := do
  let info ← getConstInfo c
  let (xs, _, _) ← forallMetaTelescopeReducing info.type
  let keys : Array DiscrTree.Key ←
    DiscrTree.mkPath (mkAppN (mkConst c (info.levelParams.map mkLevelParam)) xs)
  let indexed : Bool := match keys[0]? with
    | some (DiscrTree.Key.const d _) => d == c
    | _ => false
  if !indexed || (← getReducibilityStatus c) matches .irreducible then
    return (s.1, ← s.2.addDeclToUnfold c)
  return (s.1.addCore keys (`Strata.Dyn.Exec.certReduce ++ c) (post := true) (.inr (certReduce c)),
    s.2)

/-- A local of `g` of type `Bool` or `Option _`; with `branching`, only one that an `if`'s
condition names. -/
private def certCaseVar? (g : MVarId) (branching := false) : MetaM (Option FVarId) :=
    g.withContext do
  let t ← instantiateMVars (← g.getType)
  let named (fv : FVarId) : Bool := (t.find? fun e =>
    (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) &&
      (e.getAppArgs[1]?.any (·.containsFVar fv))).isSome
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if branching && !named d.fvarId then continue
    let ty ← whnf (← instantiateMVars d.type)
    if ty.isConstOf ``Bool || ty.isAppOfArity ``Option 1 then return some d.fvarId
  return none

end

/-- The simp lemmas of `dyn_cert`'s decomposition: `Sat`'s, the machine spec's and the handles'
definitions. -/
private meta def certSimpNames : Array Lean.Name := #[
  `Option.getD_none,
  `Option.getD_some,
  `TagOf.tag,
  `SigOf.sig,
  `TagsOf.tags,
  `TagCon.tagOf,
  `TagCon₂.tagOf,
  `TagsOf.head,
  `TagsOf.tail,
  `RunModel.fnOf,
  `RunModel.locOf,
  `Args.ofPayload,
  `Bool.false_eq_true,
  `Bool.true_eq_false,
  `reduceIte,
  `reduceDIte,
  `ite_true,
  `ite_false,
  `Fin.isValue,
  `Accounts.ImplOK,
  `Accounts.FnOK,
  `Accounts.VarOK,
  `Accounts.TreeOK,
  `Accounts.PureOK,
  `Accounts.spec,
  `Accounts.PreOK,
  `Accounts.PostOK,
  `Accounts.ResOK,
  `Accounts.OutOK,
  `Accounts.ExitOK,
  `Accounts.ArgsOK,
  `Accounts.ValOK,
  `Accounts.StOK,
  `Model.OpCertified,
  `OpImpl.fn,
  `OpImpl.shape,
  `Spec.sat_ret,
  `Spec.sat_pure,
  `Spec.sat_jump,
  `Spec.sat_fault,
  `Spec.sat_vis,
  `Spec.sat_choose,
  `Spec.sat_update,
  `Spec.sat_bind,
  `Spec.sat_ite,
  `readRef,
  `newRef,
  `writeRef,
  `modifyRef,
  `runRegion,
  `callFn,
  `bindFn,
  `Strata.Dyn.Exec.jump,
  `semanticGap,
  `semanticFailure,
  `assume,
  `chooseNat,
  `choose,
  `chooseInt,
  `Jump.exit,
  `getThe,
  `modifyThe,
  `modifyGetThe,
  `MonadStateOf.modifyGet,
  `MonadStateOf.get,
  `MonadStateOf.set,
  `Sem.instMonadStateOf,
  `HasHeap.mreq,
  `HasCall.mreq,
  `Region.slot,
  `HasHeap.newReq,
  `HasHeap.newAns,
  `HasHeap.getReq,
  `HasHeap.getAns,
  `HasHeap.setReq,
  `HasHeap.modifyReq,
  `HasCall.callReq,
  `HasCall.callAns,
  `HasCall.bindReq,
  `HasCall.bindAns,
  `Typing.LocValid,
  `Typing.allValid_nil,
  `Typing.allValid_cons,
  `Typing.allValid_append,
  `Typing.allValid_flatMap,
  `Typing.allValid_caps,
  `Typing.allValid_singleton,
  `cast_eq,
  `true_and,
  `and_true,
  `implies_true,
  `and_self]

/-- **Prove an operation's certificate** (`Model.OpCertified`, or `Accounts.ImplOK`) by
unfolding its wrapper and rule and decomposing the goal with `Spec.Sat`'s lemmas.
`dyn_cert [h₁, …]` adds simp lemmas, such as the table's accounts' definitions.  Fails, showing
the goals left, if the recipe does not close them. -/
syntax "dyn_cert" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

elab_rules : tactic
  | `(tactic| dyn_cert $[[$hs,*]]?) => do
    let hs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := (hs.map (·.getElems)).getD #[]
    let env ← getEnv
    let target ← instantiateMVars (← getMainTarget)
    let names := certSimpNames.filterMap fun n =>
      if env.contains n then some n else [`Strata.Dyn.Exec ++ n].find? env.contains
    let all := hs ++ (← names.mapM fun c => `(Lean.Parser.Tactic.simpLemma| $(mkIdent c):ident))
    -- The definitions among `hs` are unfolded as `certUnfoldable` constants are; the other `hs`
    -- are simp lemmas.
    let mut defs : Array Lean.Name := #[]
    let mut lemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
    for h in hs do
      if let `(Lean.Parser.Tactic.simpLemma| $id:ident) := h then
        if let some c ← (try some <$> realizeGlobalConstNoOverload id catch _ => pure none) then
          if !(← isProp (← getConstInfo c).type) then
            defs := defs.push c
            continue
      lemmas := lemmas.push h
    let r ← mkSimpContext (eraseLocal := false) (← `(tactic|
      simp (config := { zeta := true, failIfUnchanged := false }) only [$lemmas,*]))
    let mut baseProcs := r.simprocs
    let mut base : SimpTheorems := {}
    for n in names do
      if ← Simp.isSimproc n then baseProcs ← baseProcs.add n (post := true)
      else if ← isProp (← getConstInfo n).type then base ← base.addConst n
      else base ← base.addDeclToUnfold n
    let consts (g : MVarId) : MetaM (Array Lean.Name) := do
      return (← instantiateMVars (← g.getType)).getUsedConstants
    let mut unf := certUnfoldClosure env {} (← consts (← getMainGoal))
    -- what unfolds the `hᵢ` that are definitions, and the constants `certUnfoldable` reaches
    let mut extra ← (defs ++ unf.toArray).foldlM (init := ({}, base)) fun s c => certUnfoldAdd s c
    let ctxOf (thms : SimpTheorems) : Simp.Context :=
      r.ctx.setSimpTheorems (r.ctx.simpTheorems.push thms)
    let mut ctx := ctxOf extra.2
    let mut simprocs := baseProcs.push extra.1
    let mut todo := (← getGoals).toArray.reverse
    let mut left := #[]
    let mut fuel := 10000
    while h : todo.size > 0 do
      let g := todo[todo.size - 1]
      todo := todo.pop
      if ← g.isAssigned then continue
      if fuel == 0 then
        left := left.push g
        continue
      fuel := fuel - 1
      let (_, g) ← g.intros
      let g ← g.casesAnd
      if let some fv ← certCaseVar? g (branching := true) then
        todo := todo ++ ((← g.cases fv).map (·.mvarId)).reverse
        continue
      let hyps ← g.getNondepPropHyps
      let (res, _) ← g.withContext <| simpGoal g ctx simprocs (fvarIdsToSimp := hyps)
      let some (_, g₁) := res | continue
      if g₁ != g then
        todo := todo.push g₁
        continue
      let cs := (← consts g).filter fun c => !unf.contains c && certUnfoldable env c
      unless cs.isEmpty do
        let unf₁ := certUnfoldClosure env unf cs
        extra ← unf₁.foldM (init := extra) fun s c =>
          if unf.contains c then pure s else certUnfoldAdd s c
        unf := unf₁
        ctx := ctxOf extra.2
        simprocs := baseProcs.push extra.1
        todo := todo.push g
        continue
      if let some fv ← certCaseVar? g then
        todo := todo ++ ((← g.cases fv).map (·.mvarId)).reverse
        continue
      if let some gs ← splitTarget? g then
        todo := todo ++ gs.toArray.reverse
        continue
      if (← whnfR (← instantiateMVars (← g.getType))).isAppOfArity ``And 2 then
        todo := todo ++ (← g.apply (← mkConstWithFreshMVarLevels ``And.intro)).toArray.reverse
        continue
      left := left.push g
    setGoals left.toList
    evalTactic (← `(tactic| all_goals try (first
      | assumption | trivial | rfl
      | solve_by_elim (maxDepth := 8) [Typing.Valid.mono, Typing.CapValid.mono,
          Typing.AllValid.mono, Typing.Extends.trans, Typing.Extends.refl,
          Typing.capValid_of_allValid]
      | (simp_all [$all,*]; done)
      | (simp_all [Typing.AllValid, List.mem_flatMap, $all,*]; done))))
    let stuck ← getGoals
    unless stuck.isEmpty do
      let shown ← stuck.mapM fun g => do return m!"{g}"
      throwError m!"dyn_cert: {stuck.length} goal(s) left proving{indentExpr target}\n{
        ""}each a request, result, exit or world that the recipe could not show valid:{
        indentD (MessageData.joinSep shown "\n\n")}"

/-- **Certify a table one operation at a time**: `#dyn_certs S A [h₁, …]` proves, for each
operation of table `S` at position `k`, a theorem `cert.op : S.model.OpCertified A k S.impl.op`
by `dyn_cert [h₁, …]`, each its own declaration, and then `cert.ops`, that the operations of
`S.ops` are certified (`Model.OpsCertified`), from them.  `Model.certified_of_ops cert.ops` is
then `S.model.Certified A`.  An operation whose `cert.op` is already declared, as by a proof
written before the command, is not proved again. -/
syntax (name := dynCerts) "#dyn_certs " ident ppSpace term:max
  (" [" Lean.Parser.Tactic.simpLemma,* "]")? : command

open Command in
/-- The operations of table `ops`, by position: each's wrapper constant. -/
private meta def certOpsOf (ops : Lean.Name) : MetaM (Array Lean.Name) := do
  let mut e ← whnf (← mkAppM ``Array.toList #[mkConst ops])
  let mut out := #[]
  repeat
    let_expr List.cons _ hd tl := e | break
    let p ← whnf hd
    let some c := (p.getAppArgs[3]?).bind (·.constName?) |
      throwError "#dyn_certs: entry {out.size} of `{ops}` is not a constant wrapper: {p}"
    out := out.push c
    e ← whnf tl
  return out

open Command in
@[command_elab dynCerts] public meta def elabDynCerts : CommandElab
  | `(#dyn_certs $s:ident $a:term $[[$hs,*]]?) => do
    let hs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := (hs.map (·.getElems)).getD #[]
    let ops ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo (mkIdentFrom s (s.getId ++ `ops))
    let tbl := ops.getPrefix
    let impls ← liftTermElabM <| certOpsOf ops
    let ns ← getCurrNamespace
    let doc (str : String) : TSyntax ``Lean.Parser.Command.docComment :=
      ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (" " ++ str ++ " -/")]⟩
    let model := mkIdent (tbl ++ `model)
    let mut certs : Array Term := #[]
    for h : k in [0:impls.size] do
      let c := impls[k]
      let op := c.replacePrefix (tbl ++ `impl) .anonymous
      let thm := `cert ++ op
      certs := certs.push (mkIdent thm)
      if (← getEnv).contains (ns ++ thm) then continue
      elabCommand (← `(command|
        $(doc s!"Operation `{op}` of `{s.getId}` is certified (`#dyn_certs`)."):docComment
        theorem $(mkIdent thm) :
            $(mkIdent ``Model.OpCertified) $model $a $(quote k) $(mkIdent c) := by
          dyn_cert [$hs,*]))
    elabCommand (← `(command|
      $(doc s!"The operations of `{s.getId}` are certified, one by one (`#dyn_certs`)."):docComment
      theorem $(mkIdent `cert.ops) :
          $(mkIdent ``Model.OpsCertified) $model $a 0 $(mkIdent ops).toList :=
        ⟨$(certs.push (← `(trivial))),*⟩))
  | _ => throwUnsupportedSyntax

end Strata.Dyn.Exec
