/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public meta import Lean.Meta.Tactic.Delta
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
`runRuleIf`, or that loops through `runLoop` or `runLoopFree` (both its first and its later
activations), at an effect no higher than the declared one, with no handles or with the
`regionHandle`s of regions whose parameters hold no ref (`py_handles_ok`), is proved by their
lemmas.  A rule with its own lemmas `T.okOf.<instruction>` and `T.certOf.<instruction>` is proved by them.  Any other
rule fails the build.
-/

namespace StrataPython.Dyn.Sem

open Lean Elab Command Term Meta
open Strata.Dyn Strata.Dyn.Exec

public meta section

/-- `py_handles_ok` closes a goal `∀ s, HandlesOK V s hs`, for a rule's handles `hs` given as an
array literal of `regionHandle`s of the operation's regions whose parameters hold no ref
(`treeOK_handle`), with `hc` the laws. -/
macro "py_handles_ok " hc:term : tactic => `(tactic| (
  intro s
  first
    | exact handlesOK_nil s
    | refine handlesOK_toArray s _ ?_
      repeat' first
        | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
        | exact List.forall_mem_nil _
        | exact fun args e => treeOK_handle $hc _ _ _
            (fun _ => ⟨_, _, rfl, of_decide_eq_true rfl⟩) s args e))

/-- `py_lift_ok hc t` closes a rule's goal by the lemma `t`, raised to the declared effect, and
the handles goal that `t` leaves by `py_handles_ok hc`. -/
macro "py_lift_ok " hc:term:max t:term:max : tactic =>
  `(tactic| (refine RuleOK.lift (of_decide_eq_true rfl) $t; py_handles_ok $hc))

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
            | py_lift_ok hc (runRule_ok _ _ hc Q hQ hX _ _ ?_)
            | py_lift_ok hc (runTotal_ok _ _ _ hc Q hQ _ ?_)
            | py_lift_ok hc (runRuleFree_ok _ _ hc Q hQ hX _ _ ?_)
            | py_lift_ok hc (runTotalFree_ok _ _ _ hc Q hQ _ ?_)
            | py_lift_ok hc (runRuleIf_ok _ _ _ _ hc Q hQ hX _ _ ?_)
            | refine ⟨?_, ?_⟩ <;> (repeat intro) <;> first
                | py_lift_ok hc (runLoop_ok _ _ hc Q hQ hX _ _ _ _ ?_)
                | py_lift_ok hc (runLoopFree_ok _ _ hc Q hQ hX _ _ _ _ ?_)),
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
          `runTotal`, `runRuleFree`, `runTotalFree`, `runRuleIf`, `runLoop` or `runLoopFree` \
          wrapper at an effect no higher than its declared one, whose results and exits hold no ref \
          and whose handles are `regionHandle`s of regions whose parameters hold no ref, and has no \
          lemmas {tblNs ++ `okOf ++ o.envName} and {tblNs ++ `certOf ++ o.envName}"
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

/-- The wrappers that run a rule's `PyM` computation. -/
def pyRunners : List Lean.Name :=
  [``runRule, ``runTotal, ``runRuleFree, ``runTotalFree, ``runRuleIf, ``runLoop, ``runLoopFree]

/-- The constants of the rule monad's level and of the world: code that names one of them, after
its abbreviations are unfolded, works below the record. -/
def pyMonadConsts : List Lean.Name :=
  [``PyM, ``PyLang, ``StrataPython.Dyn.Sem.World, ``Strata.Dyn.Exec.Sem, ``Depth]

/-- The record's classes: the only classes a generic definition that a rule runs may take. -/
def pyRecordClasses : List Lean.Name :=
  [``PyPure, ``PyNew, ``PyReads, ``PyCalls, ``PyWrites, ``PyMachines, ``HasLoopPart]

/-- The record's instances at `PyM`: the only instances a rule may hand to a generic definition,
with the projections from a record class to its parent. -/
def pyRecordInstances : List Lean.Name :=
  [`StrataPython.Dyn.Sem.instPyPurePyMValue, `StrataPython.Dyn.Sem.instPyReadsPyMValueOfAtLeastReads,
    `StrataPython.Dyn.Sem.instPyCallsPyMCallsValue, `StrataPython.Dyn.Sem.instPyWritesPyMWritesValue,
    `StrataPython.Dyn.Sem.instPyNewPyMFalseValue, `StrataPython.Dyn.Sem.instPyNewPyMWritesTrueValue,
    `StrataPython.Dyn.Sem.instPyMachinesPyMWritesTrueValuePyLoopState,
    `StrataPython.Dyn.Sem.instHasLoopPartPyLoopStateOpsLoopState]

/-- `e` with every reducible definition unfolded, so that an abbreviation can't hide what it
stands for. -/
def pyUnfold (e : Expr) : MetaM Expr := do
  let env ← getEnv
  deltaExpand e fun n => getReducibilityStatusCore env n == .reducible

/-- Whether `a` works at the rule monad's level: its type, or a constant that it names or that
constant's type, names a constant of `pyMonadConsts`, abbreviations unfolded. -/
def pyAtMonad (a : Expr) : MetaM Bool := do
  let env ← getEnv
  let names (e : Expr) : MetaM Bool :=
    return (← pyUnfold e).getUsedConstants.any pyMonadConsts.contains
  if ← names (← inferType a) then return true
  for c in (← pyUnfold a).getUsedConstants do
    if pyMonadConsts.contains c then return true
    if let some ci := env.find? c then
      if ← names ci.type then return true
  return false

/-- Why the instance argument `a` is not built from the record's instances alone: its head is an
instance of `pyRecordInstances`, a projection from a record class to its parent, or an instance
that the rule takes; each class-valued argument other than a proof is again such an instance; and
every other argument is a proof, a type former, or doesn't work at the rule monad's level (`pyAtMonad`).  `none` when it
is. -/
partial def pyInstanceWhy (a : Expr) : MetaM (Option MessageData) := do
  let a := a.consumeMData
  -- An instance that the rule itself takes, such as its `[Store σ]`.
  if a.isFVar then return none
  let env ← getEnv
  let ok : Bool := match a.getAppFn.constName? with
    | some c => pyRecordInstances.contains c ||
        (env.getProjectionFnInfo? c).any fun info =>
          info.fromClass && pyRecordClasses.contains info.ctorName.getPrefix
    | none => false
  unless ok do
    return some (← addMessageContext m!"an instance argument is not one of the record's: {a}")
  for x in a.getAppArgs do
    -- A proof, such as the instance's `Level.AtLeast`, computes nothing.
    if ← isProof x then continue
    if (← isClass? (← inferType x)).isSome then
      if let some why ← pyInstanceWhy x then return some why
    else unless ← isTypeFormer x do
      if ← pyAtMonad x then
        return some (← addMessageContext m!"an argument of the instance {a} works at the rule \
          monad: {x}")
  return none

/-- Why the computation `c` of a rule is not an application of a definition that is generic in its
monad, at `PyM`: the definition takes a monad `m`, its type names no constant of `pyMonadConsts`,
`m` is `PyM`, each instance binder is of a record class (`pyRecordClasses`) and gets a record
instance (`pyInstanceWhy`), no other binder's type mentions `m`, no other argument works at the
rule monad's level (`pyAtMonad`), and its result is in `m`.  `none` when it is. -/
def pyGenericWhy (c : Expr) : MetaM (Option MessageData) := do
  let some g := c.getAppFn.constName? | return some m!"its computation is not a constant applied"
  let some gi := (← getEnv).find? g | return some m!"{.ofConstName g} is unknown"
  if (← pyUnfold gi.type).getUsedConstants.any pyMonadConsts.contains then
    return some m!"{.ofConstName g}'s type names the rule monad"
  let args := c.getAppArgs
  forallBoundedTelescope gi.type args.size fun xs body => do
    let mut mIdx : Option Nat := none
    for i in [0:xs.size] do
      let t ← inferType xs[i]!
      if t.isArrow && t.bindingDomain!.isSort && t.bindingBody!.isSort then mIdx := some i; break
    let some mi := mIdx | return some m!"{.ofConstName g} takes no monad"
    unless args[mi]?.any (·.isAppOf ``PyM) do
      return some m!"{.ofConstName g}'s monad is not PyM"
    let mv := xs[mi]!.fvarId!
    for i in [0:args.size] do
      if i == mi then continue
      let a := args[i]!
      let t ← inferType xs[i]!
      if (← xs[i]!.fvarId!.getBinderInfo).isInstImplicit then
        unless t.getAppFn.constName?.any pyRecordClasses.contains do
          return some (← addMessageContext m!"{.ofConstName g} takes an instance of a class outside \
            the record: {t}")
        if let some why ← pyInstanceWhy a then return some m!"{.ofConstName g}: {why}"
      else if t.containsFVar mv then
        return some (← addMessageContext m!"{.ofConstName g} takes an argument in its monad: {t}")
      else if ← pyAtMonad a then
        return some (← addMessageContext m!"an argument of {.ofConstName g} works at the rule \
          monad: {a}")
    -- The result is in `m`, after the arguments that the runner gives (a loop's state).
    forallTelescopeReducing body fun ys res => do
      for y in ys do
        if (← inferType y).containsFVar mv then
          return some m!"{.ofConstName g} takes an argument in its monad after those it is given"
      unless (← whnf res).getAppFn.isFVarOf mv do
        return some (← addMessageContext m!"{.ofConstName g}'s result is not in its monad: {res}")
      return none

/-- Whether `e` is a handle of one of the rule's own regions: `regionHandle r inp out`, written
out, for a region `r` that is a variable of the rule (its type is a `Region`, by `regionHandle`'s
signature), with `inp` and `out` that don't work at the rule monad (`pyAtMonad`).  A rule's
variables of type `Region` are its operation's regions: the table's wrapper applies a rule to one
`Region.slot` per region of its instruction, and to no other value of that type.  A handle that the rule makes itself, such as
`fun _ => pure …`, or one given by a definition, is not. -/
def pyOwnHandle (e : Expr) : MetaM Bool := do
  let e := e.consumeMData
  unless e.isAppOf ``regionHandle do return false
  let args := e.getAppArgs
  let some r := args[4]? | return false
  let r := r.consumeMData
  unless args.size == 7 && r.isFVar do return false
  return !(← pyAtMonad args[5]!) && !(← pyAtMonad args[6]!)

/-- The elements of the array literal `a` (`#[x, …]`), if it is one. -/
def pyArrayLit? (a : Expr) : Option (List Expr) := do
  guard (a.isAppOf ``List.toArray)
  let rec go (l : Expr) (fuel : Nat) : Option (List Expr) := match fuel with
    | 0 => none
    | n + 1 =>
      let l := l.consumeMData
      if l.isAppOf ``List.nil then some []
      else if l.isAppOfArity ``List.cons 3 then (l.getArg! 1 :: ·) <$> go (l.getArg! 2) n
      else none
  go a.appArg! 1000

/-- Why the rule `decl` is not a `pyRunners` wrapper whose computations are generic in their
monad (`pyGenericWhy`), whose handles are `#[]`, the operation's own, or handles of the rule's own
regions (`pyOwnHandle`), and whose other arguments are the
rule's own operands and targets, literals, or terms that don't work at the rule monad's level
(`pyAtMonad`).  `none` when it is. -/
def pyRuleShapeWhy (decl : Lean.Name) : MetaM (Option MessageData) := do
  let some (.defnInfo d) := (← getEnv).find? decl | return some m!"it is not a definition"
  lambdaTelescope d.value fun _ b => do
    let b := b.consumeMData
    let some h := b.getAppFn.constName? | return some m!"its body is not a constant applied"
    unless pyRunners.contains h do return some m!"its body is {.ofConstName h}, not a runner"
    let some hi := (← getEnv).find? h | return some m!"{.ofConstName h} is unknown"
    let args := b.getAppArgs
    forallBoundedTelescope hi.type args.size fun xs _ => do
      for i in [0:args.size] do
        let a := args[i]!.consumeMData
        let t ← inferType xs[i]!
        let empty := (a.isAppOf ``List.toArray && a.appArg!.isAppOf ``List.nil) ||
          a.isAppOf ``Array.mkEmpty || a.isAppOf ``Array.empty
        if t.getUsedConstants.contains ``PyM then
          if let some why ← pyGenericWhy a then return some why
        else if t.isAppOf ``Handles then
          -- The operation's own handles, none, or an array literal of handles of its regions.
          let own ← match pyArrayLit? a with
            | some es => es.allM fun e => pyOwnHandle e
            | none => pure false
          unless a.isFVar || empty || own do
            return some (← addMessageContext m!"its regions are not the operation's own: {a}")
        else unless a.isFVar || a.isLit || empty do
          if ← pyAtMonad a then
            return some (← addMessageContext m!"an argument of {.ofConstName h} works at the \
              rule monad: {a}")
      return none

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
world.  With `(below := [b₁, …])`, it also lists the definitions that it reaches outside the core
(`StrataDyn`), the trusted names, the table's own wrappers and the rules that `#py_rule_shapes`
accepts, that name one of the `bᵢ` or a constant whose type does, with abbreviations unfolded: the
code below the rule monad, which this walk alone checks. -/
syntax (name := pyPartWriters) "#py_part_writers " ident " (" &"lang" " := " ident ")"
  " (" &"forbidden" " := " "[" ident,* "]" ")" " (" &"trusted" " := " "[" ident,* "]" ")"
  (" (" &"below" " := " "[" ident,* "]" ")")? : command

elab_rules : command
  | `(#py_part_writers $tbl (lang := $lang) (forbidden := [$fs,*]) (trusted := [$ts,*])
      $[(below := [$bs?,*])]?) => do
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
    -- The definitions below the rule monad that the walk decides for, outside the core.
    if let some bs := bs? then
      let below ← bs.getElems.mapM res
      let names := Lean.Name.anonymous :: below.toList
      let core (n : Lean.Name) : Bool := match env.getModuleIdxFor? n with
        | some i => [`StrataDyn, `StrataDynTest].contains (env.header.moduleNames[i.toNat]!).getRoot
        | none => false
      let emitted : Lean.NameSet := (tableExt.getState env).foldl (init := {}) fun acc t =>
        if t.emitted.contains ops then t.emitted.foldl (·.insert ·) acc else acc
      let mut found : Array Lean.Name := #[]
      for n in seen.toList do
        if trusted.contains n || core n || !ours n then continue
        -- The table's own wrappers, which apply the rules: the declarations that its command emitted.
        if n == ops || emitted.contains n then continue
        let some (.defnInfo d) := env.find? n | continue
        -- As `pyAtMonad` decides it, with the abbreviations unfolded.
        let unfold (e : Expr) : CommandElabM (Array Lean.Name) :=
          return (← liftTermElabM (pyUnfold e)).getUsedConstants
        let cs := (← unfold d.value) ++ (← unfold d.type)
        let mut isBelow := false
        for c in cs do
          if names.contains c then isBelow := true; break
          if let some ci := env.find? c then
            if (← unfold ci.type).any names.contains then isBelow := true; break
        unless isBelow do continue
        if (semExt.getState env).entries.toList.any (·.2.decl == n) then
          if (← liftTermElabM (pyRuleShapeWhy n)).isNone then continue
        found := found.push (privateToUserName n)
      let sorted := found.qsort (·.toString < ·.toString)
      logInfo m!"#py_part_writers: {privateToUserName ops} reaches {sorted.size} definitions below the rule monad, \
        which name {", ".intercalate (below.toList.map toString)} or a constant whose type does:\n\
        {"\n".intercalate (sorted.toList.map toString)}"


syntax (name := pyRuleShapes) "#py_rule_shapes " ident " (" &"exceptions" " := " "[" ident,* "]" ")" :
  command

/-- `#py_rule_shapes E (exceptions := [op₁, …])` fails unless the rule of every instruction of the
environment `E` outside a pure function, other than the named exceptions, runs through a wrapper of
`pyRunners` a definition that is generic in its monad, applied at `PyM`, with the record's
instances alone (`pyRuleShapeWhy`).  Lean has no theorem that such a definition reaches `PyM` only
through those instances: that rests on the elaborator and on this check, and is trusted.  It also
fails at an exception whose rule has that shape, so that the list names only the rules that
don't. -/
elab_rules : command
  | `(#py_rule_shapes $envId (exceptions := [$xs,*])) => do
    let entry ← resolveEnv envId
    let env ← getEnv
    let exc := xs.getElems.map (·.getId)
    for x in exc do
      unless entry.ops.any (·.envName == x) do
        throwErrorAt envId m!"#py_rule_shapes: {x} is not an instruction of {envId.getId}"
    for o in entry.ops do
      unless o.kind matches .decl do continue
      let some r := findSemRule? env o.fullName | continue
      if r.pure then continue
      let why ← liftTermElabM <| pyRuleShapeWhy r.decl
      match why, exc.contains o.envName with
      | some w, false => logErrorAt envId m!"#py_rule_shapes: the rule of {o.envName} \
          ({.ofConstName r.decl}) is not a runner of a definition generic in its monad: {w}"
      | none, true => logErrorAt envId m!"#py_rule_shapes: the rule of {o.envName} is listed as \
          an exception, but it runs a definition generic in its monad"
      | _, _ => pure ()

end

end StrataPython.Dyn.Sem
