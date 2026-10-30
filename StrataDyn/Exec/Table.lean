/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public meta import StrataDyn.DSL.Elab
public meta import StrataDyn.Exec.Rules
meta import StrataDyn.Name
meta import StrataDyn.Util.NatTree23
public import StrataDyn.Exec.Sem

set_option autoImplicit false

/-!
# Semantic rules: coverage and the table

* `#dyn_coverage E` reports each type and instruction `E` declares, with its rule,
  `derived`, the engine's, or `missing`, and counts its ancestors' missing rules.
  `#dyn_coverage E (complete)` reports nothing, and is an error naming what is missing
  unless every type and instruction of `E` and its ancestors is covered.
* `#dyn_sem_table S for E` emits, in namespace `S`, the decoding of tags, the tags, one
  wrapper per instruction of `E` and its ancestors that has a rule or is derived, and the
  table:
  * `S.typeNames`, a name for each head, and `S.H σ`, each head's Lean type constructor at the
    token `σ`;
  * `S.interp : Interp`, `Ty.decode σ (S.H σ)` at each token `σ`, and `S.W : World`, the world
    at each token;
  * `S.T.n`, the tag of the type `n`, a function of its parameters' tags: `S.T.base.Int`.
    Types with one Lean type have one tag: under `@[dyn_type Hd.Meters] Int`,
    `S.T.hd.Meters` is `S.T.base.Int`;
  * `S.decode`, the decoding, not reducible, and at `Decode.mk (S.decode σ)` the tag of each
    Lean type as an instance: a `TagOf σ` of a type, a `TagCon σ` or `TagCon₂ σ` of a type
    constructor of one or two parameters, such as `Except`, the `TagCon σ` of `Ref σ`, and a
    closure's `TagOf σ (FnRef σ as r)` from its signature's `SigOf σ as r`.  A run's arguments
    and results find their tags through them (`Model.arg`, `Model.read?`);
  * `S.rule.o`, the wrapper of instruction `o`: `S.rule.py.add`, `S.rule.base.Except.case`,
    and, if `o`'s rule loops, `S.again.o`, its wrapper with a state;
  * `S.ops`, each wrapper as an `OpImpl` by environment name, and `S.table`;
  * `S.model`, if `E` extends `Base`: the table with what the engine needs of the base, which
    is what a module runs against.

  `(world := W)` makes `W` the world: a Lean type, the same at every token, or a function
  `(σ : Type) → [Store σ] → Type`, for a world that holds refs.  Each `W σ` is inhabited, and
  each rule's `HasPart` instances are found at it.  It defaults to `Unit`.  The definitions are
  public and exposed in a public scope, and private otherwise.

  Every type needs a rule but `base.Ref` and `base.Fn`, which the engine interprets: a
  primitive or opaque type's by `@[dyn_type]`, a datatype's by `#dyn_types`.  An
  instruction without one is reported and left out of the table.  `#dyn_sem_table S for E (trace := true)`, or
  `set_option dyn.semTable.trace true`, logs each definition it emits.

  The table checks each rule, and each datatype's type rule, again at its own type rules: the
  module of a rule may have seen another type rule, through an import that the table's module
  does not see.

Both commands, and `#dyn_types`, fail if two imported modules register a rule, or a type rule,
for one type or instruction of `E` or its ancestors, and name both declarations
(`checkNoDuplicates`).

**Heads.**  Heads `0` and `1` are a ref's and a code pointer's.  The table numbers each Lean
type constructor its types' rules give, up to reducible unfolding, from `2`, in the order of the
types, so Dyn types with one Lean type have one head.

A wrapper takes the token `σ`, the tags of the instruction's type arguments, then one operand
per argument at its own type at `σ`, then the variadic operands as an array.  A spread over the
list variable `cs` adds one operand per element of `cs`'s tag, `Ty.elems cs`, curried after the
others, and the wrapper passes the rule their payload (`Fn.ofPayload`).  A list variable's
Lean type is `List.map (interp σ) (Ty.elems cs)` and its `TagsOf` is `⟨Ty.elems cs, rfl⟩`.  A
closure operand whose arguments splice a list variable has, at the wrapper, Lean types that
equal the rule's but not by `rfl`, so the wrapper passes the rule its raw closure at the
rule's type.  Linking
instantiates it at the machine's token.  A pure rule's wrapper applies the rule to them.  A
rule's wrapper also applies it to one `Region.slot` per region, one target per successor, its
state and its `Again` if it loops, and its capabilities: the table's decoding as `Decode σ`,
`HasHeap.mreq` and `HasCall.mreq` at the machine's requests `MEff`, and each tag the rule takes
at the Lean types it names, with the proof `rfl`:

```
def rule.demo.div : ∀ (σ : Type) [Store σ],
    Fn (interp σ) (Tree (interp σ) σ (W σ) [] [[T.demo.Int]] Empty (interp σ T.demo.Int))
      [T.demo.Int, T.demo.Int] :=
  fun σ _ a0 a1 =>
    Rules.div a0 a1 (Target.mk fun p0 => Out.exit (Exit.here (Args.cons p0 Args.nil)))
```

The `k`-th successor's exit is `Out.exit` of `Exit.there` `k` times around `Exit.here`.  A rule
that does not loop has the state type `Empty`.  For one that loops, `rule.o` passes the state
`none`, `again.o` takes a state `s` after the operands and passes `some s`, and the `Again`'s
exit is `Out.again`; Lean infers the state type from the rule's, and the entry records it.  A
constructor's wrapper applies the Lean constructor; a case instruction's matches on its operand
and exits along the constructor's successor with its fields.
-/

public meta section

namespace Strata.Dyn.Exec

open Lean Elab Command Meta
open Strata.Dyn.DSL (TypeInfo OpInfo OpKind EnvEntry findEntry? ancestry allTypes allOps
  rootId nameLit)

/-! ## Environments -/

/-- The record of the environment `E`, from the reference `E`. -/
def resolveEnv (e : Ident) : CommandElabM EnvEntry := do
  let c? ← try
      some <$> liftCoreM (resolveGlobalConstNoOverload (mkIdentFrom e (e.getId ++ `env)))
    catch _ => pure none
  let some c := c? | throwErrorAt e "unknown environment `{e.getId}`"
  let some entry := findEntry? (← getEnv) (privateToUserName c).getPrefix
    | throwErrorAt e "`{e.getId}` is not declared with `environment`"
  return entry

/-- The shortest name that resolves to the constant `c` here. -/
def shortName (c : Lean.Name) : CommandElabM Lean.Name :=
  liftCoreM (unresolveNameGlobal c)

/-! ## Coverage -/

/-- One line per type and instruction of `e`: its rule, `derived`, the engine's, or
`missing`; and those that are missing. -/
def coverageOf (types : Array TypeInfo) (ops : Array OpInfo) :
    CommandElabM (Array String × Array String) := do
  let env ← getEnv
  let mut lines := #[]
  let mut missing := #[]
  for t in types do
    match engineType? t, findTypeRule? env t.fullName with
    | some c, _ => lines := lines.push s!"type {showEnvName t.envName}: the engine's {c.show}"
    | none, some r =>
      let gen := if r.generated then " (generated)" else ""
      lines := lines.push s!"type {showEnvName t.envName} ↦ {← shortName r.decl}{gen}"
    | none, none =>
      lines := lines.push s!"type {showEnvName t.envName}: missing"
      missing := missing.push (showEnvName t.envName)
  for o in ops do
    let n := showEnvName o.envName
    match o.kind, findSemRule? env o.fullName with
    | .ctor d _, _ => lines := lines.push s!"op {n}: derived constructor of {showEnvName d}"
    | .case d, _ => lines := lines.push s!"op {n}: derived case of {showEnvName d}"
    | .decl, some r =>
      lines := lines.push s!"op {n} ↦ {← shortName r.decl}{if r.pure then " (pure)" else ""}"
    | .decl, none =>
      if machineOps.contains o.fullName then
        lines := lines.push s!"op {n}: the machine's"
      else
        lines := lines.push s!"op {n}: missing"
        missing := missing.push n
  return (lines, missing)

/-- `(complete)`: require full coverage, and report nothing. -/
syntax dynCoverageComplete := " (" &"complete" ")"

syntax (name := dynCoverage) "#dyn_coverage " ident (dynCoverageComplete)? : command

elab_rules : command
  | `(#dyn_coverage $e $_:dynCoverageComplete) => do
    let entry ← resolveEnv e
    withRef e <| liftCoreM (checkNoDuplicates entry.leanNs)
    let anc := ancestry (← getEnv) entry.leanNs
    let (_, missing) ← coverageOf (anc.flatMap (·.types)) (anc.flatMap (·.ops))
    unless missing.isEmpty do
      throwErrorAt e "{e.getId} is not fully covered: no rule for \
        {", ".intercalate missing.toList}"
  | `(#dyn_coverage $e) => do
    let entry ← resolveEnv e
    withRef e <| liftCoreM (checkNoDuplicates entry.leanNs)
    let (lines, missing) ← coverageOf entry.types entry.ops
    let anc := (ancestry (← getEnv) entry.leanNs).extract 1
    let (_, ancMissing) ← coverageOf (anc.flatMap (·.types)) (anc.flatMap (·.ops))
    logInfo ("\n".intercalate (lines.push s!"{missing.size} missing, and {ancMissing.size} in \
      ancestors").toList)

/-! ## The table -/

set_option hygiene false

/-- An identifier for a constant of the interface. -/
def execId (s : String) : Ident := rootId (`Strata.Dyn.Exec ++ s.toName)

register_option dyn.semTable.trace : Bool := {
  defValue := false
  descr := "log each definition `#dyn_sem_table` emits"
}

/-- `stx` with each `_root_.c` written as the shortest name that resolves to `c` here, for
the trace. -/
def shortenIds (stx : Syntax) : CommandElabM Syntax :=
  stx.replaceM fun s => do
    let .ident _ _ n _ := s | return none
    unless n.getRoot == `_root_ do return none
    let full := n.replacePrefix `_root_ .anonymous
    let env ← getEnv
    let c := if env.contains full then full else mkPrivateName env full
    unless env.contains c do return none
    return some (mkIdent (← shortName c))

/-- `def n : ty := v`, or `def n := v` if `ty?` is `none`, logged under `trace`: public and
exposed if the scope is public. -/
def emitDefOf (trace : Bool) (n : Lean.Name) (ty? : Option Term) (v : Term) (reducible := false) :
    CommandElabM Unit := do
  let id := mkIdent n
  let isPublic := (← getScope).isPublic || !(← getEnv).header.isModule
  let sig ← match ty? with
    | some ty => `(Lean.Parser.Command.optDeclSig| : $ty)
    | none => `(Lean.Parser.Command.optDeclSig| )
  let cmd ← match isPublic, reducible with
    | true, true => `(command| @[expose, reducible] public def $id $sig:optDeclSig := $v)
    | true, false => `(command| @[expose] public def $id $sig:optDeclSig := $v)
    | false, true => `(command| @[reducible] def $id $sig:optDeclSig := $v)
    | false, false => `(command| def $id $sig:optDeclSig := $v)
  if trace then logInfo m!"{← shortenIds cmd}"
  elabCommand cmd

/-- `def n : ty := v`, logged under `trace`: public and exposed if the scope is public. -/
def emitDef (trace : Bool) (n : Lean.Name) (ty v : Term) (reducible := false) :
    CommandElabM Unit :=
  emitDefOf trace n (some ty) v reducible

/-- `instance n : ty := v`, logged under `trace`: public and exposed if the scope is public. -/
def emitInstance (trace : Bool) (n : Lean.Name) (ty v : Term) : CommandElabM Unit := do
  let id := mkIdent n
  let isPublic := (← getScope).isPublic || !(← getEnv).header.isModule
  let cmd ← if isPublic then `(command| @[expose] public instance $id:ident : $ty := $v)
    else `(command| instance $id:ident : $ty := $v)
  if trace then logInfo m!"{← shortenIds cmd}"
  elabCommand cmd

/-- `(world := W)`: the world, a Lean type or a function of the token.  It defaults to `Unit`. -/
syntax dynSemTableWorld := atomic(" (" &"world") " := " term ")"

/-- `(trace := true)`: log each emitted definition. -/
syntax dynSemTableTrace := " (" &"trace" " := " &"true" ")"

syntax (name := dynSemTable) "#dyn_sem_table " ident " for " ident
  (dynSemTableWorld)? (dynSemTableTrace)? : command

/-- The identifiers a wrapper binds for its type arguments: each type parameter's name, or
`tᵢ` if that name could be one of the wrapper's own binders. -/
def typeArgIds (params : Array String) : Array Ident := Id.run do
  let own (x : String) : Bool :=
    x == "v" || x == "vs" || x == "ts" || x == "st" ||
      (x.length > 1 && "apft".contains x.front && (x.drop 1).all Char.isDigit)
  let mut out := #[]
  for h : i in [0:params.size] do
    let x := params[i]
    out := out.push (mkIdent (if own x then s!"t{i}".toName else Lean.Name.mkSimple x))
  return out

/-- What generating one table reads. -/
structure TableCtx where
  /-- The table's namespace, `Foo.S`. -/
  ns : Lean.Name
  /-- Each type's rule, by environment name. -/
  rules : Std.HashMap Lean.Name TypeRule
  /-- The head of each Lean type constructor, with whether it takes the token. -/
  heads : Std.HashMap Lean.Name (Nat × Bool)
  /-- The world at the token `σ`. -/
  world : Term

namespace TableCtx

variable (cx : TableCtx)

/-- A constant of the table. -/
def own (n : Lean.Name) : Ident := rootId (cx.ns ++ n)

/-- The code of `t`, with type variable `i` as `vars[i]`, a list variable if `lists[i]`.  A list
variable's splice in a list literal is its elements: `[*cs, a]` is
`Ty.list (Ty.elems cs ++ [a])`. -/
partial def code (vars : Array Term) (lists : Array Bool := #[]) : DSL.Ty → Term
  | .var i => vars[i]?.getD
      (DSL.internalErrorTerm s!"#dyn_sem_table: type variable {i} is out of range")
  | .app h args =>
    let as := args.map (code vars lists)
    let c := cx.own (`T ++ DSL.leanName h)
    if as.isEmpty then c else Syntax.mkApp c as
  | .list es => Unhygienic.run `($(execId "Ty.list") $(codeList vars lists es))
where
  /-- The codes of a list literal's elements, as a `List Ty`. -/
  codeList (vars : Array Term) (lists : Array Bool) (es : Array DSL.Ty) : Term :=
    let splice? : DSL.Ty → Option Nat := fun
      | .var i => if lists[i]?.getD false then some i else none
      | _ => none
    match es.findIdx? (splice? · |>.isSome) with
    | none => Unhygienic.run `([$(es.map (code vars lists)),*])
    | some k =>
      let v := (es[k]? >>= splice? >>= (vars[·]?)).getD
        (DSL.internalErrorTerm "#dyn_sem_table: a splice is out of range")
      let post := (es.extract (k + 1) es.size).map (code vars lists)
      let mid : Term := if post.isEmpty then Unhygienic.run `($(execId "Ty.elems") $v)
        else Unhygienic.run `($(execId "Ty.elems") $v ++ [$post,*])
      (es.extract 0 k).foldr (fun e acc => Unhygienic.run `($(code vars lists e) :: $acc)) mid

/-- `[c₁, …]`, the codes of `ts`. -/
def codes (vars : Array Term) (ts : Array DSL.Ty) (lists : Array Bool := #[]) : Term :=
  Unhygienic.run `([$(ts.map (cx.code vars lists)),*])

/-- The token every wrapper binds. -/
def sigma : Term := mkIdent `σ

/-- The interpretation at the token `σ`. -/
def interp : Term := Unhygienic.run `($(cx.own `interp) $sigma)

/-- The Lean type of `t` at the token `σ`, with type variable `i` as `interp σ vars[i]`. -/
def leanTy (vars : Array Term) (t : DSL.Ty) (lists : Array Bool := #[]) : Term :=
  Syntax.mkApp (cx.own `interp) #[sigma, cx.code vars lists t]

/-- The codes of an operation's operands, the spread's elements last, as a `List Ty`: the
operands' codes consed onto `Ty.elems v` for a spread over the list variable `v`. -/
def argCodes (vars : Array Term) (lists : Array Bool) (o : OpInfo) : Term :=
  match o.variadic with
  | some (_, .list es) =>
    let spread := code.codeList cx vars lists es
    o.args.foldr (fun (_, t) acc => Unhygienic.run `($(cx.code vars lists t) :: $acc)) spread
  | _ => cx.codes vars (o.args.map (·.2)) lists

end TableCtx

/-- `Args.cons x₀ (… Args.nil)`. -/
def argsOf (xs : Array Term) : CommandElabM Term := do
  xs.foldrM (fun x acc => `($(execId "Args.cons") $x $acc)) (← `($(execId "Args.nil")))

/-- `fun (p0, …) => body`, over a payload of `n` values. -/
def payloadFun (n : Nat) (body : Array Term → CommandElabM Term) : CommandElabM Term := do
  let ps : Array Term := (Array.range n).map fun j => mkIdent s!"p{j}".toName
  let b ← body ps
  match ps.toList with
  | [] => `(fun _ => $b)
  | [p] => `(fun $p => $b)
  | p :: qs =>
    let qs := qs.toArray
    `(fun ($p, $qs,*) => $b)

/-- The exit along successor `i`, with payload `args`. -/
def exitOf (i : Nat) (args : Term) : CommandElabM Term := do
  let mut t ← `($(execId "Exit.here") $args)
  for _ in [0:i] do t ← `($(execId "Exit.there") $t)
  return t

/-- `Target.mk fun (p0, …) => e`, where `e` exits along successor `i` with the payload's `n`
values. -/
def targetOf (i n : Nat) : CommandElabM Term := do
  `($(execId "Target.mk") $(← payloadFun n fun ps => do
    `($(execId "Out.exit") $(← exitOf i (← argsOf ps)))))

/-- `fun xs => body`, or `body` if `xs` is empty. -/
def lam (xs : Array Ident) (body : Term) : CommandElabM Term :=
  if xs.isEmpty then pure body else `(fun $xs* => $body)

/-- The regions' signatures, `[([T₀, …], R), …]`. -/
def regionCodes (cx : TableCtx) (vars : Array Term) (o : OpInfo) : CommandElabM Term := do
  let lists := o.typeParams.map (·.2 == .list)
  let rs ← o.regions.mapM fun rd =>
    `(($(cx.codes vars (rd.params.map (·.2)) lists), $(cx.code vars lists rd.ret)))
  `([$rs,*])

/-- The tag of the Lean type `t` a capability names, with the rule's type variable `i` as
`vars[i]`, a tag, and hole `i` as `holes[i]`. -/
partial def tagTerm (cx : TableCtx) (vars holes : Array Term) : LTy → CommandElabM Term
  | .var i => match vars[i]? with
    | some v => pure v
    | none => throwError "#dyn_sem_table: type variable {i} is out of range"
  | .hole i => match holes[i]? with
    | some v => pure v
    | none => throwError "#dyn_sem_table: hole {i} is out of range"
  | .ref a => do `($(execId "Ty.app") 0 [$(← tagTerm cx vars holes a)])
  | .fn as r => do
    let as ← as.toArray.mapM (tagTerm cx vars holes)
    `($(execId "Ty.app") 1 [$(execId "Ty.list") [$as,*], $(← tagTerm cx vars holes r)])
  | .con d args => do
    let some (k, _) := cx.heads[d]? |
      throwError "#dyn_sem_table: a capability names {.ofConstName d}, the Lean type of no type of this table"
    let as ← args.toArray.mapM (tagTerm cx vars holes)
    `($(execId "Ty.app") $(quote k) [$as,*])

/-- The Lean type `t` at the token `σ`, with the rule's type variable `i` as the Lean type of
`vars[i]` and hole `i` as `holes[i]`. -/
partial def ltyTerm (cx : TableCtx) (vars holes : Array Term) : LTy → CommandElabM Term
  | .var i => match vars[i]? with
    | some v => pure (Syntax.mkApp (cx.own `interp) #[TableCtx.sigma, v])
    | none => throwError "#dyn_sem_table: type variable {i} is out of range"
  | .hole i => match holes[i]? with
    | some v => pure v
    | none => throwError "#dyn_sem_table: hole {i} is out of range"
  | .ref a => do `($(execId "Ref") σ $(← ltyTerm cx vars holes a))
  | .fn as r => do
    let as ← as.toArray.mapM (ltyTerm cx vars holes)
    `($(execId "FnRef") σ [$as,*] $(← ltyTerm cx vars holes r))
  | .con d args => do
    let as ← args.toArray.mapM (ltyTerm cx vars holes)
    let some (_, σ?) := cx.heads[d]?
      | throwError "#dyn_sem_table: a capability names {.ofConstName d}, the Lean type of no type of this table"
    if σ? then `(@$(rootId d) σ _ $as*) else pure (Syntax.mkApp (rootId d) as)

/-- A capability, as a value: a part of the world by instance search, the machine's cells and
calls, a tag at the Lean types it names, and a language's bundle field by field.  The table's
decoding is the instance `Decode σ` in scope. -/
partial def capTermOf (cx : TableCtx) (vars : Array Term) (interp rs : Term) :
    Lead → CommandElabM Term
  | .heap => `($(execId "HasHeap.mreq") (σ := σ) (I := $interp) (W := $(cx.world)) (rs := $rs))
  | .call => `($(execId "HasCall.mreq") (σ := σ) (I := $interp) (W := $(cx.world)) (rs := $rs))
  | .tag t => do `(⟨$(← tagTerm cx vars #[] t), rfl⟩)
  | .sig as r => do
    let as ← as.toArray.mapM (tagTerm cx vars #[])
    `(⟨([$as,*], $(← tagTerm cx vars #[] r)), ⟨rfl, rfl⟩⟩)
  | .tagCon t => do
    let a := mkIdent `tA
    let tag ← tagTerm cx vars #[← `(tA.tag)] t
    let F ← `(fun (X : Type) => $(← ltyTerm cx vars #[← `(X)] t))
    `(⟨fun $a => ⟨$tag, congrArg $F tA.ok⟩⟩)
  | .tagCon₂ t => do
    let a := mkIdent `tA
    let b := mkIdent `tB
    let tag ← tagTerm cx vars #[← `(tA.tag), ← `(tB.tag)] t
    let F ← `(fun (X Y : Type) => $(← ltyTerm cx vars #[← `(X), ← `(Y)] t))
    `(⟨fun $a $b => ⟨$tag, congr (congrArg $F tA.ok) tB.ok⟩⟩)
  | .tags t => do
    let v ← tagTerm cx vars #[] t
    `(⟨$(execId "Ty.elems") $v, rfl⟩)
  | .bundle fs => do
    let ns : Array Ident := fs.map fun (f, _) => mkIdent f
    let vs ← fs.mapM fun (_, c) => capTermOf cx vars interp rs c
    `({ $[$ns:ident := $vs],* })
  | _ => `(inferInstance)

/-- A wrapper: its value and its type, and, for a rule that loops, its wrapper with a state.
A rule that loops has its state's type, which Lean infers, so its wrappers' types are
left to Lean. -/
structure Wrapper where
  val : Term
  type : Option Term
  again : Option Term := none

/-- The wrapper of `o`, or `none` if `o` has no rule. -/
def wrapper (cx : TableCtx) (o : OpInfo) : CommandElabM (Option Wrapper) := do
  let env ← getEnv
  let tids := typeArgIds (o.typeParams.map (·.1))
  let vars : Array Term := tids.map (⟨·.raw⟩)
  let lists := o.typeParams.map (·.2 == .list)
  let interp := cx.interp
  let ts := cx.argCodes vars lists o
  let ps : Term ← `([$(o.succs.map fun s => cx.codes vars s.payload lists),*])
  let rs ← regionCodes cx vars o
  -- A spread's operands are curried in the operands' list, so only a variadic adds an array.
  let spread? : Option (Array DSL.Ty) := match o.variadic with
    | some (_, .list es) => some es
    | _ => none
  let var (x : Term) : CommandElabM Term := match o.variadic with
    | none | some (_, .list _) => pure x
    | some (_, v) => `(Array ($interp $(cx.code vars lists v)) → $x)
  let pureOut ← match o.ret with
    | some r => pure (cx.leanTy vars r lists)
    | none => `($(execId "Exit") $interp $ps)
  let semRes ← match o.ret with
    | some r => pure (cx.leanTy vars r lists)
    | none => `(Empty)
  let tree ← `($(execId "Tree") $interp σ $(cx.world) $rs $ps Empty $semRes)
  let fnTy (x : Term) : CommandElabM Term := do
    let mono ← `($(execId "Fn") $interp $(← var x) $ts)
    let mono ← if tids.isEmpty then pure mono else `(∀ ($tids* : $(execId "Ty")), $mono)
    `(∀ (σ : Type) [$(execId "Store") σ], $mono)
  -- Every wrapper is generic in the token.
  let lamσ (xs : Array Ident) (body : Term) : CommandElabM Term :=
    `(fun (σ : Type) [$(execId "Store") σ] $xs* => $body)
  let operands : Array Ident := (Array.range o.args.size).map fun i => mkIdent s!"a{i}".toName
  let opsV : Array Ident :=
    operands ++ (if o.variadic.isSome && spread?.isNone then #[mkIdent `vs] else #[])
  let opTerms : Array Term := opsV.map (⟨·.raw⟩)
  -- A closure operand whose arguments splice a list variable has another list of Lean types at
  -- the wrapper than at the rule, equal but not by `rfl`; the closure is the same raw closure.
  let ruleOps : Array Term ← (opsV.zipIdx).mapM fun (x, i) => do
    match o.args[i]? with
    | some (_, t) =>
      if mentionsList (o.typeParams.map (·.2)) t then
        `(⟨($x : $(execId "FnRef") σ _ _).raw⟩)
      else pure ⟨x.raw⟩
    | none => pure ⟨x.raw⟩
  let ruleOps : Array Term := ruleOps ++ (if spread?.isSome then #[⟨(mkIdent `vs).raw⟩] else #[])
  -- The wrapper's binders: the operands, then, for a spread, a payload of its operands.
  let lamOps (pre : Array Ident) (body : Term) : CommandElabM Term := do
    match spread? with
    | some es =>
      `(fun (σ : Type) [$(execId "Store") σ] $(pre ++ operands)* =>
          $(execId "Fn.ofPayload") $(TableCtx.code.codeList cx vars lists es) fun vs => $body)
    | none => `(fun (σ : Type) [$(execId "Store") σ] $(pre ++ opsV)* => $body)
  match o.kind with
  | .ctor d j =>
    let some tr := cx.rules[d]? | return none
    let some lc := tr.ctors[j]? | return none
    let params := vars.map fun v => Syntax.mkApp (cx.own `interp) #[TableCtx.sigma, v]
    let tok : Array Term := if tr.takesσ then #[TableCtx.sigma, Unhygienic.run `(_)] else #[]
    let c ← `(@$(rootId lc) $(tok ++ params ++ opTerms)*)
    return some { val := ← lamσ (tids ++ opsV) c, type := some (← fnTy pureOut) }
  | .case d =>
    let some tr := cx.rules[d]? | return none
    let self  : DSL.Ty :=
      .app (DSL.dynName d) (TypeExpr.Raw.vars (o.typeParams.map (·.2)))
    let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for h : j in [0:o.succs.size] do
      let some lc := tr.ctors[j]? | return none
      let fs : Array Term :=
        (Array.range (o.succs[j].payload.size)).map fun i => mkIdent s!"f{i}".toName
      let holes : Array Term := (vars ++ (if tr.takesσ then #[TableCtx.sigma, TableCtx.sigma] else #[])).map
        fun _ => Unhygienic.run `(_)
      let pat ← `(@$(rootId lc) $(holes ++ fs)*)
      let ex ← exitOf j (← argsOf fs)
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $pat => $ex))
    let v := mkIdent `v
    let caseFn ← `(fun ($v : $(cx.leanTy vars self)) => match $v:ident with $alts:matchAlt*)
    return some { val := ← lamσ tids caseFn, type := some (← fnTy pureOut) }
  | .decl =>
    let some r := findSemRule? env o.fullName | return none
    -- The leading binders, positionally: the token, each type variable at its argument's
    -- Lean type, each capability, and `_` for the rest.
    let capTerm := capTermOf cx vars interp rs
    let leadArgs ← r.leads.mapM fun
      | .sigma => pure TableCtx.sigma
      | .tyVar i => match vars[i]? with
        | some v =>
          if lists[i]?.getD false then
            `(List.map ($(cx.own `interp) σ) ($(execId "Ty.elems") $v))
          else pure (Syntax.mkApp (cx.own `interp) #[TableCtx.sigma, v])
        | none => pure (DSL.internalErrorTerm s!"#dyn_sem_table: type variable {i} is out of range")
      | .eff => `($(execId "MEff") $interp σ $(cx.world) $rs)
      | .exits => if r.again then `($(execId "Out") $interp $ps _) else `($(execId "Out") $interp $ps Empty)
      | .store | .decode | .part => `(_)
      | l => capTerm l
    let fn ← `(@$(rootId r.decl))
    let args : Array Term := leadArgs ++ ruleOps
    if r.pure then
      return some { val := ← lamOps tids (Syntax.mkApp fn args), type := some (← fnTy pureOut) }
    let regions ← o.regions.mapIdxM fun j reg => do
      let n := reg.params.size
      `($(execId "Region.slot") (σ := σ) (I := $interp) (W := $(cx.world)) (rs := $rs)
          ⟨$(quote j), Nat.le_of_ble_eq_true rfl⟩ $(← payloadFun n argsOf))
    let targets ← o.succs.mapIdxM fun i s => targetOf i s.payload.size
    let againH ← `($(execId "Again.mk") $(execId "Out.again"))
    -- The rule applied to everything, its state `stArg` and its `Again` last if it loops.
    let appWith (stArg : Option Term) : CommandElabM Term := do
      let loopArgs ← match stArg with
        | some a => pure #[a, againH]
        | none => pure #[]
      let app := Syntax.mkApp fn (leadArgs ++ ruleOps ++ regions ++ targets ++ loopArgs)
      -- The table's decoding, as the instance the rule's tags and capabilities are found at.
      if r.leads.any (· matches .decode) then
        `(letI : $(execId "Decode") σ := $(execId "Decode.mk") ($interp); $app)
      else pure app
    unless r.again do
      return some { val := ← lamOps tids (← appWith none), type := some (← fnTy tree) }
    let stId := mkIdent `st
    let first ← appWith (some (← `(none)))
    let next ← appWith (some (← `(some $stId)))
    if spread?.isSome then
      throwError "#dyn_sem_table: {showEnvName o.envName} loops and has a spread, which no \
        wrapper takes"
    return some { val := ← lamσ (tids ++ opsV) first, type := none,
                  again := some (← lamσ (tids ++ opsV ++ #[stId]) next) }

/-- The implementation of `o`, whose wrapper is `w`, and, if its rule loops, `again?` its
wrapper with a state. -/
def entryOf (cx : TableCtx) (o : OpInfo) (w : Ident) (isPure : Bool) (again? : Option Ident) :
    CommandElabM Term := do
  let n := o.typeParams.size
  let tsId := mkIdent `ts
  let vars : Array Term ← (Array.range n).mapM fun i => `($tsId[$(quote i)])
  let lists := o.typeParams.map (·.2 == .list)
  let variadic ← match o.variadic with
    | some (_, .list _) | none => `(none)
    | some (_, v) => `(some $(cx.code vars lists v))
  let ret ← match o.ret with
    | some r => `(some $(cx.code vars lists r))
    | none => `(none)
  let ps : Term ← `([$(o.succs.map fun s => cx.codes vars s.payload lists),*])
  let shape ← `($(execId "Shape.mk") $(cx.argCodes vars lists o) $variadic $ret $ps
    $(← regionCodes cx vars o))
  let binder : Term := if n == 0 then Unhygienic.run `(_) else ⟨tsId.raw⟩
  let fn := Syntax.mkApp w (#[TableCtx.sigma] ++ vars)
  match again? with
  | some a =>
    -- Lean infers the state type from the wrappers'.
    let impl ← `($(execId "Impl.loop") $fn $(Syntax.mkApp a (#[TableCtx.sigma] ++ vars)))
    `({ typeArgc := $(quote n), shape := fun $binder => $shape, St := _,
        fn := fun (σ : Type) [$(execId "Store") σ] $binder => $impl })
  | none =>
    let impl : Term ← if isPure then `($(execId "Impl.pure") $fn) else `($(execId "Impl.sem") $fn)
    `({ typeArgc := $(quote n), shape := fun $binder => $shape,
        fn := fun (σ : Type) [$(execId "Store") σ] $binder => $impl })

/-- Each head's Lean type constructor at the token `σ`: the match the table's `H` is.  `rules`
gives each Lean type constructor's rule, by head. -/
def headsTerm (rules : Array (Nat × TypeRule × Nat)) : CommandElabM Term := do
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for (k, r, n) in rules do
    let xs : Array Term := (Array.range n).map fun j => mkIdent s!"x{j}".toName
    let rhs : Term := Syntax.mkApp (rootId r.decl) ((if r.takesσ then #[TableCtx.sigma] else #[]) ++ xs)
    alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $(quote k), [$xs,*] => $rhs))
  alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => Empty))
  `(fun (σ : Type) [$(execId "Store") σ] h as => match h, as with $alts:matchAlt*)

/-- An environment name as a `Strata.Dyn.Name`. -/
def dynName : Lean.Name → Strata.Dyn.Name
  | .anonymous => .base
  | .str p s => .str (dynName p) s
  | .num p i => .num (dynName p) i

/-- The term of a 2-3 tree whose values are terms. -/
partial def treeTerm : Strata.Dyn.NatTree23 Term → CommandElabM Term
  | .leaf => `(Strata.Dyn.NatTree23.leaf)
  | .two l k v r => do
    `(Strata.Dyn.NatTree23.two $(← treeTerm l) $(quote k) $v $(← treeTerm r))
  | .three l k₁ v₁ m k₂ v₂ r => do
    `(Strata.Dyn.NatTree23.three $(← treeTerm l) $(quote k₁) $v₁ $(← treeTerm m)
        $(quote k₂) $v₂ $(← treeTerm r))

/-- A `NameMap` literal of `entries`, built here so that the kernel never builds it. -/
def nameMapTerm (entries : Array (Lean.Name × Term)) : CommandElabM Term := do
  let mut t : Strata.Dyn.NatTree23 Term := .leaf
  for (n, v) in entries do
    let some t₁ := t.insert? (dynName n).key v
      | throwError "{showEnvName n} is named twice"
    t := t₁
  `(Strata.Dyn.NameMap.mk $(← treeTerm t))

/-- The base types the engine needs, by environment name. -/
def baseTypeNames : List Lean.Name :=
  [`base.Unit, `base.Bool, `base.Int, `base.Float64, `base.String]

/-- The tags of each Lean type constructor `headRules` lists, as instances at the table's
decoding, `Decode.mk (decode σ)`: a `TagOf` of a type, a `TagCon` or a `TagCon₂` of a
constructor of one or two parameters, the `TagCon` of `Ref σ`, and the `TagOf` of a closure
from its signature's.  A model finds its arguments' and results' tags through them. -/
def emitTagInstances (cx : TableCtx) (trace : Bool) (headRules : Array (Nat × TypeRule × Nat)) :
    CommandElabM Unit := do
  let dec ← `($(execId "Decode.mk") ($(cx.own `decode) σ))
  let binders (cls : Ident) (F : Term) : CommandElabM Term :=
    `(∀ (σ : Type) [$(execId "Store") σ], @$cls σ _ $dec $F)
  let F ← `($(execId "Ref") σ)
  emitInstance trace `tagOf.ref (← binders (execId "TagCon") F)
    (← `(fun (σ : Type) [$(execId "Store") σ] => letI : $(execId "Decode") σ := $dec;
      ⟨fun tA => ⟨$(execId "Ty.app") 0 [tA.tag], congrArg $F tA.ok⟩⟩))
  emitInstance trace `tagOf.fn
    (← `(∀ (σ : Type) [$(execId "Store") σ] {as : List Type} {r : Type}
      [@$(execId "SigOf") σ _ $dec as r], @$(execId "TagOf") σ _ $dec ($(execId "FnRef") σ as r)))
    (← `(fun (σ : Type) [$(execId "Store") σ] {as r} [s : _] =>
      letI : $(execId "Decode") σ := $dec;
      ⟨$(execId "Ty.app") 1 [$(execId "Ty.list") s.sig.1, s.sig.2],
        ($(execId "Ty.decode_fn") σ ($(cx.own `H) σ) _ _).trans
          (congr (congrArg ($(execId "FnRef") σ) s.ok.1) s.ok.2)⟩))
  for (k, r, n) in headRules do
    let F : Term ← if r.takesσ then `(@$(rootId r.decl) σ _) else pure (rootId r.decl)
    let lamσ (v : Term) : CommandElabM Term :=
      `(fun (σ : Type) [$(execId "Store") σ] => letI : $(execId "Decode") σ := $dec; $v)
    let n' := `tagOf ++ s!"h{k}".toName
    let inst? : Option (Ident × Term) ← match n with
      | 0 => pure (some (execId "TagOf", ← `(⟨$(execId "Ty.app") $(quote k) [], rfl⟩)))
      | 1 => pure (some (execId "TagCon",
          ← `(⟨fun tA => ⟨$(execId "Ty.app") $(quote k) [tA.tag], congrArg $F tA.ok⟩⟩)))
      | 2 => pure (some (execId "TagCon₂",
          ← `(⟨fun tA tB => ⟨$(execId "Ty.app") $(quote k) [tA.tag, tB.tag],
            congr (congrArg $F tA.ok) tB.ok⟩⟩)))
      | _ => pure none
    if let some (cls, v) := inst? then
      emitInstance trace n' (← binders cls F) (← lamσ v)

/-- Emit the table.  See the module doc. -/
def elabSemTable (s e : Ident) (world? : Option Term) (trace : Bool) : CommandElabM Unit := do
  let trace := trace || dyn.semTable.trace.get (← getOptions)
  let world ← match world? with
    | some w => pure w
    | none => `(Unit)
  let entry ← resolveEnv e
  withRef e <| liftCoreM (checkNoDuplicates entry.leanNs)
  let env ← getEnv
  let ns := entry.leanNs
  let types := allTypes env ns
  -- Every type's rule, with every field of a datatype checked.
  let mut rules : Std.HashMap Lean.Name TypeRule := {}
  let mut missingTys : Array String := #[]
  for t in types do
    if (engineType? t).isSome then continue
    match findTypeRule? env t.fullName with
    | some r => rules := rules.insert t.envName r
    | none => missingTys := missingTys.push (showEnvName t.envName)
  unless missingTys.isEmpty do
    throwErrorAt e "no type rule for {", ".intercalate missingTys.toList}; register one with \
      @[dyn_type], or, for a datatype, run #dyn_types for its environment"
  -- Each rule again, at this table's type rules: its module may have seen another type rule,
  -- which this module does not import.
  let mut misfit := false
  let byDecl ← liftTermElabM (rulesByDecl env)
  for o in allOps env ns do
    let some r := findSemRule? env o.fullName | continue
    try discard <| liftTermElabM (checkSemRule o r.decl byDecl)
    catch ex =>
      logErrorAt e m!"the rule {.ofConstName r.decl} for {showEnvName o.envName} does not fit \
        this table's type rules: {ex.toMessageData}"
      misfit := true
  -- Each datatype's rule again too: its constructors' fields were checked at the type rules that
  -- its module saw.
  for de in ancestry env ns do
    for t in de.types do
      unless t.isData do continue
      let some r := findTypeRule? env t.fullName | continue
      try discard <| liftTermElabM (checkDataRule de t r.decl r.takesσ)
      catch ex =>
        logErrorAt e m!"the type rule {.ofConstName r.decl} for {showEnvName t.envName} does \
          not fit this table's type rules: {ex.toMessageData}"
        misfit := true
  if misfit then throwAbortCommand
  -- The heads: the engine's, then one per Lean type constructor, in the types' order.
  let mut heads : Std.HashMap Lean.Name (Nat × Bool) := {}
  let mut headRules : Array (Nat × TypeRule × Nat) := #[]
  let mut typeNames : Array Lean.Name := #[`base.Ref, `base.Fn]
  let mut typeHead : Std.HashMap Lean.Name Nat := {}
  for t in types do
    match engineType? t with
    | some .ref => typeHead := typeHead.insert t.envName 0
    | some .fn => typeHead := typeHead.insert t.envName 1
    | none =>
      let some r := rules[t.envName]? | continue
      let c ← liftTermElabM (canonDecl r.decl)
      match heads[c]? with
      | some (k, _) => typeHead := typeHead.insert t.envName k
      | none =>
        let k := typeNames.size
        heads := heads.insert c (k, r.takesσ)
        headRules := headRules.push (k, r, t.params.size)
        typeNames := typeNames.push t.envName
        typeHead := typeHead.insert t.envName k
  let tns := (← getCurrNamespace) ++ s.getId
  let worldAt : Term ← `($(rootId (tns ++ `W)) σ)
  let cx : TableCtx := { ns := tns, rules, heads, world := worldAt }
  -- A world that takes no token is the same at every token.
  let worldTakesσ ← liftTermElabM do
    let w ← Term.elabTerm world none
    Term.synthesizeSyntheticMVarsNoPostponing
    let w ← instantiateMVars w
    return !(← whnf (← inferType w)).isSort
  elabCommand (← `(command| namespace $s))
  -- The namespace is closed whatever fails inside it.
  let missing ← try
    emitDef trace `typeNames (← `(Array Strata.Dyn.Name))
      (← `(#[$(typeNames.map nameLit),*]))
    emitDef trace `H
      (← `((σ : Type) → [$(execId "Store") σ] → Nat → List Type → Type))
      (← headsTerm headRules) (reducible := true)
    emitDef trace `interp (← `($(execId "Interp")))
      (← `(fun (σ : Type) [$(execId "Store") σ] => $(execId "Ty.decode") σ ($(cx.own `H) σ)))
      (reducible := true)
    emitDef trace `W (← `($(execId "World")))
      (← if worldTakesσ then pure world else `(fun (σ : Type) [$(execId "Store") σ] => $world))
      (reducible := true)
    -- The tags.
    for t in types do
      let some k := typeHead[t.envName]? | continue
      let xs : Array Ident := (Array.range t.params.size).map fun j => mkIdent s!"x{j}".toName
      let ty ← if xs.isEmpty then `($(execId "Ty"))
        else `(∀ ($xs* : $(execId "Ty")), $(execId "Ty"))
      let args : Array Term := xs.map fun x => ⟨x.raw⟩
      let v ← lam xs (← `($(execId "Ty.app") $(quote k) [$args,*]))
      emitDef trace (`T ++ t.envName) ty v (reducible := true)
    -- The decoding, and the tags of Lean types at it as a `Decode`.  Not reducible, so that
    -- each table's instances are found at its own decoding only.
    emitDef trace `decode (← `($(execId "Interp"))) (cx.own `interp)
    emitTagInstances cx trace headRules
    -- One wrapper per instruction with a rule or derived; an entry per wrapper.
    let mut entries : Array Term := #[]
    let mut index : Array (Lean.Name × Term) := #[]
    let mut missing : Array String := #[]
    let implTy ← `($(execId "OpImpl") $(cx.own `interp) $(cx.own `W))
    for o in allOps env ns do
      if o.kind matches .decl && machineOps.contains o.fullName then
        let k := lastString o.envName
        index := index.push (o.envName, ← `($(execId ("LinkOp." ++ k))))
        continue
      match ← wrapper cx o with
      | none => missing := missing.push (showEnvName o.envName)
      | some w =>
        let wname := `rule ++ o.envName
        emitDefOf trace wname w.type w.val
        let again? ← w.again.mapM fun v => do
          let aname := `again ++ o.envName
          emitDefOf trace aname none v
          pure (cx.own aname)
        let isPure := match o.kind with
          | .decl => (findSemRule? env o.fullName).any (·.pure)
          | _ => true
        let iname := `impl ++ o.envName
        emitDef trace iname implTy (← entryOf cx o (cx.own wname) isPure again?)
        index := index.push (o.envName, ← `($(execId "LinkOp.impl") $(quote entries.size)))
        entries := entries.push (← `(($(nameLit o.envName), $(cx.own iname))))
    emitDef trace `ops (← `(Array (Strata.Dyn.Name × $implTy))) (← `(#[$entries,*]))
    emitDef trace `table (← `($(execId "Table")))
      (← `({ typeNames := $(cx.own `typeNames), interp := $(cx.own `interp), W := $(cx.own `W),
             w0 := fun (σ : Type) [$(execId "Store") σ] => default, ops := $(cx.own `ops) }))
      (reducible := true)
    -- What the engine needs of the base, if `E` extends it.
    if let [some cUnit, some cBool, some cInt, some cFloat, some cStr] :=
        baseTypeNames.map (typeHead[·]?) then
      let tc (i : Nat) : Term := Unhygienic.run `($(execId "Ty.app") $(quote i) [])
      let interp := cx.interp
      -- `base.Unit`'s value: its datatype's one constructor.
      let unitV : Term ← match rules[`base.Unit]? |>.bind (fun r => r.ctors[0]?.map (r, ·)) with
        | some (r, c) => if r.takesσ then `(@$(rootId c) σ _) else pure (rootId c)
        | none => `(())
      emitDef trace `model (← `($(execId "Model"))) (← `({
        toTable := $(cx.own `table),
        refEq := fun _ _ _ => rfl,
        fnEq := fun (σ : Type) [$(execId "Store") σ] ts r =>
          $(execId "Ty.decode_fn") σ ($(cx.own `H) σ) ts r,
        unit := $(tc cUnit),
        unitVal := fun (σ : Type) [$(execId "Store") σ] => ($unitV : $interp $(tc cUnit)),
        bool := $(tc cBool),
        ofBool := fun (σ : Type) [$(execId "Store") σ] (b : Bool) => (b : $interp $(tc cBool)),
        int := $(tc cInt),
        ofInt := fun (σ : Type) [$(execId "Store") σ] (i : Int) => (i : $interp $(tc cInt)),
        float := $(tc cFloat),
        ofFloat := fun (σ : Type) [$(execId "Store") σ] (x : Float) => (x : $interp $(tc cFloat)),
        str := $(tc cStr),
        ofStr := fun (σ : Type) [$(execId "Store") σ] (x : String) => (x : $interp $(tc cStr)),
        index := $(← nameMapTerm index),
        typeIndex := $(← nameMapTerm (types.filterMap fun t =>
          (typeHead[t.envName]?).map fun k => (t.envName, quote k))),
        decode := fun (σ : Type) [$(execId "Store") σ] => ⟨$(cx.own `decode) σ⟩,
        decode_eq := fun _ _ => rfl }))
        (reducible := true)
    pure missing
  finally
    elabCommand (← `(command| end $s))
  unless missing.isEmpty do
    logInfo m!"{s.getId}: no rule for {", ".intercalate missing.toList}"

elab_rules : command
  | `(#dyn_sem_table $s for $e $[(world := $w)]? $[$t]?) => elabSemTable s e w t.isSome

end Strata.Dyn.Exec

end
