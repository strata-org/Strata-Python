/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public import StrataDyn.DSL.Check

/-!
# Typed emitters

For each instruction `o` of an environment `E`, constructors and case instructions included,
the emitter `E.o`, under the instruction's own name, whose Lean type is `o`'s signature over
type expressions of the monad's environment `env` (`StrataDyn.Build.Typed`).  The
instruction itself is `E.o.ref`.  For

```lean
insn callCode [(as : list) r] (f : Fn as r) (*args : as) : r
terminal insn Except.case [e a] (scrutinee : Except e a) (^ok (value : a)) (^error (err : e))
insn forEach (iterable : Value) (&body (item : Value) : raising Unit) (^err (exc : Value)) : Unit
```

it generates, abbreviated:

```lean
def Base.callCode {env α m} [Monad m] [MonadBuild env α m] [Base.env ≼ env]
    {as : List (TypeExpr env)} {r : TypeExpr env}
    (f : Val env (Base.Fn as r)) (args : Vals env as)
    (result : Option Name := none) (info : Option α := none) : m (Val env r)
def Base.refNew … {a : TypeExpr env} (value : Val env a)
    (result : Option Name := none) (info : Option α := none) : m (Val env (Base.Ref a))
def Base.Except.case … (scrutinee : Val env (Base.Except e a)) (ok : Target env [a])
    (error : Target env [e]) (info : Option α := none) : m Unit
def Py.forEach … (iterable : Val env Py.Value)
    (body : Val env Py.Value → Target env [Base.Except Py.Value Base.Unit] → m Unit)
    (err : Target env [Py.Value]) (result : Option Name := none) (info : Option α := none) :
    m (Val env Base.Unit)
```

* Each type parameter is an implicit type expression of `env`, `{a : TypeExpr env}`, or list
  of them.  Lean finds it by unifying the operands' and successors' types with the signature,
  or from the expected result type.  The emitter's instance `[E.env ≼ env]` defines every type
  the signature names.
* A variadic `(*xs : τ)` is an `Array (Val env τ)`; a spread `(*xs : as)` a `Vals env as`.
* A successor `(^k (y : τ))` takes a `Target env [τ]`, a spread payload spliced in:
  `(^k (*ys : as))` takes a `Target env as`.
* A region `(&r (p : τ) : σ)` is a function of its parameters and its exit, a `Target env [σ]`,
  that emits its body in `m`.  Its parameters are named after `p`, its entry block after `r`,
  or after the optional `rBase`.
* The result is named after `result`, or, without it, after the instruction, a name that
  `Build.named` may replace.  A terminal instruction has no `result` and returns `Unit`,
  closing the block.
* The emitter's docstring starts with the instruction's, which the record keeps, so `Base`'s
  emitters have theirs too.

The emitter applies `Build.emitApplyNamed` or `Build.terminateWith`, with the type arguments
given, so `Build.run` checks what it emits as it checks any other instruction.  A successor
that is the exit of a region other than the innermost open one is recorded as a misuse
(`Build.checkExits`).

`result`, `info`, `env`, `α` and `m` are the emitter's own binders.  A type parameter or operand
of one of these names takes `_` suffixes until it meets no name of the signature, so `result`
next to `result_` becomes `result__`; every other name is kept, so a named argument keeps its
meaning.  The names generated for a region, its `rBase` and the values `d0`, `d1`, … of its
parameters, take the suffix instead when they meet a name of the signature.  Every constant the
emitter names is written from the root, so a binder cannot shadow it.

An emitter's arguments come in one order: operands, then successors and regions, then
`result`, then `info`.  An ill-typed emit is a Lean type mismatch at the operand or successor,
naming both types.

The `environment` command generates the emitters when `StrataDyn.Build.Typed` is imported,
directly or not.  `StrataDyn.DSL` imports it, so every environment declared through that module
gets them, at about 10 ms an instruction; a module that imports only `StrataDyn.DSL.Core` gets
none.  A public environment whose module imports the typed builder only privately gets private
emitters, which the module itself can use.  The emitters read each instruction's
signature from the record the `environment` command leaves, its `OpInfo`.  `Base` is declared
below the builder, so `dyn_emitters Base`, in `Build.Typed`, generates its emitters from that
record.
-/

public meta section

namespace Strata.Dyn.DSL

open Lean Elab Command

set_option hygiene false

namespace Emit

/-- A constant, from the root. -/
def root (n : Name) : Ident := mkIdent (`_root_ ++ n)

/-- The constant `Strata.Dyn.n`, from the root. -/
def dyn (n : Name) : Ident := root (`Strata.Dyn ++ n)

/-- `dyn_internal_error% msg` (`DSL/Elab.lean`), which fails to elaborate with `msg`. -/
def internalError (msg : String) : Term :=
  ⟨mkNode `Strata.Dyn.DSL.internalError #[mkAtom "dyn_internal_error% ", Syntax.mkStrLit msg]⟩

/-- What generating one environment's emitters reads. -/
structure Ctx where
  /-- The environment's Lean namespace, `Strata.Dyn.Base`. -/
  envNs : Name
  /-- Every type the environment and its ancestors declare, by environment name. -/
  types : Std.HashMap Name TypeInfo
  vis? : Option (TSyntax ``Lean.Parser.Command.visibility)

/-- The binder names of one emitter: its type parameters', and the rest renamed away from
the emitter's own. -/
structure Names where
  tps : Array Ident
  kinds : Array Kind

/-- `x`, with `_` appended while it is in `avoid`. -/
partial def avoiding (avoid : Array String) (x : String) : String :=
  if avoid.contains x then avoiding avoid (x ++ "_") else x

/-- `TypeExpr env`. -/
def exprTy : Term := Unhygienic.run `($(dyn `TypeExpr) env)

mutual
/-- The type expression of `t` in `env`, its names' handles applied to the type parameters. -/
partial def handle (cx : Ctx) (n : Names) : Ty → Term
  | .var i => (n.tps[i]?.map (fun x => (x : Term))).getD
      (internalError "type variable out of scope")
  | .app h args =>
    match cx.types[leanName h]? with
    | some info =>
      let con : Term := root (info.owner ++ info.lean)
      if args.isEmpty then Unhygienic.run `(($con : $exprTy))
      else Unhygienic.run `(($(Syntax.mkApp con (args.map fun a =>
        if a.kind n.kinds == .list then handleList cx n a else handle cx n a)) : $exprTy))
    | none => internalError s!"unknown type `{showName (leanName h)}`"
  | l@(.list _) => handleList cx n l

/-- The list of type expressions of `t`, a list literal or a list parameter: a spliced list
parameter appended with `List.append`. -/
partial def handleList (cx : Ctx) (n : Names) : Ty → Term
  | .list es => Id.run do
    let listTy : Term := Unhygienic.run `(_root_.List $exprTy)
    let mut parts : Array Term := #[]
    let mut run : Array Term := #[]
    for e in es do
      match e with
      | .var j =>
        if n.kinds[j]? == some .list then
          unless run.isEmpty do
            parts := parts.push (Unhygienic.run `(([$run,*] : $listTy)))
            run := #[]
          parts := parts.push (handle cx n e)
        else run := run.push (handle cx n e)
      | _ => run := run.push (handle cx n e)
    if !run.isEmpty || parts.isEmpty then
      parts := parts.push (Unhygienic.run `(([$run,*] : $listTy)))
    match parts.toList with
    | [] => Unhygienic.run `(([] : $listTy))
    | p :: ps => ps.foldl (fun acc q => Unhygienic.run `(_root_.List.append $acc $q)) p
  | t => handle cx n t
end

/-- The types of the operands, the regions' and the successors' included: every type of the
signature but the result's. -/
def opTypes (s : OpInfo) : Array Ty :=
  s.args.map (·.2) ++ (s.variadic.map (#[·.2])).getD #[] ++
    s.regions.flatMap (fun r => r.params.map (·.2) ++ #[r.ret]) ++ s.succs.flatMap (·.payload)

/-- Every type of the signature, in order. -/
def sigTypes (s : OpInfo) : Array Ty := opTypes s ++ (s.ret.map (#[·])).getD #[]

/-- The emitter of `s`. -/
def emitterCmd (cx : Ctx) (s : OpInfo) : CommandElabM Command := do
  let own : Array String := #["env", "α", "m", "result", "info"]
  -- Every name the signature binds.  One of the emitter's own is renamed away from all of them
  -- and from the names chosen so far; the rest are kept, so a named argument keeps its meaning.
  let sigNames := s.typeParams.map (·.1) ++ s.args.map (·.1) ++
    (s.variadic.map (#[·.1])).getD #[] ++ s.regions.map (·.name) ++ s.succs.map (·.name)
  let (chosen, named) := sigNames.foldl (init := (#[], own ++ sigNames)) fun (chosen, named) x =>
    if own.contains x then
      let x' := avoiding named x
      (chosen.push (x, x'), named.push x')
    else (chosen.push (x, x), named)
  let rename (x : String) : String := ((chosen.find? (·.1 == x)).map (·.2)).getD x
  let n : Names :=
    { tps := s.typeParams.map fun (x, _) => mkIdent (Name.mkSimple (rename x))
      kinds := s.typeParams.map (·.2) }
  let opId (x : String) : Ident := mkIdent (Name.mkSimple (rename x))
  -- The names the emitter generates in the body, a region's entry block's and its parameters',
  -- are renamed away from every binder named by the signature.
  let genId (x : String) : Ident := mkIdent (Name.mkSimple (avoiding named x))
  let mut bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[
    ← `(bracketedBinder| {env : $(dyn `Env) _root_.Unit}),
    ← `(bracketedBinder| {α : Type}),
    ← `(bracketedBinder| {m : Type → Type}),
    ← `(bracketedBinder| [_root_.Monad m]),
    ← `(bracketedBinder| [$(dyn `MonadBuild) env α m]),
    ← `(bracketedBinder| [$(dyn `RefinedBy) $(root (cx.envNs ++ `env)) env])]
  -- Type parameters.
  for (x, (_, k)) in n.tps.zip s.typeParams do
    match k with
    | .type => bs := bs.push (← `(bracketedBinder| {$x : $exprTy}))
    | .list => bs := bs.push (← `(bracketedBinder| {$x : _root_.List $exprTy}))
  -- Explicit arguments.
  let mut ops : Array Term := #[]
  for (x, t) in s.args do
    let x := opId x
    bs := bs.push (← `(bracketedBinder| ($x : $(dyn `Val) env $(handle cx n t))))
    ops := ops.push (← `($(dyn `Val.id) $x))
  let mut rest : Term ← `(#[$ops,*])
  if let some (x, t) := s.variadic then
    let x := opId x
    if t.kind n.kinds == .list then
      bs := bs.push (← `(bracketedBinder| ($x : $(dyn `Vals) env $(handleList cx n t))))
      rest ← `($(dyn `Vals.idsTo) $rest $x)
    else
      bs := bs.push (← `(bracketedBinder|
        ($x : _root_.Array ($(dyn `Val) env $(handle cx n t)))))
      rest ← `($rest ++ _root_.Array.map $(dyn `Val.id) $x)
  let mut regions : Array Term := #[]
  let mut baseBinders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
  for ⟨r, ps, ret⟩ in s.regions do
    let baseId := genId (r ++ "Base")
    baseBinders := baseBinders.push
      (← `(bracketedBinder| ($baseId : _root_.String := $(quote r))))
    let rId := opId r
    let exitT ← `($(dyn `Target) env [$(handle cx n ret)])
    let fnT ← ps.foldrM (init := (← `($exitT → m _root_.Unit))) fun (_, t) acc =>
      `($(dyn `Val) env $(handle cx n t) → $acc)
    bs := bs.push (← `(bracketedBinder| ($rId : $fnT)))
    let ds := (List.range ps.size).toArray.map fun i => genId s!"d{i}"
    let vals ← ds.mapM fun d => `($(dyn `Val.mk) ($(dyn `ValDecl.id) $d))
    let mut body : Term ← `(_root_.Functor.map _root_.Prod.fst
      ($(dyn `Build.regionWith) (env := env) (α := α) (m := m) #[$ds,*]
        ($(dyn `Build.withExit) (env := env) (α := α) $(handle cx n ret)
          ($rId $vals*))
        (base := $baseId)))
    for ((p, t), d) in (ps.zip ds).reverse do
      body ← `(_root_.Bind.bind ($(dyn `MonadBuild.liftBuild)
          ($(dyn `Build.freshVal) (env := env) (α := α)
            ($(dyn `Name.str) $(dyn `Name.base) $(quote p)) $(handle cx n t)))
        fun $d => $body)
    regions := regions.push body
  let mut succs : Array Term := #[]
  let mut exits : Array Term := #[]
  for ⟨sc, payload⟩ in s.succs do
    let kId := opId sc
    bs := bs.push (← `(bracketedBinder|
      ($kId : $(dyn `Target) env $(handleList cx n (.list (payload.flatMap fun
        | .list es => es
        | t => #[t]))))))
    succs := succs.push (← `($(dyn `Target.raw) $kId))
    exits := exits.push (← `($(dyn `Target.exitOf) $kId))
  if s.ret.isSome then
    bs := bs.push (← `(bracketedBinder|
      (result : _root_.Option $(dyn `Name) := _root_.Option.none)))
  bs := bs.push (← `(bracketedBinder| (info : _root_.Option α := _root_.Option.none)))
  bs := bs ++ baseBinders
  -- The type arguments, as `ta[…]` builds them, a list parameter as the literal of its types,
  -- as a handle writes it; `ta[` is a token only where `Strata.Dyn` is open.
  let mut tas : Term ← `($(dyn `KindedTypeArgs.nil))
  for (x, kd) in (n.tps.zip n.kinds).reverse do
    tas ← match kd with
      | .type => `($(dyn `KindedTypeArgs.ty) $x $tas)
      | .list => `($(dyn `KindedTypeArgs.list)
          ($(dyn `TypeCon.ListArg.toTypeList) .types $x) $tas)
  let typeArgs ← `($(dyn `TypeArgsOf.given) $tas)
  let ref := root (cx.envNs ++ s.lean ++ `ref)
  -- A result not named by the caller is named after the instruction, and `Build.named` may
  -- rename it.
  let stem := match s.envName with
    | .str _ x => x
    | _ => "v"
  let lift ← `($(dyn `Build.liftOf) env α m)
  let (ty, val) ← match s.ret with
    | some t => do
      pure (← `(m ($(dyn `Val) env $(handle cx n t))),
        ← `(let _ : _root_.MonadLiftT ($(dyn `BuildM) env α) m := $lift
          _root_.Functor.map $(dyn `Val.mk)
            ($(dyn `Build.emitApplyNamed) (env := env) (m := m) result $(quote stem)
              $(handle cx n t) $ref $rest #[$succs,*] #[$regions,*] info $typeArgs)))
    | none => do
      pure (← `(m _root_.Unit),
        ← `(let _ : _root_.MonadLiftT ($(dyn `BuildM) env α) m := $lift
          $(dyn `Build.terminateWith) (env := env) (m := m) $ref $rest #[$succs,*]
            #[$regions,*] info (typeArgs := $typeArgs)))
  -- An exit among the successors must be the innermost open region's.
  let val ← if exits.isEmpty then pure val else
    `(_root_.Bind.bind ($(dyn `MonadBuild.liftBuild)
      ($(dyn `Build.checkExits) (env := env) (α := α) #[$exits,*])) fun _ => $val)
  let doc := mkDoc s!"{(s.doc.map (·.trimAscii.toString ++ "\n\n")).getD ""}Emit \
    `{showName s.envName}`, its type arguments inferred from its operands' and successors' types."
  let id := root (cx.envNs ++ s.lean)
  `($doc:docComment $[$cx.vis?:visibility]? def $id:ident $bs* : $ty := $val)

/-- Every type the environment `envNs` and its ancestors declare, by environment name. -/
def typesOf (env : Environment) (envNs : Name) : Std.HashMap Name TypeInfo := Id.run do
  let mut m : Std.HashMap Name TypeInfo := {}
  for e in ancestry env envNs do
    for t in e.types do m := m.insert t.envName t
  return m

/-- Generate the emitters of the environment `envNs`, from its record. -/
def generate (envNs : Name) (vis? : Option (TSyntax ``Lean.Parser.Command.visibility)) :
    CommandElabM Unit := do
  let env ← getEnv
  let some entry := findEntry? env envNs
    | throwError "`{envNs}` is not an environment"
  let cx : Ctx := { envNs, types := typesOf env envNs, vis? }
  for s in entry.ops do
    elabCommand (← emitterCmd cx s)

/-- Whether the typed builder is imported, so that the emitters can be generated. -/
def available (env : Environment) : Bool := env.contains `Strata.Dyn.MonadBuild

/-- The visibility of the emitters of an environment declared with `vis?`, public when
`isPublic`: `private` when the typed builder is imported only privately, since a public emitter
could not name it, and `vis?` otherwise. -/
def visibility (env : Environment) (isPublic : Bool)
    (vis? : Option (TSyntax ``Lean.Parser.Command.visibility)) :
    Option (TSyntax ``Lean.Parser.Command.visibility) :=
  if isPublic && !(env.setExporting true).contains `Strata.Dyn.MonadBuild then
    some (Lean.Parser.Command.visibility.ofBool false)
  else vis?

end Emit

/-- `dyn_emitters E`: generate the emitters of the environment `E`, declared before the
typed builder.  Only `Base` needs it. -/
syntax (name := dynEmitters) "dyn_emitters " ident : command

@[command_elab dynEmitters] def elabDynEmitters : CommandElab := fun stx => do
  let `(dyn_emitters $e:ident) := stx | throwUnsupportedSyntax
  let ns := (← getCurrNamespace) ++ e.getId
  let some entry := findEntry? (← getEnv) ns
    | throwErrorAt e "`{e.getId}` is not an environment declared in this namespace"
  unless Emit.available (← getEnv) do
    throwErrorAt e "the emitters need `public import StrataDyn.Build.Typed`"
  let isModule := (← getEnv).header.isModule
  let vis? := if entry.isPublic && isModule then some (Lean.Parser.Command.visibility.ofBool true)
    else none
  Emit.generate ns vis?

end Strata.Dyn.DSL

end
