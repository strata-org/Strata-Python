/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public import StrataDyn.Exec.Sem

set_option autoImplicit false

/-!
# Worlds

`#dyn_world W` makes the structure `W` a language's world, whose parts its rules name by type
(`HasPart W P`).  `W` may take parameters, such as the run token of a world that holds refs,
`(σ : Type) [Store σ]`.  For each field of type `P`, the command emits:

* the part instance `HasPart W P`, which reads and writes the field, and updates it in place
  (`modifyGet`);
* its laws, `LawfulHasPart W P`, each by `rfl`;

and, for each ordered pair of parts of types `P` and `Q`, the theorem
`W.indep_p_q : HasPart.Indep W P Q`, named by the parts' fields, that writing the first leaves the
second as it is.  The declarations go into `W`'s namespace.

A field whose type was itself declared with `#dyn_world`, a parent language's world, gives
that world's parts as parts of `W`, through the field, so the parent's rules run on the child's
world.  The parts' types must be pairwise distinct, since a rule names a part by its type.  A
field inherited from a structure that `W` extends is that structure as one part, unless that
structure is a world.  `W` may take explicit and instance parameters, but no universe parameter
and no implicit one, and no field's type may depend on another field.

A `HasPart` instance written by hand must name its fields, `{ get := …, set := … }`, and needs
its own `modifyGet` to update in place when a rule isn't specialized to the world.
-/

namespace Strata.Dyn.Exec

open Lean Elab Command Meta

public meta section

/-- The structures declared with `#dyn_world`. -/
initialize worldExt : SimplePersistentEnvExtension Lean.Name Lean.NameSet ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.insert n
    addImportedFn := fun ess => ess.foldl (fun s es => es.foldl (fun s n => s.insert n) s) {} }

/-- A part of a world: the fields that lead to it from the world, and its type, over the world's
parameters. -/
structure WorldPart where
  path : List Lean.Name
  ty : Expr
  deriving Inhabited

/-- The parts of the structure `w` applied to `args`: each field, and, through a field whose type
is a world, that world's parts. -/
partial def worldParts (w : Lean.Name) (args : Array Expr) : MetaM (Array WorldPart) := do
  let env ← getEnv
  let wTy := mkAppN (← mkConstWithFreshMVarLevels w) args
  withLocalDeclD `w wTy fun x => do
    let mut out := #[]
    for f in getStructureFields env w do
      let fty ← instantiateMVars (← inferType (← mkProjection x f))
      if fty.containsFVar x.fvarId! then
        throwError "the type of field {f.toString (escape := false)} depends on another field"
      match fty.getAppFn.constName? with
      | some h =>
        if (worldExt.getState env).contains h then
          for p in ← worldParts h fty.getAppArgs do
            out := out.push { p with path := f :: p.path }
          continue
      | none => pure ()
      out := out.push ⟨[f], fty⟩
    return out

/-- `w.f₁.f₂…`, reading the part at `path`. -/
def partGet (w : Term) : List Lean.Name → MacroM Term
  | [] => pure w
  | f :: fs => do partGet (← `($w.$(mkIdent f):ident)) fs

/-- `{ w with f₁ := { w.f₁ with f₂ := … x } }`, writing `x` to the part at `path`. -/
def partSet (w x : Term) : List Lean.Name → MacroM Term
  | [] => pure x
  | [f] => `({ $w with $(mkIdent f):ident := $x })
  | f :: fs => do
    let inner ← partSet (← `($w.$(mkIdent f):ident)) x fs
    `({ $w with $(mkIdent f):ident := $inner })

/-- A part as its fields read: `parent.count`. -/
def partPath (p : WorldPart) : String :=
  ".".intercalate (p.path.map (·.toString (escape := false)))

/-- A doc comment with the text `s`. -/
def docOf (s : String) : TSyntax ``Lean.Parser.Command.docComment :=
  ⟨mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (" " ++ s ++ " -/")]⟩

/-- A part's name in a theorem's name: its fields, joined by `_`. -/
def partName (p : WorldPart) : String :=
  "_".intercalate (p.path.map (·.toString (escape := false)))

syntax (name := dynWorld) "#dyn_world " ident : command

@[command_elab dynWorld] def elabDynWorld : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let w ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  let fail (msg : MessageData) : CommandElabM Unit :=
    throwErrorAt id "#dyn_world {id.getId}: {msg}"
  unless isStructure env w do fail m!"{id.getId} is not a structure"
  let ind ← getConstInfoInduct w
  unless ind.levelParams.isEmpty do fail m!"{id.getId} takes a universe parameter"
  -- The declarations go into the world's namespace, and are as visible as the world: a public
  -- table may use a public world's parts, and a private world's parts are private.
  let wName := privateToUserName w
  let isPrivate := isPrivateName w && env.header.isModule
  -- The world's parameters, as binders, and its parts, delaborated over them.
  let (binders, wArgs, parts) ← liftTermElabM do
    forallBoundedTelescope ind.type ind.numParams fun xs _ => do
      let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      let mut wArgs : Array Term := #[]
      for x in xs do
        let d ← x.fvarId!.getDecl
        let ty ← PrettyPrinter.delab d.type
        if d.binderInfo.isInstImplicit then
          binders := binders.push (← `(bracketedBinder| [$ty]))
        else if !d.binderInfo.isExplicit then
          throwErrorAt id "#dyn_world {id.getId}: its parameter {d.userName} is implicit"
        else
          let n := mkIdent d.userName
          binders := binders.push (← `(bracketedBinder| {$n : $ty}))
          wArgs := wArgs.push n
      let parts ← try worldParts w xs catch e =>
        throwErrorAt id "#dyn_world {id.getId}: {e.toMessageData}"
      -- A rule names a part by its type, so two parts of one type cannot both be parts.
      let mut seen : Array _ := #[]
      for p in parts do
        for q in seen do
          if ← isDefEq q.ty p.ty then
            throwErrorAt id "#dyn_world {id.getId}: the fields {partPath q} and \
              {partPath p} both have type {q.ty}, but a rule names a part by its type"
        seen := seen.push p
      let parts ← parts.mapM fun p => return (p, ← PrettyPrinter.delab p.ty)
      return (binders, wArgs, parts)
  let ns := wName
  -- The names of the declarations, each from its parts, which must all differ.
  let mut names : Std.HashMap Lean.Name String := {}
  let declName (s : String) : Lean.Name := Lean.Name.str ns s
  let mut want : Array (Lean.Name × String) := #[]
  for (p, _) in parts do
    want := want.push (declName s!"instHasPart_{partName p}", s!"part {partPath p}")
    want := want.push (declName s!"instLawfulHasPart_{partName p}", s!"part {partPath p}")
  for (p, _) in parts do
    for (q, _) in parts do
      unless p.path == q.path do
        want := want.push (declName s!"indep_{partName p}_{partName q}",
          s!"parts {partPath p} and {partPath q}")
  for (n, what) in want do
    if let some other := names[n]? then
      throwErrorAt id "#dyn_world {id.getId}: {other} and {what} would both declare {n}; \
        rename a field"
    names := names.insert n what
  let wTerm : Term := Syntax.mkApp id wArgs
  let vis? : Option (TSyntax ``Lean.Parser.Command.visibility) ←
    if isPrivate then some <$> `(Lean.Parser.Command.visibility| private)
    else some <$> `(Lean.Parser.Command.visibility| public)
  let vis? := if env.header.isModule then vis? else none
  for (p, ty) in parts do
    let get ← liftMacroM <| partGet (← `(w)) p.path
    let set ← liftMacroM <| partSet (← `(w)) (← `(x)) p.path
    let setP ← liftMacroM <| partSet (← `(w)) (← `(p)) p.path
    let inst := mkIdent (`_root_ ++ declName s!"instHasPart_{partName p}")
    let laws := mkIdent (`_root_ ++ declName s!"instLawfulHasPart_{partName p}")
    let field := partPath p
    let instDoc := docOf s!"Part `{field}` of the world `{wName}`."
    let lawsDoc := docOf s!"The laws of part `{field}` of the world `{wName}`."
    elabCommand (← `($instDoc:docComment
      @[expose] $[$vis?:visibility]? instance $inst:ident $binders* : HasPart $wTerm $ty :=
        { get := fun w => $get, set := fun w x => $set,
          modifyGet := fun f w => match f $get with | (a, p) => (a, $setP) }))
    elabCommand (← `($lawsDoc:docComment
      $[$vis?:visibility]? instance $laws:ident $binders* : LawfulHasPart $wTerm $ty :=
        ⟨fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩))
  for (p, pty) in parts do
    for (q, qty) in parts do
      if p.path == q.path then continue
      let thm := mkIdent (`_root_ ++ declName s!"indep_{partName p}_{partName q}")
      let fp := partPath p
      let fq := partPath q
      let doc := docOf
        s!"Writing part `{fp}` of the world `{wName}` leaves part `{fq}` as it is."
      elabCommand (← `($doc:docComment
        $[$vis?:visibility]? theorem $thm:ident $binders* : HasPart.Indep $wTerm $pty $qty :=
          fun _ _ => rfl))
  modifyEnv (worldExt.addEntry · w)

end

end Strata.Dyn.Exec
