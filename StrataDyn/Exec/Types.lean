/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Elab.Command
public meta import StrataDyn.DSL.Elab
public meta import StrataDyn.Exec.Rules
public meta import StrataDyn.Exec.Table
public import StrataDyn.Exec.Sem

set_option autoImplicit false

/-!
# Semantic rules: datatypes

`#dyn_types E` emits, for each datatype `T` that the environment `E` declares without a
hand-written rule, `T.Val`, its Lean type: an inductive with a constructor per Dyn
constructor, of the same name, whose fields are the Dyn fields' Lean types, and the type rule
that registers it.  Mutually recursive datatypes are one `mutual` block.  A datatype whose
fields hold refs or closures, directly or through other types, takes the run token first:
`CellList.Val (σ : Type) [Store σ]`, whose `cons` holds a `Ref σ Int`, and
`Box.Val (σ : Type) [Store σ] (A : Type)`, whose `box` holds a `Ref σ A`.  The others take only
their parameters, as `While.IntList.Val` takes none.  The base's `Unit` and `Except` have
hand-written rules, Lean's `Unit` and `Except`, so they are not generated.  A type's handle,
which the builder uses, is the `environment` command's (`Env/Handle.lean`); the engine tags
values by Lean types instead (`Exec/Sem.lean`).

A datatype names its fields by their Lean types, so `#dyn_types E` comes after `E`'s
primitive and opaque types' rules, which its datatypes' fields need, and before its rules.  The
names are public if the environment is.
-/

public meta section

namespace Strata.Dyn.Exec

open Lean Elab Command
open Strata.Dyn.DSL (TypeInfo OpInfo EnvEntry rootId)

set_option hygiene false

/-! ## Datatypes -/

/-- The heads `t` mentions, at any depth. -/
partial def heads : DSL.Ty → Array Lean.Name
  | .var _ => #[]
  | .app h args => #[DSL.leanName h] ++ args.flatMap heads
  | .list es => es.flatMap heads

/-- What generating `E`'s datatypes reads. -/
structure GenCtx where
  /-- Every type of `E` and its ancestors, by environment name. -/
  types : Std.HashMap Lean.Name TypeInfo
  /-- `E`'s datatypes' Lean types, and whether each takes the token. -/
  own : Std.HashMap Lean.Name (Lean.Name × Bool) := {}

/-- The Lean type of a field of type `t`, with type parameter `i` as `params[i]`, at the token
`σ`. -/
partial def fieldTerm (cx : GenCtx) (params : Array Term) : DSL.Ty → CommandElabM Term
  | .var i => match params[i]? with
    | some p => pure p
    | none => throwError "type parameter {i} is out of range"
  | .list _ => throwError "a list of types has no Lean interpretation"
  | .app h args => do
    let h := DSL.leanName h
    let some t := cx.types[h]? | throwError "unknown Dyn type {showEnvName h}"
    match engineType? t, args.toList with
    | some .ref, [a] => `($(execId "Ref") σ $(← fieldTerm cx params a))
    | some .fn, [.list es, r] =>
      `($(execId "FnRef") σ [$(← es.mapM (fieldTerm cx params)),*] $(← fieldTerm cx params r))
    | some _, _ => throwError "{showEnvName h} has the wrong arguments"
    | none, _ =>
      let as ← args.mapM (fieldTerm cx params)
      let some (decl, σ?) := cx.own[h]? <|>
          (findTypeRule? (← getEnv) t.fullName).map (fun r => (r.decl, r.takesσ))
        | throwError "no type rule for {showEnvName h}: register one with @[dyn_type], or \
            run #dyn_types for its environment, before this datatype's"
      -- A member of the group being declared is named without `_root_`, as a local of it.
      let f : Term := if cx.own.contains h then mkIdent decl else rootId decl
      return Syntax.mkApp f ((if σ? then #[(mkIdent `σ : Term)] else #[]) ++ as)

/-- Whether values of `t` may hold refs or closures, given which of `E`'s datatypes do. -/
def holdsCells (cx : GenCtx) (env : Environment) (byLocal : Lean.Name → Bool) (t : DSL.Ty) :
    Bool :=
  (heads t).any fun h => match cx.types[h]? with
    | some u => match engineType? u with
      | some _ => true
      | none => byLocal h || ((findTypeRule? env u.fullName).any (·.takesσ))
    | none => false

/-- Generate `E`'s datatypes. -/
def emitData (entry : EnvEntry) : CommandElabM Unit := do
  let env ← getEnv
  -- A datatype with a hand-written rule, as the base's `Unit` and `Except`, keeps it.
  let datas := entry.types.filter fun t => t.isData && (findTypeRule? env t.fullName).isNone
  if datas.isEmpty then return
  for t in datas do
    if t.params.any (·.2.2 == .list) then
      throwError "{showEnvName t.envName} takes a list of types, which no Lean type interprets"
  let ctorsOf (t : TypeInfo) : Array OpInfo :=
    (entry.ops.filterMap fun o => match o.kind with
      | .ctor d j => if d == t.envName then some (j, o) else none
      | _ => none).qsort (·.1 < ·.1) |>.map (·.2)
  let fieldsOf (t : TypeInfo) : Array DSL.Ty := (ctorsOf t).flatMap (·.args.map (·.2))
  let names := datas.map (·.envName)
  -- Reachability among the datatypes, through their fields.
  let direct (t : TypeInfo) : Array Lean.Name :=
    ((fieldsOf t).flatMap heads).filter names.contains
  let mut reach : Std.HashMap Lean.Name (Array Lean.Name) := {}
  for t in datas do reach := reach.insert t.envName (direct t)
  for _ in datas do
    for t in datas do
      let r := (reach[t.envName]?).getD #[]
      let r₁ := r ++ r.flatMap (fun u => (reach[u]?).getD #[]) |>.filter (!r.contains ·)
      reach := reach.insert t.envName (r ++ r₁.toList.eraseDups.toArray)
  let reaches (a b : Lean.Name) : Bool := ((reach[a]?).getD #[]).contains b
  -- Which hold cells: a fixpoint through the datatypes.
  let cx₀ : GenCtx := { types := typesOf env entry.leanNs }
  let mut cells : Array Lean.Name := #[]
  for _ in datas do
    for t in datas do
      if !cells.contains t.envName &&
          (fieldsOf t).any (holdsCells cx₀ env cells.contains) then
        cells := cells.push t.envName
  -- The groups of mutually reachable datatypes, each after those it mentions.
  let mut done : Array Lean.Name := #[]
  let mut groups : Array (Array TypeInfo) := #[]
  for _ in datas do
    for t in datas do
      if done.contains t.envName then continue
      let g := datas.filter fun u => u.envName == t.envName ||
        (reaches t.envName u.envName && reaches u.envName t.envName)
      let outside := (g.flatMap fun u => direct u).filter fun n => !g.any (·.envName == n)
      unless outside.all done.contains do continue
      groups := groups.push g
      done := done ++ g.map (·.envName)
  let isPublic := entry.isPublic && (← getEnv).header.isModule
  let mut cx := cx₀
  for g in groups do
    -- A mutual group's members take the token alike.
    let σ? := g.any fun u => cells.contains u.envName
    let mut cmds : Array Command := #[]
    for t in g do
      cx := { cx with own := cx.own.insert t.envName (t.fullName ++ `Val, σ?) }
    for t in g do
      let params : Array Ident := t.params.map fun p => mkIdent (Lean.Name.mkSimple p.1)
      let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      if σ? then
        binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| (σ : Type)))
        binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| [$(execId "Store") σ]))
      for p in params do
        binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($p : Type)))
      let mut ctors : Array (TSyntax ``Lean.Parser.Command.ctor) := #[]
      for c in ctorsOf t do
        let mut fs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
        for (x, fty) in c.args do
          let ft ← fieldTerm cx (params.map (⟨·.raw⟩)) fty
          fs := fs.push (← `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent (Lean.Name.mkSimple x)) : $ft)))
        let cid := mkIdent (Lean.Name.mkSimple (lastString c.lean))
        ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $cid:ident $fs:bracketedBinder*))
      let id := mkIdent (`_root_ ++ t.fullName ++ `Val)
      let doc := DSL.mkDoc s!"The Lean type of `{showEnvName t.envName}`, generated by `#dyn_types`."
      let cmd ← if isPublic then
          `(command| $doc:docComment public inductive $id $binders* : Type where $ctors:ctor*)
        else `(command| $doc:docComment inductive $id $binders* : Type where $ctors:ctor*)
      cmds := cmds.push cmd
    match cmds with
    | #[cmd] => elabCommand cmd
    | _ => elabCommand (mkNode ``Lean.Parser.Command.mutual
        #[mkAtom "mutual", mkNullNode (cmds.map (·.raw)), mkAtom "end"])
    -- A private environment's datatypes are private, under their mangled names.
    let real (n : Lean.Name) : CommandElabM Lean.Name := do
      let env ← getEnv
      return if env.contains n then n else mkPrivateName env n
    for t in g do
      let decl := t.fullName ++ `Val
      let ctors ← (ctorsOf t).mapM fun c => real (decl ++ Lean.Name.mkSimple (lastString c.lean))
      let r : TypeRule :=
        { key := t.fullName, decl := ← real decl, ctors, takesσ := σ?, generated := true }
      modifyEnv (typeExt.addEntry · r)

syntax (name := dynTypes) "#dyn_types " ident : command

elab_rules : command
  | `(#dyn_types $e) => do
    let entry ← resolveEnv e
    withRef e <| liftCoreM (checkNoDuplicates entry.leanNs)
    emitData entry

end Strata.Dyn.Exec

end
