/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Environment
public meta import Lean.EnvExtension
public meta import Std.Data.HashMap

/-!
# The `environment` command: what the elaborator records

An environment's description as the elaborator sees it, and the persistent environment
extension that carries it across modules.  A child resolves its parent's declarations from
this record, never by evaluating `P.env`.

Environment names (`py.add`) are kept as Lean `Name`s with string components; the elaborator
turns them into `Strata.Mantle.Name` literals when it emits code.
-/

public meta section

namespace Strata.Mantle.DSL

open Lean

/-- A type in a block, resolved: a type variable by de Bruijn level, or a declared type,
by environment name, applied to types.  Abbreviations are already expanded. -/
inductive RTy where
  | var (level : Nat)
  | app (head : Name) (args : Array RTy)
  deriving Inhabited, Repr, BEq

/-- Replace each variable `i` with `args[i]`. -/
partial def RTy.subst (args : Array RTy) : RTy → RTy
  | .var i => args.getD i (.var i)
  | .app h as => .app h (as.map (RTy.subst args))

/-- A type or datatype an environment declares. -/
structure TypeInfo where
  /-- Its environment name, `base.Ref`. -/
  envName : Name
  /-- The Lean namespace of the declaring environment, `Strata.Mantle.Base`. -/
  owner : Name
  /-- Its Lean name, relative to `owner`: `Ref`. -/
  lean : Name
  /-- One entry per parameter: its name, and whether it is positive. -/
  params : Array (String × Bool)
  /-- The constructors' environment names, if it is a datatype. -/
  ctors : Array Name := #[]
  deriving Inhabited, Repr

/-- A type abbreviation an environment declares. -/
structure AbbrevInfo where
  envName : Name
  owner : Name
  lean : Name
  arity : Nat
  /-- The expansion, over variables `0 … arity - 1`. -/
  body : RTy
  deriving Inhabited, Repr

/-- An instruction an environment declares. -/
structure OpInfo where
  envName : Name
  owner : Name
  lean : Name
  /-- How many type parameters it binds. -/
  typeArgc : Nat
  deriving Inhabited, Repr

/-- What one `environment` command recorded. -/
structure EnvEntry where
  /-- The Lean namespace, `Strata.Mantle.Base`; `env` is `leanNs ++ env`. -/
  leanNs : Name
  isPublic : Bool
  /-- The declared parent's `leanNs`. -/
  parent : Option Name
  types : Array TypeInfo
  abbrevs : Array AbbrevInfo
  ops : Array OpInfo
  /-- Every environment name the environment declares itself: types, constructors and
  instructions, in `names` order. -/
  names : Array Name
  deriving Inhabited, Repr

/-- Every `environment` command's record, in this module and every module it imports. -/
initialize envEntries : SimplePersistentEnvExtension EnvEntry (Std.HashMap Name EnvEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert e.leanNs e
    addImportedFn := fun ess =>
      ess.foldl (fun m es => es.foldl (fun m e => m.insert e.leanNs e) m) {} }

/-- The record of the environment whose Lean namespace is `ns`. -/
def findEntry? (env : Environment) (ns : Name) : Option EnvEntry :=
  (envEntries.getState env)[ns]?

/-- `ns`'s record and every ancestor's, nearest first. -/
partial def ancestry (env : Environment) (ns : Name) : Array EnvEntry :=
  go ns #[]
where
  go (ns : Name) (acc : Array EnvEntry) : Array EnvEntry :=
    match findEntry? env ns with
    | none => acc
    | some e =>
      let acc := acc.push e
      match e.parent with
      | some p => go p acc
      | none => acc

end Strata.Mantle.DSL

end
