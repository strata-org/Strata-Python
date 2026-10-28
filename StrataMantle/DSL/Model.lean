/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Environment
public meta import Lean.EnvExtension
public meta import Std.Data.HashMap
public meta import StrataMantle.Env.TypeExprRaw

/-!
# The `environment` command: what the elaborator records

An environment's description as the elaborator sees it, and the persistent environment
extension that carries it across modules.  A child resolves its parent's declarations from
this record, never by evaluating `P.env`.

Environment names (`py.add`) are kept as Lean `Name`s with string components; the elaborator
turns them into `Strata.Mantle.Name` literals when it emits code.  A resolved type is a
`TypeExpr.Raw`, of the core's kinds.
-/

public meta section

namespace Strata.Mantle.DSL

open Lean

/-- Lean's `Name`, which environment names are kept as.  Under `Strata.Mantle.DSL` it shadows
the core's `Strata.Mantle.Name`. -/
abbrev Name := Lean.Name

/-- The core's kinds. -/
abbrev Kind := Strata.Mantle.Kind

/-- A resolved type: a `TypeExpr.Raw`, a variable by de Bruijn level, or a declared type, by
environment name, applied to types and lists.  Abbreviations are already expanded, and every
list is a literal. -/
abbrev Ty := Strata.Mantle.TypeExpr.Raw

/-- An environment name as a `Strata.Mantle.Name`. -/
def mantleName : Name → Strata.Mantle.Name
  | .anonymous => .base
  | .str p s => .str (mantleName p) s
  | .num p i => .num (mantleName p) i

/-- A `Strata.Mantle.Name` as an environment name. -/
def leanName : Strata.Mantle.Name → Name
  | .base => .anonymous
  | .str p s => .str (leanName p) s
  | .num p i => .num (leanName p) i

/-- A type or datatype an environment declares. -/
structure TypeInfo where
  /-- Its environment name, `base.Ref`. -/
  envName : Name
  /-- The Lean namespace of the declaring environment, `Strata.Mantle.Base`. -/
  owner : Name
  /-- Its Lean name, relative to `owner`: `Ref`. -/
  lean : Name
  /-- One entry per parameter: its name, whether it is positive, and its kind. -/
  params : Array (String × Bool × Kind)
  /-- The constructors' environment names, if it is a datatype. -/
  ctors : Array Name := #[]
  deriving Inhabited, Repr

/-- A type abbreviation an environment declares. -/
structure AbbrevInfo where
  envName : Name
  owner : Name
  lean : Name
  /-- Each parameter's kind. -/
  params : Array Kind
  /-- The expansion, over the parameters, by de Bruijn level. -/
  body : Ty
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
  /-- The same names, in the order the stages add them to `nameSet`. -/
  order : Array Name
  /-- Whether the declarations the command generated failed to elaborate.  A child may not
  extend such an environment. -/
  failed : Bool := false
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
