/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public meta import Lean.Environment
public meta import Lean.EnvExtension
public meta import Std.Data.HashMap
public meta import StrataDyn.Env.TypeExprRaw

/-!
# The `environment` command: what the elaborator records

An environment's description as the elaborator sees it, and the persistent environment
extension that carries it across modules.  A child resolves its parent's declarations from
this record, never by evaluating `P.env`, and so do the typed emitters (`DSL/Emit.lean`):
each instruction's record is its full signature, resolved.

Environment names (`py.add`) are kept as Lean `Name`s with string components; the elaborator
turns them into `Strata.Dyn.Name` literals when it emits code.  A resolved type is a
`TypeExpr.Raw`, of the core's kinds.
-/

public meta section

namespace Strata.Dyn.DSL

open Lean

/-- Lean's `Name`, which environment names are kept as.  Under `Strata.Dyn.DSL` it shadows
the core's `Strata.Dyn.Name`. -/
abbrev Name := Lean.Name

/-- The core's kinds. -/
abbrev Kind := Strata.Dyn.Kind

/-- A resolved type: a `TypeExpr.Raw`, a variable by de Bruijn level, or a declared type, by
environment name, applied to types and lists.  Abbreviations are already expanded, and every
list is a literal. -/
abbrev Ty := Strata.Dyn.TypeExpr.Raw

/-- An environment name as a `Strata.Dyn.Name`. -/
def dynName : Name → Strata.Dyn.Name
  | .anonymous => .base
  | .str p s => .str (dynName p) s
  | .num p i => .num (dynName p) i

/-- A `Strata.Dyn.Name` as an environment name. -/
def leanName : Strata.Dyn.Name → Name
  | .base => .anonymous
  | .str p s => .str (leanName p) s
  | .num p i => .num (leanName p) i

/-- A type or datatype an environment declares. -/
structure TypeInfo where
  /-- Its environment name, `base.Ref`. -/
  envName : Name
  /-- The Lean namespace of the declaring environment, `Strata.Dyn.Base`. -/
  owner : Name
  /-- Its Lean name, relative to `owner`: `Ref`. -/
  lean : Name
  /-- One entry per parameter: its name, whether it is positive, and its kind. -/
  params : Array (String × Bool × Kind)
  /-- The constructors' environment names, in declaration order, if it is a datatype.  Each
  is an instruction of kind `ctor` in `EnvEntry.ops`, as is the case instruction. -/
  ctors : Array Name := #[]
  /-- Whether it is a datatype. -/
  isData : Bool := false
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

/-- A region of an instruction, resolved: its name, entry parameters and the type it leaves
with. -/
structure RRegion where
  name : String
  params : Array (String × Ty)
  ret : Ty
  deriving Inhabited, Repr, BEq

/-- A successor of an instruction, resolved: its name and the types of the values it
receives, a list for a spread, which receives one value per element. -/
structure RSucc where
  name : String
  payload : Array Ty
  deriving Inhabited, Repr, BEq

/-- Where an instruction comes from: declared by `insn`, or derived from a datatype. -/
inductive OpKind where
  /-- An `insn`. -/
  | decl
  /-- Constructor `idx` of the datatype `data`, by environment name. -/
  | ctor (data : Name) (idx : Nat)
  /-- The case instruction of the datatype `data`. -/
  | case (data : Name)
  deriving Inhabited, Repr, BEq

/-- An instruction an environment declares, with its signature.  Types are over the
instruction's type parameters, by de Bruijn level. -/
structure OpInfo where
  envName : Name
  owner : Name
  lean : Name
  kind : OpKind := .decl
  /-- One entry per type parameter, in declaration order: its name and kind. -/
  typeParams : Array (String × Kind) := #[]
  args : Array (String × Ty) := #[]
  /-- The variadic's name and type: a type, or a list for a spread. -/
  variadic : Option (String × Ty) := none
  regions : Array RRegion := #[]
  succs : Array RSucc := #[]
  /-- The result type, or `none` for a terminal instruction. -/
  ret : Option Ty
  /-- The docstring the instruction is declared with, which its emitter repeats. -/
  doc : Option String := none
  deriving Inhabited, Repr

/-- How many type parameters the instruction binds, of either kind. -/
def OpInfo.typeArgc (o : OpInfo) : Nat := o.typeParams.size

/-- What one `environment` command recorded. -/
structure EnvEntry where
  /-- The Lean namespace, `Strata.Dyn.Base`; `env` is `leanNs ++ env`. -/
  leanNs : Name
  isPublic : Bool
  /-- The declared parent's `leanNs`. -/
  parent : Option Name
  types : Array TypeInfo
  abbrevs : Array AbbrevInfo
  /-- The instructions, in declaration order: a datatype group's constructors, then its case
  instructions, as `Env.addData` declares them. -/
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

/-- `t` as a block writes it, with variable `i` named `vars[i]`: `base.Except py.Value a`,
`base.Fn [*as, base.Int] r`.  A literal that is one splice is the list variable's name. -/
partial def showTy (vars : Array String) : Ty → String
  | .var i => vars.getD i s!"#{i}"
  | .list #[.var j] => vars.getD j s!"#{j}"
  | .list es => s!"[{", ".intercalate (es.toList.map elem)}]"
  | .app h args =>
    let h := (leanName h).toString (escape := false)
    if args.isEmpty then h
    else " ".intercalate (h :: args.toList.map fun a =>
      match a with
      | .app _ bs => if bs.isEmpty then showTy vars a else s!"({showTy vars a})"
      | _ => showTy vars a)
where
  /-- An element of a list literal, where a variable is a splice. -/
  elem : Ty → String
    | .var j => s!"*{vars.getD j s!"#{j}"}"
    | t => showTy vars t

/-- The signature as a block writes it, with every type name in full:
`insn demo.unbox [a] (b : demo.Box a) (^none) : a`. -/
def OpInfo.show (o : OpInfo) : String :=
  let ty := showTy (o.typeParams.map (·.1))
  let tp : String × Kind → String
    | (x, .type) => x
    | (x, .list) => s!"({x} : list)"
  let tps := if o.typeParams.isEmpty then []
    else [s!"[{" ".intercalate (o.typeParams.toList.map tp)}]"]
  let args := o.args.toList.map fun (x, t) => s!"({x} : {ty t})"
  let var := (o.variadic.map fun (x, t) => s!"(*{x} : {ty t})").toList
  let params (ps : Array (String × Ty)) : String :=
    String.join (ps.toList.map fun (x, t) => s!" ({x} : {ty t})")
  let regs := o.regions.toList.map fun r => s!"(&{r.name}{params r.params} : {ty r.ret})"
  let succs := o.succs.toList.map fun k =>
    let ps := String.join (k.payload.toList.map fun t =>
      match t with
      | .list _ => s!" (*_ : {ty t})"
      | _ => s!" (_ : {ty t})")
    if k.payload.isEmpty then s!"(^{k.name})" else s!"(^{k.name}{ps})"
  let head := (if o.ret.isNone then "terminal insn " else "insn ") ++
    o.envName.toString (escape := false)
  let ret := (o.ret.map fun t => [s!": {ty t}"]).getD []
  " ".intercalate (head :: tps ++ args ++ var ++ regs ++ succs ++ ret)

/-- The Lean name of a declaration: `owner ++ lean`. -/
def TypeInfo.fullName (t : TypeInfo) : Name := t.owner ++ t.lean

@[inherit_doc TypeInfo.fullName]
def OpInfo.fullName (o : OpInfo) : Name := o.owner ++ o.lean

/-- A declaration a record holds: a type or an instruction, with the record that declares
it. -/
inductive DeclInfo where
  | type (entry : EnvEntry) (info : TypeInfo)
  | op (entry : EnvEntry) (info : OpInfo)

/-- The declaration whose Lean name is `full`, such as `Strata.Dyn.Base.Int` or
`Strata.Dyn.Base.Except.ok`: the record of the longest prefix of `full` that names an
environment, and its type or instruction with the rest as its Lean name. -/
def findDecl? (env : Environment) (full : Name) : Option DeclInfo :=
  go full.getPrefix
where
  go : Name → Option DeclInfo
    | .anonymous => none
    | ns@(.num p _) => (findEntry? env ns).bind (lookup ns) <|> go p
    | ns@(.str p _) => (findEntry? env ns).bind (lookup ns) <|> go p
  lookup (ns : Name) (e : EnvEntry) : Option DeclInfo :=
    let rel := full.replacePrefix ns .anonymous
    match e.types.find? (·.lean == rel) with
    | some t => some (.type e t)
    | none => (e.ops.find? (·.lean == rel)).map (.op e)

/-- Every type of `ns` and its ancestors, farthest ancestor first, in declaration order. -/
def allTypes (env : Environment) (ns : Name) : Array TypeInfo :=
  (ancestry env ns).reverse.flatMap (·.types)

/-- Every instruction of `ns` and its ancestors, farthest ancestor first, in declaration
order. -/
def allOps (env : Environment) (ns : Name) : Array OpInfo :=
  (ancestry env ns).reverse.flatMap (·.ops)

end Strata.Dyn.DSL

end
