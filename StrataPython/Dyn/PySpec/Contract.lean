/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Check
public import StrataPython.Dyn.PySpec.Emit
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Contracts of externs

`planFunction` gives a model function's contract as checked clauses, in the order of
`docs/PythonToDyn.md` §12.2 and §12.3, and its frame (§12.5). `emitExtern` writes the plan
as an extern of the IR. The synthesized externs of §12.1 (`__init__`, the `__getattr__`s and an
overload set's dispatch) have their own plans.
-/

namespace StrataPython.Dyn.PySpec

open Strata.Dyn
open StrataPython.Specs
open StrataPython.Dyn.PyBuild
open StrataDDM (SourceRange)

public section

/-- Where a clause comes from. -/
inductive ClauseKind where
  /-- The binding clause of §12.2. -/
  | binding
  /-- The presence clause of a parameter. -/
  | presence (param : String)
  /-- The declared-type clause of a parameter. -/
  | paramType (param : String)
  /-- An `@admit` clause. -/
  | admitted
  /-- Any other clause: a schema, a precondition, a return type. -/
  | other
deriving Inhabited, BEq

/-- A clause: its message, its condition, and where it comes from. -/
structure ClausePlan where
  message : String
  body : CExpr
  kind : ClauseKind := .other
deriving Inhabited

/-- An extern's contract, checked. -/
structure ContractPlan where
  requires : Array ClausePlan := #[]
  /-- The `free ensures` clauses. A clause holds on a raise. -/
  ensures : Array ClausePlan := #[]
  writes : Array FrameLoc := #[]
  /-- Whether the extern has no frame at all, so that a call may change any location. -/
  anyWrites : Bool := false
deriving Inhabited

/-- The text of an assert's message, its f-string parts as their source text (§12.2). -/
def messageText (parts : Array MessagePart) : String :=
  String.join (parts.map fun
    | .str s => s
    | .expr _ src => s!"\{{src}}"
    | .untranslated src => s!"\{{src}}").toList

/-- Run a check in `ctx` with `role`. -/
def withRole {β : Type} (role : Role) (m : CheckM β) : CheckM β :=
  withReader ({ · with role }) m

/-- The declared type of a checked value, or the model class of an instance (§12.5: "the
declared types are those of the parameters, of the fields and of the ghosts"). -/
inductive ValueType where
  | spec (tp : SpecType)
  | cls (c : ModelClass)

/-- The type of the field `f` that `c` or a model base of it declares. -/
def ModelClass.fieldType? (t : Table) (c : ModelClass) (f : String) (fuel : Nat := t.baseDepth) :
    Option SpecType :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match c.decl.fields.find? (·.name == f) with
    | some fd => some fd.type
    | none => c.decl.bases.findSome? fun b => (t.classOf? b).bind (·.fieldType? t f fuel)

/-- The declared type of `e`, where the declarations give it: a parameter, `result`, a ghost,
a field of a model class, or an item of a declared container. -/
def valueType? (e : CExpr) : CheckM (Option ValueType) := do
  let ctx ← read
  match e with
  | .param p =>
    if let some c := ctx.owner then
      if ctx.decl.args.args[0]?.map (·.name) == some p.name then return some (.cls c)
    return (ctx.decl.paramType? p.name).map .spec
  | .result => return some (.spec ctx.decl.returnType)
  | .ghost m n =>
    -- Only an invariant states a ghost's type (§12.5).
    let g := (ctx.table.ghosts m).find? (·.name == n)
    return (g.bind (ghostInvariantType? ctx.table)).map .spec
  | .attr a f =>
    let cls := match ← valueType? a with
      | some (.cls c) => some c
      | some (.spec tp) => modelClassOf? ctx.table tp
      | none => none
    return (cls.bind (·.fieldType? ctx.table f)).map .spec
  | .item a k =>
    let some (.spec tp) ← valueType? a | return none
    if let .str f := k then
      if let some ft := tp.lookupTypedDictField f then return some (.spec ft)
    if let some (_, v) := mappingItems? tp then return some (.spec v)
    return (sequenceElement? tp).map .spec
  | _ => return none

/-- Whether every value of the declared type `tp` is an `int`, `float`, `complex`, `bool`, `str`,
`bytes` or `None`. The values of these exact classes read no other state in comparisons and
arithmetic; a subclass may, which the rule leaves to §12.4's "reading a parameter itself is
not a read of state". -/
def isScalarType (t : Table) (tp : SpecType) : Bool :=
  let a := typeAtoms t tp
  !a.any && !a.untestable &&
    a.classes.all fun
      | .std "builtins" n => ["int", "float", "complex", "bool", "str", "bytes"].contains n
      | _ => false

/-- Whether every value of the declared type `tp` is an object that is neither a class nor a
module: every atom is `None`, a literal, a model class (§12.11 rejects a program class that
derives from one and from `type` or `ModuleType`), or a class of `builtins` that no class or
module is an instance of. An abstract class such as `collections.abc.Sequence` is not enough: a
class whose metaclass derives from it is an instance of it. -/
def isObjectType (t : Table) (tp : SpecType) : Bool :=
  let a := typeAtoms t tp
  !a.any && !a.untestable && a.classes.all fun
    | .std "builtins" n => n != "object" && n != "type"
    | .std .. => false
    | .model _ => true

/-- Whether the declared types show that `e` and every container of its path are neither a
class nor a module (§12.5). -/
def containersAreObjects (e : CExpr) : CheckM Bool := do
  let own ← match ← valueType? e with
    | some (.cls _) => pure true
    | some (.spec tp) => pure (isObjectType (← read).table tp)
    | none => pure false
  match e with
  | .attr a _ | .item a _ => return own && (← containersAreObjects a)
  | _ => return own

/-- Whether `e` is what an argument reaches along a path of items and declared fields, every
object on it being neither a class nor a module: covered state (§12.4). -/
def argReached (e : CExpr) : CheckM Bool := do
  let rec rooted : CExpr → Bool
    | .param _ => true
    | .attr a _ | .item a _ => rooted a
    | _ => false
  return rooted e && (← containersAreObjects e)

/-- The locations of a target that names a slot of `sub` (§12.5): `own`, the slot's own
locations, and `values`, the reads of the values that the slot holds. A target rooted at a ghost
also gives the ghost's cell and what its object reaches. When the declared types show that every
container is neither a class nor a module, the argument or ghost regions hold the slot and its
value already, so the target gives its own location only where computing it needs no raising
read. -/
def slotTarget (sub : CExpr) (own : Array FrameLoc) (values : Array CExpr) :
    CheckM (Array FrameLoc) := do
  let rec root : CExpr → Option CExpr
    | .attr a _ | .item a _ => root a
    | e => some e
  let ghostLocs : Array FrameLoc := match root sub with
    | some (.ghost m n) => #[.ghostCell m n, .reach (.ghost m n)]
    | _ => #[]
  if ← containersAreObjects sub then
    let direct := match sub with
      | .param _ | .ghost .. => true
      | _ => false
    return ghostLocs ++ (if direct then own else #[])
  return ghostLocs ++ own ++ values.map .reach

/-- The frame locations of a `@modifies` target (§12.5). -/
def frameTarget (e : SpecExpr) : CheckM (Array FrameLoc) := do
  let ctx ← read
  match e with
  | .var n loc =>
    if (ctx.decl.paramRef? n).isSome then
      return #[.obj (← checkExpr e)]
    if (ctx.table.ghosts ctx.module).any (·.name == n) then
      return #[.ghostCell ctx.module n, .reach (.ghost ctx.module n)]
    let _ ← reject "frame-target" s!"@modifies of '{ctx.display}' names '{n}', which is neither a parameter nor a ghost" loc
    return #[]
  | .getIndex s f _ =>
    let sub ← checkExpr s
    -- The target is an attribute or an item by the rule for `s.f`; where that rule can't
    -- decide, it gives both, which is larger. `decided` runs `checkExpr` on the whole target
    -- only to learn which one the rule picks, and drops that run's rejections. That is safe:
    -- `sub` above reports every problem of the subject, and the rule's own rejection,
    -- `attr-or-item`, means only that it can't decide, which gives both locations here.
    let decided := (((checkExpr e).run ctx).run {}).1
    match decided with
    | .attr _ _ => slotTarget sub #[.attr sub f] #[.attr sub f]
    | .item _ _ => slotTarget sub #[.item sub f] #[.item sub (.str f)]
    | _ => slotTarget sub #[.attr sub f, .item sub f] #[.attr sub f, .item sub (.str f)]
  | .getItem s k _ =>
    let sub ← checkExpr s
    let key ← checkExpr k
    slotTarget sub #[.obj sub] #[.item sub key]
  | _ =>
    let _ ← reject "frame-target" s!"@modifies of '{ctx.display}' has a target that §12.5 can't represent" e.loc
    return #[]

/-- The paths that a frame covers: each location's value, by which the old-part check of §12.4
decides whether a read is covered. -/
structure Covered where
  /-- Values whose own locations are in the frame (`py.objLoc`). -/
  own : Array CExpr := #[]
  /-- Values all of whose reached locations are in the frame (`py.reachLoc`). -/
  reach : Array CExpr := #[]
  /-- The ghosts whose cells are in the frame. -/
  ghosts : Array (String × String) := #[]
  /-- Attribute and item reads whose slots are in the frame (`py.attrLoc`, `py.itemLoc`). What
      is rooted at them is covered too, as a target's (§12.4). -/
  slots : Array CExpr := #[]

/-- A path of attributes and string items from a parameter, a binder or a ghost, as text, to
compare paths. -/
def CExpr.path? : CExpr → Option String
  | .param p => some s!"param {p.name}"
  | .binder n => some s!"binder {n}"
  | .ghost m n => some s!"ghost {m}.{n}"
  | .attr e f => (e.path?).map (s!"{·}.{f}")
  | .item e (.str k) => (e.path?).map (s!"{·}[{k}]")
  | _ => Option.none

/-- Whether the frame covers what reading `e`'s own state reads. -/
def Covered.covers (c : Covered) (e : CExpr) : Bool :=
  match e.path? with
  | Option.none => false
  | some p =>
    let prefixOf (q : CExpr) := (q.path?).any fun q => p == q || p.startsWith (q ++ ".") ||
      p.startsWith (q ++ "[")
    c.own.any (fun q => q.path? == some p) || c.slots.any prefixOf || c.reach.any prefixOf

/-- Reject an old part that reads state outside covered state (§12.4): what a `@modifies` target
names and what is rooted at it, and what an argument reaches along a path of items and declared
fields of objects that are neither classes nor modules. For example, a ghost's contents that
`@modifies` doesn't list, an undeclared attribute, a class's attribute, or the contents of an
operand of a comparison or an arithmetic operator that is not a scalar. Reading a parameter
itself is not a read of state. -/
def checkOldPart (c : Covered) (e : CExpr) (loc : SourceRange) : CheckM Unit := do
  let ctx ← read
  let bad (what : String) : CheckM Unit := do
    let _ ← reject "old-uncovered" s!"an OLD of '{ctx.display}' reads {what}, which isn't covered state, so the clause would assume false" loc
  let covered (e : CExpr) : CheckM Bool := do return c.covers e || (← argReached e)
  let rec scalar (e : CExpr) : CheckM Bool := do
    match e with
    | .int _ | .float _ | .bool _ | .none | .str _ | .len _ | .const _ => return true
    | .neg a => scalar a
    | .arith _ a b => return (← scalar a) && (← scalar b)
    | _ => match ← valueType? e with
      | some (.spec tp) => return isScalarType ctx.table tp
      | _ => return false
  let operand (a : CExpr) : CheckM Unit := do
    unless (← scalar a) || (← covered a) do bad "a value whose contents an operator may read"
  let rec go (e : CExpr) : CheckM Unit := do
    match e with
    | .ghost m n => unless c.ghosts.contains (m, n) do bad s!"the ghost '{n}'"
    | .attr a _ =>
      unless ← covered e do bad "an attribute that is not a declared field of an argument or a target"
      -- A slot that the frame covers may change, whatever the reads that locate it.
      unless c.covers e do go a
    | .item a k =>
      unless (← covered e) || (← covered a) do bad "an item of a container"
      unless c.covers e do go a
      go k
    | .len a | .contains _ a => unless ← covered a do bad "the members of a container"
                                go a
    | .quant _ coll body => unless ← covered coll do bad "the members of a container"
                            go coll; go body
    | .isInstance a (.model _) | .typeTest a _ | .subclassOf a _ =>
      bad "a model class, which is a module global"; go a
    | .isInstance a _ | .neg a | .isNone a _ | .reSearch _ a | .enum a _ | .notEnum a _
    | .strIsOneOf a _ | .intIsOneOf a _ | .isDefined a | .not a | .old a => go a
    | .cmp op a b =>
      -- `in` reads the members of its right operand; any operator may read the contents of an
      -- operand that is not a scalar, as `==` on lists does.
      if op == "in_" || op == "notIn" then
        unless ← covered b do bad "the members of a container"
      else operand b
      operand a; go a; go b
    | .arith _ a b => operand a; operand b; go a; go b
    | .and a b | .or a b | .implies a b => go a; go b
    | _ => pure ()
  go e

/-- The parameter that a frame target is rooted at: `x` of `x`, `x.f` or `x["k"]`. -/
def frameRoot? : SpecExpr → Option String
  | .var n _ => some n
  | .getIndex s _ _ | .getItem s _ _ => frameRoot? s
  | _ => none

/-- The built-in class that tests an abstract container type, for a parameter that a frame
target is rooted at (§12.5, *Abstract containers*). -/
def concreteContainer? (tp : SpecType) : Option ClassRef :=
  match tp.atoms with
  | #[.ident id _] =>
    let s := toString id
    if s == "typing.Mapping" || s == "typing.MutableMapping" then some (builtin "dict")
    else if s == "typing.Sequence" || s == "typing.MutableSequence" then some (builtin "list")
    else none
  | _ => none

/-- The requires clauses of §12.2's steps 1 to 4 for the function: binding, presence, declared
types and schemas. `skipBinding` leaves out step 1, which an overload's extern states once. -/
def signatureClauses (skipBinding : Bool := false) : CheckM (Array ClausePlan) := do
  let ctx ← read
  let d := ctx.decl
  let named := d.namedParams
  let mut out : Array ClausePlan := #[]
  unless skipBinding do
    out := out.push { message := s!"arguments bind to '{ctx.display}'", kind := .binding
                      body := .bindsTo d.args.args.size d.args.kwargs.isSome named }
  for a in d.args.args ++ d.args.kwonly do
    if a.default.isNone then
      let some p := d.paramRef? a.name | continue
      out := out.push { message := s!"'{a.name}' is required", kind := .presence a.name
                        body := .isDefined (.param { p with noneDefault := false }) }
  let isMethod := ctx.owner.isSome
  for i in [0:d.args.args.size + d.args.kwonly.size] do
    let a := (d.args.args ++ d.args.kwonly)[i]!
    let some p := d.paramRef? a.name | continue
    let v := CExpr.param p
    if isMethod && i == 0 then
      if let some c := ctx.owner then
        out := out.push { message := s!"declared type of parameter '{a.name}'"
                          kind := .paramType a.name, body := .subclassOf v (.model c) }
      continue
    let roots := d.modifies.filterMap frameRoot?
    let concrete := if roots.contains a.name then concreteContainer? a.type else none
    let typeTest := match concrete with
      | some cls => some (CExpr.typeTest v #[cls])
      | none => paramTypeTest ctx.table a.type v
    match typeTest with
    | none => pure ()
    | some test =>
      let untestable := (typeAtoms ctx.table a.type).classes.isEmpty &&
        !(typeAtoms ctx.table a.type).none && (typeAtoms ctx.table a.type).strs.isEmpty &&
        (typeAtoms ctx.table a.type).ints.isEmpty
      let message := if untestable then
          s!"declared type of parameter '{a.name}' ({a.type}) has no runtime test"
        else s!"declared type of parameter '{a.name}'"
      let body := if a.default.isSome then .or (.isNone v true) test else test
      out := out.push { message, body, kind := .paramType a.name }
  for a in d.args.args ++ d.args.kwonly do
    let some p := d.paramRef? a.name | continue
    let v := CExpr.param p
    if let some s := schema ctx.table a.type v 0 8 then
      let body := if a.default.isSome then .or (.isNone v true) s else s
      out := out.push { message := s!"schema of parameter '{a.name}'", body }
  if let some (kn, .unpacked tp) := d.args.kwargs then
    if let some fields := tp.asTypedDict then
      if let some s := schema ctx.table tp (.extraKwargs named) 0 8 then
        out := out.push { message := s!"schema of parameter '{kn}'", body := s }
      out := out.push { message := s!"keywords of '{ctx.display}' are declared"
                        body := .kwargsWithin (named ++ fields.map (·.name)) }
  return out

/-- The `**kw` rule of §12.2: a TypedDict with `Unpack`, or `Any`; anything else rejects the
model. -/
def checkKwargs : CheckM Unit := do
  let ctx ← read
  if let some (kn, kt) := ctx.decl.args.kwargs then
    let isAny := kt.type.asIdent == some .typingAny
    let isUnpackedTypedDict := match kt with
      | .unpacked tp => tp.isTypedDict
      | .each _ => false
    unless isAny || isUnpackedTypedDict do
      let _ ← reject "kwargs-type" s!"the **{kn} of '{ctx.display}' is not Unpack of a TypedDict, so the model can't say what each keyword is" ctx.decl.loc

/-- The model frame of a function (§12.5): `py.instanceState`, what the arguments reach, and the
targets of `@modifies`. -/
def frameOf : CheckM (Array FrameLoc) := do
  let ctx ← read
  let targets ← withRole .frame (ctx.decl.modifies.mapM frameTarget)
  return #[.instanceState, .args, .kwargs] ++ targets.flatten

/-- What the frame `locs` covers. -/
def coveredBy (locs : Array FrameLoc) : Covered :=
  locs.foldl (init := {}) fun c l =>
    match l with
    | .obj e => { c with own := c.own.push e }
    | .reach e => { c with reach := c.reach.push e }
    | .ghostCell m n => { c with ghosts := c.ghosts.push (m, n) }
    | .attr e f => { c with slots := c.slots.push (.attr e f) }
    | .item e k => { c with slots := c.slots.push (.item e (.str k)) }
    -- A guarded location covers its target only where its condition holds.
    | .args | .kwargs | .instanceState | .guarded .. => c

/-- The special methods that may return `NotImplemented`: those of the binary operators, on either
side and in place, of the comparisons, and `__length_hint__`, whose `NotImplemented` makes
`operator.length_hint` give its default. -/
def notImplementedMethods : List String :=
  let ops := ["add", "sub", "mul", "matmul", "truediv", "floordiv", "mod", "pow", "lshift",
    "rshift", "and", "or", "xor"]
  ops.flatMap (fun o => [s!"__{o}__", s!"__r{o}__", s!"__i{o}__"]) ++
    ["__divmod__", "__rdivmod__", "__eq__", "__ne__", "__lt__", "__le__", "__gt__", "__ge__",
     "__length_hint__"]

/-- Reject a clause that uses a condition as a value, as `CExpr.condAsValue` says, whose CPython
value the IR's condition doesn't give. -/
def checkNoCondValue (e : CExpr) (loc : SourceRange) : CheckM Unit := do
  if e.condAsValue then
    let _ ← reject "condition-value" s!"a clause of '{(← read).display}' uses a condition, such as 'and', 'or' or a regex search, as a value" loc

/-- The contract of a model function (§12.2, §12.3, §12.5). -/
def planFunction : CheckM ContractPlan := do
  let ctx ← read
  let d := ctx.decl
  for dropped in d.dropped do
    -- `checkGhostInits` rejects a ghost's `init=` for every definition.
    if dropped.kind != .admit && dropped.kind != .ghostInit then
      let _ ← reject "dropped-clause" s!"PySpec dropped the {dropped.kind.tag} clause '{dropped.source}' of '{ctx.display}'" dropped.loc
  for e in d.postconditions do
    let _ ← reject "ensures" s!"'{ctx.display}' has an @ensures, which a model can't verify; use @admit" e.loc
  checkKwargs
  let sig ← withRole .pre (signatureClauses)
  let mut pre : Array ClausePlan := #[]
  for h : i in [0:d.preconditions.size] do
    let a := d.preconditions[i]
    let text := messageText a.message
    let message := if text.isEmpty then s!"precondition {i}" else text
    let body ← withRole .pre (checkExpr a.formula)
    checkNoCondValue body a.formula.loc
    pre := pre.push { message, body }
  let writes ← frameOf
  let covered := coveredBy writes
  let mut post : Array ClausePlan := #[]
  if let some test := returnTypeTest ctx.table d.returnType .result then
    -- A binary or comparison special method may return `NotImplemented`, whatever its declared
    -- type, so that CPython tries the other operand (§12.3).
    let test := if ctx.owner.isSome && notImplementedMethods.contains d.name then
        .or test (.isInstance .result (.std "types" "NotImplementedType"))
      else test
    post := post.push { message := s!"return type of '{ctx.display}'", body := test }
  for e in d.admittedPostconditions do
    let c ← withRole .post (checkExpr e)
    checkNoCondValue c e.loc
    let c := c.splitOld
    for part in c.oldContents do
      withRole .post (checkOldPart covered part e.loc)
    post := post.push { message := s!"admitted postcondition of '{ctx.display}'", body := c
                        kind := .admitted }
  return { requires := sig ++ pre, ensures := post, writes }

/-! ## Emission -/

/-- Run `body` with failures going to `fail`. A clause region never leaves through `Frame.exit`,
the exit of the Python builder's frame, so the exit given is the region's, unused. -/
def runIn {β : Type} (ctx : EmitCtx) (fail : PyTarget [Py.Value]) (body : EM β) :
    BuildM Py.env Info β :=
  Build.withExit Py.failing fun exit => Prod.fst <$> ((body.run ctx).run { handler := fail, exit })

/-- Run an emission in a clause region whose failures go to a failure block that gives
`onFail`. -/
def inClause (ctx : EmitCtx) (onFail : Bool) (body : EM Unit) : BuildM Py.env Info Unit :=
  Emit.withFailureBlock [Py.Value] (some onFail) fun fail => runIn ctx fail body

/-- The location set of `l`, in a frame region, with failures going to `unreachable`. -/
def emitLoc (l : FrameLoc) : EM ValId := do
  match l with
  | .guarded test inner => do
    -- The weaker reading of the test, so that it can't make the frame smaller.
    let c ← cond test false
    branchJoin c (emitLoc inner)
      (buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.instanceState.ref #[]))
      (ty := Base.Loc) (name := nm "l")
  | .instanceState => buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.instanceState.ref #[])
  | .obj e => do buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.objLoc.ref #[← value e])
  | .attr e f => do
    let v ← value e
    buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.attrLoc.ref #[v, ← strC f])
  | .item e k => do
    let v ← value e
    buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.itemLoc.ref #[v, ← strC k])
  | .ghostCell m n =>
    let cell ← buildPy (Build.emitGhost (ghostName m n) Py.Value)
    buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Base.cellLoc.ref #[cell]
      (typeArgs := ta[Py.Value]))
  | .args => do
    buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.reachLoc.ref #[(← read).args])
  | .kwargs => do
    buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.reachLoc.ref #[(← read).kwargs])
  | .reach e => do
    buildPy (Build.emitApply (env := Py.env) (nm "l") Base.Loc Py.reachLoc.ref #[← value e])

/-- Emit the extern `name` with the contract `plan`. -/
def emitExtern (name : Name) (plan : ContractPlan) (info : Info) :
    Except String {fn : Func Py.env Info // fn.WF} :=
  let params := #[(nm "args", Py.Value), (nm "kwargs", Py.Value)]
  let r := Build.buildExtern name params (Py.raising Py.Value) info fun ps => do
    let base : EmitCtx := { args := ps[0]!, kwargs := ps[1]! }
    for c in plan.requires do
      Build.requires (message := some c.message)
        (inClause base false do
          let b ← cond c.body true
          buildPy (Build.Raw.ret (env := Py.env) (α := Info) b))
    for c in plan.ensures do
      Build.ensures (nm "r") (Py.raising Py.Value) (free := true) (message := some c.message)
        fun r => inClause { base with requires := false, post := true } true do
          let okL ← liftPy (freshLabel [Py.Value] "ok")
          let raisedL ← liftPy (freshLabel [Py.Value] "raised")
          buildPy (Base.Except.case (Val.ofId (Py.raising Py.Value) r) okL.goto raisedL.goto)
          let res ← liftPy (startBlockWith okL (nm "result"))
          let b ← withReader ({ · with result := some res.id }) (cond c.body false)
          buildPy (Build.Raw.ret (env := Py.env) (α := Info) b)
          let _ ← liftPy (startBlockWith raisedL (nm "exc"))
          let t ← boolC true
          buildPy (Build.Raw.ret (env := Py.env) (α := Info) t)
    unless plan.anyWrites do
      Build.writes (plan.writes.map fun l => .region do
        Emit.withFailureBlock [Py.Value] none fun fail => do
          let v ← runIn base fail (emitLoc l)
          Build.Raw.ret (env := Py.env) (α := Info) v)
  match r with
  | .ok fn => .ok fn
  | .error e => .error (toString e)

end -- public section

end StrataPython.Dyn.PySpec
