/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Contract
public import StrataPython.Dyn.PySpec.Mro
public import StrataDyn.WF
public import StrataPython.Specs.DDM
public import StrataDyn.DDM
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Model modules

`translateModels` turns a PySpec model set into modules of the IR, one per PySpec module, by
`docs/PythonToDyn.md` §12.1: a module body that binds the module's names, a class body
function for each class with the class's facts (§12.10), an extern for each function and
method, the synthesized externs, the ghosts, and a predicate for each class invariant
(§12.6). Any rejection rejects the whole set.
-/

namespace StrataPython.Dyn.PySpec

open Strata.Dyn
open StrataPython.Specs
open StrataPython.Dyn.PyBuild
open StrataDDM (SourceRange)

public section

/-- The IR name of the dotted name `s`, one segment per component. -/
def dottedName (s : String) : Name :=
  (s.splitOn ".").foldl (init := .base) fun n c => n.str c

/-- The IR name `module.seg₁.….segₙ`: a function of a module, or a method of a class. -/
def qualified (module : String) (segs : List String) : Name :=
  segs.foldl (init := dottedName module) Name.str

/-- A message part of the facts: a string attribute. -/
def strAttr (s : String) : AttrValue := .const (.str s)

/-- A record attribute. -/
def recAttr (fs : Array (String × AttrValue)) : AttrValue :=
  .record (fs.map fun (k, v) => (Name.base.str k, v))

/-- A key `py.k`. -/
def factKey (k : String) : Name := (Name.base.str "py").str k

/-- A declared type, as a fact (§12.10): a fully qualified name, `{name, args}` for a
generic, `{union = […]}` for a union, a literal as `{str = …}` or an integer, and
`{expr = "TypedDict"}` for a TypedDict, which the notation can't write. -/
def typeFact (t : Table) (tp : SpecType) (fuel : Nat := 16) : AttrValue :=
  match fuel with
  | 0 => recAttr #[("expr", strAttr "Type")]
  | fuel + 1 =>
    let atom : SpecAtomType → AttrValue := fun
      | .ident id args =>
        let n := match t.classOf? id with
          | some c => c.fullName
          | none => toString id
        if args.isEmpty then strAttr n
        else recAttr #[("name", strAttr n), ("args", .list (args.map (typeFact t · fuel)))]
      | .intLiteral i => .const (.int i)
      | .stringLiteral s => recAttr #[("str", strAttr s)]
      | .typedDict .. => recAttr #[("expr", strAttr "TypedDict")]
    match tp.atoms.toList with
    | [a] => atom a
    | as => recAttr #[("union", .list (as.toArray.map atom))]

/-- Whether the declared type `tp` accepts the literal `lit`, an int, bool, float or `None`. -/
def literalAccepted (t : Table) (tp : SpecType) (lit : SpecExpr) : Bool :=
  let a := typeAtoms t tp
  let has (n : String) : Bool := a.classes.any fun | .std "builtins" n' => n' == n | _ => false
  a.any || match lit with
    | .intLit i _ => has "int" || a.ints.contains i
    | .boolLit _ _ => has "bool" || has "int"
    | .floatLit _ _ => has "float"
    | .noneLit _ => a.none
    | _ => false

/-- The fact that states the literal `lit`, as `py.fields` writes a default. -/
def literalFact? : SpecExpr → Option AttrValue
  | .intLit i _ => some (.const (.int i))
  | .boolLit b _ => some (.const (.bool b))
  | .floatLit s _ => (floatOfText? s).map fun f => .const (.float f)
  | .noneLit _ => some (.const .unit)
  | _ => none

/-- The IR value of the literal `lit`. -/
def literalValue? : SpecExpr → Option (PyM Info ValId)
  | .intLit i _ => some (intLit i)
  | .boolLit b _ => some (boolLit b)
  | .floatLit s _ => (floatOfText? s).map floatLit
  | .noneLit _ => some noneLit
  | _ => none

/-- The facts of a model class's body (§12.10). -/
def classFacts (t : Table) (c : ModelClass) (initFn : Name)
    (invariants : Array AttrValue) : Array Attr := Id.run do
  let d := c.decl
  let mut attrs : Array Attr := #[]
  unless d.bases.isEmpty do
    attrs := attrs.push (factKey "bases", .list (d.bases.map fun b =>
      strAttr ((t.classOf? b).map (·.fullName) |>.getD (toString b))))
  let field (f : ClassField) : Array (String × AttrValue) :=
    #[("name", strAttr f.name), ("trustedType", typeFact t f.type)] ++
      ((f.value.bind literalFact?).map fun v => #[("default", v)]).getD #[]
  -- `py.fields` holds what the class body declares. A field that the stub's `__init__` assigns
  -- goes apart, in `py.initFields`, since no code states it.
  attrs := attrs.push (factKey "fields", .list ((d.fields.filter (·.source matches .body _)).map
    (recAttr ∘ field)))
  let initFields := d.fields.filter (·.source matches .init _)
  unless initFields.isEmpty do
    attrs := attrs.push (factKey "initFields", .list (initFields.map fun f =>
      recAttr ((field f).push ("in", .const (.func initFn)))))
  unless invariants.isEmpty do
    attrs := attrs.push (factKey "invariants", .list invariants)
  return attrs

/-- The names a model class's dictionaries along its model bases define, for the class
`__getattr__`'s `@exhaustive` test: its fields. -/
def ModelClass.declaredFields (t : Table) (c : ModelClass) (fuel : Nat := t.baseDepth) :
    Array String :=
  match fuel with
  | 0 => #[]
  | fuel + 1 =>
    c.decl.fields.map (·.name) ++ c.decl.bases.foldl (init := #[]) fun acc b =>
      match t.classOf? b with
      | some base => acc ++ base.declaredFields t fuel
      | none => acc

/-- What the translation of one module accumulates. -/
structure ModState where
  funcs : Array {fn : Func Py.env Info // fn.WF} := #[]
  ghosts : Array {g : Ghost Py.env Info // g.WF} := #[]
  rejections : Array Rejection := #[]

abbrev ModM := StateM ModState

/-- Record a rejection. -/
def ModM.reject (r : Rejection) : ModM Unit := modify fun s => { s with rejections := s.rejections.push r }

/-- Record a function, or an internal error if it could not be built. -/
def ModM.addFunc (module : String) (r : Except String {fn : Func Py.env Info // fn.WF}) :
    ModM Unit :=
  match r with
  | .ok fn => modify fun s => { s with funcs := s.funcs.push fn }
  | .error e => ModM.reject { rule := "internal", module, message := e }

/-- Run a check, recording its rejections. -/
def ModM.check {β : Type} (ctx : FnCtx) (m : CheckM β) : ModM β := do
  let (r, st) := (m.run ctx).run {}
  modify fun s =>
    { s with rejections := s.rejections ++ st.rejections }
  return r

/-- The display name of a function: `'f'`, or `'C.m'`. -/
def displayName (owner : Option ModelClass) (f : String) : String :=
  match owner with
  | some c => s!"{c.qualName}.{f}"
  | none => f

/-! ## Functions -/

/-- Translate the model function `d`, of the class `owner` if it is a method. -/
def translateFunction (t : Table) (module : String) (owner : Option ModelClass)
    (d : FunctionDecl) : ModM Unit := do
  let ctx : FnCtx := { table := t, module, display := displayName owner d.name, decl := d, owner }
  let plan ← ModM.check ctx planFunction
  let segs := (owner.map (·.path.toList)).getD [] ++ [d.name]
  ModM.addFunc module (emitExtern (qualified module segs) plan { range := d.loc })

/-- The dispatch literal of an overload stub: its first parameter's `Literal` string. -/
def dispatchLiteral? (d : FunctionDecl) : Option String :=
  d.args.args[0]? >>= (·.type.asStringLiteral)

/-- Guard each clause by `v == lit`, and name it for `lit`. -/
def guarded (v : CExpr) (lit : String) (cs : Array ClausePlan) : Array ClausePlan :=
  cs.map fun c =>
    { c with message := s!"{c.message} for '{lit}'", body := .implies (.enum v #[lit]) c.body }

/-- The synthesized extern of an overload set (§12.1, *Overloads*). -/
def translateOverloads (t : Table) (module name : String) (stubs : Array FunctionDecl)
    (base : Option FunctionDecl) : ModM Unit := do
  let some first := stubs[0]? | return
  let some dispatch := first.args.args[0]? | do
    ModM.reject
                  { rule := "overload-dispatch", module, loc := first.loc
                    message := s!"the overloads of '{name}' have no dispatch parameter" }
  let v : CExpr := .param { name := dispatch.name, pos := 0, noneDefault := false }
  -- Each stub's presence and type clauses of the dispatch parameter are left out below by that
  -- parameter's name, so every stub must give that name to its first parameter. So must the base,
  -- the signature that calls bind to at run time.
  for s in stubs do
    unless (s.args.args[0]?.map (·.name)) == some dispatch.name do
      ModM.reject
                    { rule := "overload-dispatch", module, loc := s.loc
                      message := s!"the overloads of '{name}' name their first parameter differently" }
  if let some b := base then
    unless (b.args.args[0]?.map (·.name)) == some dispatch.name do
      ModM.reject
                    { rule := "overload-dispatch", module, loc := b.loc
                      message := s!"the base of '{name}' names its first parameter differently from its overloads" }
  let mut lits : Array String := #[]
  for s in stubs do
    match dispatchLiteral? s with
    | some l =>
      -- Two stubs of one literal would give contradictory clauses for it.
      if lits.contains l then
        ModM.reject
                      { rule := "overload-dispatch", module, loc := s.loc
                        message := s!"two overloads of '{name}' dispatch on the literal '{l}'" }
      lits := lits.push l
    | none => ModM.reject
                            { rule := "overload-dispatch", module, loc := s.loc
                              message := s!"an overload of '{name}' doesn't dispatch on a string literal" }
  let sameParams (a b : FunctionDecl) :=
    a.args.args.map (·.name) == b.args.args.map (·.name) &&
    a.args.kwonly.map (·.name) == b.args.kwonly.map (·.name) &&
    a.args.kwargs.map (·.1) == b.args.kwargs.map (·.1)
  let common := stubs.all (sameParams first)
  let mut requires : Array ClausePlan := #[]
  let mut ensures : Array ClausePlan := #[]
  -- Without a base, the frame is the model frame plus the stubs' targets (§12.1).
  let mut writes : Array FrameLoc := #[.instanceState, .args, .kwargs]
  match base with
  | some b =>
    let plan ← ModM.check { table := t, module, display := name, decl := b } planFunction
    requires := requires ++ plan.requires
    ensures := ensures ++ plan.ensures
    writes := plan.writes
  | none =>
    if common then
      requires := requires.push
        { message := s!"arguments bind to '{name}'"
          body := .bindsTo first.args.args.size first.args.kwargs.isSome first.namedParams }
  requires := requires.push { message := s!"'{dispatch.name}' is required", body := .isDefined v }
  requires := requires.push { message := s!"'{name}' called with unknown string", body := .strIsOneOf v lits }
  for s in stubs do
    let some lit := dispatchLiteral? s | continue
    let ctx : FnCtx := { table := t, module, display := name, decl := s }
    let plan ← ModM.check ctx planFunction
    -- The dispatch parameter's binding, presence and type are stated above.
    -- A stub's binding clause is left out when it came first, or matches the base's.
    let skipBinding := match base with
      | some b => sameParams b s
      | none => common
    let own := plan.requires.filter fun c =>
      !(skipBinding && c.kind == .binding) && c.kind != .presence dispatch.name &&
      c.kind != .paramType dispatch.name
    requires := requires ++ guarded v lit own
    if let some test := returnTypeTest t s.returnType .result then
      ensures := ensures.push { message := s!"overload of '{name}' for '{lit}'"
                                body := .implies (.enum v #[lit]) test }
    -- A stub's `@admit` describes only the calls that select it (§12.13).
    ensures := ensures ++ (guarded v lit
      (plan.ensures.filter (·.kind == .admitted)))
    -- A stub's targets apply only where `v == lit`, as its clauses do: elsewhere they read
    -- parameters that the call may lack.
    writes := writes ++ (plan.writes.filterMap fun
      | .instanceState | .args | .kwargs => none
      | l => some (.guarded (.enum v #[lit]) l))
  ModM.addFunc module (emitExtern (qualified module [name]) { requires, ensures, writes }
    { range := first.loc })

/-! ## Classes -/

/-- The synthesized `__init__` of a class without one (§12.1): any arguments, `None` on return,
and the model frame with its receiver's reach. -/
def initPlan (c : ModelClass) : ContractPlan :=
  let self : CExpr := .param { name := "self", pos := 0, noneDefault := false }
  { requires := #[
      { message := "'self' is required", body := .isDefined self, kind := .presence "self" },
      { message := "declared type of parameter 'self'", body := .subclassOf self (.model c)
        kind := .paramType "self" }]
    ensures := #[{ message := s!"synthesized __init__ of '{c.qualName}'", body := .isNone .result true }]
    writes := #[.instanceState, .args, .kwargs] }

/-- The names of the overloaded methods that `c` or a model base of it declares, which have no
plain definition in their class. -/
def ModelClass.overloadedNames (t : Table) (c : ModelClass) (fuel : Nat := t.baseDepth) :
    Array String :=
  match fuel with
  | 0 => #[]
  | fuel + 1 =>
    let plain := c.decl.methods.filter (!·.isOverload) |>.map (·.name)
    let own := (c.decl.methods.filter (·.isOverload)).foldl (init := #[]) fun acc m =>
      if plain.contains m.name || acc.contains m.name then acc else acc.push m.name
    c.decl.bases.foldl (init := own) fun acc b =>
      match t.classOf? b with
      | some base => acc ++ base.overloadedNames t fuel
      | none => acc

/-- The class `__getattr__` (§12.1): an unknown value with no `ensures` clause and the frame
`writes()`; with `@exhaustive`, the requires clause that the name is one of the declared
fields or overloaded methods. -/
def classGetattrPlan (t : Table) (c : ModelClass) : ContractPlan :=
  let name : CExpr := .param { name := "name", pos := 1, noneDefault := false }
  if c.decl.exhaustive then
    { requires := #[{ message := s!"Unknown method of '{c.qualName}'"
                      body := .and (.isDefined name)
                        (.strIsOneOf name (c.declaredFields t ++ c.overloadedNames t)) }] }
  else {}

/-- An invariant's entry of `py.invariants`, and its predicate function if it has one
(§12.6). -/
def translateInvariant (t : Table) (c : ModelClass) (i : Nat) (inv : ClassInvariant) :
    ModM AttrValue := do
  let untranslated := recAttr #[("source", strAttr inv.source), ("untranslated", .const (.bool true))]
  let some formula := inv.formula | return untranslated
  let decl : FunctionDecl :=
    { loc := inv.loc, nameLoc := inv.loc, name := "<invariant>"
      args := { args := #[], kwonly := #[] }, returnType := default, isOverload := false
      preconditions := #[], postconditions := #[] }
  let ctx : FnCtx :=
    { table := t, module := c.module, display := c.qualName, decl, owner := some c
      role := .invariant inv.binder }
  let (body, st) := ((checkExpr formula).run ctx).run {}
  -- An invariant that §12 can't represent is recorded as its source text, not rejected.
  unless st.rejections.isEmpty && !body.condAsValue do return untranslated
  let ghosts := (t.ghosts c.module).filter fun g => body.ghostsRead.contains g.name
  let fname := (qualified c.module c.path.toList).str "<invariant>" |>.str (toString i)
  let params := #[(nm "self", Py.Value)] ++ ghosts.map fun g => (nm g.name, Py.Value)
  let r := Build.build fname Base.Bool { range := inv.loc } do
    let ps ← params.mapM fun (n, ty) => Build.freshVal n ty
    let _ ← Build.Raw.startFreshBlock ps "entry"
    let self := (ps.map (·.id))[0]!
    let ectx : EmitCtx :=
      { args := self, kwargs := self, requires := false
        binders := [(inv.binder, self)]
        ghostParams := (ghosts.toList.zip (ps.toList.drop 1)).map fun (g, p) =>
          ((c.module, g.name), p.id) }
    Emit.withFailureBlock [Py.Value] none fun fail => do
      let b ← runIn ectx fail (cond body false)
      Build.Raw.ret (env := Py.env) (α := Info) b
  match r with
  | .ok fn =>
    modify fun s => { s with funcs := s.funcs.push fn }
    let g : Array (String × AttrValue) := if ghosts.isEmpty then #[] else
      #[("ghosts", .list (ghosts.map fun g => .const (.ghost (ghostName c.module g.name))))]
    return recAttr (#[("fn", .const (.func fname))] ++ g)
  | .error e =>
    ModM.reject { rule := "internal", module := c.module, message := toString e }
    return untranslated

/-- The class that `self._C` names in an instance of `c` (§12.10): a nested class, or a class
variable bound to a class, in the first namespace along the MRO of `c` that binds `_C`. A method
named `_C` there names no class. -/
def initFieldClass? (t : Table) (c : ModelClass) (name : String) : Option ModelClass := Id.run do
  let classes := t.classes
  let listed : Std.HashMap ClassNode (Array ClassNode) := classes.foldl (init := {}) fun acc k =>
    acc.insert (.model k.module k.path) (k.decl.bases.map t.baseNode)
  let byNode : Std.HashMap ClassNode ModelClass := classes.foldl (init := {}) fun acc k =>
    acc.insert (.model k.module k.path) k
  let some mro := ((linearize (ClassNode.basesIn (listed[·]?)) (t.baseDepth + 3)
      (.model c.module c.path)).run' {}).run | return none
  -- The first namespace that binds the name decides, as CPython's lookup does.
  for n in mro do
    let some k := byNode[n]? | continue
    if k.decl.methods.any (·.name == name) then return none
    if let some s := k.decl.subclasses.find? (·.name == name) then
      return some { module := k.module, path := k.path.push name, decl := s }
    if let some cv := k.decl.classVars.find? (·.name == name) then
      if let some s := k.decl.subclasses.find? (·.name == cv.value) then
        return some { module := k.module, path := k.path.push cv.value, decl := s }
      if let some (.cls g) := t.find? k.module cv.value then return some g
      return none
  return none

/-- A binding that a model class body stores in its namespace. -/
inductive BodyBinding where
  /-- A method, or the externs of an overloaded name. -/
  | func (name : String)
  /-- A field with a value. -/
  | field (f : ClassField)
  | classVar (cv : ClassVariable)
  | nested (d : ClassDef)
deriving Inhabited

/-- The name that the binding `b` binds. -/
def BodyBinding.name : BodyBinding → String
  | .func n => n
  | .field f => f.name
  | .classVar cv => cv.name
  | .nested d => d.name

/-- The bindings of the class body `d`, in source order. An overloaded name is bound where its
first stub is. -/
def bodyBindings (d : ClassDef) : Array (Nat × BodyBinding) :=
  let funcs := d.methods.foldl (init := #[]) fun (acc : Array (Nat × BodyBinding)) m =>
    if acc.any (·.2.name == m.name) then acc else acc.push (m.loc.start.byteIdx, .func m.name)
  let fields := d.fields.filterMap fun f =>
    f.value.map fun _ => (f.loc.start.byteIdx, BodyBinding.field f)
  let all := funcs ++ fields ++ d.classVars.map (fun cv => (cv.loc.start.byteIdx, .classVar cv)) ++
    d.subclasses.map (fun s => (s.loc.start.byteIdx, .nested s))
  all.qsort (·.1 < ·.1)

/-- The class body function of `c`, whose module is being translated, and the externs and
predicates of its methods, nested classes and invariants. The body stores into `ns` the
synthesized externs, then the methods' closures, the field values, the class variables and the
nested classes in source order. -/
def translateClass (t : Table) (globals : Array String) (c : ModelClass) : ModM Unit := do
  let d := c.decl
  let segs := c.path.toList
  -- PySpec rejects two plain definitions of one name. An overloaded method without a plain
  -- definition is bound to an extern with no clause and no frame (§12.1).
  let methods := d.methods.filter (!·.isOverload)
  let overloaded := (d.methods.filter (·.isOverload)).foldl (init := #[]) fun acc m =>
    if methods.any (·.name == m.name) || acc.contains m.name then acc else acc.push m.name
  -- CPython calls a base's `__init_subclass__` when a subclass's class statement runs, so the
  -- module body, or a program's class statement, would run library code.
  if d.methods.any (·.name == "__init_subclass__") || d.classVars.any (·.name == "__init_subclass__") then
    ModM.reject
                  { rule := "init-subclass", module := c.module, loc := d.loc
                    message := s!"'{c.qualName}' declares __init_subclass__, which runs library code when a subclass is defined" }
  for m in d.methods.filter (·.isOverload) do
    let hasContract := !m.preconditions.isEmpty || !m.postconditions.isEmpty ||
      !m.admittedPostconditions.isEmpty || !m.modifies.isEmpty || !m.ghosts.isEmpty ||
      !m.dropped.isEmpty
    if hasContract then
      ModM.reject
                    { rule := "overload-method-contract", module := c.module, loc := m.loc
                      message := s!"the @overload stub '{c.qualName}.{m.name}' has a contract, which nothing would carry" }
  -- A `__getattr__` that the class or a model base declares replaces the synthesized one.
  let ownGetattr := c.declares t "__getattr__"
  -- A model base's `__init__` is inherited; only a class without one gets the synthesized one.
  let hasInit := c.declares t "__init__"
  for m in methods do
    translateFunction t c.module (some c) m
  -- A field from `self.f = self._C()` has the class that `self._C` names; the table reads the
  -- field's type `m._C` by its flattened name, so the two must agree.
  -- A name that the class body annotates twice must get the same type both times.
  let declared := d.fields.filter (·.source matches .body _)
  for h : i in [0:declared.size] do
    let f := declared[i]
    if let some g := (declared.extract (i + 1) declared.size).find? (·.name == f.name) then
      unless g.type == f.type do
        ModM.reject
                    { rule := "field-two-types", module := c.module, loc := d.loc
                      message := s!"the class body of '{c.qualName}' declares the field '{f.name}' both as '{f.type}' and as '{g.type}'" }
  for f in d.fields do
    let .init v := f.source | continue
    let name := (v.splitOn "(").head!
    let resolved := initFieldClass? t c name
    -- The class body may also declare the field; the two must name the same class.
    if let some decl := d.fields.find? fun g => g.name == f.name && g.source matches .body _ then
      let declared := decl.type.asIdent.bind t.classOf?
      unless resolved.isSome && (resolved.map (·.fullName)) == (declared.map (·.fullName)) do
        ModM.reject
                    { rule := "field-two-types", module := c.module, loc := d.loc
                      message := s!"the class body of '{c.qualName}' declares the field '{f.name}' as '{decl.type}', but its __init__ assigns it 'self.{v}'" }
    let byType := f.type.asIdent.bind t.classOf?
    unless resolved.isSome && (resolved.map (·.fullName)) == (byType.map (·.fullName)) do
      ModM.reject
                    { rule := "init-field-class", module := c.module, loc := d.loc
                      message := s!"the field '{f.name}' of '{c.qualName}' is 'self.{name}()', which names no class of the model, or another class than its type '{f.type}'" }
  for n in overloaded do
    ModM.addFunc c.module (emitExtern (qualified c.module (segs ++ [n])) { anyWrites := true }
      { range := d.loc })
  -- A nested class's body reads a model base of this module from the module's globals.
  for s in d.subclasses do
    for b in s.bases do
      if let some bc := t.classOf? b then
        if bc.module == c.module && !globals.contains bc.path[0]! then
          ModM.reject
                        { rule := "unbound-base", module := c.module, loc := s.loc
                          message := s!"the base '{b}' of '{c.qualName}.{s.name}' isn't bound when the class statement runs" }
  for ⟨s, _⟩ in c.decl.subclasses.attach do
    translateClass t globals { module := c.module, path := c.path.push s.name, decl := s }
  let initName := qualified c.module (segs ++ ["__init__"])
  let getattrName := qualified c.module (segs ++ ["__getattr__"])
  unless hasInit do
    ModM.addFunc c.module (emitExtern initName (initPlan c) { range := d.loc })
  unless ownGetattr do
    ModM.addFunc c.module (emitExtern getattrName (classGetattrPlan t c) { range := d.loc })
  let mut invariants : Array AttrValue := #[]
  for h : i in [0:d.invariants.size] do
    invariants := invariants.push (← translateInvariant t c i d.invariants[i])
  -- The class body stores its bindings in source order, and a class variable reads its value as
  -- a class body does: from the namespace as bound so far, then the module's globals bound
  -- before the class statement (`globals`), then the builtins. A value that isn't bound there
  -- rejects the model, since the module body must never raise.
  let bindings := bodyBindings d
  -- A class variable or a field's value needs its place among the other bindings.
  let placed (b : BodyBinding) : Bool := b matches .classVar _ | .field _
  let positions := bindings.map (·.1)
  for h : k in [0:bindings.size] do
    let (p, b) := bindings[k]
    if placed b && (positions.filter (· == p)).size > 1 then
      ModM.reject
                    { rule := "internal", module := c.module, loc := d.loc
                      message := s!"the model doesn't give the order of the class body of '{c.qualName}'" }
  -- A name bound twice would leave the class facts and the namespace apart, e.g. a method
  -- whose name a later class variable takes.
  let mut bound : Array String := #[]
  for (_, b) in bindings do
    -- The translation builds `__init__` and `__getattr__` from a method, or synthesizes them.
    if !(b matches .func _) && (b.name == "__init__" || b.name == "__getattr__") then
      ModM.reject
                    { rule := "special-binding", module := c.module, loc := d.loc
                      message := s!"the class body of '{c.qualName}' binds '{b.name}' other than with a def" }
    if bound.contains b.name then
      ModM.reject
                    { rule := "rebound-name", module := c.module, loc := d.loc
                      message := s!"the class body of '{c.qualName}' binds '{b.name}' more than once" }
    if let .classVar cv := b then
      unless bound.contains cv.value || globals.contains cv.value ||
          builtinClasses.contains cv.value do
        ModM.reject
                      { rule := "unresolved-name", module := c.module, loc := d.loc
                        message := s!"the class variable '{cv.name}' of '{c.qualName}' reads '{cv.value}', which neither the class body nor the module has bound when the class body reads it" }
    bound := bound.push b.name
  -- A field's value is a literal of the field's type.
  for f in d.fields do
    let some lit := f.value | continue
    if f.name.startsWith "__" && f.name.endsWith "__" then
      -- Class creation gives a meaning to such names, e.g. `__slots__` or `__init_subclass__`.
      ModM.reject
                    { rule := "field-value", module := c.module, loc := d.loc
                      message := s!"the field '{f.name}' of '{c.qualName}' has a value and a dunder name" }
    else if (literalValue? lit).isNone || (literalFact? lit).isNone then
      ModM.reject
                    { rule := "field-value", module := c.module, loc := d.loc
                      message := s!"the value of the field '{f.name}' of '{c.qualName}' is not a literal that the translation reads" }
    else if !literalAccepted t f.type lit then
      ModM.reject
                    { rule := "field-value", module := c.module, loc := d.loc
                      message := s!"the value of the field '{f.name}' of '{c.qualName}' doesn't have its declared type" }
  let bodyName := qualified c.module (segs ++ ["<body>"])
  let facts := classFacts t c initName invariants
  let r := buildFuncTyped bodyName #[(nm "args", Py.Value), (nm "kwargs", Py.Value)]
    { range := d.loc, attrs := facts } fun ps => do
    let zero ← intLit 0
    let ns ← emitFailing (nm "ns") Py.getItem.ref #[ps[0]!, zero]
    let store (n : String) (v : ValId) : PyM Info Unit := do
      let _ ← emitActing (nm "store") Py.setItem.ref #[ns, ← strLit n, v]
    store "__module__" (← loadGlobal c.module "__name__")
    store "__qualname__" (← strLit c.qualName)
    unless hasInit do store "__init__" (← funcValue initName)
    unless ownGetattr do store "__getattr__" (← funcValue getattrName)
    let mut known : Array String := #[]
    for (_, b) in bindings do
      match b with
      | .func n => store n (← funcValue (qualified c.module (segs ++ [n])))
      | .field f => if let some mk := f.value.bind literalValue? then store f.name (← mk)
      | .classVar cv =>
        let v ← if known.contains cv.value then
            emitFailing (nm cv.value) Py.getItem.ref #[ns, ← strLit cv.value]
          else loadGlobal c.module cv.value
        store cv.name v
      | .nested s =>
        let inner := qualified c.module (segs ++ [s.name, "<body>"])
        let bc ← emitFailing (nm "__build_class__") Py.qualifiedRef.ref
          #[← emitConst (nm "m") (.str "builtins"), ← emitConst (nm "n") (.str "__build_class__")]
        let clo ← funcValue inner
        let bases ← s.bases.mapM fun b => do match t.classOf? b with
          | some bc' => do
            let v ← requireGlobal bc'.module bc'.path[0]!
            bc'.path.toList.drop 1 |>.foldlM (init := v) fun acc seg => getAttr acc seg
          | none => emitFailing (nm b.name) Py.qualifiedRef.ref #[← emitConst (nm "m") (.str (toString b.pythonModule)), ← emitConst (nm "n") (.str b.name)]
        let tup ← emitTotal (nm "tuple") Py.mkTuple.ref (#[clo, ← strLit s.name] ++ bases)
        let kw ← emitTotal (nm "kwargs") Py.mkKwargs.ref #[]
        store s.name (← emitFailing (nm s.name) Py.call.ref #[bc, tup, kw])
      known := known.push b.name
    emitReturnNone
  ModM.addFunc c.module (r.mapError toString)
termination_by sizeOf c.decl
decreasing_by
  have hlt := Array.sizeOf_lt_of_mem ‹s ∈ c.decl.subclasses›
  have hsub : sizeOf c.decl.subclasses < sizeOf c.decl := by
    obtain ⟨_, _, ⟨_, _, _, _, _, _, _, _, _⟩⟩ := c
    simp only [ClassDef.mk.sizeOf_spec]
    omega
  omega

/-! ## Modules -/

/-- The ghost `g` of `module` (§12.1, *Module ghost*): its initializer, a literal, and its
invariant: `py.isDefined`, and the test of its declared type when every atom of the type has a
test of a standard class or `None`. -/
def translateGhost (t : Table) (module : String) (g : Ghost) : ModM Unit := do
  let stdOnly := (ghostInvariantType? t g).isSome
  -- The initializer is a literal, and an instance of a class that the declared type accepts.
  let lit? : Option (Option (PyM Info ValId)) := g.init.map literalValue?
  match lit?, g.type with
  | some none, _ =>
    ModM.reject
                  { rule := "ghost-initializer", module, loc := g.loc
                    message := s!"the initializer of the ghost '{g.name}' is not a literal" }
  | some (some _), some tp =>
    unless g.init.any (literalAccepted t tp) do
      ModM.reject
                    { rule := "ghost-initializer", module, loc := g.loc
                      message := s!"the initializer of the ghost '{g.name}' doesn't have its declared type" }
  | _, _ => pure ()
  let initBody : Option (BuildM Py.env Info Unit) := lit?.bind id |>.map fun lit => do
    let v ← Build.withExit Py.Value fun ret => Build.withExit Py.failing fun exit =>
      Prod.fst <$> lit.run { handler := ret, exit }
    Build.Raw.ret (env := Py.env) (α := Info) v
  -- Every ghost holds a Python value, never `py.undef`; a declared type of standard classes adds
  -- its test.
  let typeTest : Option CExpr := if stdOnly then
      g.type.map fun tp => (returnTypeTest t tp (.binder "v")).getD (.const true)
    else none
  let test := match typeTest with
    | some tt => CExpr.and (.isDefined (.binder "v")) tt
    | none => .isDefined (.binder "v")
  let invBody : Option (ValId → BuildM Py.env Info Unit) := some fun v => do
    Emit.withFailureBlock [Py.Value] none fun fail => do
      let ectx : EmitCtx := { args := v, kwargs := v, binders := [("v", v)], requires := false }
      let b ← runIn ectx fail (cond test false)
      Build.Raw.ret (env := Py.env) (α := Info) b
  match Build.ghost (ghostName module g.name) Py.Value initBody invBody { range := g.loc } with
  | .ok gh => modify fun s => { s with ghosts := s.ghosts.push gh }
  | .error e => ModM.reject { rule := "internal", module, message := toString e }

/-- Whether the model module `m` declares its own `__getattr__`, which replaces the synthesized
one. -/
def ModelInput.definesGetattr (m : ModelInput) : Bool :=
  m.sigs.any fun | .functionDecl f => f.name == "__getattr__" | _ => false

/-- The module body of `m` (§12.1): `__name__`, the names imported from other model modules,
the classes, the functions and the module `__getattr__`, in the order of the source. -/
def moduleBody (t : Table) (m : ModelInput) : Except String {fn : Func Py.env Info // fn.WF} :=
  let module := toString m.module
  (buildFuncTyped (qualified module ["<module>"]) #[] {} fun _ => do
    let _ ← writeGlobal module "__name__" (← strLit module)
    for sig in m.sigs do
      match sig with
      | .externTypeDecl n src =>
        unless isStd src do
          let _ ← writeGlobal module n (← importFrom (toString src.pythonModule) src.name)
      | .classDef d =>
        let c : ModelClass := { module, path := #[d.name], decl := d }
        let bc ← emitFailing (nm "__build_class__") Py.qualifiedRef.ref
          #[← emitConst (nm "m") (.str "builtins"), ← emitConst (nm "n") (.str "__build_class__")]
        let clo ← funcValue (qualified module [d.name, "<body>"])
        let bases ← d.bases.mapM fun b => do match t.classOf? b with
          | some bc' => readCell (← globalCell bc'.module bc'.path[0]!) (nm b.name)
          | none => emitFailing (nm b.name) Py.qualifiedRef.ref #[← emitConst (nm "m") (.str (toString b.pythonModule)), ← emitConst (nm "n") (.str b.name)]
        let tup ← emitTotal (nm "tuple") Py.mkTuple.ref (#[clo, ← strLit c.decl.name] ++ bases)
        let kw ← emitTotal (nm "kwargs") Py.mkKwargs.ref #[]
        let _ ← writeGlobal module d.name (← emitFailing (nm d.name) Py.call.ref #[bc, tup, kw])
      | .functionDecl f =>
        let _ ← writeGlobal module f.name (← funcValue (qualified module [f.name]))
      | _ => pure ()
    unless m.definesGetattr do
      let _ ← writeGlobal module "__getattr__" (← funcValue (qualified module ["__getattr__"]))
    emitReturnNone).mapError toString

/-- The overload stubs of the name `n` in `m`, and its last non-overload declaration. -/
def functionSet (m : ModelInput) (n : String) : Array FunctionDecl × Option FunctionDecl :=
  m.sigs.foldl (init := (#[], none)) fun (stubs, base) sig =>
    match sig with
    | .functionDecl f =>
      if f.name != n then (stubs, base)
      else if f.isOverload then (stubs.push f, base) else (stubs, some f)
    | _ => (stubs, base)

/-- The methods of `c` and of its nested classes, each with its qualified name, such as
`"C.Inner.m"`. -/
def classMethods (c : ClassDef) : Array (String × FunctionDecl) :=
  c.methods.map (fun f => (s!"{c.name}.{f.name}", f)) ++
    c.subclasses.attach.flatMap fun ⟨s, _⟩ =>
      (classMethods s).map fun (n, f) => (s!"{c.name}.{n}", f)
termination_by sizeOf c
decreasing_by
  have := Array.sizeOf_lt_of_mem ‹s ∈ c.subclasses›
  cases c; simp_all only [ClassDef.mk.sizeOf_spec]; omega

/-- Reject each function or method of `m` whose `@ghost` has an `init=` that runs at import.
CPython runs the decorators of every definition, also of one that a later definition of the
same name replaces, or of an overload stub, which the IR doesn't translate. -/
def checkGhostInits (m : ModelInput) : ModM Unit := do
  let decls := m.sigs.flatMap fun
    | .functionDecl f => #[(f.name, f)]
    | .classDef c => classMethods c
    | _ => #[]
  for (name, f) in decls do
    for d in f.dropped do
      if d.kind == .ghostInit then
        ModM.reject { rule := "dropped-clause", module := toString m.module, loc := d.loc
                      message := s!"PySpec dropped the {d.kind.tag} clause '{d.source}' of '{name}'" }

/-- The IR module of the model module `m`. -/
def translateModule (t : Table) (m : ModelInput) : ModM (Option (Module Py.env Info)) := do
  let module := toString m.module
  checkGhostInits m
  ModM.addFunc module (moduleBody t m)
  -- Every class and ghost of the source, also one whose name a later binding takes, since the
  -- module body still runs it; each function name once, as its last binding gives it.
  let mut done : Array String := #[]
  -- The names that the module body has bound so far.
  let mut globals : Array String := #["__name__"]
  for sig in m.sigs do
    match sig with
    | .externTypeDecl n src => unless isStd src do globals := globals.push n
    | .classDef d =>
      translateClass t globals { module, path := #[d.name], decl := d }
      globals := globals.push d.name
    | .ghostDecl g => translateGhost t module g
    | .functionDecl f =>
      globals := globals.push f.name
      unless done.contains f.name do
        done := done.push f.name
        let (stubs, base) := functionSet m f.name
        if stubs.isEmpty then
          if let some b := base then translateFunction t module none b
        else translateOverloads t module f.name stubs base
    | _ => pure ()
  unless m.definesGetattr do
    ModM.addFunc module (emitExtern (qualified module ["__getattr__"]) {} {})
  let s ← get
  match Module.ofChecked (dottedName module) s.funcs {} s.ghosts with
  | .ok mod => return some mod
  | .error bad =>
    ModM.reject
                  { rule := "duplicate-name", module
                    message := s!"the module defines a name twice or references one it doesn't define: {bad.map Build.nameText}" }
    return none

/-- The classes of `builtins` that CPython 3.12 accepts as a base of a class statement, less
the ones whose subclasses §12 doesn't model: `type`, and descriptors such as `property`. The
module body reads a standard-library base with `py.qualifiedRef`, which §2 allows only for
`builtins`. `StdBasesTest` checks the list against CPython. Another base, such as `bool` or
`typing.Protocol`, rejects the model. -/
def subclassableStd : Std.HashSet String := Std.HashSet.ofList [
    "builtins.ArithmeticError", "builtins.AssertionError", "builtins.AttributeError",
    "builtins.BaseException", "builtins.BaseExceptionGroup", "builtins.BlockingIOError",
    "builtins.BrokenPipeError", "builtins.BufferError", "builtins.BytesWarning",
    "builtins.ChildProcessError", "builtins.ConnectionAbortedError", "builtins.ConnectionError",
    "builtins.ConnectionRefusedError", "builtins.ConnectionResetError",
    "builtins.DeprecationWarning", "builtins.EOFError", "builtins.EncodingWarning",
    "builtins.EnvironmentError", "builtins.Exception", "builtins.ExceptionGroup",
    "builtins.FileExistsError", "builtins.FileNotFoundError", "builtins.FloatingPointError",
    "builtins.FutureWarning", "builtins.GeneratorExit", "builtins.IOError", "builtins.ImportError",
    "builtins.ImportWarning", "builtins.IndentationError", "builtins.IndexError",
    "builtins.InterruptedError", "builtins.IsADirectoryError", "builtins.KeyError",
    "builtins.KeyboardInterrupt", "builtins.LookupError", "builtins.MemoryError",
    "builtins.ModuleNotFoundError", "builtins.NameError", "builtins.NotADirectoryError",
    "builtins.NotImplementedError", "builtins.OSError", "builtins.OverflowError",
    "builtins.PendingDeprecationWarning", "builtins.PermissionError",
    "builtins.ProcessLookupError", "builtins.RecursionError", "builtins.ReferenceError",
    "builtins.ResourceWarning", "builtins.RuntimeError", "builtins.RuntimeWarning",
    "builtins.StopAsyncIteration", "builtins.StopIteration", "builtins.SyntaxError",
    "builtins.SyntaxWarning", "builtins.SystemError", "builtins.SystemExit", "builtins.TabError",
    "builtins.TimeoutError", "builtins.TypeError", "builtins.UnboundLocalError",
    "builtins.UnicodeDecodeError", "builtins.UnicodeEncodeError", "builtins.UnicodeError",
    "builtins.UnicodeTranslateError", "builtins.UnicodeWarning", "builtins.UserWarning",
    "builtins.ValueError", "builtins.Warning", "builtins.ZeroDivisionError", "builtins.bytearray",
    "builtins.bytes", "builtins.complex", "builtins.dict", "builtins.enumerate", "builtins.filter",
    "builtins.float", "builtins.frozenset", "builtins.int", "builtins.list", "builtins.map",
    "builtins.object", "builtins.reversed", "builtins.set", "builtins.str", "builtins.tuple",
    "builtins.zip"]

/-- The class statements of `m` that CPython can't run, so that the module body would raise
(§12.1), given the table `t` of its set and the bases that `listed` gives each of its classes:
* a class whose bases have no C3 order;
* which is stronger than CPython, a class whose MRO holds two standard-library classes other than
  `object`, whose layouts or orders may conflict;
* a class with a standard-library base outside `subclassableStd`;
* a class with a base of `m` whose name `m` binds more than once, since `t` gives only its last
  binding. -/
def classCreationRejections (t : Table) (listed : Std.HashMap ClassNode (Array ClassNode))
    (m : ModelInput) (cache : MroCache) : Array Rejection × MroCache := Id.run do
  let module := toString m.module
  -- Bases are declared before their subclasses, so a path of bases holds each class once,
  -- then a standard-library class and `object`.
  let fuel := t.baseDepth + 3
  -- The number of bindings of each global name, and the position of its last one.
  let bindings : Array (Nat × String) := m.sigs.mapIdx (·, ·) |>.filterMap fun (i, s) =>
    match s with
    | .classDef d => some (i, d.name)
    | .functionDecl f => some (i, f.name)
    | .typeDef d => some (i, d.name)
    | .externTypeDecl n src => if isStd src then none else some (i, n)
    | .ghostDecl _ => none
  let count : Std.HashMap String Nat :=
    bindings.foldl (init := {}) fun acc (_, n) => acc.insert n (acc.getD n 0 + 1)
  let last : Std.HashMap String Nat := bindings.foldl (init := {}) fun acc (i, n) => acc.insert n i
  let mut cache := cache
  let mut out : Array Rejection := #[]
  for h : i in [0:m.sigs.size] do
    let .classDef d := m.sigs[i] | continue
    let isLast := last[d.name]? == some i
    for c in #[{ module, path := #[d.name], decl := d : ModelClass }] ++ nestedClasses module #[d.name] d do
      let reject (rule message : String) :=
        out.push { rule, module, loc := c.decl.loc, message }
      for b in c.decl.bases do
        match t.baseNode b with
        | .std n =>
          unless subclassableStd.contains n do
            out := reject "class-base" s!"the base '{n}' of '{c.qualName}' is not a standard-library class known to accept subclasses"
        | .model bm bp =>
          if bm == module && count.getD bp[0]! 0 > 1 then
            out := reject "rebound-base" s!"the base '{b}' of '{c.qualName}' names a class whose name the module binds more than once"
      let node := ClassNode.model c.module c.path
      let bases := ClassNode.basesIn ((listed.insert node (c.decl.bases.map t.baseNode))[·]?)
      let (mro, cache') := (linearize bases fuel node).run (cache.erase node)
      -- A class that a later binding replaces isn't the table's class of its node.
      if isLast then cache := cache'
      match mro with
      | none => out := reject "class-mro" s!"CPython can't order the bases of '{c.qualName}'"
      | some mro =>
        let stds := mro.filterMap fun
          | .std n => if n == "builtins.object" then none else some n
          | _ => none
        if stds.length > 1 then
          out := reject "class-bases" s!"the MRO of '{c.qualName}' holds the standard-library classes {stds}, whose layouts may conflict"
  return (out, cache)

/-- A translated model set. -/
structure ModelSet where
  table : Table
  /-- One IR module per model module. -/
  modules : Array (Module Py.env Info)

/-- The translation of the model set `inputs`, or every reason the set is rejected. Signatures
from a file without the current format version are refused. -/
def translateModelSet (inputs : Array ModelInput) : Except (Array Rejection) ModelSet := do
  let stale := inputs.filter (·.version != some formatVersion)
  unless stale.isEmpty do
    throw (stale.map fun m =>
      { rule := "format-version", module := toString m.module
        message := s!"the signatures of '{m.module}' come from a file without format version {formatVersion}" })
  let table ← buildTable inputs
  let mut modules := #[]
  let mut rejections := #[]
  let mut cache : MroCache := {}
  let listed : Std.HashMap ClassNode (Array ClassNode) := table.classes.foldl (init := {})
    fun acc c => acc.insert (.model c.module c.path) (c.decl.bases.map table.baseNode)
  for m in inputs do
    let (rs, cache') := classCreationRejections table listed m cache
    rejections := rejections ++ rs
    cache := cache'
  for m in inputs do
    let (r, s) := (translateModule table m).run {}
    rejections := rejections ++ s.rejections
    if let some mod := r then modules := modules.push mod
  -- Two modules may give one IR name, such as a function `put_item` of `servicelib.Storage`
  -- and a method `put_item` of a class `Storage` of `servicelib`.
  let mut owner : Std.HashMap String String := {}
  for mod in modules do
    let mname := Build.nameText mod.raw.name
    for f in mod.raw.funcs do
      let n := Build.nameText f.name
      match owner[n]? with
      | some other =>
        rejections := rejections.push
          { rule := "name-clash", module := mname
            message := s!"the modules '{other}' and '{mname}' both give the name '{n}'" }
      | none => owner := owner.insert n mname
  if rejections.isEmpty then return { table, modules } else throw rejections

/-- The IR modules of the model set `inputs`, one per input, or every reason the set is
rejected. -/
def translateModels (inputs : Array ModelInput) :
    Except (Array Rejection) (Array (Module Py.env Info)) :=
  (·.modules) <$> translateModelSet inputs

end -- public section

end StrataPython.Dyn.PySpec
