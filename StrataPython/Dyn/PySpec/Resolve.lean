/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Std.Data.HashSet
public import StrataPython.Specs.Decls

set_option autoImplicit false

/-!
# The model table

A PySpec model set is a model module and every model module that it imports, each read into its
signatures. The translation to the IR (`docs/PythonToDyn.md` §12) first builds one table of
the set: what each name of each module is. Every later step looks names up here.

The table rejects a set that §12 cannot represent: two inputs with one module name, an import
cycle among the modules, and a nested class whose flattened name is ambiguous.
-/

namespace StrataPython.Dyn.PySpec

open StrataPython.Specs
open StrataDDM (SourceRange)

public section

/-- Why the translation rejects a model set: a rule ID, a message, and where in which module. -/
structure Rejection where
  rule : String
  message : String
  module : String := ""
  loc : SourceRange := .none
deriving Inhabited, Repr

/-- One PySpec module of a model set: its name, the format version of the file it was read
from (`none` for a file without one), and its signatures. -/
structure ModelInput where
  module : ModuleName
  version : Option Nat
  sigs : Array Signature
deriving Inhabited

/-- The modules whose names PySpec resolves without a model: its prelude. -/
def preludeModules : List String := ["builtins", "typing", "_types", "re"]

/-- Whether `id` names something of the standard library rather than of a model module. -/
def isStd (id : PythonIdent) : Bool := preludeModules.contains (toString id.pythonModule)

/-- A class of a model module. `path` is its path in the module, the outer classes first:
`#["Database", "_Exceptions"]` for a nested class. -/
structure ModelClass where
  module : String
  path : Array String
  decl : ClassDef
deriving Inhabited

/-- The class's name in the module, its path joined by dots, as Python's `__qualname__`. -/
def ModelClass.qualName (c : ModelClass) : String := ".".intercalate c.path.toList

/-- The fully qualified name of the class, `module.Outer.Inner`. -/
def ModelClass.fullName (c : ModelClass) : String := s!"{c.module}.{c.qualName}"

/-- What a name of a model module is. -/
inductive Entry where
  | cls (c : ModelClass)
  | func (overloads : Array FunctionDecl) (base : Option FunctionDecl)
  | alias (definition : SpecType)
  | ghost (g : Ghost)
  /-- A name that the module imports from another model module. -/
  | imported (source : PythonIdent)
deriving Inhabited

/-- The table: for each module, in input order, its names, the latest binding of each name
first. -/
structure Table where
  modules : Array (String × Array (String × Entry)) := #[]
  /-- The flattened PySpec name of each nested class, `module._C`, with its class. -/
  nested : Array (String × ModelClass) := #[]
  /-- The entries of `modules`, keyed by module and name. -/
  index : Std.HashMap (String × String) Entry := {}
  /-- The classes of `nested`, keyed by flattened name. -/
  nestedIndex : Std.HashMap String ModelClass := {}
  /-- The ghosts of each module. -/
  ghostIndex : Std.HashMap String (Array Ghost) := {}
deriving Inhabited

/-- A bound on the length of a chain of model bases: a base is declared before its subclass,
so a chain holds each class at most once. -/
def Table.baseDepth (t : Table) : Nat := t.index.size + t.nestedIndex.size + 1

/-- The entry for `name` in `module`. -/
def Table.find? (t : Table) (module name : String) : Option Entry :=
  t.index[(module, name)]?

/-- What `id` names, following imports through at most `fuel` modules. `fuel` bounds the
chain; the table has no cycles of imports, since the set has none. -/
def Table.resolve (t : Table) (id : PythonIdent) (fuel : Nat := 64) : Option Entry :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    match t.find? (toString id.pythonModule) id.name with
    | some (.imported src) => t.resolve src fuel
    | some e => some e
    | none => (t.nestedIndex[toString id]?).map .cls

/-- The model class that `id` names, if any. -/
def Table.classOf? (t : Table) (id : PythonIdent) : Option ModelClass :=
  match t.resolve id with
  | some (.cls c) => some c
  | _ => none

/-- The classes of `d` and the classes nested in it, at any depth, with their paths. -/
def nestedClasses (module : String) (path : Array String) (d : ClassDef) :
    Array ModelClass :=
  d.subclasses.attach.foldl (init := #[]) fun acc ⟨s, _⟩ =>
    let p := path.push s.name
    (acc.push { module, path := p, decl := s }) ++ nestedClasses module p s
termination_by sizeOf d
decreasing_by
  have hlt := Array.sizeOf_lt_of_mem ‹s ∈ d.subclasses›
  cases d
  simp only [ClassDef.mk.sizeOf_spec] at *
  omega

/-- The names a module binds, and its nested classes. An overload set and its non-overload
declaration are one entry; any other later binding of a name replaces the earlier one, as in
CPython. -/
def moduleEntries (m : ModelInput) : Array (String × Entry) × Array ModelClass := Id.run do
  let module := toString m.module
  -- Every binding in order, and the latest entry of each name.
  let mut binds : Array (String × Entry) := #[]
  let mut latest : Std.HashMap String Entry := {}
  let mut nested : Array ModelClass := #[]
  for sig in m.sigs do
    let bind (n : String) (e : Entry) := (binds.push (n, e), latest.insert n e)
    match sig with
    | .classDef d =>
      (binds, latest) := bind d.name (.cls { module, path := #[d.name], decl := d })
      nested := nested ++ nestedClasses module #[d.name] d
    | .functionDecl f =>
      let prev : Option Entry := latest[f.name]?
      let entry : Entry :=
        match prev, f.isOverload with
        | some (Entry.func ovs base), true => .func (ovs.push f) base
        | some (Entry.func ovs _), false => .func ovs (some f)
        | _, true => .func #[f] none
        | _, false => .func #[] (some f)
      (binds, latest) := bind f.name entry
    | .typeDef d => (binds, latest) := bind d.name (.alias d.definition)
    | .ghostDecl g => (binds, latest) := bind g.name (.ghost g)
    | .externTypeDecl n src =>
      unless isStd src do (binds, latest) := bind n (.imported src)
  -- The latest binding of each name, the latest first.
  let mut names : Array (String × Entry) := #[]
  let mut done : Std.HashSet String := {}
  for (n, e) in binds.reverse do
    unless done.contains n do
      names := names.push (n, e)
      done := done.insert n
  return (names, nested)

/-- The modules that `m` imports from, in order. -/
def importsOf (m : ModelInput) : Array String :=
  m.sigs.foldl (init := #[]) fun acc sig =>
    match sig with
    | .externTypeDecl _ src =>
      let mod := toString src.pythonModule
      if isStd src || acc.contains mod then acc else acc.push mod
    | _ => acc

/-- The modules outside the standard library that the type `tp` names, as in `M.C` after
`import M`. `fuel` bounds the nesting of type arguments. -/
def typeModules (tp : SpecType) (fuel : Nat := 16) : Array String :=
  match fuel with
  | 0 => #[]
  | fuel + 1 =>
    let ofIdents := tp.idents.foldl (init := #[]) fun acc si =>
      let acc := if isStd si.name then acc else acc.push (toString si.name.pythonModule)
      si.args.foldl (init := acc) fun acc a => acc ++ typeModules a fuel
    tp.typedDicts.foldl (init := ofIdents) fun acc td =>
      td.fieldTypes.foldl (init := acc) fun acc ft => acc ++ typeModules ft fuel

/-- The types that the function `d` declares. -/
def _root_.StrataPython.Specs.FunctionDecl.declaredTypes (d : FunctionDecl) : Array SpecType :=
  (d.args.args ++ d.args.kwonly).map (·.type) ++ (d.args.kwargs.map (·.2.type)).toArray ++ #[d.returnType]

/-- The types that the class `c` and its nested classes declare, and its bases as types. -/
def _root_.StrataPython.Specs.ClassDef.declaredTypes (c : ClassDef) : Array SpecType :=
  c.bases.map (SpecType.ident .none ·) ++ c.fields.map (·.type) ++
    c.methods.flatMap (·.declaredTypes) ++
    c.subclasses.attach.flatMap fun ⟨s, _⟩ => s.declaredTypes
termination_by sizeOf c
decreasing_by
  have hlt := Array.sizeOf_lt_of_mem ‹s ∈ c.subclasses›
  cases c
  simp only [ClassDef.mk.sizeOf_spec] at *
  omega

/-- The modules outside the standard library that the types of `m` name, other than `m` and the
modules it imports from. A model set reads them when PySpec wrote them, as for `import M`. -/
def typeReferences (m : ModelInput) : Array String :=
  let types := m.sigs.flatMap fun
    | .functionDecl d => d.declaredTypes
    | .classDef c => c.declaredTypes
    | .typeDef d => #[d.definition]
    | .ghostDecl g => g.type.toArray
    | .externTypeDecl .. => #[]
  let own := toString m.module
  let froms := importsOf m
  (types.flatMap (typeModules ·)).foldl (init := #[]) fun acc mod =>
    if mod == own || froms.contains mod || acc.contains mod then acc else acc.push mod

/-- Whether the import graph `graph` has a cycle that reaches `start` again. -/
def reachesItself (graph : Array (String × Array String)) (start : String) : Bool :=
  let next (m : String) := ((graph.find? (·.1 == m)).map (·.2)).getD #[]
  -- Breadth-first over at most `graph.size` rounds: a cycle through `start` has at most that
  -- many edges.
  let rec go (fuel : Nat) (frontier seen : Array String) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      let succs := frontier.foldl (init := #[]) fun acc m => acc ++ next m
      if succs.contains start then true
      else
        let fresh := succs.filter (!seen.contains ·)
        if fresh.isEmpty then false else go fuel fresh (seen ++ fresh)
  go (graph.size + 1) #[start] #[start]

/-- The table of the model set `inputs`, or why the set is rejected. -/
def buildTable (inputs : Array ModelInput) : Except (Array Rejection) Table := Id.run do
  let mut rejections : Array Rejection := #[]
  let mut seen : Array String := #[]
  for m in inputs do
    let name := toString m.module
    if seen.contains name then
      rejections := rejections.push
        { rule := "duplicate-module", module := name, message := s!"two inputs are the module '{name}'" }
    seen := seen.push name
  let graph := inputs.map fun m => (toString m.module, importsOf m)
  for (name, _) in graph do
    if reachesItself graph name then
      rejections := rejections.push
        { rule := "import-cycle", module := name
          message := s!"the model module '{name}' imports itself through other model modules" }
  let mut table : Table := {}
  for m in inputs do
    let module := toString m.module
    let (names, nested) := moduleEntries m
    -- `names` has the latest binding first; the ghosts go in declaration order.
    let ghosts := (names.filterMap fun | (_, .ghost g) => some g | _ => none).reverse
    table := { table with
      modules := table.modules.push (module, names)
      index := names.foldl (init := table.index) fun i (n, e) => i.insert (module, n) e
      ghostIndex := table.ghostIndex.insert module ghosts }
    for c in nested do
      let flat := s!"{c.module}.{c.decl.name}"
      if table.nestedIndex.contains flat || (table.index.contains (module, c.decl.name)) then
        rejections := rejections.push
          { rule := "ambiguous-nested-class", module := c.module, loc := c.decl.loc
            message := s!"the nested class '{c.qualName}' has the flattened name '{flat}', which another class of the module has too" }
      table := { table with
        nested := table.nested.push (flat, c), nestedIndex := table.nestedIndex.insert flat c }
  if rejections.isEmpty then return .ok table else return .error rejections

end -- public section

end StrataPython.Dyn.PySpec
