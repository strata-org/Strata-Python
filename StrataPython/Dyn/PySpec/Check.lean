/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Clause
public import StrataPython.Dyn.Shape

set_option autoImplicit false

/-!
# Checking clauses

`checkExpr` turns a PySpec `SpecExpr` into a `CExpr` by the rules of
`docs/PythonToDyn.md` §12.4, and `typeTest` and `schema` give the declared-type tests of
§12.3. Each rule that §12 can't represent records a `Rejection` and gives `.const false` in its
place; the caller rejects the whole model set if any rejection was recorded, so that value is
never emitted.
-/

namespace StrataPython.Dyn.PySpec

open StrataPython.Specs
open StrataDDM (SourceRange)

public section

/-- The role of the clause being checked. -/
inductive Role where
  /-- A `requires` clause. -/
  | pre
  /-- A `free ensures` clause, which may read `result` and apply `OLD`. -/
  | post
  /-- A frame target of `@modifies`. -/
  | frame
  /-- A class invariant, whose parameter `binder` stands for the instance. -/
  | invariant (binder : String)
deriving Inhabited, BEq

/-- What a clause of one function sees. -/
structure FnCtx where
  table : Table
  module : String
  /-- The function's name in messages: `'f'`, or `'C.m'` for a method. -/
  display : String
  decl : FunctionDecl
  /-- The class of a method. -/
  owner : Option ModelClass := none
  role : Role := .pre
  /-- The quantifier binders in scope, innermost first, with their element types. -/
  binders : List (String × Option SpecType) := []
deriving Inhabited

/-- What checking clauses records. -/
structure CheckState where
  rejections : Array Rejection := #[]
deriving Inhabited

abbrev CheckM := ReaderT FnCtx (StateM CheckState)

/-- Record a rejection at `loc`, and give a placeholder that is never emitted. -/
def reject (rule message : String) (loc : SourceRange) : CheckM CExpr := do
  let ctx ← read
  modify fun s => { s with rejections := s.rejections.push { rule, message, module := ctx.module, loc } }
  return .const false

/-! ## Names -/

/-- The parameter `name` of the function, with its position. -/
def _root_.StrataPython.Specs.FunctionDecl.paramRef? (d : FunctionDecl) (name : String) : Option ParamRef :=
  match d.args.args.findIdx? (·.name == name) with
  | some i =>
    let a := d.args.args[i]!
    some { name, pos := i, noneDefault := a.default.isSome }
  | none =>
    (d.args.kwonly.find? (·.name == name)).map fun a =>
      { name, pos := -1, noneDefault := a.default.isSome }

/-- The names of the named parameters, in order: those that `py.extraKwargs` leaves out. -/
def _root_.StrataPython.Specs.FunctionDecl.namedParams (d : FunctionDecl) : Array String :=
  (d.args.args ++ d.args.kwonly).map (·.name)

/-- The declared type of the parameter `name`. -/
def _root_.StrataPython.Specs.FunctionDecl.paramType? (d : FunctionDecl) (name : String) : Option SpecType :=
  ((d.args.args ++ d.args.kwonly).find? (·.name == name)).map (·.type)

/-- The ghosts of the module `module`. -/
def Table.ghosts (t : Table) (module : String) : Array Ghost :=
  (t.ghostIndex[module]?).getD #[]

/-! ## Types -/

/-- The class `n` of `builtins`. -/
@[expose] def builtin (n : String) : ClassRef := .std "builtins" n

/-- What a declared type's atom tests, as §12.3's table gives it: the classes it accepts,
whether it accepts `None`, its literals, and whether it accepts anything. An atom without a
test accepts nothing here: the caller drops it, or gives no test when every atom lacks one. -/
structure AtomTest where
  classes : Array ClassRef := #[]
  none : Bool := false
  strs : Array String := #[]
  ints : Array Int := #[]
  any : Bool := false
  /-- Whether some atom has no runtime test. -/
  untestable : Bool := false

/-- The test of one named atom. -/
def identTest (t : Table) (id : PythonIdent) : AtomTest :=
  let s := toString id
  if s == "typing.Any" then { any := true }
  else if s == "_types.NoneType" then { none := true }
  else if s == "builtins.int" then { classes := #[builtin "int"] }
  else if s == "builtins.float" then { classes := #[builtin "float", builtin "int"] }
  else if s == "builtins.complex" then
    { classes := #[builtin "complex", builtin "float", builtin "int"] }
  else if ["builtins.bytes", "builtins.str", "builtins.bool", "builtins.bytearray",
      "builtins.dict", "builtins.Exception"].contains s then
    { classes := #[builtin id.name] }
  else if s == "typing.List" then { classes := #[builtin "list"] }
  else if s == "typing.Dict" then { classes := #[builtin "dict"] }
  else if s == "typing.Sequence" then { classes := #[.std "collections.abc" "Sequence"] }
  else if s == "typing.Mapping" then { classes := #[.std "collections.abc" "Mapping"] }
  else if s == "typing.MutableSequence" then
    { classes := #[.std "collections.abc" "MutableSequence"] }
  else if s == "typing.MutableMapping" then
    { classes := #[.std "collections.abc" "MutableMapping"] }
  else if s == "typing.Generator" then { classes := #[.std "collections.abc" "Generator"] }
  else if isStd id then { untestable := true }
  else match t.resolve id with
    | some (.cls c) => { classes := #[.model c] }
    | _ => { untestable := true }

/-- The longest chain of type aliases that a declared-type test, and a return type's schema,
follow. -/
def aliasChainBound : Nat := 16

/-- The test of a declared type, its atoms combined. `aliasFuel` bounds how many type aliases
an atom follows. -/
def typeAtoms (t : Table) (tp : SpecType) (aliasFuel : Nat := aliasChainBound) : AtomTest :=
  let one (acc : AtomTest) (a : AtomTest) : AtomTest :=
    { classes := acc.classes ++ a.classes, none := acc.none || a.none
      strs := acc.strs ++ a.strs, ints := acc.ints ++ a.ints, any := acc.any || a.any
      untestable := acc.untestable || a.untestable }
  tp.atoms.foldl (init := {}) fun acc atom =>
    match atom with
    | .ident id _ =>
      match aliasFuel, t.resolve id with
      | fuel + 1, some (.alias d) => one acc (typeAtoms t d fuel)
      | _, _ => one acc (identTest t id)
    | .intLiteral i => one acc { ints := #[i] }
    | .stringLiteral s => one acc { strs := #[s] }
    | .typedDict .. => one acc { classes := #[builtin "dict"] }
termination_by aliasFuel

/-- The disjunction of `cs`, or `false` for none. -/
@[expose] def disj (cs : Array CExpr) : CExpr :=
  match cs.toList with
  | [] => .const false
  | c :: rest => rest.foldl .or c

/-- The test of a parameter's declared type `tp` on `v` (§12.3): each class atom by
`py.typeIsSubclass` and then `py.isInstance`, together on one tuple; `None` by identity; the
literals by `py.strIsOneOf` and `py.intIsOneOf`. `none` when the type is `Any`. An atom without
a test is dropped, which is stronger; a type of only such atoms gives `false`. -/
def paramTypeTest (t : Table) (tp : SpecType) (v : CExpr) : Option CExpr :=
  let a := typeAtoms t tp
  if a.any then none
  else
    let parts := (if a.classes.isEmpty then #[] else #[CExpr.typeTest v a.classes]) ++
      (if a.none then #[CExpr.isNone v true] else #[]) ++
      (if a.strs.isEmpty then #[] else #[CExpr.strIsOneOf v a.strs]) ++
      (if a.ints.isEmpty then #[] else #[CExpr.intIsOneOf v a.ints])
    some (disj parts)

/-- The coarse test of a return type `tp` on `v` (§12.3): `py.isInstance` alone, a literal as
its class, `bytes` as `bytes`, `bytearray` or `memoryview`, and a model class as the pair of
`py.typeIsSubclass` and `py.isInstance`. `none` when there is no test: for `Any`, for `-> None`,
or when an atom has no test, since the whole union is then weaker, and `true`. -/
@[expose] def returnTypeTest (t : Table) (tp : SpecType) (v : CExpr) : Option CExpr :=
  let a := typeAtoms t tp
  if a.any || a.untestable then none
  else if a.classes.isEmpty && a.strs.isEmpty && a.ints.isEmpty then none
  else
    let classes := a.classes ++ (if a.strs.isEmpty then #[] else #[builtin "str"]) ++
      (if a.ints.isEmpty then #[] else #[builtin "int"])
    -- A `bytes` atom accepts `bytearray` and `memoryview` too, as PEP 484 promotes them; a
    -- model class gives the pair, by a trusted assumption (§12.3, §12.9).
    let classes := classes.flatMap fun
      | .std "builtins" "bytes" => #[builtin "bytes", builtin "bytearray", builtin "memoryview"]
      | c => #[c]
    let parts := classes.map (fun
        | .model c => CExpr.typeTest v #[.model c]
        | c => CExpr.isInstance v c) ++
      (if a.none then #[CExpr.isNone v true] else #[])
    some (disj parts)

/-- The element type of a `List[T]`, `Sequence[T]` or `MutableSequence[T]` (§12.3). -/
@[expose] def sequenceElement? (tp : SpecType) : Option SpecType :=
  match tp.atoms with
  | #[.ident id #[e]] =>
    if ["typing.List", "typing.Sequence", "typing.MutableSequence"].contains (toString id) then
      some e else none
  | _ => none

/-- The key and value types of a `Dict[K, V]`, `Mapping[K, V]` or `MutableMapping[K, V]`
(§12.3). -/
@[expose] def mappingItems? (tp : SpecType) : Option (SpecType × SpecType) :=
  match tp.atoms with
  | #[.ident id #[k, v]] =>
    if ["typing.Dict", "typing.Mapping", "typing.MutableMapping"].contains (toString id) then
      some (k, v) else none
  | _ => none

/-- The declared type of the ghost `g`, when its test adds to the ghost's invariant (§12.1,
*Module ghost*): every atom has a test of a standard class or `None`. -/
def ghostInvariantType? (t : Table) (g : Ghost) : Option SpecType :=
  g.type.bind fun tp =>
    let a := typeAtoms t tp
    if !a.any && !a.untestable && a.classes.all (fun | .std .. => true | _ => false) then some tp
    else none

/-- The binder names that schemas use, one per nesting depth. -/
def schemaBinder (depth : Nat) (what : String) : String := s!"{what}.{depth}"

mutual

/-- The schema of the parameter type `tp` on `v` (§12.3): the element test of a `List[T]` or
`Sequence[T]`, the key and value tests of a `Dict[K, V]` or `Mapping[K, V]`, and the keys of a
TypedDict, and for a union, each atom's schema for a value of that atom. `none` when it has
none. `fuel` bounds the nesting; past it, the schema is `false`, which is stronger. -/
def schema (t : Table) (tp : SpecType) (v : CExpr) (depth : Nat) (fuel : Nat) : Option CExpr :=
  match fuel with
  | 0 => some (.const false)
  | fuel + 1 =>
    if tp.atoms.size > 1 then
      -- A union: each atom's schema, for a value that passes the atom's type test. The test in
      -- the condition is the stricter pair, which alone would weaken the clause; but the union's
      -- type test, an earlier clause, makes one atom's pair hold, so it doesn't.
      let parts := tp.atoms.filterMap fun atom => do
        let single ← match atom with
          | .ident .. | .typedDict .. => some (SpecType.ofAtom tp.loc atom)
          | _ => none
        let s ← schema t single v depth fuel
        match paramTypeTest t single v with
        | some test => some (CExpr.implies test s)
        | none => some s
      if parts.isEmpty then none else some (parts.toList.tail.foldl .and parts[0]!)
    else if let some fields := tp.asTypedDict then
      let parts := fields.filterMap fun f =>
        let val := CExpr.item v (.str f.name)
        let valTest := elementTest t f.type val (depth + 1) fuel
        if f.required then
          some (match valTest with
            | some test => .and (.contains f.name v) test
            | none => .contains f.name v)
        else valTest.map (.implies (.contains f.name v))
      if parts.isEmpty then none else some (parts.toList.tail.foldl .and parts[0]!)
    else if let some elem := sequenceElement? tp then
      let x := schemaBinder depth "item"
      (elementTest t elem (.binder x) (depth + 1) fuel).map
        (.quant (.members true x) v)
    else if let some (k, val) := mappingItems? tp then
      let kb := schemaBinder depth "key"
      let vb := schemaBinder depth "value"
      let kt := elementTest t k (.binder kb) (depth + 1) fuel
      let vt := elementTest t val (.binder vb) (depth + 1) fuel
      match kt, vt with
      | none, none => none
      | some a, none => some (.quant (.entries true kb none) v a)
      | none, some b => some (.quant (.entries true none vb) v b)
      | some a, some b => some (.quant (.entries true kb vb) v (.and a b))
    else none

/-- The test of an element type: its declared-type test, and then its schema. -/
def elementTest (t : Table) (tp : SpecType) (v : CExpr) (depth : Nat) (fuel : Nat) :
    Option CExpr :=
  match paramTypeTest t tp v, schema t tp v depth fuel with
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (.and a b)

end

/-! ## Return schemas -/

/-- A step on the way from `result` to a position of a return type's schema (§12.3, *Return
schema*). A clause holds under the presence tests, class tests and quantifiers of its path. -/
inductive Guard where
  /-- `"key" in of` implies what follows: the member `key` is not required. -/
  | present (key : String) (of : CExpr)
  /-- `test` implies what follows: the class test of a union's one atom that isn't `None`. -/
  | isA (test : CExpr)
  /-- What follows holds for each member `binder` of `coll`, with `py.allIn`. -/
  | each (binder : String) (coll : CExpr)
  /-- What follows holds for each entry, `key` and `value`, of the dict `d`, with `py.allItems`. -/
  | entries (key value : String) (d : CExpr)
deriving Inhabited

/-- `body` past the steps `gs`, the first step outermost. -/
@[expose] def Guard.wrapAll (gs : List Guard) (body : CExpr) : CExpr :=
  gs.foldr (init := body) fun g b =>
    match g with
    | .present k v => .implies (.contains k v) b
    | .isA t => .implies t b
    | .each x c => .quant (.members true x) c b
    | .entries k v d => .quant (.entries true (some k) (some v)) d b

/-- A position of a return type's schema: the value there, read from `result`, its declared type,
the steps on its way, its level (`result` is level 0, and each member, element or entry adds one),
and the aliases that the way followed. -/
structure SchemaPosition where
  path : String
  value : CExpr
  type : SpecType
  guards : List Guard
  level : Nat
  aliases : List String
  /-- Whether the position's atom gets its class test as a guard although its type is not a
  union: the result of a special method that may return `NotImplemented` (§12.3). -/
  forceGuard : Bool := false
deriving Inhabited

/-- One clause of a return type's schema: the path of its position, the steps on its way, and
the test at the position. Its condition is `Guard.wrapAll guards test`. -/
structure SchemaClause where
  path : String
  guards : List Guard
  test : CExpr
deriving Inhabited

/-- The atoms of `tp`, with every alias replaced by its definition's atoms, and the names of the
aliases followed. `fuel` counts `tp` and each alias on a chain, so `resolvedAtoms t tp (n + 1)`
follows chains of at most `n` aliases, and gives `none` on a longer one. -/
@[expose] def resolvedAtoms (t : Table) (tp : SpecType) : Nat → Option (Array SpecAtomType × List String)
  | 0 => none
  | fuel + 1 =>
    tp.atoms.foldlM (init := (#[], [])) fun (acc, names) atom =>
      match atom with
      | .ident id #[] =>
        match t.resolve id with
        | some (.alias d) => do
          let (as, ns) ← resolvedAtoms t d fuel
          pure (acc ++ as, names ++ toString id :: ns)
        | _ => pure (acc.push atom, names)
      | _ => pure (acc.push atom, names)

/-- Whether `a` is `None`'s type. -/
@[expose] def isNoneAtom : SpecAtomType → Bool
  | .ident id _ => toString id == "_types.NoneType"
  | _ => false

/-- `m` after the path `p`: a member's path. -/
@[expose] def joinPath (p m : String) : String := if p.isEmpty then m else s!"{p}.{m}"

/-- The clauses of the children of `p`, whose atom is `a`, with the children's positions: one
per member of a TypedDict, the element of a sequence, or the entries of a mapping. A child
without a test gives no clause and no position, except a required member, whose clause states its
presence. -/
@[expose] def atomChildren (t : Table) (p : SchemaPosition) (a : SpecAtomType) :
    List (SchemaClause × SchemaPosition) :=
  let next (path : String) (value : CExpr) (type : SpecType) (guards : List Guard) :
      SchemaPosition :=
    { path, value, type, guards, level := p.level + 1, aliases := p.aliases }
  match a with
  | .typedDict fs fts frs =>
    (fs.zip fts).toList.zipIdx.filterMap fun ((m, ft), i) =>
      let v := CExpr.item p.value (.str m)
      let present := CExpr.contains m p.value
      -- A member counts as required only when PySpec says so; a missing flag is the weaker reading.
      if frs.getD i false then
        let test := match returnTypeTest t ft v with
          | some x => CExpr.and present x
          | none => present
        some ({ path := joinPath p.path m, guards := p.guards, test },
          next (joinPath p.path m) v ft p.guards)
      else
        (returnTypeTest t ft v).map fun x =>
          ({ path := joinPath p.path m, guards := p.guards, test := .implies present x },
            next (joinPath p.path m) v ft (p.guards ++ [.present m p.value]))
  | .ident _ _ =>
    match sequenceElement? (SpecType.ofAtom .none a), mappingItems? (SpecType.ofAtom .none a) with
    | some e, _ =>
      let x := schemaBinder p.level "item"
      let gs := p.guards ++ [.each x p.value]
      match returnTypeTest t e (.binder x) with
      | some test => [({ path := p.path ++ "[]", guards := gs, test }, next (p.path ++ "[]") (.binder x) e gs)]
      | none => []
    | none, some (k, val) =>
      let kb := schemaBinder p.level "key"
      let vb := schemaBinder p.level "value"
      let gs := p.guards ++ [.entries kb vb p.value]
      let test := match returnTypeTest t k (.binder kb), returnTypeTest t val (.binder vb) with
        | some a, some b => some (CExpr.and a b)
        | some a, none => some a
        | none, some b => some b
        | none, none => none
      match test with
      | some test => [({ path := p.path ++ "{}", guards := gs, test }, next (p.path ++ "{}") (.binder vb) val gs)]
      | none => []
    | none, none => []
  | _ => []

/-- The clauses of the children of `p`, with their positions. Every alias of `p`'s type is
followed first. Only a type with exactly one atom that isn't `None` has children; when it has
other atoms, or `forceGuard` holds, the children hold under that atom's class test. An alias
that the way to `p` already followed stops there, and so does a chain of more than
`aliasChainBound` aliases, where `typeAtoms` stops too. -/
@[expose] def schemaChildren (t : Table) (p : SchemaPosition) : List (SchemaClause × SchemaPosition) :=
  match resolvedAtoms t p.type (aliasChainBound + 1) with
  | none => []
  | some (atoms, names) =>
    if names.any (p.aliases.contains ·) then []
    else
      let p := { p with aliases := p.aliases ++ names }
      match (atoms.filter (!isNoneAtom ·)).toList with
      | [a] =>
        if atoms.size > 1 || p.forceGuard then
          match returnTypeTest t (SpecType.ofAtom p.type.loc a) p.value with
          | some test => atomChildren t { p with guards := p.guards ++ [.isA test] } a
          | none => []
        else atomChildren t p a
      | _ => []

/-- The bound on the levels of a return type's schema. -/
def returnSchemaDepth : Nat := 8

/-- The bound on the number of a return type's schema clauses. -/
def returnSchemaBudget : Nat := 256

/-- The clauses of the positions below `ps`, level by level, at most `cap` of them, for at most
`fuel` levels. A level stops as soon as `cap` clauses are made, and only the capacity left goes
to the next level. -/
@[expose] def schemaLevels (t : Table) : Nat → List SchemaPosition → Nat → List SchemaClause
  | 0, _, _ => []
  | fuel + 1, ps, cap =>
    if cap = 0 then []
    else
      let step := (ps.flatMap (schemaChildren t)).take cap
      step.map (·.1) ++ schemaLevels t fuel (step.map (·.2)) (cap - step.length)

/-- The schema of the return type `tp` (§12.3, *Return schema*): one condition per member, element
or entries of the result, at every level up to `returnSchemaDepth`, at most `returnSchemaBudget`
of them, each with the path of its position. `forceGuard` puts every clause under the class test
of the type's atom. -/
@[expose] def returnSchema (t : Table) (tp : SpecType) (forceGuard : Bool := false) :
    List (String × CExpr) :=
  let root : SchemaPosition :=
    { path := "", value := .result, type := tp, guards := [], level := 0, aliases := [], forceGuard }
  (schemaLevels t returnSchemaDepth [root] returnSchemaBudget).map fun c =>
    (c.path, Guard.wrapAll c.guards c.test)

/-! ## Expressions -/

/-- The attributes of `dict`, which an item read of the same name would hide. -/
def dictAttributes : List String :=
  ["keys", "values", "items", "get", "pop", "popitem", "update", "copy", "setdefault",
   "clear", "fromkeys"]

/-- The classes of CPython 3.12's `builtins`, which `isinstance` may name and a class variable may
read. `StdBasesTest` checks the list against CPython. -/
def builtinClasses : List String :=
  ["ArithmeticError", "AssertionError", "AttributeError", "BaseException", "BaseExceptionGroup",
   "BlockingIOError", "BrokenPipeError", "BufferError", "BytesWarning", "ChildProcessError",
   "ConnectionAbortedError", "ConnectionError", "ConnectionRefusedError", "ConnectionResetError",
   "DeprecationWarning", "EOFError", "EncodingWarning", "EnvironmentError", "Exception",
   "ExceptionGroup", "FileExistsError", "FileNotFoundError", "FloatingPointError", "FutureWarning",
   "GeneratorExit", "IOError", "ImportError", "ImportWarning", "IndentationError", "IndexError",
   "InterruptedError", "IsADirectoryError", "KeyError", "KeyboardInterrupt", "LookupError",
   "MemoryError", "ModuleNotFoundError", "NameError", "NotADirectoryError", "NotImplementedError",
   "OSError", "OverflowError", "PendingDeprecationWarning", "PermissionError",
   "ProcessLookupError", "RecursionError", "ReferenceError", "ResourceWarning", "RuntimeError",
   "RuntimeWarning", "StopAsyncIteration", "StopIteration", "SyntaxError", "SyntaxWarning",
   "SystemError", "SystemExit", "TabError", "TimeoutError", "TypeError", "UnboundLocalError",
   "UnicodeDecodeError", "UnicodeEncodeError", "UnicodeError", "UnicodeTranslateError",
   "UnicodeWarning", "UserWarning", "ValueError", "Warning", "ZeroDivisionError", "bool",
   "bytearray", "bytes", "classmethod", "complex", "dict", "enumerate", "filter", "float",
   "frozenset", "int", "list", "map", "memoryview", "object", "property", "range", "reversed",
   "set", "slice", "staticmethod", "str", "super", "tuple", "type", "zip"]

/-- Whether the class body of `c`, or of a model base of it, binds the name `m`: as a method, a
class variable, a nested class or a field with a value. -/
def ModelClass.declares (t : Table) (c : ModelClass) (m : String) (fuel : Nat := t.baseDepth) :
    Bool :=
  match fuel with
  | 0 => true
  | fuel + 1 =>
    c.decl.methods.any (·.name == m) || c.decl.classVars.any (·.name == m) ||
      c.decl.subclasses.any (·.name == m) ||
      c.decl.fields.any (fun f => f.name == m && f.value.isSome) ||
      c.decl.bases.any fun b => match t.classOf? b with
        | some base => base.declares t m fuel
        | none => false

/-- The float that PySpec's text of a float literal denotes: CPython's `str` of the float, such
as `1.5`, `-2.5e-07`, `inf` or `-inf`, or an integer's digits, as `0`, up to 2^53. -/
def floatOfText? (s : String) : Option Float :=
  let (neg, body) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
  let v := if body == "inf" then some (Float.ofBits 0x7FF0000000000000)
    else (StrataPython.Dyn.PyTranslate.parseFloat? body).orElse fun _ =>
      -- Digits of an int above 2^53 don't convert exactly, while CPython compares exactly.
      body.toNat?.bind fun n => if n ≤ 2 ^ 53 then some (Float.ofNat n) else none
  v.map fun f => if neg then -f else f

/-- The declared type of `e`, where §12.4's rules can compute it. -/
def typeOf (e : SpecExpr) : CheckM (Option SpecType) := do
  let ctx ← read
  match e with
  | .var n _ =>
    if let some (_, tp) := ctx.binders.find? (·.1 == n) then return tp
    if n == resultBinder && ctx.role == .post then return some ctx.decl.returnType
    if let some (kn, kt) := ctx.decl.args.kwargs then
      if kn == n then
        return match kt with
          | .unpacked tp => some tp
          | .each _ => none
    if let some tp := ctx.decl.paramType? n then return some tp
    return (ctx.table.ghosts ctx.module |>.find? (·.name == n)).bind (·.type)
  | .getIndex s f _ =>
    let some tp ← typeOf s | return none
    if let some ft := tp.lookupTypedDictField f then return some ft
    if let some (k, v) := tp.extractDictKeyValueTypes then
      if k.isStringLikeType then return some v
    if let some id := tp.asIdent then
      if let some c := ctx.table.classOf? id then
        return (c.decl.fields.find? (·.name == f)).map (·.type)
    return none
  | .getItem s _ _ =>
    let some tp ← typeOf s | return none
    return (tp.extractDictKeyValueTypes.map (·.2))
  | .old inner _ => typeOf inner
  | _ => return none

/-- Whether a value of declared type `tp` is a model class's instance, so that `s.f` is an
attribute. -/
def modelClassOf? (t : Table) (tp : SpecType) : Option ModelClass :=
  tp.asIdent.bind t.classOf?

/-- The binder types of a quantifier over a collection of type `tp`. -/
def binderTypes (tp : Option SpecType) (d : SpecQuantDomain) :
    List (String × Option SpecType) :=
  let dictKV := tp.bind (·.extractDictKeyValueTypes)
  match d with
  | .overList x => [(x, tp.bind (·.extractElementType))]
  | .overDictKeys k => [(k, dictKV.map (·.1))]
  | .overDictValues v => [(v, dictKV.map (·.2))]
  | .overDictItems k v => [(v, dictKV.map (·.2)), (k, dictKV.map (·.1))]

/-- The class that a bare name in `isinstance(x, T)` names, as CPython resolves it when the
lambda runs (§12.4): a class of the module, an imported class, an alias of a class, or a
class of `builtins`. -/
def classOfName (name : String) (loc : SourceRange) : CheckM (Option (Array ClassRef)) := do
  let ctx ← read
  let notClass (what : String) : CheckM (Option (Array ClassRef)) := do
    let _ ← reject "isinstance-name" s!"isinstance of '{ctx.display}' names '{name}', which {what}" loc
    return none
  -- A standard-library name is a class only for the classes of `builtins` and `re`'s
  -- `Pattern` and `Match`; `typing`'s names are not classes.
  let stdClass (src : PythonIdent) : Option ClassRef :=
    let m := toString src.pythonModule
    if (m == "builtins" && builtinClasses.contains src.name) ||
        (m == "re" && ["Pattern", "Match"].contains src.name) then
      some (.std m src.name)
    else none
  if ctx.binders.any (·.1 == name) || (ctx.decl.paramRef? name).isSome then
    let _ ← reject "isinstance-shadowed" s!"isinstance of '{ctx.display}' names '{name}', which is a parameter or a binder" loc
    return none
  match ctx.table.find? ctx.module name with
  | some (.cls c) => return some #[.model c]
  | some (.imported src) =>
    if isStd src then
      return ← match stdClass src with
        | some c => pure (some #[c])
        | none => notClass "is not a class of the standard library"
    match ctx.table.resolve src with
    | some (.cls c) => return some #[.model c]
    | _ => notClass "is not a class"
  | some (.alias d) =>
    -- A class or a union of classes; CPython's isinstance raises TypeError for a TypedDict, a
    -- Literal or a generic.
    let classes := d.atoms.filterMap fun
      | .ident id #[] => match ctx.table.classOf? id with
        | some c => some (ClassRef.model c)
        | none => if isStd id then stdClass id else none
      | _ => none
    if classes.size == d.atoms.size && !classes.isEmpty then return some classes
    let _ ← reject "isinstance-alias" s!"isinstance of '{ctx.display}' names the alias '{name}', which is not a class or a union of classes" loc
    return none
  | some _ => notClass "is not a class"
  | none =>
    if builtinClasses.contains name then return some #[builtin name]
    notClass "the model doesn't define"

/-- Reject a clause that PySpec read as the builtin `name`, such as `len`, when the model module
binds that name, as `len = int` does: CPython then calls the module's value. -/
def shadowedBuiltin (name : String) (loc : SourceRange) : CheckM Unit := do
  let ctx ← read
  if (ctx.table.find? ctx.module name).isSome then
    let _ ← reject "shadowed-builtin" s!"a clause of '{ctx.display}' calls '{name}', which the module binds to something else" loc

mutual

/-- The checked form of `e` (§12.4). -/
def checkExpr (e : SpecExpr) : CheckM CExpr := do
  let ctx ← read
  match e with
  | .placeholder loc =>
    reject "placeholder" s!"a clause of '{ctx.display}' holds a part that PySpec couldn't read" loc
  | .var n loc =>
    if ctx.binders.any (·.1 == n) then return .binder n
    if let .invariant b := ctx.role then
      if b == n then return .binder n
    if n == resultBinder && ctx.role == .post then return .result
    if n == resultBinder then
      return ← reject "result-outside-post" s!"'{ctx.display}' reads result outside @ensures or @admit" loc
    let ghosts := ctx.table.ghosts ctx.module
    let isGhost := ghosts.any (·.name == n)
    if let some (kn, _) := ctx.decl.args.kwargs then
      if kn == n then return .extraKwargs ctx.decl.namedParams
    if let some p := ctx.decl.paramRef? n then
      if isGhost then
        return ← reject "ghost-shadowed-by-param" s!"a parameter of '{ctx.display}' has the name of the ghost '{n}', which its contract names" loc
      return .param p
    if isGhost then return .ghost ctx.module n
    reject "unknown-name" s!"a clause of '{ctx.display}' names '{n}', which is neither a parameter, a binder nor a ghost" loc
  | .intLit i _ => return .int i
  | .boolLit b _ => return .bool b
  | .noneLit _ => return .none
  | .floatLit s loc =>
    match floatOfText? s with
    | some f => return .float f
    | none => reject "float-literal" s!"a clause of '{ctx.display}' holds the float '{s}', which doesn't parse" loc
  | .getIndex s f loc => do
    let sub ← checkExpr s
    let isKw := match s, ctx.decl.args.kwargs with
      | .var n _, some (kn, _) => n == kn
      | _, _ => false
    if isKw || ctx.role == .pre then return .item sub (.str f)
    let isBinder := match s, ctx.role with
      | .var n _, .invariant b => n == b
      | _, _ => false
    let tp ← typeOf s
    let ownerOfBinder := if isBinder then ctx.owner else none
    match ownerOfBinder <|> tp.bind (modelClassOf? ctx.table) with
    | some c =>
      if c.declares ctx.table "__getitem__" then
        return ← reject "attr-or-item" s!"'{ctx.display}' reads '.{f}' of '{c.qualName}', which declares __getitem__" loc
      return .attr sub f
    | none =>
      let dictLike := tp.any fun tp =>
        tp.isTypedDict || (tp.extractDictKeyValueTypes.any (·.1.isStringLikeType))
      if dictLike then
        if dictAttributes.contains f then
          return ← reject "attr-or-item" s!"'{ctx.display}' reads '{f}' of a dict, which is both an item and an attribute of dict" loc
        return .item sub (.str f)
      reject "attr-or-item" s!"'{ctx.display}' reads '{f}' of a value whose type doesn't say whether it is an attribute or an item" loc
  | .getItem s k _ => return .item (← checkExpr s) (← checkExpr k)
  | .isInstanceOf s n loc =>
    shadowedBuiltin "isinstance" loc
    let sub ← checkExpr s
    match ← classOfName n loc with
    | some cs => return disj (cs.map (.isInstance sub))
    | none => return .const false
  | .stringLen s loc | .len s loc =>
    shadowedBuiltin "len" loc
    return .len (← checkExpr s)
  | .intGe a b _ | .floatGe a b _ => return .cmp "gtE" (← checkExpr a) (← checkExpr b)
  | .intLe a b _ | .floatLe a b _ => return .cmp "ltE" (← checkExpr a) (← checkExpr b)
  | .add a b _ => return .arith "add" (← checkExpr a) (← checkExpr b)
  | .sub a b _ => return .arith "sub" (← checkExpr a) (← checkExpr b)
  | .mul a b _ => return .arith "mult" (← checkExpr a) (← checkExpr b)
  | .floorDiv a b _ => return .arith "floorDiv" (← checkExpr a) (← checkExpr b)
  | .mod a b _ => return .arith "mod" (← checkExpr a) (← checkExpr b)
  | .pow a b _ => return .arith "pow" (← checkExpr a) (← checkExpr b)
  | .neg a _ => return .neg (← checkExpr a)
  -- `compile(p).search(s) is None` is the negation of the match (§12.4).
  | .pcmp .eq (.regexMatch s p loc) (.noneLit _) _ =>
    shadowedBuiltin "compile" loc
    return .not (.reSearch p (← checkExpr s))
  | .pcmp .ne (.regexMatch s p loc) (.noneLit _) _ =>
    shadowedBuiltin "compile" loc
    return .reSearch p (← checkExpr s)
  | .pcmp op a b _ =>
    match op, b with
    | .eq, .noneLit _ => return .isNone (← checkExpr a) true
    | .ne, .noneLit _ => return .isNone (← checkExpr a) false
    | _, _ =>
      let name := match op with
        | .lt => "lt" | .le => "ltE" | .gt => "gt" | .ge => "gtE" | .eq => "eq" | .ne => "notEq"
        | .isIn => "in_" | .notIn => "notIn"
      return .cmp name (← checkExpr a) (← checkExpr b)
  | .enumMember s vals _ => return .enum (← checkExpr s) vals
  | .regexMatch s p loc =>
    shadowedBuiltin "compile" loc
    return .reSearch p (← checkExpr s)
  | .containsKey c k _ => return .contains k (← checkExpr c)
  | .implies a b _ => return .implies (← checkExpr a) (← checkExpr b)
  | .not (.enumMember s #[v] _) _ => return .notEnum (← checkExpr s) v
  | .not a _ => return .not (← checkExpr a)
  | .and a b _ => return .and (← checkExpr a) (← checkExpr b)
  | .or a b _ => return .or (← checkExpr a) (← checkExpr b)
  | .old inner loc =>
    if ctx.role != .post then
      return ← reject "old-outside-post" s!"'{ctx.display}' applies OLD outside @ensures or @admit" loc
    let c ← checkExpr inner
    if c.mentionsResult then
      return ← reject "old-result" s!"'{ctx.display}' applies OLD to result" loc
    return .old c
  | .quantifier kind domain coll body loc =>
    shadowedBuiltin (if kind == .forall then "all" else "any") loc
    if let .overDictItems k v := domain then
      if k == v then
        return ← reject "duplicate-binder" s!"a quantifier of '{ctx.display}' binds '{k}' twice" loc
    let collC ← checkExpr coll
    let tp ← typeOf coll
    let all := kind == .forall
    let q : Quant := match domain with
      | .overList x => .members all x
      | .overDictKeys k => .entries all (some k) none
      | .overDictValues v => .entries all none (some v)
      | .overDictItems k v => .entries all (some k) (some v)
    let bodyC ← withReader (fun c => { c with binders := binderTypes tp domain ++ c.binders })
      (checkExpr body)
    return .quant q collC bodyC

end

end -- public section

end StrataPython.Dyn.PySpec
