/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.PySpec.Module
meta import StrataPython.Dyn.PySpec.Module
meta import StrataDyn.WF
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-! # The PySpec translation's pure parts

The model table's rejections, the format-version check, `CExpr.splitOld` on §12.4's three
examples, the declared-type tests and schemas of §12.3, float literals, and the checks of whole
model sets. The translation of whole models is tested by `StrataPythonTestExtra/PySpecDynTest`. -/

namespace StrataPython.PySpecTest

open StrataPython.Specs
open StrataPython.Dyn.PySpec
open StrataDDM (SourceRange)

meta section

/-- A short text of a checked clause, to compare. -/
def cls : ClassRef → String
  | .std m n => s!"{m}.{n}"
  | .model c => c.fullName

def txt : CExpr → String
  | .param p => p.name
  | .ghost _ n => s!"ghost {n}"
  | .binder n => n
  | .result => "result"
  | .int i => toString i
  | .none => "None"
  | .str s => s!"\"{s}\""
  | .attr e f => s!"{txt e}.{f}"
  | .item e k => s!"{txt e}[{txt k}]"
  | .len e => s!"len({txt e})"
  | .arith op a b => s!"{op}({txt a}, {txt b})"
  | .cmp op a b => s!"{op}({txt a}, {txt b})"
  | .isNone e p => if p then s!"{txt e} is None" else s!"{txt e} is not None"
  | .old e => s!"old({txt e})"
  | .typeTest e cs => s!"typeTest({txt e}, {cs.map cls})"
  | .isInstance e c => s!"isinstance({txt e}, {cls c})"
  | .strIsOneOf e ls => s!"strIsOneOf({txt e}, {ls})"
  | .intIsOneOf e ls => s!"intIsOneOf({txt e}, {ls})"
  | .or a b => s!"or({txt a}, {txt b})"
  | .implies a b => s!"implies({txt a}, {txt b})"
  | .contains k e => s!"contains({txt e}, {k})"
  | .float f => toString f
  | .and a b => s!"and({txt a}, {txt b})"
  | .quant (.members _ x) c b => s!"all({x} in {txt c}: {txt b})"
  | .quant (.entries _ k v) c b => s!"allItems({k.getD "_"}, {v.getD "_"} in {txt c}: {txt b})"
  | .const b => toString b
  | _ => "?"

def xs : CExpr := .param { name := "xs", pos := 0, noneDefault := false }

/-! ## `OLD` -/

-- `len(OLD(xs)) == len(xs) + 1`: only `len(xs)` at the call moves into `base.old`.
#guard txt (CExpr.cmp "eq" (.len (.old xs)) (.arith "add" (.len xs) (.int 1))).splitOld ==
  "eq(old(len(xs)), add(len(xs), 1))"

-- `allocated == OLD(allocated) + 1`: the whole `OLD(allocated) + 1` moves.
#guard txt (CExpr.cmp "eq" (.ghost "m" "allocated")
    (.arith "add" (.old (.ghost "m" "allocated")) (.int 1))).splitOld ==
  "eq(ghost allocated, old(add(ghost allocated, 1)))"

-- `len(OLD(d)["k"])`: the item and the length move too.
#guard txt (CExpr.len (.item (.old xs) (.str "k"))).splitOld == "old(len(xs[\"k\"]))"

-- `OLD(xs) == xs`: the `xs` outside `OLD` is the list after the call, so only `OLD(xs)` moves.
#guard txt (CExpr.cmp "eq" (.old xs) xs).splitOld == "eq(old(xs), xs)"

-- A part that reads `result` never moves.
#guard txt (CExpr.cmp "eq" .result (.old xs)).splitOld == "eq(result, old(xs))"

/-! ## Declared types (§12.3) -/

def tp (s : String) : SpecType := .ident .none (PythonIdent.ofString s).get! #[]

def emptyTable : Table := {}

#guard (paramTypeTest emptyTable (tp "builtins.int") xs).map txt ==
  some "typeTest(xs, #[builtins.int])"
#guard (paramTypeTest emptyTable (tp "builtins.float") xs).map txt ==
  some "typeTest(xs, #[builtins.float, builtins.int])"
#guard (paramTypeTest emptyTable (tp "builtins.complex") xs).map txt ==
  some "typeTest(xs, #[builtins.complex, builtins.float, builtins.int])"
#guard (paramTypeTest emptyTable (tp "typing.Any") xs).map txt == none
#guard (paramTypeTest emptyTable (.union .none (tp "builtins.str") (.noneType .none)) xs).map txt ==
  some "or(typeTest(xs, #[builtins.str]), xs is None)"
#guard (paramTypeTest emptyTable (.stringLiteral .none "a") xs).map txt ==
  some "strIsOneOf(xs, #[a])"
#guard (paramTypeTest emptyTable (.intLiteral .none 3) xs).map txt ==
  some "intIsOneOf(xs, #[3])"
-- An atom without a test, such as `BinaryIO`, gives `false` alone.
#guard (paramTypeTest emptyTable (tp "typing.BinaryIO") xs).map txt == some "false"
-- A return type with such an atom gives no test at all, which is weaker.
#guard (returnTypeTest emptyTable (.union .none (tp "builtins.int") (tp "typing.BinaryIO")) xs).map txt ==
  none
#guard (returnTypeTest emptyTable (tp "builtins.int") .result).map txt ==
  some "isinstance(result, builtins.int)"
-- `List[str]`'s schema tests each element.
#guard (schema emptyTable (.ident .none .typingList #[tp "builtins.str"]) xs 0 8).map txt ==
  some "all(item.0 in xs: typeTest(item.0, #[builtins.str]))"
#guard (paramTypeTest emptyTable (tp "builtins.bytes") xs).map txt == some "typeTest(xs, #[builtins.bytes])"
#guard (paramTypeTest emptyTable (tp "builtins.bool") xs).map txt == some "typeTest(xs, #[builtins.bool])"
#guard (paramTypeTest emptyTable (tp "typing.Sequence") xs).map txt ==
  some "typeTest(xs, #[collections.abc.Sequence])"
#guard (paramTypeTest emptyTable (tp "typing.Mapping") xs).map txt ==
  some "typeTest(xs, #[collections.abc.Mapping])"
#guard (paramTypeTest emptyTable (tp "typing.Generator") xs).map txt ==
  some "typeTest(xs, #[collections.abc.Generator])"
-- `Dict[str, int]`'s schema tests each key and value.
#guard (schema emptyTable (.ident .none .typingDict #[tp "builtins.str", tp "builtins.int"]) xs 0 8).map txt ==
  some "allItems(key.0, value.0 in xs: and(typeTest(key.0, #[builtins.str]), typeTest(value.0, #[builtins.int])))"
-- A TypedDict is a dict whose required keys are present, each with its value's test.
def td : SpecType := .typedDict .none #["a", "b"] #[tp "builtins.int", tp "typing.Any"] #[true, false]
#guard (paramTypeTest emptyTable td xs).map txt == some "typeTest(xs, #[builtins.dict])"
#guard (schema emptyTable td xs 0 8).map txt ==
  some "and(contains(xs, a), typeTest(xs[\"a\"], #[builtins.int]))"
-- In a union, each atom's schema holds for a value of that atom.
#guard (schema emptyTable (.union .none (.ident .none .typingList #[tp "builtins.str"]) (.noneType .none)) xs 0 8).map txt ==
  some "implies(typeTest(xs, #[builtins.list]), all(item.0 in xs: typeTest(item.0, #[builtins.str])))"
-- Past its nesting bound, a schema is `false`, which is stronger.
#guard (schema emptyTable (.ident .none .typingList #[tp "builtins.str"]) xs 0 0).map txt == some "false"

/-! ## Float literals -/

#guard (floatOfText? "1.5") == some 1.5 && (floatOfText? "-2.5e-07") == some (-2.5e-07)
#guard (floatOfText? "0") == some 0 && (floatOfText? "-inf").map (·.isInf) == some true
#guard (floatOfText? "nan").isNone && (floatOfText? "1.5x").isNone

/-! ## The model table -/

def input (m : String) (sigs : Array Signature) (version : Option Nat := some formatVersion) :
    ModelInput :=
  { module := ModuleName.ofString! m, version, sigs }

def rules (r : Except (Array Rejection) Table) : List String :=
  match r with
  | .ok _ => []
  | .error rs => (rs.map (·.rule)).toList

#guard rules (buildTable #[input "a" #[], input "a" #[]]) == ["duplicate-module"]

-- `a` imports from `b`, which imports from `a`.
#guard rules (buildTable #[
    input "a" #[.externTypeDecl "B" (PythonIdent.ofString "b.B").get!],
    input "b" #[.externTypeDecl "A" (PythonIdent.ofString "a.A").get!]]) ==
  ["import-cycle", "import-cycle"]

-- A nested class `_E` and a top-level class `_E` share the flattened name `a._E`.
def nestedE : ClassDef := { loc := .none, name := "_E", methods := #[] }
#guard rules (buildTable #[input "a" #[
    .classDef { loc := .none, name := "_E", methods := #[] },
    .classDef { loc := .none, name := "Outer", methods := #[], subclasses := #[nestedE] }]]) ==
  ["ambiguous-nested-class"]

-- Signatures from a file without the format command are refused.
#guard match translateModels #[input "a" #[] (version := none)] with
  | .error rs => (rs.map (·.rule)).toList == ["format-version"]
  | .ok _ => false

-- So are signatures from a file of format version 1.
#guard match translateModels #[input "a" #[] (version := some 1)] with
  | .error rs => (rs.map (·.rule)).toList == ["format-version"]
  | .ok _ => false

/-! ## Model sets -/

def ident (s : String) : PythonIdent := (PythonIdent.ofString s).get!

def method (n : String) : FunctionDecl :=
  { loc := .none, nameLoc := .none, name := n
    args := { args := #[{ name := "self", type := tp "typing.Any" }], kwonly := #[] }
    returnType := tp "typing.Any", isOverload := false, preconditions := #[], postconditions := #[] }

def cdef (n : String) (methods : Array String) (bases : Array String := #[]) : ClassDef :=
  { loc := .none, name := n, methods := methods.map method, bases := bases.map ident }

def tableOf (sigs : Array Signature) : Table := match buildTable #[input "m" sigs] with
  | .ok t => t
  | .error _ => {}

/-! ## Classes that CPython can't create -/

def setRules (sigs : Array Signature) : List String :=
  match translateModelSet #[input "m" sigs] with
  | .ok _ => []
  | .error rs => (rs.map (·.rule)).toList

#guard setRules #[.classDef (cdef "A" #[]), .classDef (cdef "B" #[]),
  .classDef (cdef "X" #[] #["m.A", "m.B"]), .classDef (cdef "Y" #[] #["m.B", "m.A"]),
  .classDef (cdef "Z" #[] #["m.X", "m.Y"])] == ["class-mro"]
#guard setRules #[.classDef (cdef "M" #[] #["builtins.dict", "builtins.Exception"])] == ["class-bases"]
#guard setRules #[.classDef (cdef "E" #[] #["builtins.Exception"])] == []

-- A class variable needs its place among the class body's bindings, so a class variable
-- without a position, beside a method without one, rejects the model.
#guard setRules #[.classDef { cdef "C" #["m"] with
  classVars := #[{ name := "y", value := "int" }] }] == ["internal"]
#guard setRules #[.classDef { cdef "C" #["m"] with
  classVars := #[{ name := "y", value := "int", loc := { start := ⟨5⟩, stop := ⟨6⟩ } }] }] == []

/-! ## Return types and mutable containers (§12.3) -/

-- A `bytes` result may be a `bytearray` or a `memoryview`; a model class gives the pair.
#guard (returnTypeTest emptyTable (tp "builtins.bytes") .result).map txt ==
  some "or(or(isinstance(result, builtins.bytes), isinstance(result, builtins.bytearray)), isinstance(result, builtins.memoryview))"
#guard (returnTypeTest (tableOf #[.classDef (cdef "Item" #[])]) (tp "m.Item") .result).map txt ==
  some "typeTest(result, #[m.Item])"
-- `MutableMapping[str, int]` is tested as its abstract class, with the schema of its items.
def mmap : SpecType := .ident .none (ident "typing.MutableMapping") #[tp "builtins.str", tp "builtins.int"]
#guard (paramTypeTest emptyTable mmap xs).map txt == some "typeTest(xs, #[collections.abc.MutableMapping])"
#guard (schema emptyTable mmap xs 0 8).map txt ==
  some "allItems(key.0, value.0 in xs: and(typeTest(key.0, #[builtins.str]), typeTest(value.0, #[builtins.int])))"

/-! ## Covered state of `OLD` (§12.4) -/

-- In a method of `Item`, an `OLD` may read the declared field `self.n`, which the arguments
-- reach, but not an undeclared attribute or a ghost that `@modifies` doesn't list.
def itemMethodCtx : FnCtx :=
  let t := tableOf #[.classDef { cdef "Item" #[] with fields := #[{ name := "n", type := tp "builtins.int" }] }]
  { table := t, module := "m", display := "Item.get", role := .post
    owner := t.classOf? (ident "m.Item")
    decl := { method "get" with args := { args := #[{ name := "self", type := tp "m.Item" }], kwonly := #[] } } }
def selfP : CExpr := .param { name := "self", pos := 0, noneDefault := false }
def oldRules (e : CExpr) : List String :=
  (((checkOldPart {} e .none).run itemMethodCtx).run {}).2.rejections.toList.map (·.rule)
#guard oldRules (.attr selfP "n") == []
#guard oldRules (.attr selfP "y") == ["old-uncovered"]
#guard oldRules (.ghost "m" "g") == ["old-uncovered"]
#guard oldRules (.arith "add" (.attr selfP "n") (.int 1)) == []

/-! ## Inherited `__init__` and `__getattr__` -/

-- A class whose model base declares `__init__` or `__getattr__` gets no synthesized one, so it
-- inherits the base's.
def funcNames (sigs : Array Signature) : Array String :=
  match translateModelSet #[input "m" sigs] with
  | .ok s => s.modules.flatMap fun m => m.raw.funcs.map (Strata.Dyn.Build.nameText ·.name)
  | .error _ => #[]
#guard (funcNames #[.classDef (cdef "B" #["__init__", "__getattr__"]), .classDef (cdef "C" #[] #["m.B"])]).filter
    (fun n => n.endsWith "__init__" || n.endsWith "__getattr__") ==
  #["m.B.__init__", "m.B.__getattr__", "m.__getattr__"]

/-! ## Unbound binders -/

-- `checkExpr` gives a binder only inside its quantifier, and `result` only in a post-state
-- clause. A clause that reads either elsewhere makes the extern fail to build.
def externError (body : CExpr) : Option String :=
  match emitExtern (qualified "m" ["f"]) { requires := #[{ message := "c", body }] } {} with
  | .ok _ => none
  | .error e => some e
#guard externError (.bool true) == none
#guard (externError (.binder "x")).any (·.contains "internal: the binder 'x' is read where nothing binds it")
#guard (externError .result).any (·.contains "internal: result is read where nothing binds it")

end -- meta section

end StrataPython.PySpecTest
