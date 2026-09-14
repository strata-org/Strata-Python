/-
Static class table: C3 linearization, layouts (annotated fields plus every
`self.f` store along the MRO), method resolution, exception hierarchy.
-/
import Pylate.Syntax.Nodes
import Pylate.Fset

namespace Pylate

/-- Parent links of the builtin exception hierarchy (the slice the subset
    can name). BaseException is the root, not Exception: SystemExit,
    KeyboardInterrupt, and GeneratorExit sit outside Exception, so
    `except Exception` is not a catch-all; only a bare `except` (or
    `except BaseException`) is. -/
def builtinExcParent : List (String × String) :=
  [("Exception", "BaseException"),
   ("SystemExit", "BaseException"),
   ("KeyboardInterrupt", "BaseException"),
   ("GeneratorExit", "BaseException"),
   ("ArithmeticError", "Exception"),
   ("ZeroDivisionError", "ArithmeticError"),
   ("OverflowError", "ArithmeticError"),
   ("FloatingPointError", "ArithmeticError"),
   ("AssertionError", "Exception"),
   ("AttributeError", "Exception"),
   ("FrozenInstanceError", "AttributeError"),
   ("LookupError", "Exception"),
   ("IndexError", "LookupError"),
   ("KeyError", "LookupError"),
   ("NameError", "Exception"),
   ("UnboundLocalError", "NameError"),
   ("RuntimeError", "Exception"),
   ("NotImplementedError", "RuntimeError"),
   ("RecursionError", "RuntimeError"),
   ("StopIteration", "Exception"),
   ("StopAsyncIteration", "Exception"),
   ("TypeError", "Exception"),
   ("ValueError", "Exception"),
   ("UnicodeError", "ValueError"),
   ("UnicodeEncodeError", "UnicodeError"),
   ("UnicodeDecodeError", "UnicodeError"),
   ("OSError", "Exception"),
   ("FileNotFoundError", "OSError"),
   ("EOFError", "Exception"),
   ("MemoryError", "Exception"),
   ("SystemError", "Exception")]

def builtinExcs : List String :=
  "BaseException" :: builtinExcParent.map (·.1)

partial def builtinExcChain (e : String) : List String :=
  match builtinExcParent.find? (·.1 == e) with
  | some (_, p) => e :: builtinExcChain p
  | none => [e]

structure ClassInfo where
  name        : String
  bases       : List String
  mro         : List String          -- self first; user classes only
  fullMro     : List String          -- self first; includes builtin bases
  layout      : Fset String
  ownLayout   : Fset String
  ownMethods  : List (String × FuncDef)
  isExc       : Bool
  isDataclass : Bool
  isTypedDict : Bool
  fields      : List FieldDecl
  total       : Bool
  /-- Names this class's own `__slots__` declares, if it has one. -/
  slots       : Option (List String) := none
  /-- Every class on the MRO declares `__slots__`, and the chain leaves user
      code only at `object`.

      When this holds CPython gives instances no `__dict__`, so a store to a name
      outside the layout raises `AttributeError` rather than adding a field --
      the shape invariant is enforced by the runtime instead of by admission.
      Both halves are needed: measured, a subclass that declares nothing gets a
      `__dict__` back and `o.zz = 5` is allowed again, while `__slots__ = ()` in
      that subclass keeps the guarantee. A non-`object` builtin on the chain
      brings its own `__dict__` (`BaseException` instances have one), so those do
      not qualify either. -/
  slotsComplete : Bool := false
deriving Inhabited

abbrev ClassTable := List (String × ClassInfo)

structure ClassTableError where
  p      : Pos
  rule   : String
  detail : String
deriving Inhabited

def ClassTable.getCls? (t : ClassTable) (c : String) : Option ClassInfo :=
  (List.find? (·.1 == c) t).map (·.2)

-- --------------------------------------------------------------------- C3

/-- C3 merge. No legal head means the class declaration is invalid, exactly
    as in CPython; admission must reject it rather than invent an order. -/
partial def c3Merge? (seqs : List (List String)) : Option (List String) :=
  let seqs := seqs.filter (!·.isEmpty)
  if seqs.isEmpty then some []
  else
    let heads := seqs.filterMap List.head?
    let good := heads.find? (fun h =>
      seqs.all (fun s => !(s.drop 1).contains h))
    match good with
    | none => none
    | some pick => do
      let rest ← c3Merge? (seqs.map (fun s => s.filter (· != pick)))
      pure (pick :: rest)

-- --------------------------------------------------- layout contributions

/-- Every `self.f` stored anywhere in a statement list. -/
partial def selfStoreTarget : Target → Fset String
  | .tattr _ (.name _ "self") f => [f]
  | .ttuple _ ts => ts.foldl (fun acc t => Fset.union (selfStoreTarget t) acc) []
  | _ => []

mutual
partial def selfStoreStmt (s : Stmt) : Fset String :=
  match s with
  | .assign _ t _ => selfStoreTarget t
  | .ifS _ _ a b | .whileS _ _ a b | .forS _ _ _ a b =>
    Fset.union (selfStores a) (selfStores b)
  | .tryS _ a hs b c =>
    Fset.union (selfStores a) <| Fset.union (selfStores b) <|
      Fset.union (selfStores c)
        (hs.foldl (fun acc h => match h with
          | .mk _ _ _ hb => Fset.union (selfStores hb) acc) [])
  | .delS .. => []
  | _ => []

partial def selfStores (ss : List Stmt) : Fset String :=
  ss.foldl (fun acc s => Fset.union (selfStoreStmt s) acc) []
end

/-- Synthesized `__init__` for a (frozen) dataclass: bind each annotated
    field from the same-named parameter. -/
def dataclassInit (c : ClassDef) : FuncDef :=
  let params := Param.mk "self" none none ::
    c.fields.map (fun f => Param.mk f.name f.ann none)
  let body := c.fields.map (fun f =>
    Stmt.assign c.p (Target.tattr c.p (Expr.name c.p "self") f.name)
      (Expr.name c.p f.name))
  FuncDef.mk c.p "__init__" params none body false false

def buildClassTable (cds : List ClassDef) :
    Except ClassTableError ClassTable := Id.run do
  let userNames := cds.map (·.name)
  let mut table : ClassTable := []
  let mut fullMros : List (String × List String) := []
  for cd in cds do
    -- A second `class C` shadows the first at runtime, but the table is keyed
    -- by name and `getCls?` returns the first match, so the second declaration
    -- would be invisible: measured, `class E(KeyError)` followed by
    -- `class E(ValueError)` sent `raise E("x")` to the `except KeyError`
    -- clause where CPython takes `except ValueError`. Two classes of the same
    -- name are two tags the model cannot tell apart, so refuse the program
    -- rather than pick one.
    if (table.getCls? cd.name).isSome then
      return .error {
        p := cd.p
        rule := "duplicate-class"
        detail := s!"class {cd.name} is declared more than once: the later declaration replaces the earlier one at runtime, so neither the MRO nor the dispatch table derived from a name is well defined"
      }
    let directBases := if cd.bases.isEmpty then ["object"] else cd.bases
    let mut baseMros : List (List String) := []
    for base in directBases do
      match fullMros.find? (·.1 == base) with
      | some (_, mro) => baseMros := baseMros ++ [mro]
      | none =>
        if userNames.contains base then
          return .error {
            p := cd.p
            rule := "unbound-base"
            detail := s!"class {cd.name} uses base {base} before {base} is bound"
          }
        else if base == "object" then
          baseMros := baseMros ++ [["object"]]
        else if builtinExcs.contains base then
          baseMros := baseMros ++ [builtinExcChain base ++ ["object"]]
        else
          return .error {
            p := cd.p
            rule := "unsupported-base"
            detail := s!"class {cd.name} has unsupported base {base}"
          }
    let some tail := c3Merge? (baseMros ++ [directBases])
      | return .error {
          p := cd.p
          rule := "invalid-mro"
          detail := s!"class {cd.name} has no consistent C3 MRO for bases {", ".intercalate cd.bases}"
        }
    let fullMro := cd.name :: tail
    let mro := fullMro.filter userNames.contains
    let isTypedDict := cd.isTypedDict || cd.bases.any (fun b =>
      (table.getCls? b).any (·.isTypedDict))
    let inheritedFields := if isTypedDict then
      cd.bases.flatMap (fun b => (table.getCls? b).map (·.fields) |>.getD [])
      else []
    let effectiveFields := inheritedFields.foldl (fun acc f =>
      if acc.any (·.name == f.name) then acc else acc ++ [f]) cd.fields
    let methods := if cd.isDataclass && !cd.methods.any (·.name == "__init__")
      then dataclassInit cd :: cd.methods else cd.methods
    let ownLayout := methods.foldl (fun fields method =>
      Fset.union (selfStores method.body) fields) (cd.fields.map (·.name))
    -- layout: annotated fields and self.f stores of every class on the MRO
    let mut layout : Fset String := []
    for m in mro do
      match cds.find? (·.name == m) with
      | some md =>
        let mm := if md.isDataclass && !md.methods.any (·.name == "__init__")
          then dataclassInit md :: md.methods else md.methods
        layout := Fset.union (md.fields.map (·.name)) layout
        for meth in mm do
          layout := Fset.union (selfStores meth.body) layout
      | none => pure ()
    let isExc := fullMro.contains "BaseException"
    -- Slots-completeness, and the consistency CPython checks at construction.
    let mroSlots := mro.flatMap (fun m =>
      if m == cd.name then (cd.slots).getD []
      else ((table.getCls? m).bind (·.slots)).getD [])
    let everyLinkSlotted := mro.all (fun m =>
      if m == cd.name then cd.slots.isSome
      else (table.getCls? m).any (·.slots.isSome))
    let chainIsUserCode := fullMro.all (fun c =>
      c == "object" || userNames.contains c)
    let slotsComplete := everyLinkSlotted && chainIsUserCode
    -- A field the class assigns that no `__slots__` on the chain declares is an
    -- `AttributeError` in CPython at construction time, not at the store, so it
    -- is worth naming here rather than letting the analysis find it later.
    if cd.slots.isSome then
      let unslotted := ownLayout.filter (fun f => !mroSlots.contains f)
      if !unslotted.isEmpty then
        return .error {
          p := cd.p
          rule := "slots-mismatch"
          detail := s!"class {cd.name} assigns {", ".intercalate unslotted} but no __slots__ on its MRO declares them: CPython raises AttributeError when __init__ runs"
        }
    table := table ++ [(cd.name,
      ⟨cd.name, cd.bases, mro, fullMro, layout, ownLayout,
       methods.map (fun m => (m.name, m)), isExc, cd.isDataclass,
       isTypedDict, effectiveFields, cd.total, cd.slots, slotsComplete⟩)]
    fullMros := fullMros ++ [(cd.name, fullMro)]
  return .ok table

/-- First class *after* `owner` on `runtime`'s MRO defining method `m`: what a
    zero-argument `super()` in `owner`'s body resolves to for a receiver whose
    class is `runtime`.

    The search is keyed on the receiver's class, not on `owner`'s bases, because
    that is what CPython does and the two differ under multiple inheritance.
    Measured: with `Left(Base)`, `Right(Base)` and `Bottom(Left, Right)`, a
    `super().m()` inside `Left.m` reaches `Right.m` when the receiver is a
    `Bottom` -- `left>right>base` -- and `Base.m` when it is a `Left`. Resolving
    against `Left`'s own base would give `Base` in both cases and silently skip
    `Right`. The analysis has the receiver's tag, so it can make the distinction
    the enclosing class alone cannot.

    An `owner` absent from the MRO yields `none`, as does exhausting the chain;
    `object` is not in the table, so its `__init__` is handled at the call. -/
def resolveMethodAfter (t : ClassTable) (runtime owner m : String) :
    Option (String × FuncDef) :=
  match t.getCls? runtime with
  | none => none
  | some ci =>
    let after := (ci.mro.dropWhile (· != owner)).drop 1
    after.firstM (fun d => do
      let di ← t.getCls? d
      let (_, fd) ← di.ownMethods.find? (·.1 == m)
      pure (d, fd))

/-- First class on C's MRO defining method m. -/
def resolveMethod (t : ClassTable) (c m : String) : Option (String × FuncDef) :=
  match t.getCls? c with
  | none => none
  | some ci => ci.mro.firstM (fun d => do
      let di ← t.getCls? d
      let (_, fd) ← di.ownMethods.find? (·.1 == m)
      pure (d, fd))

/-- The classes whose instances `isinstance(x, C)` admits: C and every
    user class whose MRO contains C. -/
def subclassClosure (t : ClassTable) (c : String) : List String :=
  c :: (t.filterMap (fun (n, ci) =>
    if n != c && ci.mro.contains c then some n else none))

/-- MRO for exception matching: a user class walks its own C3 order, then
    continues through the builtin chain of its builtin bases up to
    BaseException. A builtin name walks the parent table. There is no
    catch-all special case: `except Exception` matches exactly the
    Exception-derived classes, and only a bare `except` clause (handler
    class none) or `except BaseException` catches everything. -/
def excMro (t : ClassTable) (e : String) : List String :=
  match t.getCls? e with
  | some ci => ci.fullMro.filter (· != "object")
  | none => builtinExcChain e

def excCaught (t : ClassTable) (raised handler : String) : Bool :=
  (excMro t raised).contains handler

end Pylate
