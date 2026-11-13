/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.Dyn.Scope
public import StrataPython.Dyn.OldSplit
import StrataPython.Dyn.Termination

set_option autoImplicit false

/-!
# Loop-invariant markers

A module states loop invariants with `loop_invariant(lambda: P)` and `OLD(e)`, imported with
`from pyhard import loop_invariant, OLD` (`docs/PythonToDyn.md` §6.11). The translator drops the
marker calls, which is faithful only if the marker names surely are `pyhard`'s markers wherever
the module calls them. `analyze` checks the module-wide half of that:

* the import is one `from pyhard import …` of marker names only, with no `as`, at the module's
  top level, after nothing but a docstring and `from __future__` imports, so that the names are
  bound before any marker call can run;
* no other import loads `pyhard`;
* no scope of the module binds a marker name, by any binding form that the scope pass knows,
  and no scope declares one `global` or `nonlocal`.

The translator checks where each marker call stands and its shape, and the guard that it puts
before the loop checks at run time that `loop_invariant` is still the marker, since other code,
such as another module, can rebind it where no scope pass sees it.
-/

namespace StrataPython.Dyn.PyMarkers

open StrataDDM (SourceRange)
open StrataPython (stmt expr alias keyword comprehension cmpop)
open StrataPython.Dyn.PyScope

public section

/-- The module that defines the markers. -/
def markerModule : String := "pyhard"

/-- The names that `markerModule` defines as markers. -/
def allMarkers : Array String := #["loop_invariant", "OLD"]

/-- The markers that a module imports. -/
structure Markers where
  /-- The marker names that the module's import binds, in the import's order. -/
  names : Array String
  /-- The names of `invariantBuiltins` that some scope of the module binds, or declares
  `global` or `nonlocal`: an invariant can't use them as the builtins. -/
  reboundBuiltins : Array String := #[]
  deriving Repr, Inhabited

/-- Whether `name` is one of the module's markers. -/
def Markers.has (m : Markers) (name : String) : Bool := m.names.contains name

/-- Whether an import of `m` loads the marker module or one of its submodules. -/
def loadsMarkerModule (m : String) : Bool :=
  m == markerModule || m.startsWith (markerModule ++ ".")

/-- A rejection of a misuse of the markers, worded as the translator's other rejections. -/
def unsupported (what : String) (range : SourceRange) : Diagnostic :=
  { kind := .unsupported, message := s!"{what} is not supported", range }

/-- Whether a program module named `m` is named like the marker module: some component of its
dotted name is `pyhard` (`pyhard`, `pyhard.x`, `pkg.pyhard`). The translator rejects such a module,
whatever it contains, as a defensive check: if PyHard's module weren't loaded first (§12.9), CPython
could import such a module in its place (§6.11). -/
def namedLikeMarkerModule (m : String) : Bool :=
  (m.splitOn ".").contains markerModule

/-- The rejection of a main script whose file is named like the marker module, `pyhard.py`: it is
translated as `__main__`, so `translate` can't see its name. A defensive check: if PyHard's module
weren't loaded first (§12.9), CPython would import the script as `pyhard` when it imports the
markers. -/
def mainFileProblem? (path : System.FilePath) : Option String :=
  -- A Python Ion file of `pyhard.py` is `pyhard.py.ion`, `pyhard.python.st.ion` or `pyhard.st.ion`.
  let name := path.fileName.getD ""
  let name := match [".python.st.ion", ".py.ion", ".st.ion", ".ion", ".py"].find? (name.endsWith ·) with
    | some sfx => (name.dropEnd sfx.length).toString
    | none => name
  if name == markerModule then
    some "a main script named pyhard.py is not supported: without PyHard's pyhard loaded first, CPython would import the script in its place"
  else none

/-- Whether `s` may come before the marker import: a docstring or a `from __future__`
import. -/
def mayPrecede (first : Bool) : stmt SourceRange → Bool
  | .Expr _ (.Constant _ (.ConString ..) _) => first
  | .ImportFrom _ m _ _ => (m.val.map (·.val)) == some "__future__"
  | _ => false

/-- The index of the first statement that `mayPrecede` doesn't allow. -/
def firstOther (stmts : Array (stmt SourceRange)) : Nat :=
  (List.range stmts.size).find? (fun i => !(stmts[i]?.map (mayPrecede (i == 0))).getD false)
    |>.getD stmts.size

/-- The marker import at `s`, if `s` is `from pyhard import …`: its aliases. -/
def markerImport? : stmt SourceRange → Option (SourceRange × Array (alias SourceRange))
  | .ImportFrom sr m aliases level =>
    if (m.val.map (·.val)) == some markerModule && (level.val.map (·.value)).getD 0 == 0 then
      some (sr, aliases.val)
    else none
  | _ => none

/-- The rebindings of the marker `name` in `t`: a range for each scope that binds it, other than
the module scope's import, or that declares it `global` or `nonlocal`.  The module scope's is
`moduleRange`. -/
def rebindings (t : Table) (name : String) (moduleRange : SourceRange) : Array SourceRange :=
  t.scopes.filterMap fun s =>
    match s.symbol? name with
    | none => none
    | some sym =>
      let u := sym.uses
      let atModule := s.kind == .module
      let bad := u.param || u.assigned || u.declaredGlobal || u.declaredNonlocal ||
        u.annotated || u.compIter || (u.imported && !atModule)
      if bad then some (if atModule then moduleRange else s.range) else none

/-- The builtins that an invariant may call, each lowered to its operation. -/
def invariantBuiltins : Array String := #["len", "isinstance", "all", "any"]

/-- Whether some scope of `t` binds `name`, or declares it `global` or `nonlocal`. -/
def boundAnywhere (t : Table) (name : String) : Bool :=
  t.scopes.any fun s => match s.symbol? name with
    | some sym => sym.uses.bound || sym.uses.declaredGlobal || sym.uses.declaredNonlocal
    | none => false

/-- Check the module-wide rules of the markers. With no `from pyhard import …` at the top, the
module has no markers, and `loop_invariant` is an ordinary name; any other import of `pyhard`
is still rejected, so that a module can't get the markers in a way the translator doesn't
recognize. -/
def analyze (stmts : Array (stmt SourceRange)) (t : Table) : Option Markers × Array Diagnostic :=
  Id.run do
  let mut ds : Array Diagnostic := #[]
  let i := firstOther stmts
  let head := stmts[i]? >>= markerImport?
  -- Every import of the marker module other than the one at the top is rejected.
  let headRanges := (head.map fun (_, as) => as.map (·.ann)).getD #[]
  for imp in t.imports do
    if loadsMarkerModule imp.loads && !headRanges.contains imp.range then
      ds := ds.push (unsupported "importing pyhard other than at the top of the module" imp.range)
  let some (importRange, aliases) := head | return (none, ds)
  let mut names : Array String := #[]
  for a in aliases do
    let .mk_alias asr ⟨_, n⟩ ⟨_, asname⟩ := a
    if !allMarkers.contains n then
      ds := ds.push (unsupported "importing names from pyhard other than loop_invariant and OLD"
        asr)
    else if asname.isSome then
      ds := ds.push (unsupported "renaming a pyhard marker" asr)
    else if names.contains n then
      ds := ds.push (unsupported "importing a pyhard marker twice" asr)
    else names := names.push n
  for n in names do
    -- The scope table keeps no position for a module-level binding, so that one is reported at
    -- the marker import; another scope's at its `def`, `class`, `lambda` or comprehension.
    for r in rebindings t n importRange do
      ds := ds.push (unsupported s!"rebinding the marker {n}" r)
    -- The module scope binds the name only by the marker import.
    if ((t.importsIn 0).filter (·.name == n)).size != 1 then
      ds := ds.push (unsupported s!"rebinding the marker {n}" importRange)
  return (some { names, reboundBuiltins := invariantBuiltins.filter (boundAnywhere t) }, ds)

/-! ## What an invariant may contain

An invariant `P` is lowered with the translator's own expression lowering into a contract region
(§6.11), which may apply no operation that writes.  `checkInvariant` admits only the constructs
whose lowering applies none: names, literals, operators, comparisons, `and`, `or`, `not`,
conditional expressions, attributes, subscripts and slices, and calls of `len`, `isinstance`,
`all` and `any`, the last two on a generator expression with one `for` clause. -/

/-- A rejection of `what` in an invariant, at `range`. -/
abbrev InvCheck := Except (String × SourceRange) Unit

/-- Reject `what` at `range`. -/
def bad (what : String) (range : SourceRange) : InvCheck := .error (what, range)

/-- The method of `e` if it is `d.items()`, `d.keys()` or `d.values()`: the method's name and `d`. -/
def dictView? : expr SourceRange → Option (String × expr SourceRange)
  | .Call _ (.Attribute _ d ⟨_, m⟩ _) args kws =>
    if args.val.isEmpty && kws.val.isEmpty && (m == "items" || m == "keys" || m == "values") then
      some (m, d)
    else none
  | _ => none

/-- What is wrong with `target`, the target of a quantifier over `iter`, where `view` is the dict
view that `iter` calls, if it calls one: a pair of names over `items()`, a name otherwise.
`mangle` gives a name as CPython stores it, private names mangled. -/
def targetProblem (mangle : String → String) (view : Option String) (target : expr SourceRange) :
    Option String :=
  -- Two names, which must differ as CPython stores them: in `for k, k in d.items()`, and in a
  -- method of `C` in `for __k, _C__k in d.items()`, CPython binds one name, to the value.
  let pair := match target with
    | .Tuple _ ⟨_, #[.Name _ ⟨_, k⟩ _, .Name _ ⟨_, v⟩ _]⟩ _ => mangle k != mangle v
    | _ => false
  let name := target matches .Name ..
  if view == some "items" then
    if pair then none else some "a quantifier over items() whose target is not two different names"
  else if name then none
  else some "a quantifier whose target is not a name in a loop invariant"

/-! ## Old parts

An `OLD(e)` reads `e` in the state at the function's entry. As in PySpec models (§12.4 of
`docs/PythonToDyn.md`), the part read there is the largest subexpression around it that reads no
state outside its `OLD`s: `len(OLD(xs))` reads `len(xs)` at entry, and `OLD(xs) == xs` reads only
`xs` there. The rule is `OldSplit`'s, over the instance below, which covers the constructs that
`checkInvariant` admits; `splitOld` rewrites an invariant so that each old part is one `OLD(…)`. -/

/-- `OLD(x)`, at `x`'s range. -/
def wrapOld (x : expr SourceRange) : expr SourceRange :=
  .Call x.ann (.Name x.ann ⟨x.ann, "OLD"⟩ (.Load x.ann)) ⟨x.ann, #[x]⟩ ⟨x.ann, #[]⟩

/-- Whether `e` is a dict view `d.items()`, `d.keys()` or `d.values()`. -/
def isDictView (e : expr SourceRange) : Bool := (dictView? e).isSome

/-- The children that the old-part rule looks into: a builtin call's arguments, a dict view's
dict, the operands of operators, comparisons, `and`, `or`, `not` and conditional expressions, an
attribute's value, a subscript's value and index, a slice's bounds, and a quantifier's element,
iterable and guards. -/
def oldChildren : expr SourceRange → List (expr SourceRange)
  | .Call _ (.Name ..) args _ => args.val.toList
  | e@(.Call _ (.Attribute _ d _ _) _ _) => if isDictView e then [d] else []
  | .BinOp _ l _ r => [l, r]
  | .UnaryOp _ _ x | .Attribute _ x _ _ => [x]
  | .BoolOp _ _ vs => vs.val.toList
  | .Compare _ l _ rs => l :: rs.val.toList
  | .IfExp _ a b d => [a, b, d]
  | .Subscript _ v i _ => [v, i]
  | .Slice _ lo hi st => lo.val.toList ++ hi.val.toList ++ st.val.toList
  | .GeneratorExp _ elt gens => match gens.val.toList with
    | [.mk_comprehension _ _ iter ifs _] => elt :: iter :: ifs.val.toList
    | _ => []
  | _ => []

/-- `e` with its `oldChildren` replaced, in order, by those of `cs`. -/
def withOldChildren (e : expr SourceRange) (cs : List (expr SourceRange)) : expr SourceRange :=
  match e, cs with
  | .Call sr f@(.Name ..) args kws, cs => .Call sr f ⟨args.ann, cs.toArray⟩ kws
  | e@(.Call sr (.Attribute asr _ m ctx) args kws), [d] =>
    if isDictView e then .Call sr (.Attribute asr d m ctx) args kws else e
  | .BinOp sr _ op _, [l, r] => .BinOp sr l op r
  | .UnaryOp sr op _, [x] => .UnaryOp sr op x
  | .Attribute sr _ n ctx, [x] => .Attribute sr x n ctx
  | .BoolOp sr op vs, cs => .BoolOp sr op ⟨vs.ann, cs.toArray⟩
  | .Compare sr _ ops rs, l :: cs => .Compare sr l ops ⟨rs.ann, cs.toArray⟩
  | .IfExp sr _ _ _, [a, b, d] => .IfExp sr a b d
  | .Subscript sr _ _ ctx, [v, i] => .Subscript sr v i ctx
  | .Slice sr lo hi st, cs =>
    let take (o : StrataDDM.Ann (Option (expr SourceRange)) SourceRange)
        (cs : List (expr SourceRange)) :
        StrataDDM.Ann (Option (expr SourceRange)) SourceRange × List (expr SourceRange) :=
      match o.val, cs with
      | some _, c :: rest => (⟨o.ann, some c⟩, rest)
      | _, cs => (o, cs)
    let (lo, cs) := take lo cs
    let (hi, cs) := take hi cs
    let (st, _) := take st cs
    .Slice sr lo hi st
  | e@(.GeneratorExp sr _ gens), elt :: iter :: ifs =>
    match gens.val.toList with
    | [.mk_comprehension csr t _ gifs a] =>
      .GeneratorExp sr elt ⟨gens.ann, #[.mk_comprehension csr t iter ⟨gifs.ann, ifs.toArray⟩ a]⟩
    | _ => e
  | e, _ => e

/-- Whether the node itself reads state: a name (a quantifier's binder included), a call other
than a builtin's or a dict view's, a generator expression that isn't a quantifier's, and every
construct that `checkInvariant` rejects, so that no unknown construct enters an old part. -/
def readsStateNode : expr SourceRange → Bool
  | .Name .. => true
  | e@(.Call _ f _ _) => !(f matches .Name ..) && !isDictView e
  | .GeneratorExp _ _ gens => gens.val.size != 1
  | .Constant .. | .BinOp .. | .UnaryOp .. | .Attribute .. | .BoolOp .. | .Compare ..
  | .IfExp .. | .Subscript .. | .Slice .. => false
  | _ => true

/-- Whether the node may become an old part: not a slice (a slice object), a quantifier's
generator or a dict view, none of which is a value that `base.old` returns, and the view stays
with its quantifier. -/
def wrappableNode : expr SourceRange → Bool
  | .Slice .. | .GeneratorExp .. => false
  | e => !isDictView e

/-- An element of an annotated array is smaller than the annotated array. -/
private theorem ann_mem_sizeOf {β γ : Type} [SizeOf β] [SizeOf γ] {x : β}
    {a : StrataDDM.Ann (Array β) γ} (h : x ∈ a.val) : sizeOf x < sizeOf a := by
  have hmem := Array.sizeOf_lt_of_mem h
  rw [sizeOf_ann]
  omega

/-- The value inside an annotated `some` is smaller than the annotated option. -/
private theorem ann_some_sizeOf {β γ : Type} [SizeOf β] [SizeOf γ] {x : β}
    {a : StrataDDM.Ann (Option β) γ} (h : a.val = some x) : sizeOf x < sizeOf a := by
  rw [sizeOf_ann, h]
  simp only [Option.some.sizeOf_spec]
  omega

/-- Every child that the old-part rule looks into, `oldChildren e`, is smaller than `e`. -/
theorem oldChildren_lt (e c : expr SourceRange) (h : c ∈ oldChildren e) : sizeOf c < sizeOf e := by
  revert c
  -- Expose what `oldChildren` matches on: a call's callee, and a quantifier's clauses.
  cases e
  case' Call _ f _ _ => cases f
  case' GeneratorExp _ _ gens => obtain ⟨_, ⟨_ | ⟨⟨⟩, _ | _⟩⟩⟩ := gens
  all_goals simp only [oldChildren]
  -- Split a dict view's `if`.
  all_goals try split
  all_goals simp only [List.forall_mem_cons, List.forall_mem_append, List.not_mem_nil,
    false_implies, implies_true, and_true, Array.mem_toList_iff, Option.mem_toList]
  all_goals repeat' apply And.intro
  -- A child inside an annotated array or option: its size is below the annotated value's.
  all_goals try (intro x hx; first | have h := ann_mem_sizeOf hx | have h := ann_some_sizeOf hx)
  all_goals simp only [expr.Call.sizeOf_spec, expr.Name.sizeOf_spec, expr.Attribute.sizeOf_spec,
    expr.BinOp.sizeOf_spec, expr.BoolOp.sizeOf_spec, expr.UnaryOp.sizeOf_spec,
    expr.IfExp.sizeOf_spec, expr.Compare.sizeOf_spec, expr.Subscript.sizeOf_spec,
    expr.Slice.sizeOf_spec, expr.GeneratorExp.sizeOf_spec,
    comprehension.mk_comprehension.sizeOf_spec, StrataDDM.Ann.mk.sizeOf_spec, Array.mk.sizeOf_spec,
    List.cons.sizeOf_spec, List.nil.sizeOf_spec] <;> omega

/-- Rebuilding `e` with as many new children as `oldChildren e` has gives a node whose
`oldChildren` are exactly the new children, in order. -/
theorem withOldChildren_oldChildren (e : expr SourceRange) (cs : List (expr SourceRange))
    (h : cs.length = (oldChildren e).length) : oldChildren (withOldChildren e cs) = cs := by
  cases e with
  | Call sr f args kws =>
    cases f with
    | Name => simp [withOldChildren, oldChildren]
    | Attribute asr d m ctx =>
      -- Whether a call is a dict view doesn't depend on the dict.
      have hd (d' : expr SourceRange) :
          isDictView (.Call sr (.Attribute asr d' m ctx) args kws) =
            isDictView (.Call sr (.Attribute asr d m ctx) args kws) := by
        obtain ⟨_, _⟩ := m; simp only [isDictView, dictView?]; split <;> rfl
      by_cases hv : isDictView (.Call sr (.Attribute asr d m ctx) args kws) <;>
        rcases cs with _ | ⟨_, _ | _⟩ <;> simp_all [withOldChildren, oldChildren]
    | _ => simp_all [withOldChildren, oldChildren]
  -- A slice by the bounds it has, and a generator expression by its number of clauses.
  | Slice sr lo hi st =>
    obtain ⟨_, _ | _⟩ := lo <;> obtain ⟨_, _ | _⟩ := hi <;> obtain ⟨_, _ | _⟩ := st <;>
      rcases cs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;> simp_all [withOldChildren, oldChildren]
  | GeneratorExp sr elt gens =>
    obtain ⟨_, ⟨_ | ⟨⟨⟩, _ | _⟩⟩⟩ := gens <;> rcases cs with _ | ⟨_, _ | _⟩ <;>
      simp_all [withOldChildren, oldChildren]
  | _ =>
    rcases cs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;> simp_all [withOldChildren, oldChildren]

/-- Loop invariants' syntax for the old-part rule. -/
instance : OldSyntax (expr SourceRange) where
  -- `⟨[a]⟩` matches the same arrays as `#[a]`, but Lean can generate this match's equations,
  -- which the proofs about `oldArg?` need.
  oldArg?
    | .Call _ (.Name _ ⟨_, "OLD"⟩ _) ⟨_, ⟨[a]⟩⟩ _ => some a
    | _ => none
  mkOld := wrapOld
  wrappable := wrappableNode
  readsState := readsStateNode
  children := oldChildren
  children_lt := oldChildren_lt
  oldArg_lt e a h := by
    split at h <;> cases h
    simp only [expr.Call.sizeOf_spec, expr.Name.sizeOf_spec, StrataDDM.Ann.mk.sizeOf_spec,
      Array.mk.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec] <;> omega
  mapChildren e f := withOldChildren e ((oldChildren e).attach.map fun ⟨c, h⟩ => f c h)
  children_mapChildren e f := by
    rw [withOldChildren_oldChildren]; simp only [List.length_map, List.length_attach]

/-- `e` with each old part written as one `OLD(…)` (`OldSplit.splitOld`): `len(OLD(xs)) ==
len(xs) + 1` becomes `OLD(len(xs)) == len(xs) + 1`. -/
def splitOld (e : expr SourceRange) : expr SourceRange := OldSplit.splitOld e

/-- Whether `e` holds an `OLD` (`OldSplit.hasOld`). -/
def hasOld (e : expr SourceRange) : Bool := OldSplit.hasOld e

mutual

/-- The names that `e` reads, with repeats: a quantifier's binders, and a callee's names, such as
`d` of `d.items()` and the builtin `len`, included. -/
def namesIn (e : expr SourceRange) : Array String :=
  match e with
  | .Name _ ⟨_, n⟩ _ => #[n]
  | .Call _ f args _ => namesIn f ++ args.val.attach.flatMap fun ⟨a, _⟩ => namesIn a
  | .BinOp _ l _ r => namesIn l ++ namesIn r
  | .UnaryOp _ _ x | .Attribute _ x _ _ => namesIn x
  | .BoolOp _ _ vs => vs.val.attach.flatMap fun ⟨v, _⟩ => namesIn v
  | .Compare _ l _ rs => namesIn l ++ rs.val.attach.flatMap fun ⟨r, _⟩ => namesIn r
  | .IfExp _ a b d => namesIn a ++ namesIn b ++ namesIn d
  | .Subscript _ v i _ => namesIn v ++ namesIn i
  | .Slice _ ⟨_, lo⟩ ⟨_, hi⟩ ⟨_, st⟩ => optNamesIn lo ++ optNamesIn hi ++ optNamesIn st
  | .GeneratorExp _ elt gens => namesIn elt ++ gens.val.attach.flatMap fun ⟨g, _⟩ => compNamesIn g
  | _ => #[]
termination_by sizeOf e

/-- `namesIn` of an optional expression. -/
def optNamesIn (e : Option (expr SourceRange)) : Array String :=
  match e with
  | some x => namesIn x
  | none => #[]
termination_by sizeOf e

/-- `namesIn` of a quantifier's clause: its iterable and its guards. -/
def compNamesIn (c : comprehension SourceRange) : Array String :=
  match c with
  | .mk_comprehension _ _ iter ifs _ => namesIn iter ++ ifs.val.attach.flatMap fun ⟨x, _⟩ => namesIn x
termination_by sizeOf c

end

/-- What `checkInvariant` needs besides the expression. -/
structure InvCtx where
  markers : Markers
  /-- Why the lowering of a name would reject it, if it would, such as a marker name. -/
  nameProblem : String → Option String
  /-- The loop is in the module body, where `OLD` has no meaning. -/
  atModule : Bool
  /-- Inside the argument of an `OLD`. -/
  inOld : Bool := false
  /-- A name as CPython stores it in the loop's scope, a private name mangled. -/
  mangle : String → String

mutual

/-- Check the invariant expression `e` in the context `c`. -/
def checkInvariant (c : InvCtx) (e : expr SourceRange) : InvCheck := do
  let m := c.markers
  match e with
  | .Name sr ⟨_, n⟩ _ => if let some what := c.nameProblem n then bad what sr
  | .Constant .. => pure ()
  | .BinOp _ l _ r => checkInvariant c l; checkInvariant c r
  | .UnaryOp _ _ x => checkInvariant c x
  | .BoolOp _ _ vs => for v in vs.val do checkInvariant c v
  | .Compare sr l ops rs =>
    -- `is` can tell a value computed again in an old region from the one CPython would read:
    -- `OLD(p) is p` for a literal default `p=1.5`.
    if ops.val.any (· matches .Is _ | .IsNot _) && (hasOld l || rs.val.any hasOld) then
      return ← bad "is with an OLD part in a loop invariant" sr
    checkInvariant c l
    for r in rs.val do checkInvariant c r
  | .IfExp _ x a b => checkInvariant c x; checkInvariant c a; checkInvariant c b
  | .Attribute _ v _ _ => checkInvariant c v
  | .Subscript _ v i _ => checkInvariant c v; checkInvariant c i
  | .Slice _ ⟨_, lo⟩ ⟨_, hi⟩ ⟨_, st⟩ =>
    if let some x := lo then checkInvariant c x
    if let some x := hi then checkInvariant c x
    if let some x := st then checkInvariant c x
  | .Call sr f args kws =>
    unless kws.val.isEmpty do return ← bad "a keyword argument in a loop invariant" sr
    if args.val.any (· matches .Starred ..) then
      return ← bad "a starred expression in a loop invariant" sr
    match f with
    | .Name fsr ⟨_, n⟩ _ =>
      if n == "OLD" then
        if !m.has "OLD" then return ← bad "OLD without importing it from pyhard" fsr
        if c.atModule then return ← bad "OLD at module level in a loop invariant" sr
        if c.inOld then return ← bad "an OLD inside an OLD in a loop invariant" sr
        unless args.val.size == 1 do return ← bad "a call in a loop invariant" sr
        for a in args.val do checkInvariant { c with inOld := true } a
        return
      if !invariantBuiltins.contains n then return ← bad "a call in a loop invariant" sr
      if m.reboundBuiltins.contains n then
        return ← bad s!"{n} in a loop invariant of a module that binds {n}" fsr
      let quantifier := n == "all" || n == "any"
      unless args.val.size == (if n == "isinstance" then 2 else 1) do
        return ← bad "a call in a loop invariant" sr
      for a in args.val do
        if quantifier then checkQuantifier c sr a else checkInvariant c a
    | _ => bad "a call in a loop invariant" sr
  | .Lambda sr .. => bad "a lambda in a loop invariant" sr
  | .NamedExpr sr .. => bad "an assignment expression in a loop invariant" sr
  | .Yield sr .. | .YieldFrom sr .. => bad "yield in a loop invariant" sr
  | .Await sr .. => bad "await in a loop invariant" sr
  | .Starred sr .. => bad "a starred expression in a loop invariant" sr
  | .List sr .. | .Tuple sr .. | .Set sr .. | .Dict sr .. => bad "a display in a loop invariant" sr
  | .ListComp sr .. | .SetComp sr .. | .DictComp sr .. | .GeneratorExp sr .. =>
    bad "a comprehension in a loop invariant" sr
  | .JoinedStr sr .. | .FormattedValue sr .. | .TemplateStr sr .. | .Interpolation sr .. =>
    bad "an f-string in a loop invariant" sr
termination_by sizeOf e

/-- Check `g`, the argument of `all` or `any` at `sr`: a generator expression with one `for`
clause, not `async`, whose target is a name, or a pair of names over `d.items()`. -/
def checkQuantifier (c : InvCtx) (sr : SourceRange) (g : expr SourceRange) : InvCheck := do
  let .GeneratorExp _ elt gens := g | bad "a call in a loop invariant" sr
  unless gens.val.size == 1 do
    return ← bad "a quantifier with several for clauses in a loop invariant" sr
  for _hc : cl in gens.val do
    match cl, _hc with
    | .mk_comprehension _ target iter ifs isAsync, _hc =>
    if isAsync.value != 0 then return ← bad "an async quantifier in a loop invariant" sr
    if let some what := targetProblem c.mangle ((dictView? iter).map (·.1)) target then
      return ← bad what sr
    have := Array.sizeOf_lt_of_mem _hc
    -- The view's dict, or the iterable.
    match _hi : iter with
    | .Call _ (.Attribute _ d _ _) _ _ =>
      if (dictView? iter).isSome then checkInvariant c d
      else return ← bad "a call in a loop invariant" sr
    | other => checkInvariant c other
    for x in ifs.val do checkInvariant c x
  checkInvariant c elt
termination_by sizeOf g

end

end -- public section

end StrataPython.Dyn.PyMarkers
