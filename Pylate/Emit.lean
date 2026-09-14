/-
Log emission: serialize an analysis run (or a rejection) into the JSON
format of RENDER_SPEC.md. The renderer and the instrumenter consume this
file and nothing else; status derivation lives here so every consumer
classifies identically.
-/
import Lean.Data.Json
import Pylate.Machine
import Pylate.Tables.Binary
import Pylate.Syntax.Check

namespace Pylate

open Lean (Json)

def dedupStr (xs : List String) : List String :=
  xs.foldr Fset.insert []

/-- Kinds that pose a dispatch question, so a target has to be resolved: the
    four value operations plus the protocol operations, which resolve
    `__bool__`, `__contains__`, `__eq__` and the unary duals. Stores are
    excluded by convention as posing no dispatch question, and a name read or
    an identity test is not dispatched at all.

    The `deferred` half of the summary must agree with the derived
    `deferred-dispatch` and `case-split` obligations, so both are gated on
    this one predicate. Mirrors `resid_status.is_dispatch_site`. -/
def isDispatchSite (r : Residual) : Bool :=
  !(r.kind == "setattr" || r.kind == "setitem" || r.kind == "name"
    || r.kind == "identity" || r.kind == "contract")

def residStatus (r : Residual) : String :=
  let tgts := dedupStr (r.cases.map (·.2))
  if r.cases.any (·.2 == "deferred") then "UNKNOWN"
  else if r.cases.isEmpty && !r.errors.isEmpty then "MUST_RAISE"
  else if tgts.length == 1 && r.errors.isEmpty then "RESOLVED"
  else if tgts.length > 1 then s!"SPLIT({tgts.length})"
  else ""

def tagJson (t : Tag) : Json := Json.str t.render

/-- Set components are unordered, so every emitted array is sorted: two
    analyzers that agree as sets must produce identical logs. -/
def sortedStrs (xs : List String) : Array Json :=
  ((xs.toArray.qsort (fun a b => a < b)).map Json.str)

def locLt (a b : Loc) : Bool :=
  if a.site != b.site then a.site.render < b.site.render
  else if a.cls.render != b.cls.render then a.cls.render < b.cls.render
  else !a.recent && b.recent

def locJson (l : Loc) : Json :=
  Json.mkObj [("site", Json.str l.site.render), ("cls", Json.str l.cls.render),
              ("recent", Json.bool l.recent)]

def valJson (v : AbsVal) : Json :=
  Json.mkObj [
    ("tags", Json.arr (sortedStrs (v.tags.map Tag.render))),
    ("locs", Json.arr ((v.locs.toArray.qsort locLt).map locJson)),
    ("funcs", Json.arr (sortedStrs v.funcs)),
    ("classes", Json.arr (sortedStrs v.classes)),
    -- The whole literal bag, every kind, rendered in Python spelling.
    ("literals", Json.arr (sortedStrs (v.lits.map Lit.render))),
    -- The `*` marker, per tag: these are the tags whose values `literals` does
    -- not enumerate.
    ("open", Json.arr (sortedStrs (v.litsOpen.map Tag.render))),
    -- Kept as aliases so every existing reader of the log keeps working; they
    -- are the `str` projection of the two fields above.
    ("string_literals", Json.arr (sortedStrs v.strLits)),
    ("string_open", Json.bool v.strOpen),
    ("witness", Json.bool v.witness)]

def lineJson (st : AState) : Json :=
  let roots := st.env.fold (init := []) (fun acc _ v => Fset.union v.locs acc)
  let reach := reachableLocs st roots
  let env := st.env.toList.foldr (fun (x, v) acc =>
    if (acc.map Prod.fst).contains x then acc else (x, valJson v) :: acc) []
  -- A cell holding bottom reads exactly like an absent cell, so it is not
  -- emitted: the two analyzers must not differ over a vacuous row.
  -- Internal edges take part in reachability above but are not emitted.
  let cells : List (Loc × CellSelector × AbsVal) :=
    st.heap.fold (init := []) fun acc key v =>
      if reach.contains key.1 && !v.isBot && !key.2.internal then
        (key.1, key.2, v) :: acc
      else acc
  -- Definite non-emptiness is reported as a `nonempty` cell.
  let cells := st.sizes.fold (init := cells) fun acc l size =>
    if size.emptiness == .nonempty && reach.contains l &&
        !(acc.any (fun (l', f, _) => l' == l && f == CellSelector.nonempty)) then
      -- `litV` rather than `V [.tbool]`: the cell exists exactly when the
      -- collection is *definitely* non-empty, so an unknown bool would render
      -- the marker as `*` and read as if the fact were in doubt.
      (l, CellSelector.nonempty, litV (.lbool true)) :: acc
    else acc
  -- Cells are emitted by their rendering, which is injective, so the log still
  -- names each cell uniquely without carrying the selector type.
  let heap := (cells.toArray.qsort (fun (l₁, f₁, _) (l₂, f₂, _) =>
      if l₁ != l₂ then locLt l₁ l₂ else f₁.render < f₂.render)).map
    (fun (l, f, v) =>
      Json.mkObj [("loc", locJson l), ("field", Json.str f.render),
                  ("val", valJson v)])
  -- Sizes are emitted alongside the heap rather than as a cell: `exact 2` is a
  -- property of the location, and the `nonempty` cell above can only say that
  -- the count is not zero.
  let sizes := (st.sizes.toList.filter (fun (l, _) => reach.contains l)).toArray
  let sizes := (sizes.qsort (fun a b => locLt a.1 b.1)).map (fun (l, size) =>
    Json.mkObj [("loc", locJson l), ("size", Json.str size.render)])
  Json.mkObj [("env", Json.mkObj env), ("heap", Json.arr heap),
              ("sizes", Json.arr sizes)]

def residJson (r : Residual) : Json :=
  Json.mkObj [
    ("line", Json.num r.line), ("col", Json.num r.col),
    ("kind", Json.str r.kind), ("desc", Json.str r.desc),
    ("expr", Json.str r.expr),
    ("ord", Json.num r.ord),
    ("result", valJson r.result),
    ("at", match r.atSt with
      | some st => lineJson st
      | none => Json.null),
    ("cases", Json.mkObj (r.cases.map (fun (t, o) => (t, Json.str o)))),
    ("steps", Json.arr ((r.steps.map fun (kind, tag, outcome) =>
      Json.mkObj [("kind", Json.str kind), ("tag", Json.str tag),
                  ("outcome", Json.str outcome)])).toArray),
    ("errors", Json.arr (r.errors.map Json.str).toArray),
    ("reached", Json.bool r.reached),
    ("updates", Json.arr (r.updates.map Json.str).toArray),
    ("contexts", Json.mkObj (r.perCtx.map (fun (l, s) => (l, Json.mkObj [
      ("cases", Json.mkObj (s.cases.map (fun (t, o) => (t, Json.str o)))),
      ("errors", Json.arr (s.errors.map Json.str).toArray),
      ("result", valJson s.result)]))))]

def obligJson (o : Oblig) : Json :=
  Json.mkObj [
    ("line", Json.num o.line), ("col", Json.num o.col),
    ("node", Json.str o.node.render), ("kind", Json.str o.kind),
    ("detail", Json.str o.detail)]

def violJson (v : Violation) : Json :=
  Json.mkObj [
    ("line", Json.num v.line), ("col", Json.num v.col),
    ("node", Json.str v.node.render), ("rule", Json.str v.rule),
    ("detail", Json.str v.detail)]

/-- The derived obligations restating residual statuses for the SMT
    hand-off, in analyzer.py's detail format. -/
def derivedObligs (residuals : List (NodeId × Residual)) : List Json :=
  residuals.filterMap fun (nid, r) =>
    let casesTxt := " | ".intercalate
      ((r.cases.map (fun (t, o) => s!"{t}->{o}")))
    let errsTxt := "; ".intercalate r.errors
    let mk := fun (kind detail : String) =>
      Json.mkObj [("line", Json.num r.line), ("col", Json.num r.col),
                  ("node", Json.str nid.render), ("kind", Json.str kind),
                  ("detail", Json.str detail)]
    -- A store resolves no target, so it raises no dispatch obligation; it can
    -- still fail, and a store that always fails must not go unrecorded.
    match residStatus r with
    | "MUST_RAISE" => some (mk "guaranteed-error" s!"{r.kind} {r.desc}: {errsTxt}")
    | "UNKNOWN" =>
      if isDispatchSite r then
        some (mk "deferred-dispatch" s!"{r.kind} {r.desc}: {casesTxt}")
      else none
    | s =>
      if s.startsWith "SPLIT" then
        if isDispatchSite r then
          some (mk "case-split" s!"{r.kind} {r.desc}: {casesTxt}")
        else none
      else if !r.errors.isEmpty then
        some (mk "error-guard" s!"{r.kind} {r.desc}: {errsTxt}")
      else none

/-- The global dispatch table (RENDER_SPEC 4b): one row per (tag, op)
    pair, aggregated over the residual table. -/
def dispatchTable (t : ClassTable) (residuals : List (NodeId × Residual)) :
    List Json := Id.run do
  let mut seen : Fset (String × String) := []
  let mut rows : List Json := []
  -- `store` and `field ...` are sentinels of the attribute and item protocols,
  -- but a call's outcome label is the callee's own name, and a function may be
  -- called `store`. Classify by the site's kind so a name cannot impersonate a
  -- sentinel.
  let cellSite := fun (kind : String) =>
    kind == "setattr" || kind == "getattr" ||
      kind == "setitem" || kind == "getitem"
  let target := fun (kind outcome : String) =>
    if outcome == "deferred" then Json.mkObj [("kind", Json.str "deferred")]
    else if cellSite kind &&
        (outcome.startsWith "field" || outcome == "store") then
      Json.mkObj [("kind", Json.str "field")]
    else if outcome.startsWith "construct " then
      Json.mkObj [("kind", Json.str "construct"),
                  ("class", Json.str (outcome.drop 10).toString)]
    else if outcome.startsWith "builtin " then
      Json.mkObj [("kind", Json.str "builtin"),
                  ("rule", Json.str (outcome.drop 8).toString)]
    else match outcome.splitOn "." with
      | [cn, mn] =>
        match t.getCls? cn with
        | some ci =>
          match ci.ownMethods.find? (·.1 == mn) with
          | some (_, fd) =>
            Json.mkObj [("kind", Json.str "code"),
                        ("label", Json.str outcome),
                        ("line", Json.num fd.p.line),
                        ("node", Json.str fd.p.id.render)]
          | none => Json.mkObj [("kind", Json.str "code"),
                                ("label", Json.str outcome)]
        | none => Json.mkObj [("kind", Json.str "code"),
                              ("label", Json.str outcome)]
      | _ => Json.mkObj [("kind", Json.str "code"),
                         ("label", Json.str outcome)]
  for (_, r) in residuals do
    let op := s!"{r.kind} {r.desc}"
    for (tag, outcome) in r.cases do
      if !seen.contains (tag, op) then
        seen := (tag, op) :: seen
        rows := rows ++ [Json.mkObj [("tag", Json.str tag),
          ("op", Json.str op), ("target", target r.kind outcome)]]
    for err in r.errors do
      match err.splitOn " -> " with
      | [tag, exc] =>
        if !seen.contains (tag, op) then
          seen := (tag, op) :: seen
          let tgt := if exc.startsWith "abort " then
            Json.mkObj [("kind", Json.str "abort"),
                        ("exc", Json.str (exc.drop 6).toString)]
          else
            Json.mkObj [("kind", Json.str "raise"), ("exc", Json.str exc)]
          rows := rows ++ [Json.mkObj [("tag", Json.str tag),
            ("op", Json.str op), ("target", tgt)]]
      | _ => pure ()
  return rows

-- -------------------------------------------------- resolved declarations

partial def annJson : Ann → Json
  | .any => Json.mkObj [("kind", Json.str "any")]
  | .atom name =>
    Json.mkObj [("kind", Json.str "atom"), ("name", Json.str name)]
  | .union members =>
    Json.mkObj [
      ("kind", Json.str "union"),
      ("members", Json.arr (members.map annJson).toArray)]
  | .generic name args variadic =>
    Json.mkObj [
      ("kind", Json.str "generic"),
      ("name", Json.str name),
      ("args", Json.arr (args.map annJson).toArray),
      ("variadic", Json.bool variadic)]
  | .literal values =>
    let valueJson : Const → Json
      | .cint n => Json.mkObj [
          ("kind", Json.str "int"), ("value", Json.str (toString n))]
      | .cbool b => Json.mkObj [
          ("kind", Json.str "bool"), ("value", Json.bool b)]
      | .cfloat s => Json.mkObj [
          ("kind", Json.str "float"), ("value", Json.str s)]
      | .cstr s => Json.mkObj [
          ("kind", Json.str "str"), ("value", Json.str s)]
      | .cnone => Json.mkObj [("kind", Json.str "none")]
    Json.mkObj [
      ("kind", Json.str "literal"),
      ("values", Json.arr (values.map valueJson).toArray)]
  | .required inner =>
    Json.mkObj [("kind", Json.str "required"), ("inner", annJson inner)]
  | .notRequired inner =>
    Json.mkObj [("kind", Json.str "not-required"), ("inner", annJson inner)]
  | .readOnly inner =>
    Json.mkObj [("kind", Json.str "read-only"), ("inner", annJson inner)]

def accessorSelector (name : String) : String :=
  if name.startsWith "@get:" || name.startsWith "@set:" then
    (name.drop 5).toString
  else name

def memberSelectors (t : ClassTable) : List String :=
  dedupStr (t.flatMap fun (_, ci) =>
    ci.ownMethods.map (fun (name, _) => accessorSelector name))

def fieldNames (t : ClassTable) : List String :=
  dedupStr (t.flatMap fun (_, ci) => ci.ownLayout)

def fieldOwner? (t : ClassTable) (ci : ClassInfo)
    (field : String) : Option String :=
  ci.mro.find? fun owner =>
    (t.getCls? owner).any (·.ownLayout.contains field)

def declaredBases (ci : ClassInfo) : List String :=
  if ci.isTypedDict && ci.bases.isEmpty then ["TypedDict"] else ci.bases

def runtimeBases (ci : ClassInfo) : List String :=
  if ci.isTypedDict then ["dict"]
  else if ci.bases.isEmpty then ["object"]
  else ci.bases

def runtimeMro (ci : ClassInfo) : List String :=
  if ci.isTypedDict then [ci.name, "dict", "object"]
  else ci.fullMro

def memberJson (t : ClassTable) (ci : ClassInfo)
    (selector : String) : Option (String × Json) :=
  let getter := resolveMethod t ci.name s!"@get:{selector}"
  let setter := resolveMethod t ci.name s!"@set:{selector}"
  if getter.isSome || setter.isSome then
    some (selector, Json.mkObj [
      ("kind", Json.str "property"),
      ("owner", Json.str ((getter.orElse fun _ => setter).map (·.1)
        |>.getD "")),
      ("getter_owner", match getter with
        | some (owner, _) => Json.str owner
        | none => Json.null),
      ("setter_owner", match setter with
        | some (owner, _) => Json.str owner
        | none => Json.null)])
  else
    match resolveMethod t ci.name selector with
    | some (owner, _) =>
      some (selector, Json.mkObj [
        ("kind", Json.str "method"),
        ("owner", Json.str owner)])
    | none => none

def fieldJson (t : ClassTable) (ci : ClassInfo)
    (field : String) : Option (String × Json) := do
  let owner ← fieldOwner? t ci field
  let ownerInfo ← t.getCls? owner
  let decl := ownerInfo.fields.find? (·.name == field)
  pure (field, Json.mkObj [
    ("owner", Json.str owner),
    ("annotation", match decl.bind (·.ann) with
      | some ann => annJson ann
      | none => Json.null)])

def classResolutionJson (t : ClassTable) (ci : ClassInfo) : Json :=
  let typedDict := if ci.isTypedDict then
    Json.mkObj [
      ("runtime_tag", Json.str "dict"),
      ("required_keys", Json.arr
        ((ci.fields.filter (·.required)).map (Json.str ∘ (·.name))).toArray),
      ("optional_keys", Json.arr
        ((ci.fields.filter (!·.required)).map (Json.str ∘ (·.name))).toArray),
      ("read_only_keys", Json.arr
        ((ci.fields.filter (·.readOnly)).map (Json.str ∘ (·.name))).toArray)]
  else Json.null
  let dataclass := if ci.isDataclass then
    Json.mkObj [
      ("frozen", Json.bool true),
      ("generated_methods", Json.arr
        ((["__init__", "__repr__", "__eq__", "__hash__", "__setattr__",
           "__delattr__"].map Json.str).toArray)),
      ("mutation_error", Json.str "FrozenInstanceError")]
  else Json.null
  Json.mkObj [
    ("declared_bases", Json.arr (declaredBases ci |>.map Json.str).toArray),
    ("runtime_bases", Json.arr (runtimeBases ci |>.map Json.str).toArray),
    ("shape_mro", Json.arr (ci.mro.map Json.str).toArray),
    ("runtime_mro", Json.arr (runtimeMro ci |>.map Json.str).toArray),
    ("members", Json.mkObj
      ((memberSelectors t).filterMap (memberJson t ci))),
    ("fields", Json.mkObj ((fieldNames t).filterMap (fieldJson t ci))),
    ("subclasses", Json.arr (subclassClosure t ci.name |>.map Json.str).toArray),
    ("exception_mro", Json.arr
      ((if ci.isExc then excMro t ci.name ++ ["object"] else [])
        |>.map Json.str |>.toArray)),
    ("dataclass", dataclass),
    ("typed_dict", typedDict)]

def binaryOps : List BinOp :=
  [.add, .sub, .mul, .div, .floordiv, .mod, .pow, .bitOr, .bitAnd,
   .bitXor, .lshift, .rshift]

def binaryOrdersJson (ctx : Actx) : List Json := Id.run do
  let classes := ctx.classes.filter (fun (_, ci) => !ci.isTypedDict)
  let mut rows : List Json := []
  for (left, _) in classes do
    for (right, _) in classes do
      for op in binaryOps do
        let leftTag := Tag.tobj left
        let rightTag := Tag.tobj right
        let leftVal := V [leftTag]
        let rightVal := V [rightTag]
        let (candidates, _) :=
          (Binary.candidates op leftTag rightTag leftVal rightVal).run ctx
        if !candidates.isEmpty then
          rows := rows ++ [Json.mkObj [
            ("left", Json.str left),
            ("op", Json.str op.render),
            ("right", Json.str right),
            ("candidates", Json.arr
              (candidates.map (Json.str ∘ Binary.Candidate.label)).toArray)]]
  return rows

def resolutionJson (ctx : Actx) : Json :=
  Json.mkObj [
    ("classes", Json.mkObj (ctx.classes.map fun (name, ci) =>
      (name, classResolutionJson ctx.classes ci))),
    ("binary_orders", Json.arr (binaryOrdersJson ctx).toArray)]

/-- The sort plan for the Laurel lowering (SMT_ENCODING.md, sort regimes).
    Pylate emits data; lowering that data into the Laurel Strata dialect is a
    separate step, and Laurel is what reaches a solver.
    Both regimes report the residual polymorphism (carrier = union of a
    binding's fixpoint tags across all lines, definedness tags excluded;
    flavor = deduplicated multi-tag carrier). They differ in what the
    lowering may lean on:
    - checked (default): every binding uses the universal value sort;
      fixpoint tag claims appear only as switch branches whose catch-all
      is assert false, so the operational semantics CHECKS the fixpoint.
    - residual: bindings are carved into per-flavor ADTs (and native
      sorts when monomorphic). Smallest encoding, but carrier
      completeness becomes TRUSTED: a tag the analysis missed is
      unrepresentable, the catch-all is vacuous there, and soundness
      rests on the fixpoint certificate plus transfer soundness. -/
def sortsJson (ctx : Actx) (mode : String) : Json := Id.run do
  -- Keyed, because this ran once per binding, per heap cell, per line snapshot,
  -- and each call did a linear `find?` followed by either a `map` rebuilding the
  -- whole list or an `append` copying its spine. On a 4116-line file it was the
  -- single dominant cost of the entire run -- and it is output formatting, not
  -- analysis. A native profile put essentially all self time in this function's
  -- list traversals.
  let mut carriers : Std.HashMap String (Fset String) := {}
  let add := fun (cs : Std.HashMap String (Fset String)) (k : String)
      (tags : List Tag) =>
    let ts := (tags.filter (fun t =>
      t != Tag.tunbound && t != Tag.tuninit)).map Tag.render
    if ts.isEmpty then cs else
    match cs[k]? with
    | some existing => cs.insert k (Fset.union ts existing)
    | none => cs.insert k (ts.foldr Fset.insert [])
  for (_, st) in (lineStates ctx).toList do
    for (x, v) in st.env.toList do
      carriers := add carriers x v.tags
    for ((l, f), v) in st.heap.toList do
      if f.internal then continue
      carriers := add carriers
        s!"{l.cls.render}@{l.site}{if l.recent then "" else "*"}.{f.render}" v.tags
    for (l, size) in st.sizes.toList do
      if size.emptiness == .nonempty then
        carriers := add carriers
          s!"{l.cls.render}@{l.site}{if l.recent then "" else "*"}.nonempty"
          [Tag.tbool]
  let mut mono := 0
  let mut flavors : List (String × List String) := []
  let mut bindings : List (String × Json) := []
  -- Sorted, because a hash map has no order and this reaches the log.
  for (k, s) in carriers.toList.mergeSort (·.1 < ·.1) do
    let names := (s.toArray.qsort (fun a b => a < b)).toList
    let entry := fun (sort : String) => Json.mkObj
      [("carrier", Json.arr (names.map Json.str).toArray),
       ("sort", Json.str sort)]
    if names.length == 1 then
      mono := mono + 1
      bindings := bindings ++ [(k, entry (
        if mode == "residual" then s!"native:{names.head!}"
        else "universal"))]
    else
      let fname := "|".intercalate names
      if !(flavors.any (·.1 == fname)) then
        flavors := flavors ++ [(fname, names)]
      bindings := bindings ++ [(k, entry (
        if mode == "residual" then s!"adt:{fname}" else "universal"))]
  let trust := if mode == "residual" then
      "sorts carved from the fixpoint's residual tag sets: carrier \
       completeness is TRUSTED, a missed flow is unrepresentable and \
       escapes the switch catch-alls; requires the fixpoint certificate"
    else
      "bindings use the universal value sort: fixpoint tag claims \
       appear only as switch branches with assert-false catch-alls, \
       so the operational semantics checks the fixpoint"
  return Json.mkObj [
    ("mode", Json.str mode),
    ("trust", Json.str trust),
    ("summary", Json.mkObj [
      ("bindings", Json.num carriers.size),
      ("monomorphic", Json.num mono),
      ("flavors", Json.num flavors.length)]),
    ("flavors", Json.arr (flavors.map (fun (n, vs) => Json.mkObj
      [("name", Json.str n),
       ("variants", Json.arr (vs.map Json.str).toArray)])).toArray),
    ("bindings", Json.mkObj bindings)]

/-- Every heap cell the run produced, checked against the class it sits on.
    `CellSelector.validFor` is consulted by `RuleCompile` for rule data and by
    the `cell-validity` validator condition, but the kernel's own `heapSet` does
    not consult it, so the 398 hand-written transfer sites are covered here
    instead: any cell an analyzed program leaves on a class that cannot hold it
    is reported, and `run_all.py` fails on a non-empty list. Empty on the whole
    golden corpus. -/
def cellViolations (ctx : Actx) : List String :=
  let rows := (lineStates ctx).toList.flatMap fun (_, st) =>
    st.heap.toList.filterMap fun ((l, f), v) =>
      if v.isBot || f.validFor l.cls then none
      else some s!"{l.cls.render}@{l.site}.{f.render}"
  rows.eraseDups

/-- Every program point the analysis recorded a state at, keyed by its address.

    This is the `states` map as data. A key is a program point plus the call
    frames that led to it -- `3.2@loop-head < 4.1` is the loop head of node `3.2`
    reached through the call at node `4.1` -- so a reader can ask what one
    specific loop head, handler entry or branch merge held under one specific call
    chain. `lines` is this map joined by source line, which cannot answer that.

    Join points are the reason the key needs the `@kind` part: a `while` owns its
    pre-loop state and four more (`loop-head`, `loop-exit`, `break-target`,
    `continue-target`), and a `try` owns a `handler-entry` per clause plus three,
    all on one node. -/
def pointsJson (ctx : Actx) : Json :=
  let rows := ctx.states.toList.mergeSort (fun a b =>
    if a.2.1.line != b.2.1.line then a.2.1.line < b.2.1.line
    else a.1.render < b.1.render)
  Json.mkObj (rows.map (fun (addr, p, st) =>
    (addr.render, Json.mkObj [
      ("line", Json.num p.line),
      ("col", Json.num p.col),
      ("node", Json.str addr.point.owner.render),
      ("join", match addr.point.joinKind with
        | some kind => Json.str kind.render
        | none => Json.null),
      ("frames", Json.arr (addr.frames.map (fun f => Json.str f.render)).toArray),
      ("state", lineJson st)])))

def emitAccepted (file : String) (src : List String) (ctx : Actx)
    (m : AMulti) (sortsMode : String := "checked") : Json :=
  let resids := ctx.residuals
  let dispatchSites := resids.filter (fun (_, r) => isDispatchSite r)
  let ns := dispatchSites.length
  let nd := (dispatchSites.filter
    (fun (_, r) => residStatus r == "RESOLVED")).length
  let ndef := (dispatchSites.filter (fun (_, r) =>
    let s := residStatus r
    s == "UNKNOWN" || s.startsWith "SPLIT")).length
  let allObligs := (ctx.obligations.map obligJson) ++ derivedObligs resids
  Json.mkObj [
    ("pylate_log", Json.num 1),
    ("file", Json.str file),
    ("source", Json.arr (src.map Json.str).toArray),
    ("status", Json.str "accepted"),
    ("policy", Json.mkObj [
      ("preset", Json.str ctx.policy.preset),
      ("modes", Json.mkObj (ctx.policy.modes.map (fun (c, m) =>
        (c, Json.str (if m == RMode.abort then "abort" else "model")))))]),
    ("sorts", sortsJson ctx sortsMode),
    -- Every machine raise the analysis produced, modelled or aborted by
    -- policy. This is the complete exceptional record of the run.
    ("machine_raises", Json.arr (ctx.machineRaises.map (fun site =>
      Json.mkObj [
        ("node", Json.str site.node.render),
        ("line", Json.num site.line),
        ("col", Json.num site.col),
        ("exc", Json.str site.exc),
        ("mode", Json.str
          (if site.mode == RMode.abort then "abort" else "model"))])).toArray),
    ("violations", Json.arr #[]),
    ("residuals", Json.mkObj (resids.map (fun (nid, r) =>
        (nid.render, residJson r)))),
    ("obligations", Json.arr allObligs.toArray),
    ("dispatch", Json.arr (dispatchTable ctx.classes resids).toArray),
    ("resolution", resolutionJson ctx),
    ("handlers", Json.mkObj (ctx.handlerTables.map (fun (nid, line, rows) =>
      (toString nid, Json.mkObj [
        ("line", Json.num line),
        ("rows", Json.arr (rows.map (fun (e, r) => match r with
          | some (cn, ln) => Json.mkObj [("exc", Json.str e),
              ("caught_by", Json.mkObj [("clause", Json.str cn),
                                        ("line", Json.num ln)])]
          | none => Json.mkObj [("exc", Json.str e),
              ("match", Json.str "propagates")])).toArray)])))),
    ("lines", Json.mkObj (((lineStates ctx).toList.mergeSort (·.1 < ·.1)).map (fun (l, st) =>
        (toString l, lineJson st)))),
    ("points", pointsJson ctx),
    ("summary", Json.mkObj [("sites", Json.num ns),
                            ("devirt", Json.num nd),
                            ("deferred", Json.num ndef)]),
    ("cell_violations",
      Json.arr ((cellViolations ctx).map Json.str).toArray),
    ("module", Json.mkObj [
      ("may_raise", Json.arr (m.excs.map Json.str).toArray),
      ("unreached", Json.arr ((unreached ctx).map Json.str).toArray)])]

/-- The admission verdict alone: the shape of `emitRejected` with an accepted
    status and no analysis in it.

    Admission is decided by the lowering, before any policy applies, so a gate
    that only asks "is this program in the subset, and if not why" does not need
    the fixpoint. Skipping it is what makes that gate affordable per build: the
    admission check over the corpus is dominated by one 4,000-line program whose
    analysis it never needed. -/
def emitCheckOnly (file : String) (src : List String) : Json :=
  Json.mkObj [
    ("pylate_log", Json.num 1),
    ("file", Json.str file),
    ("source", Json.arr (src.map Json.str).toArray),
    ("status", Json.str "accepted"),
    ("violations", Json.arr #[]),
    ("residuals", Json.mkObj []),
    ("obligations", Json.arr #[]),
    ("dispatch", Json.arr #[]),
    ("resolution", Json.mkObj [
      ("classes", Json.mkObj []), ("binary_orders", Json.arr #[])]),
    ("handlers", Json.mkObj []),
    ("lines", Json.mkObj []),
    ("summary", Json.mkObj [("sites", Json.num 0), ("devirt", Json.num 0),
                            ("deferred", Json.num 0)]),
    ("module", Json.mkObj [("may_raise", Json.arr #[]),
                           ("unreached", Json.arr #[])])]

def emitRejected (file : String) (src : List String)
    (vs : Array Violation) : Json :=
  let sorted := (vs.toList.toArray.qsort
    (fun a b => a.line < b.line || (a.line == b.line && a.col < b.col)))
  Json.mkObj [
    ("pylate_log", Json.num 1),
    ("file", Json.str file),
    ("source", Json.arr (src.map Json.str).toArray),
    ("status", Json.str "rejected"),
    ("violations", Json.arr (sorted.map violJson)),
    ("residuals", Json.mkObj []),
    ("obligations", Json.arr #[]),
    ("dispatch", Json.arr #[]),
    ("resolution", Json.mkObj [
      ("classes", Json.mkObj []), ("binary_orders", Json.arr #[])]),
    ("handlers", Json.mkObj []),
    ("lines", Json.mkObj []),
    ("summary", Json.mkObj [("sites", Json.num 0), ("devirt", Json.num 0),
                            ("deferred", Json.num 0)]),
    ("module", Json.mkObj [("may_raise", Json.arr #[]),
                           ("unreached", Json.arr #[])])]

end Pylate
