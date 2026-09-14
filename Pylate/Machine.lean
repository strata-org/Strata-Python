/-
The analysis machine: the write-only logs (residual table,
obligations, per-line snapshots, 4c handler tables), the analysis
context and its state monad, the policy-aware machine-raise helper,
name reading, annotation assume/assert, generator exception plumbing,
and the opaque-call havoc.
-/
import Std.Data.HashMap
import Pylate.Syntax.ClassTable
import Pylate.Tables.MethodInventory
import Pylate.Engine.Policy
import Pylate.Engine.Exc
import Pylate.Engine.Update
import Pylate.Tables.ShapePolicy
import Pylate.Tables.BuiltinOutcomes

namespace Pylate

/-- Per-invocation slice of a residual: the rows contributed under one
    inlined call chain, so the render can show each particular
    invocation while the global table keeps the join. -/
structure CtxSlice where
  cases  : List (String × String) := []
  errors : Fset String := []
  result : AbsVal := AbsVal.bot
deriving Repr, Inhabited

structure Residual where
  line    : Nat
  col     : Nat
  kind    : String
  desc    : String
  expr    : String := ""
  ord     : Nat := 0
  result  : AbsVal := AbsVal.bot
  atSt    : Option AState := none
  cases   : List (String × String) := []
  /-- Protocol steps executed while evaluating this site: an argument
      conversion, an iterator acquisition, a hook call. They are not dispatch
      alternatives of the site and must not change its devirtualization. -/
  steps   : List (String × String × String) := []
  errors  : Fset String := []
  updates : Fset String := []
  /-- Whether this site's own operation ran on some path. A site claimed by
      `resSite` whose operand raised first is never reached, and reporting it
      as raising would blame it for a failure it did not produce. -/
  reached : Bool := false
  perCtx  : List (String × CtxSlice) := []
deriving Repr, Inhabited

structure Oblig where
  line   : Nat
  col    : Nat
  node   : NodeId
  kind   : String
  detail : String
deriving Repr, Inhabited

structure MachineRaiseSite where
  node : NodeId
  line : Nat
  col  : Nat
  exc  : String
  mode : RMode
deriving Repr, Inhabited

structure Actx where
  classes     : ClassTable := []
  funcs       : List (String × FuncDef) := []
  glb         : List (String × AbsVal) := []
  residuals   : List (NodeId × Residual) := []
  obligations : List Oblig := []
  machineRaises : List MachineRaiseSite := []
  /-- Entry snapshots, keyed by `Addr` -- program point plus call context -- and
      carrying the `Pos` they were taken at so the per-line view can be derived
      from them.

      The context has to be in the key. This map lives in the analysis context
      rather than being threaded like `AState`, and the analysis is
      context-sensitive by inlining, so one syntactic node is reached once per call
      chain. Keying on the point alone would join every context that reaches a
      node, which is what lets a value from one call path appear on another.

      A `HashMap` rather than a list: `snap` runs once per statement execution and
      each entry carries an `AState` per cell, so a linear structure cost O(L^2)
      states for an L-line file and dominated the analysis on a large one. -/
  states      : Std.HashMap Addr (Pos × AState) := {}
  callStack   : List String := []
  localScopes : List (Fset String) := []
  handling    : List (Fset String) := []
  called      : Fset String := []
  yields      : List (List AbsVal) := []
  genExc      : List (NodeId × Fset String) := []
  ordCtr      : Nat := 0
  policy      : Policy := Policy.strict
  -- 4c handler match tables: try node -> line -> (exc class, caught-by
  -- clause name and line, or none = propagates)
  handlerTables : List (NodeId × Nat × List (String × Option (String × Nat))) := []
  -- dispatch-resolution memos: the class table is fixed for the run, so
  -- resolution is a pure function of its key and the caches are sound
  resolveCache : Std.HashMap (String × String) (Option (String × FuncDef)) := {}
  excMroCache  : Std.HashMap String (List String) := {}
  closureCache : Std.HashMap String (List String) := {}
  -- invocation labels: callee:callSiteLine per inlined frame, so two
  -- calls to the same helper are distinct contexts (callStack cannot
  -- serve: it carries names only and collapses them)
  ctxStack : List String := []
  /-- Call sites as node paths, innermost first, each paired with the digest of
      the stack up to and including it, so entering a call is a cons and leaving is
      a `drop 1` with no digest recomputation either way.

      This is what `Addr` reads to tell `foo > bar > x` from
      `foo > qux > bar > x`. `ctxStack` alongside it is the rendered form the
      output uses. -/
  ctxFrames : List (NodeId × UInt64) := []
  /-- Exception classes that an enclosing `try` in the program being analysed
      would catch, innermost last. The abort policy consults it so a machine
      raise the program handles is modelled rather than pruned: aborting a
      caught exception would kill a handler the source clearly relies on. -/
  activeHandlers : List (Fset String) := []
deriving Inhabited

abbrev M := StateM Actx

/-- The current inlined call chain, outermost first; the module level is
    "module". Labels the per-invocation residual slices. -/
def ctxLabel (c : Actx) : String :=
  if c.ctxStack.isEmpty then "module"
  else " > ".intercalate c.ctxStack.reverse

/-- The digest of the current frame stack. -/
def ctxDigest (c : Actx) : UInt64 :=
  (c.ctxFrames.head?.map (·.2)).getD (mixHash 13 17)

/-- The address of a program point in the current call context. O(1). -/
def addrAt (c : Actx) (pp : PP) : Addr :=
  { digest := mixHash (ctxDigest c) (hash pp)
    point := pp
    frames := c.ctxFrames.map (·.1) }


def oblige (p : Pos) (kind detail : String) : M Unit :=
  modify fun c =>
    if c.obligations.any (fun o => o.node == p.id && o.kind == kind) then c
    else { c with obligations :=
      c.obligations ++ [⟨p.line, p.col, p.id, kind, detail⟩] }

private def joinOutcome (old new : String) : String :=
  let parts := old.splitOn " | "
  if parts.contains new then old else old ++ " | " ++ new

/-- A row whose kind differs from the site's own kind was produced by a nested
    protocol step, not by this site's dispatch. -/
def resCase (p : Pos) (kind desc tag outcome : String) : M Unit :=
  modify fun c =>
    let lbl := ctxLabel c
    let fresh : Residual :=
      { line := p.line
        col := p.col
        kind := kind
        desc := desc
        ord := c.ordCtr }
    let updRows := fun (cases : List (String × String))
        (errors : Fset String) =>
      if outcome.startsWith "!" then
        let cls := (outcome.drop 1).toString
        -- The `code` tag marks a failure propagating out of called code. The
        -- policy governs machine raises only, so labelling such a row `abort`
        -- claims an assertion failure the analysis never made: an explicit
        -- `raise ValueError` reaching here has no abort obligation, and the
        -- exception is a modelled edge.
        let shown := if tag != "code" && c.policy.aborts (excCategory cls)
          then s!"abort {cls}" else cls
        (cases, Fset.insert s!"{tag} -> {shown}" errors)
      else match cases.find? (·.1 == tag) with
        | some _ =>
          (cases.map (fun (t, o) =>
            if t == tag then (t, joinOutcome o outcome) else (t, o)), errors)
        | none => (cases ++ [(tag, outcome)], errors)
    let upd := fun (r : Residual) =>
      if r.kind != kind then
        -- Keep failures visible in `errors`; the step itself is not a target.
        let es := if outcome.startsWith "!" then
            let cls := (outcome.drop 1).toString
            let shown := if tag != "code" && c.policy.aborts (excCategory cls)
              then s!"abort {cls}" else cls
            Fset.insert s!"{tag} -> {shown}" r.errors
          else r.errors
        { r with
          steps := r.steps ++ [(kind, tag, outcome)]
          errors := es }
      else
      let (cs, es) := updRows r.cases r.errors
      let slice := ((r.perCtx.find? (·.1 == lbl)).map (·.2)).getD {}
      let (scs, ses) := updRows slice.cases slice.errors
      let slice' : CtxSlice :=
        { slice with
          cases := scs
          errors := ses }
      let perCtx := if r.perCtx.any (·.1 == lbl)
        then r.perCtx.map (fun (l, s) =>
          if l == lbl then (l, slice') else (l, s))
        else r.perCtx ++ [(lbl, slice')]
      { r with
        cases := cs
        errors := es
        reached := true
        perCtx := perCtx }
    match c.residuals.find? (·.1 == p.id) with
    | some _ =>
      { c with residuals := c.residuals.map (fun (i, r) =>
          if i == p.id then (i, upd r) else (i, r)) }
    | none => { c with ordCtr := c.ordCtr + 1
                       residuals := c.residuals ++ [(p.id, upd fresh)] }

/-- Claim a site's residual kind and description before anything it evaluates
    can record against the same node. Adds no outcome rows. -/
def resSite (p : Pos) (kind desc : String) : M Unit :=
  modify fun c =>
    match c.residuals.find? (·.1 == p.id) with
    | some _ => c
    | none =>
      { c with
        ordCtr := c.ordCtr + 1
        residuals := c.residuals ++ [(p.id,
          { line := p.line, col := p.col, kind, desc, ord := c.ordCtr })] }

/-- Record an outcome on a site that already has a residual, reusing its kind
    and description. A hook invoked while evaluating a site must not decide how
    that site is classified. -/
def resCaseAt (p : Pos) (fallbackKind fallbackDesc tag outcome : String) :
    M Unit := do
  let c ← get
  match c.residuals.find? (·.1 == p.id) with
  | some (_, existing) => resCase p existing.kind existing.desc tag outcome
  | none => resCase p fallbackKind fallbackDesc tag outcome

/-- Report an outcome only if the site already has a residual.

    A propagating exception is an outcome of an operation that dispatches, and
    such a site already has a row from its own `resCase`. A structural node --
    `not`, an f-string, a literal -- resolves no target and has no row, so
    attaching to it would mint a dispatch site that does not exist. `resCaseAt`
    creates one; this does not, which is the difference between reporting an
    outcome and inventing a site. -/
def resCaseIfPresent (p : Pos) (tag outcome : String) : M Unit := do
  let c <- get
  match c.residuals.find? (·.1 == p.id) with
  | some (_, existing) => resCase p existing.kind existing.desc tag outcome
  | none => pure ()

/-- Classes that the residual table actually reports. `machineRaises` is
    deliberately not consulted: it is populated by the raise itself, so counting
    it would make the check below vacuous. -/
def reportedClasses (c : Actx) : Fset String :=
  c.residuals.foldl (fun out (_, residual) =>
    residual.errors.foldl (fun out row =>
      match (row.splitOn " -> ").getLast? with
      | some outcome =>
        Fset.insert (if outcome.startsWith "abort " then
          (outcome.drop 6).toString else outcome) out
      | none => out) out) []

/-- `classes` are the exceptional outcomes a statement produced. Attribution to
    a particular operand site is the transfer's business; what must not happen
    is an outcome that no site reports at all, which is how an empty-list
    `list.pop` came to have `IndexError` in its flow and nothing in the log. -/
def verifyReported (p : Pos) (before : Fset String)
    (classes : Fset String) : M Unit := do
  if classes.isEmpty then return
  let c ← get
  let reported := reportedClasses c
  -- A class the interpreter never machine-raised cannot be an interpreter
  -- outcome, so it came from an explicit `raise`, which is not a dispatch site.
  -- Provenance itself does not survive the legacy AMulti bridge, which carries
  -- only a class set, so this criterion stands in for it until statement
  -- routing stops going through AMulti.
  let machineRaised : Fset String :=
    c.machineRaises.foldl (fun out site => Fset.insert site.exc out) []
  for cls in classes do
    if machineRaised.contains cls && !(reported.contains cls)
        && !(before.contains cls) then
      oblige p "unreported-outcome"
        s!"{cls} is an outcome of this statement but no site reports it"

def resExpr (p : Pos) (src : String) : M Unit :=
  modify fun c =>
    { c with residuals := c.residuals.map (fun (i, r) =>
        if i == p.id then (i, { r with expr := src }) else (i, r)) }

def resAt (p : Pos) (st : AState) : M Unit :=
  modify fun c =>
    { c with residuals := c.residuals.map (fun (i, r) =>
        if i == p.id then
          (i, { r with atSt := some (match r.atSt with
                  | some prev => prev.join st
                  | none => st) })
        else (i, r)) }

def resResult (p : Pos) (v : AbsVal) : M Unit :=
  modify fun c =>
    let lbl := ctxLabel c
    { c with residuals := c.residuals.map (fun (i, r) =>
        if i == p.id then
          let slice := ((r.perCtx.find? (·.1 == lbl)).map (·.2)).getD {}
          let slice' : CtxSlice := { slice with result := slice.result.join v }
          let perCtx := if r.perCtx.any (·.1 == lbl)
            then r.perCtx.map (fun (l, s) =>
              if l == lbl then (l, slice') else (l, s))
            else r.perCtx ++ [(lbl, slice')]
          (i, { r with
                result := v
                perCtx := perCtx })
        else (i, r)) }

def resUpdate (p : Pos) (mode : String) : M Unit :=
  modify fun c =>
    { c with residuals := c.residuals.map (fun (i, r) =>
        if i == p.id then (i, { r with updates := Fset.insert mode r.updates })
        else (i, r)) }

/-- Record the state at a program point.

    The `line == 0` guard skips the nodes CPython gives no position to -- the
    operator families and `expr_context`. `Label.lean` maps those categories to
    line 0 for exactly this test. -/
def snapAt (pp : PP) (p : Pos) (st : AState) : M Unit :=
  if p.line == 0 then pure () else
  modify fun c =>
    let key := addrAt c pp
    let joined := match c.states[key]? with
      | some (_, old) => old.join st
      | none => st
    { c with states := c.states.insert key (p, joined) }

/-- The state at a node. -/
def snap (p : Pos) (st : AState) : M Unit := snapAt (.node p.id) p st

/-- The state at a join a node induces: a loop head, an `if` merge, a handler
    entry. -/
def snapJoin (kind : JoinKind) (p : Pos) (st : AState) : M Unit :=
  snapAt (.join p.id kind) p st

/-- The per-line view, **derived** by folding `states` and joining by line.

    A computed projection rather than a second map, so the line view cannot drift
    from the per-point view. The rendered output reads this. -/
def lineStates (c : Actx) : Std.HashMap Nat AState :=
  c.states.fold (init := {}) fun acc _ (p, st) =>
    match acc[p.line]? with
    | some old => acc.insert p.line (old.join st)
    | none => acc.insert p.line st

def markCalled (n : String) : M Unit :=
  modify fun c => { c with called := Fset.insert n c.called }

-- ----------------------------------------------------------- exceptions


/-- Whether an enclosing handler in the analysed program catches this class. -/
def handledHere (c : Actx) (cls : String) : Bool :=
  c.activeHandlers.any fun caught =>
    caught.any fun handler =>
      handler == cls || (excMro c.classes cls).contains handler

/-- Machine raise under the abort policy. An abort-category class emits
    an obligation and contributes no exceptional continuation (the
    success path continues as if the raise were proven absent); a
    modeled class joins the exception flow as before. Explicit user
    raises never come through here, and neither does a class an enclosing
    handler catches: pruning that would kill a live handler. -/

def mraise (p : Pos) (e : Exc) (st : AState) (ts : Fset String)
    (declaredCategory : Option String := none) : M Exc := do
  let c ← get
  let mut out := e
  for cls in ts do
    -- `declaredCategory` marks a raise *our* semantics declares rather than one
    -- CPython performs. A violated parameter annotation is the case: CPython
    -- does not check annotations at runtime, so the call raises nothing there,
    -- and we stop because we cannot continue soundly -- not because an
    -- exception happens. Two consequences follow. Its category is not derived
    -- from the class, since the class is only how the failure would eventually
    -- surface. And it is uncatchable: `handledHere` suppresses an abort because
    -- pruning a class a handler catches would kill a live handler, but no
    -- `except TypeError` can catch an exception no execution produces.
    let cat := declaredCategory.getD (excCategory cls)
    let aborts := c.policy.aborts cat &&
      (declaredCategory.isSome || !handledHere c cls)
    let mode := if aborts then RMode.abort else RMode.model
    -- One syntactic site is reached from several escape contexts: each user
    -- function is analyzed standalone as its own entry point, and again inlined
    -- at every call. A context whose enclosing `try` catches the class models
    -- it; one without a handler aborts. The log carries one row per (site,
    -- class), so the two verdicts must be combined rather than raced: `abort`
    -- wins, because it is a proof duty owed for the context that does not
    -- handle the raise, and dropping it would discharge that duty for free.
    modify fun c =>
      match c.machineRaises.find? (fun r => r.node == p.id && r.exc == cls) with
      | some existing =>
        if existing.mode == RMode.abort || mode == RMode.model then c
        else { c with machineRaises := c.machineRaises.map fun r =>
          if r.node == p.id && r.exc == cls then { r with mode } else r }
      | none => { c with machineRaises := c.machineRaises ++
          [⟨p.id, p.line, p.col, cls, mode⟩] }
    if aborts then
      oblige p s!"abort:{cls}"
        s!"machine raise of {cls} aborts under policy ({cat}=abort): prove this site safe"
    else
      out := Exc.add out st [cls]
  pure out

-- ------------------------------------------------------------- helpers

def readName (st : AState) (x : String) : M AbsVal := do
  let v := st.envGet x
  if v.tags == [Tag.tunbound] then
    let c ← get
    match c.glb.find? (·.1 == x) with
    | some (_, g) => pure g
    | none =>
      if x == "NotImplemented" then pure (V [.tnotimpl])
      else if builtinTypeNames.contains x || builtinExcs.contains x then
        pure (V [.ttype] (classes := [x]))
      else if builtinFuncs.contains x then pure (V [.tfunc] (funcs := [x]))
      else pure v
  else pure v


def annAtomTags (t : ClassTable) (n : String) : Option (Fset Tag) :=
  match n with
  | "int" => some [Tag.tbool, Tag.tint]
  | "bool" => some [Tag.tbool]
  | "float" => some [Tag.tbool, Tag.tint, Tag.tfloat]
  | "complex" => some [Tag.tbool, Tag.tint, Tag.tfloat, Tag.tcomplex]
  | "str" => some [Tag.tstr]
  | "None" | "NoneType" => some [Tag.tnone]
  | "list" | "List" => some [Tag.tlist]
  | "dict" | "Dict" => some [Tag.tdict]
  | "set" | "Set" => some [Tag.tset]
  | "tuple" | "Tuple" => some [Tag.ttuple]
  | "NotImplemented" | "NotImplementedType" => some [Tag.tnotimpl]
  | _ =>
    match t.getCls? n with
    | some ci =>
      if ci.isTypedDict then some [Tag.tdict]
      else some ((subclassClosure t n).map Tag.tobj)
    | none => none

partial def annTags (t : ClassTable) : Ann → Option (Fset Tag)
  | .any => none
  | .atom n => annAtomTags t n
  | .union members => do
    let mut out : Fset Tag := []
    for a in members do
      let ts ← annTags t a
      out := Fset.union ts out
    pure out
  | .generic n _ _ => annAtomTags t n
  | .literal values =>
    some (values.foldl (fun out v =>
      Fset.insert (match v with
        | .cint _ => .tint | .cbool _ => .tbool | .cfloat _ => .tfloat
        | .cstr _ => .tstr | .cnone => .tnone) out) [])
  | .required a | .notRequired a | .readOnly a => annTags t a

structure AnnStrings where
  hasString : Bool := false
  literals  : Fset String := []
  isOpen    : Bool := false
deriving Inhabited

partial def annStrings : Ann → AnnStrings
  | .any => {}
  | .atom "str" => ⟨true, [], true⟩
  | .atom _ => {}
  | .generic _ _ _ => {}
  | .literal values =>
    let ss := values.filterMap (fun v => match v with
      | .cstr s => some s | _ => none)
    ⟨!ss.isEmpty, ss.foldr Fset.insert [], false⟩
  | .union members =>
    members.foldl (fun out a =>
      let d := annStrings a
      ⟨out.hasString || d.hasString,
       Fset.union out.literals d.literals,
       out.isOpen || d.isOpen⟩) {}
  | .required a | .notRequired a | .readOnly a => annStrings a

/-- Assume-side of a contract: meet with the annotation's tag set; an
    unknown (`any`) value is not refined (no witness region). -/
def assumeAnn (t : ClassTable) (v : AbsVal) (a : Ann) : AbsVal :=
  match annTags t a with
  | none => v
  | some tags =>
    if Tag.tany ∈ v.tags then v
    else
      let narrowed :=
        v.restrictTags (Fset.insert Tag.tunbound (Fset.insert Tag.tuninit tags))
      let sd := annStrings a
      if Tag.tstr ∈ narrowed.tags && sd.hasString && !sd.isOpen then
        -- A closed `Literal[...]` names the strings exactly, so the `str` side
        -- of the bag becomes those and stops being open. Literals of other tags
        -- are left alone: the annotation says nothing about them, and with one
        -- bag per value that has to be said explicitly.
        let refined := if narrowed.strOpen then sd.literals
          else Fset.inter narrowed.strLits sd.literals
        { narrowed with
          lits := Fset.union
            (narrowed.lits.filter (fun l => decide (l.tag ≠ Tag.tstr)))
            (refined.map Lit.lstr)
          litsOpen := narrowed.litsOpen.filter (fun t => decide (t ≠ Tag.tstr)) }
      else narrowed

def annEntailed (t : ClassTable) (v : AbsVal) (a : Ann) : Bool :=
  match annTags t a with
  | none => true
  | some tags =>
    let tagsOk := Fset.subset (v.tags.filter (fun tg =>
      tg != Tag.tany && tg != Tag.tunbound && tg != Tag.tuninit &&
      tg != Tag.tmissing)) tags
    let sd := annStrings a
    let stringsOk := if Tag.tstr ∈ v.tags && sd.hasString && !sd.isOpen
      then !v.strOpen && Fset.subset v.strLits sd.literals
      else true
    tagsOk && stringsOk && !(Tag.tany ∈ v.tags)

/-- Heap-aware contract entailment. Bottom collection edges represent an
    empty collection and satisfy every element contract vacuously; a top-level
    unknown value never entails a concrete annotation. -/
partial def annEntailedDeep (fuel : Nat) (t : ClassTable) (st : AState)
    (v : AbsVal) (a : Ann) : Bool :=
  if v.isBot then true
  else if fuel == 0 || !annEntailed t v a then false
  else
    let recur := annEntailedDeep (fuel - 1) t st
    match a with
    | .any => true
    | .required inner | .notRequired inner | .readOnly inner =>
      recur v inner
    | .union members =>
      -- A value entails a union when every *part* of it is covered by some
      -- member, not when the whole of it entails one member. `int | None`
      -- materializes to `{int, none}`, which entails neither `int` nor `None`
      -- alone, so requiring one member rejected every union annotation --
      -- including the one the value had just been built from by
      -- `materializeAnn`. Silent while this was a soft note; an abort once the
      -- call site started enforcing it.
      members.any (fun member => recur v member) ||
      (let slices := members.map (fun member => (member, assumeAnn t v member))
       let covered := slices.foldl (fun acc slice => acc.join slice.2) AbsVal.bot
       -- Every tag of the value belongs to some member, and each member's
       -- slice satisfies that member in full.
       --
       -- Precision debt, in the sound direction: the slice is cut by tags, so
       -- `list[int] | list[str]` against two list locations puts both in each
       -- slice and neither member accepts both. That rejects, which costs an
       -- obligation rather than dropping one.
       v.tags.all (fun tg => covered.tags.contains tg) &&
       slices.all (fun slice => recur slice.2 slice.1))
    | .literal _ => annEntailed t v a
    | .generic name args variadic =>
      let matching := fun (cls : LocCls) =>
        v.locs.filter (fun location => location.cls == cls)
      match name with
      | "list" | "List" =>
        let locations := matching .list
        !locations.isEmpty && locations.all (fun location =>
          recur (st.heapGet location .elem) (args.headD .any))
      | "set" | "Set" =>
        let locations := matching .set
        !locations.isEmpty && locations.all (fun location =>
          recur (st.heapGet location .elem) (args.headD .any))
      | "dict" | "Dict" =>
        let locations := matching .dict
        !locations.isEmpty && locations.all (fun location =>
          recur (st.heapGet location .dictKeys) (args.headD .any) &&
          recur (st.heapGet location .dictValues) (args[1]?.getD .any))
      | "tuple" | "Tuple" =>
        let locations := matching .tuple
        !locations.isEmpty && locations.all (fun location =>
          if variadic then
            recur (st.heapGet location .elem) (args.headD .any)
          else
            st.tupleSlotCount location == args.length &&
              args.zipIdx.all (fun (slotAnn, index) =>
                let slot := st.heapGet location (.tupleSlot index)
                !slot.isBot && recur slot slotAnn))
      | _ => annEntailed t v a
    | .atom name =>
      match t.getCls? name with
      | some info =>
        if info.isTypedDict then
          -- A TypedDict is structural: `{"name": "w"}` *is* an `InventoryRow`
          -- at runtime, and there is no nominal tag to check. Requiring a
          -- `LocCls.td` location rejected every locally built row, because a
          -- dict literal allocates a plain `dict` -- only a parameter
          -- materialized from the annotation gets the `td` class. So both
          -- carry the shape, and the shape is what is checked.
          let locations := v.locs.filter (fun location =>
            location.cls == LocCls.td name || location.cls == LocCls.dict)
          !locations.isEmpty && locations.length == v.locs.length &&
            locations.all (fun location =>
              -- A required key must have a *cell*. Reading its value and
              -- testing for `tmissing` cannot see a key that was never
              -- written at all, which is exactly how a dict literal omits one.
              info.fields.all (fun field =>
                let value := st.heapGet location (.literalKey field.name)
                let present := value.withoutTags [.tmissing]
                (!field.required ||
                    (st.heapHas location (.literalKey field.name) &&
                      !(Tag.tmissing ∈ value.tags))) &&
                  match field.ann with
                  | some fieldAnn => recur present fieldAnn
                  | none => true)
              -- An undeclared key means the value is not of this shape. The
              -- key summary answers it: closed, and every literal declared.
              && (let keys := st.heapGet location .dictKeys
                  !keys.strOpen &&
                    keys.strLits.all (fun key =>
                      info.fields.any (·.name == key))))
        else annEntailed t v a
      | none => annEntailed t v a


def genExcOf (v : AbsVal) : M (Fset String) := do
  let c ← get
  let mut out : Fset String := []
  for l in v.locs do
    if l.cls == LocCls.gen then
      match c.genExc.find? (·.1 == l.site) with
      | some (_, ts) => out := Fset.union ts out
      | none => pure ()
  return out


def alwaysTruthyObj (t : ClassTable) (c : String) : Bool :=
  (resolveMethod t c "__bool__").isNone && (resolveMethod t c "__len__").isNone


/-- The havoc half of the assert/havoc/assume contract for opaque calls:
    every heap cell reachable from the escaping arguments is joined with
    its contract-met value (the field's declared annotation when one
    exists, `any` otherwise). This revises stale narrowing: a cell
    refined to `int` out of a declared `int | str | None` returns to the
    declaration after code the analyzer cannot see may have mutated it.
    Locals are untouched, because Python binds values, not cells. -/
def havocReachable (p : Pos) (args : List AbsVal) (st : AState) :
    M AState := do
  let c ← get
  let roots := args.foldl (fun acc v => Fset.union v.locs acc) []
  let locs := reachableLocs st roots
  if locs.isEmpty then return st
  oblige p "external-havoc"
    "opaque call: reachable cells widened to their declared contracts; external code is assumed to respect field annotations"
  let mut st := st
  for ((l, f), _) in st.heap do
    if locs.contains l then
      let contract : AbsVal :=
        match l.cls with
        | .obj cn =>
          match c.classes.find? (·.1 == cn), f with
          | some (_, ci), .field name =>
            match ci.fields.find? (·.name == name) with
            | some field =>
              match field.ann with
              | some ann =>
                match annTags c.classes ann with
                | some tags => V tags
                | none => anyV
              | none => anyV
            | none => anyV
          | _, _ => anyV
        | _ => anyV
      st := st.heapJoin l f contract
  return st

def excsAfterGen (ts : Fset String) : Fset String :=
  ts.map (fun e => if e == "StopIteration" then "RuntimeError" else e)

-- ------------------------------------------------------ the interpreter


-- ---------------------------------------------- memoized dispatch lookups

/-- Memoized method resolution: the C3 walk for (class, accessor) runs
    once per key; every later dispatch of the same pair, dunders
    included, is a cache hit. -/
def resolveMethodM (cn m : String) : M (Option (String × FuncDef)) := do
  let c ← get
  match c.resolveCache.get? (cn, m) with
  | some r => pure r
  | none =>
    let r := resolveMethod c.classes cn m
    modify fun c => { c with resolveCache := c.resolveCache.insert (cn, m) r }
    pure r

/-- `super()` resolution: the first definer of `m` after `owner` on the
    *receiver's* MRO. Shares the resolve cache by keying on the owner too, so
    the same `(runtime, owner, m)` triple walks the chain once. -/
def resolveMethodAfterM (runtime owner m : String) :
    M (Option (String × FuncDef)) := do
  let c ← get
  let key := (runtime, s!"@after:{owner}:{m}")
  match c.resolveCache.get? key with
  | some r => pure r
  | none =>
    let r := resolveMethodAfter c.classes runtime owner m
    modify fun c => { c with resolveCache := c.resolveCache.insert key r }
    pure r

/-- Write one key of a TypedDict, whichever operation is doing the writing.

    This existed three times -- `RuleDict`, `RuleObjects`, `RuleAnalyzer` --
    and the copies had already diverged once: two dropped the heap write for an
    undeclared key, so `row["bogus"] = 1` failed a later entailment check while
    `row.update(bogus=1)` passed it in the same program. All three raised
    `shape-break`, so the store was flagged either way; what diverged was the
    heap, which is the part no obligation reports.

    They differed in exactly two things, and both are now table data: which
    `ShapeOp` is writing, and the verb the declared-type obligation uses. So the
    function is one definition taking the operation.

    `definite` is a separate condition, not a separate rule: a conditional write
    cannot be strong even when the target is unambiguous. -/
def updateTypedDictField (operation : ShapeOp) (p : Pos) (receiver : AbsVal)
    (location : Loc) (typeName key : String) (info : ClassInfo)
    (value : AbsVal) (definite : Bool) (state : AState) : M AState := do
  let context ← get
  match info.fields.find? (·.name == key) with
  | some field =>
    if let some detail := shapeObligation operation typeName field then
      oblige p "shape-break" detail
    if let some annotation := field.ann then
      if !annEntailedDeep 16 context.classes state value annotation then
        oblige p "type-error" (declaredTypeObligation operation typeName key)
    let stored := match field.ann with
      | some annotation => assumeAnn context.classes value annotation
      | none => value
    let state :=
      if definite then state.heapStore receiver location (.literalKey key) stored
      else state.heapJoin location (.literalKey key) stored
    pure (state.heapJoin location .dictValues stored)
  | none =>
    if let some detail := undeclaredKeyObligation operation typeName key then
      oblige p "shape-break" detail
    -- The key really is added at runtime, so it is recorded even though the store
    -- breaks the declared shape: the heap has to describe the object that exists,
    -- not the one that was declared.
    pure <| (state.heapJoin location .dictKeys (strLitV key)).heapJoin
      location .dictValues value

/-- The first of these dunders that the class defines, with the name that hit.

    This is a *static* protocol chain: it advances because the method is absent
    from the MRO, decided before anything runs. `Plan.protocolChain` is the other
    kind -- it advances because a candidate *returned* `NotImplemented` -- and the
    two are not interchangeable, which is why this exists rather than reusing it.
    Python has both: `x in c` picks a method by what `type(c)` defines, while
    `a + b` runs `__add__` and only then decides whether to try `__radd__`.

    Taking the order as a list makes it data. `truth` and `membership` pass their
    chains in, so the sequence is visible at the call site instead of being implied
    by the indentation of nested `match ← resolveMethodM`. -/
def firstDefinedDunder (className : String) (names : List String) :
    M (Option (String × String × FuncDef)) := do
  for name in names do
    if let some (owner, function) ← resolveMethodM className name then
      return some (name, owner, function)
  return none

/-- Memoized exception MRO (handler matching). -/
def excMroM (e : String) : M (List String) := do
  let c ← get
  match c.excMroCache.get? e with
  | some r => pure r
  | none =>
    let r := excMro c.classes e
    modify fun c => { c with excMroCache := c.excMroCache.insert e r }
    pure r

def excCaughtM (raised handler : String) : M Bool := do
  pure ((← excMroM raised).contains handler)

/-- Memoized isinstance closure. -/
def subclassClosureM (cn : String) : M (List String) := do
  let c ← get
  match c.closureCache.get? cn with
  | some r => pure r
  | none =>
    let r := subclassClosure c.classes cn
    modify fun c => { c with closureCache := c.closureCache.insert cn r }
    pure r

/-- Runtime `isinstance` tags. This intentionally differs from annotation
    compatibility: Python's runtime hierarchy has `bool <: int`, but int,
    float, and complex are otherwise distinct concrete classes. -/
def builtinInstanceTags : String → Option (Fset Tag)
  | "object" => some [
      .tnone, .tbool, .tint, .tfloat, .tcomplex, .tstr,
      .tlist, .tdict, .tdictkeys, .tdictitems, .tdictvalues,
      .tset, .ttuple, .trange, .tgen, .ttype, .tunion, .tfunc,
      .tnotimpl]
  | "int" => some [.tbool, .tint]
  | "bool" => some [.tbool]
  | "float" => some [.tfloat]
  | "complex" => some [.tcomplex]
  | "str" => some [.tstr]
  | "list" => some [.tlist]
  | "dict" => some [.tdict]
  | "set" => some [.tset]
  | "tuple" => some [.ttuple]
  | "range" => some [.trange]
  | _ => none

partial def isinstanceTagsM (classExpr : Expr) : M (Fset Tag) := do
  let c ← get
  match classExpr with
  | .name _ cn =>
    match c.classes.getCls? cn with
    | some _ => pure ((← subclassClosureM cn).map Tag.tobj)
    | none =>
      match builtinInstanceTags cn with
      | some tags => pure tags
      | none =>
        if builtinExcs.contains cn then
          pure ((builtinExcs.filter (fun raised =>
            (excMro c.classes raised).contains cn)).map Tag.tobj)
        else pure []
  | .tuplelit _ elements =>
    let mut out : Fset Tag := []
    for element in elements do
      out := Fset.union (← isinstanceTagsM element) out
    pure out
  | _ => pure []

def unreached (c : Actx) : List String :=
  let fnames := c.funcs.map (·.1)
  let mnames := c.classes.flatMap (fun (cn, ci) =>
    ci.ownMethods.map (fun (m, _) => s!"{cn}.{m}"))
  (fnames ++ mnames).filter (fun n => !c.called.contains n)

end Pylate
