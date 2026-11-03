/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataPython.Specs
meta import all StrataPython.Specs.DDM

open StrataDDM (SourceRange)
open StrataPython
open StrataPython.Specs

meta section

/-- `SourceRange` tag for the round-trip samples. -/
def rtLoc : SourceRange := .none

/-- Round-trip a `SpecExpr` through `toDDM` then `fromDDM`. -/
def rtSpecExpr (e : SpecExpr) : SpecExpr := e.toDDM.fromDDM

/-- Every `PCmpOp` variant. -/
def allPCmpOps : List PCmpOp :=
  [.lt, .le, .gt, .ge, .eq, .ne, .isIn, .notIn]

-- `PCmpOp.ofTag?` inverts `PCmpOp.tag` for every variant: see the kernel-checked
-- `PCmpOp.ofTag_tag` in `StrataPython.Specs.DeclsProps`.

-- An unknown tag string is not parsed back into a `PCmpOp`.
#guard PCmpOp.ofTag? "definitely-not-a-tag" == none
#guard PCmpOp.ofTag? "" == none
#guard PCmpOp.ofTag? "isIn" == none

/-- Every `PCmpOp` variant survives a `pcmp` round-trip (the existing test only covers `.isIn`). -/
private def pcmpOpRoundTripTest : IO Unit := do
  let x := SpecExpr.var "x" rtLoc
  let y := SpecExpr.var "y" rtLoc
  for op in allPCmpOps do
    let e := SpecExpr.pcmp op x y rtLoc
    let e' := rtSpecExpr e
    unless e'.softBEq e do
      throw <| IO.userError s!"pcmp round-trip mismatch for op '{op.tag}': {e} -> {e'}"

/-- Nested `SpecExpr` trees survive round-trip; guards the recursive `toDDM`/`fromDDM`. -/
private def nestedRoundTripTest : IO Unit := do
  let x  := SpecExpr.var "x" rtLoc
  let y  := SpecExpr.var "y" rtLoc
  let a  := SpecExpr.var "a" rtLoc
  let b  := SpecExpr.var "b" rtLoc
  let c  := SpecExpr.var "c" rtLoc
  let d  := SpecExpr.var "d" rtLoc
  let bt := SpecExpr.boolLit true rtLoc
  let bf := SpecExpr.boolLit false rtLoc
  let nl := SpecExpr.noneLit rtLoc
  let samples : List (String × SpecExpr) :=
    [ ("pcmp lt over arith",
        .pcmp .lt (.add x y rtLoc) (.mul x (.neg y rtLoc) rtLoc) rtLoc),
      ("and of pcmp eq and or/not",
        .and (.pcmp .eq a b rtLoc) (.or c (.not d rtLoc) rtLoc) rtLoc),
      ("deep arithmetic",
        .add (.sub (.mul x y rtLoc) (.floorDiv x y rtLoc) rtLoc)
             (.mod (.pow x y rtLoc) (.neg x rtLoc) rtLoc) rtLoc),
      ("boolean tower with literals",
        .and bt (.or bf (.not (.and bt bf rtLoc) rtLoc) rtLoc) rtLoc),
      ("noneLit nested under pcmp ne",
        .pcmp .ne x nl rtLoc),
      ("nested notIn and isIn",
        .or (.pcmp .isIn x y rtLoc) (.pcmp .notIn a b rtLoc) rtLoc),
      ("comparisons mixed with arith bounds",
        .and (.intGe (.add x y rtLoc) (.intLit 3 rtLoc) rtLoc)
             (.intLe (.mul x y rtLoc) (.intLit 10 rtLoc) rtLoc) rtLoc),
      ("neg of neg",
        .neg (.neg (.neg x rtLoc) rtLoc) rtLoc),
      ("old wrapping arith",
        .old (.add x y rtLoc) rtLoc),
      ("old wrapping getIndex",
        .old (.getIndex x "field" rtLoc) rtLoc),
      ("old wrapping old",
        .old (.old x rtLoc) rtLoc) ]
  for (name, e) in samples do
    let e' := rtSpecExpr e
    unless e'.softBEq e do
      throw <| IO.userError s!"nested round-trip mismatch for '{name}': {e} -> {e'}"

/-- A `pcmpExpr` whose tag string is not a known `PCmpOp` falls back to
    `.placeholder` in `fromDDM` (the `PCmpOp.ofTag? = none` branch at DDM.lean
    ~485). This exercises the actual `fromDDM` fallback, not `ofTag?` alone. -/
private def unknownPcmpTagFallbackTest : IO Unit := do
  let lhs := (SpecExpr.var "x" rtLoc).toDDM
  let rhs := (SpecExpr.var "y" rtLoc).toDDM
  let bogus : DDM.SpecExprDecl SourceRange :=
    .pcmpExpr rtLoc ⟨rtLoc, "bogus"⟩ lhs rhs
  let result := bogus.fromDDM
  unless result.softBEq (.placeholder rtLoc) do
    throw <| IO.userError s!"unknown pcmp tag expected placeholder, got {result}"

/-- `FunctionDecl` round-trip through `toDDM`/`fromDDM` keeps verified and
    admitted postconditions in their own stores (guards the
    `mkAdmittedPostconditionEntry` encoding inside the shared postconditions
    sequence — chosen over a new `FunDecl` clause so previously serialized
    spec Ion keeps parsing). -/
private def funcDeclAdmittedRoundTripTest : IO Unit := do
  let ensured := SpecExpr.intGe (.var "result" rtLoc) (.intLit 0 rtLoc) rtLoc
  let admitted := SpecExpr.intLe (.var "result" rtLoc) (.intLit 100 rtLoc) rtLoc
  let mkDecl (postconditions admittedPostconditions : Array SpecExpr) : FunctionDecl := {
    loc := rtLoc, nameLoc := rtLoc, name := "f"
    args := { args := #[], kwonly := #[] }
    returnType := .ident rtLoc .typingAny
    isOverload := false
    preconditions := #[]
    postconditions, admittedPostconditions
  }
  -- Both stores populated: each survives in its own field.
  match (mkDecl #[ensured] #[admitted]).toDDM.fromDDM with
  | .error (_, msg) => throw <| IO.userError s!"FunctionDecl round-trip failed: {msg}"
  | .ok d =>
    unless d.postconditions.size == 1 && d.postconditions[0]!.softBEq ensured do
      throw <| IO.userError "verified postcondition did not survive the round-trip"
    unless d.admittedPostconditions.size == 1
        && d.admittedPostconditions[0]!.softBEq admitted do
      throw <| IO.userError "admitted postcondition did not survive the round-trip"
  -- Verified-only: the legacy shape (no admitted entries) still round-trips
  -- and the admitted store reads back empty.
  match (mkDecl #[ensured] #[]).toDDM.fromDDM with
  | .error (_, msg) => throw <| IO.userError s!"FunctionDecl round-trip failed: {msg}"
  | .ok d =>
    unless d.postconditions.size == 1 && d.postconditions[0]!.softBEq ensured do
      throw <| IO.userError "verified-only postcondition did not survive the round-trip"
    unless d.admittedPostconditions.isEmpty do
      throw <| IO.userError "admitted store must read back empty when no admitted entries"
  -- Admitted-only: no `mkPostconditionEntry` ops at all; the verified store
  -- reads back empty and the admitted store is populated.
  match (mkDecl #[] #[admitted]).toDDM.fromDDM with
  | .error (_, msg) => throw <| IO.userError s!"FunctionDecl round-trip failed: {msg}"
  | .ok d =>
    unless d.postconditions.isEmpty do
      throw <| IO.userError "verified store must read back empty when no verified entries"
    unless d.admittedPostconditions.size == 1
        && d.admittedPostconditions[0]!.softBEq admitted do
      throw <| IO.userError "admitted-only postcondition did not survive the round-trip"
  -- Both stores empty: an empty postconditions sequence reads back as two
  -- empty stores.
  match (mkDecl #[] #[]).toDDM.fromDDM with
  | .error (_, msg) => throw <| IO.userError s!"FunctionDecl round-trip failed: {msg}"
  | .ok d =>
    unless d.admittedPostconditions.isEmpty do
      throw <| IO.userError "empty admitted store must read back empty"
  -- Multiple entries per store: pins the de-interleaving of the shared
  -- sequence — routing by entry op and order preservation within each store.
  let ensured2 := SpecExpr.intGe (.var "result" rtLoc) (.intLit 1 rtLoc) rtLoc
  let admitted2 := SpecExpr.intLe (.var "result" rtLoc) (.intLit 200 rtLoc) rtLoc
  match (mkDecl #[ensured, ensured2] #[admitted, admitted2]).toDDM.fromDDM with
  | .error (_, msg) => throw <| IO.userError s!"FunctionDecl round-trip failed: {msg}"
  | .ok d =>
    unless d.postconditions.size == 2
        && d.postconditions[0]!.softBEq ensured
        && d.postconditions[1]!.softBEq ensured2 do
      throw <| IO.userError
        "verified store must keep both entries in order after de-interleaving"
    unless d.admittedPostconditions.size == 2
        && d.admittedPostconditions[0]!.softBEq admitted
        && d.admittedPostconditions[1]!.softBEq admitted2 do
      throw <| IO.userError
        "admitted store must keep both entries in order after de-interleaving"

/-- An `admitted` entry is only meaningful in the postconditions sequence.
    If foreign or hand-authored DDM places one in `modifies` or `invariants`,
    `fromDDM` fails, instead of reinterpreting its expression as an ordinary frame
    target or invariant. -/
private def misplacedEntryReadErrorTest : IO Unit := do
  let expr := SpecExpr.var "x" rtLoc
  let admittedEntry : DDM.PostconditionEntry SourceRange :=
    .mkAdmittedPostconditionEntry rtLoc expr.toDDM
  let malformedFun : DDM.FunDecl SourceRange :=
    .mkFunDecl rtLoc
      (name := ⟨rtLoc, "f"⟩)
      (args := ⟨rtLoc, #[]⟩)
      (kwonly := ⟨rtLoc, #[]⟩)
      (kwargs := ⟨rtLoc, none⟩)
      (returnType := (SpecType.ident rtLoc .typingAny).toDDM)
      (isOverload := ⟨rtLoc, false⟩)
      (preconditions := ⟨rtLoc, #[]⟩)
      (postconditions := ⟨rtLoc, #[]⟩)
      (snapshots := ⟨rtLoc, none⟩)
      (modifiesClause := ⟨rtLoc, some <|
        .mkModifiesClause rtLoc ⟨rtLoc, #[admittedEntry]⟩⟩)
      (ghosts := ⟨rtLoc, none⟩)
  match malformedFun.fromDDM with
  | .error (_, msg) =>
    unless msg == "A modifies target of 'f' that is not a plain entry" do
      throw <| IO.userError s!"unexpected read error: {msg}"
  | .ok _ => throw <| IO.userError "an admitted modifies entry must be a read error"
  let malformedClass : DDM.ClassDecl SourceRange :=
    .mkClassDecl rtLoc
      (name := ⟨rtLoc, "C"⟩)
      (bases := ⟨rtLoc, #[]⟩)
      (fields := ⟨rtLoc, #[]⟩)
      (classVars := ⟨rtLoc, #[]⟩)
      (subclasses := ⟨rtLoc, #[]⟩)
      (methods := ⟨rtLoc, #[]⟩)
      (exhaustive := ⟨rtLoc, false⟩)
      (invariants := ⟨rtLoc, some <|
        .mkInvariantsClause rtLoc ⟨rtLoc, #[admittedEntry]⟩⟩)
  match malformedClass.fromDDM with
  | .error (_, msg) =>
    unless msg == "An invariant of 'C' that is not an invariant entry" do
      throw <| IO.userError s!"unexpected read error: {msg}"
  | .ok _ => throw <| IO.userError "an admitted invariant entry must be a read error"

/-- Every `DroppedKind`, a dropped entry's source text, and both `**kwargs` forms survive the
    round trip; an invariant entry among the postconditions is a read error. -/
private def droppedAndKwargsRoundTripTest : IO Unit := do
  let kinds : Array DroppedKind := #[.assert, .requires, .ensures, .admit, .modifies, .ghostInit]
  let any := SpecType.ident rtLoc .typingAny
  for unpacked in [false, true] do
    let kwargs := some ("kw", if unpacked then KwargsType.unpacked any else .each any)
    let d : FunctionDecl := {
      loc := rtLoc, nameLoc := rtLoc, name := "f"
      args := { args := #[], kwonly := #[], kwargs }
      returnType := SpecType.ident rtLoc .typingAny, isOverload := false
      preconditions := #[{ message := #[.str "a ", .expr (.var "x" rtLoc) "x", .untranslated "y.z()"],
                           formula := .var "x" rtLoc }]
      postconditions := #[]
      dropped := kinds.map fun kind => { kind, source := s!"src {kind.tag} é" } }
    match d.toDDM.fromDDM with
    | .error (_, msg) => throw <| IO.userError s!"FunctionDecl round trip failed: {msg}"
    | .ok d' =>
      unless d'.dropped.map (fun c => (c.kind.tag, c.source)) ==
          kinds.map (fun k => (k.tag, s!"src {k.tag} é")) do
        throw <| IO.userError "dropped clauses changed in the round trip"
      let kept : Bool := match d'.args.kwargs with
        | some ("kw", .unpacked t) => unpacked && t.asIdent == some .typingAny
        | some ("kw", .each t) => !unpacked && t.asIdent == some .typingAny
        | _ => false
      unless kept do
        throw <| IO.userError "the **kwargs form changed in the round trip"
      let parts := d'.preconditions[0]!.message.map fun
        | .str s => s!"str {s}" | .expr _ src => s!"expr {src}" | .untranslated src => s!"untranslated {src}"
      unless parts == #["str a ", "expr x", "untranslated y.z()"] do
        throw <| IO.userError s!"message parts changed in the round trip: {parts}"
  let misplaced : DDM.FunDecl SourceRange :=
    .mkFunDecl rtLoc
      (name := ⟨rtLoc, "f"⟩) (args := ⟨rtLoc, #[]⟩) (kwonly := ⟨rtLoc, #[]⟩)
      (kwargs := ⟨rtLoc, none⟩) (returnType := (SpecType.ident rtLoc .typingAny).toDDM)
      (isOverload := ⟨rtLoc, false⟩) (preconditions := ⟨rtLoc, #[]⟩)
      (postconditions := ⟨rtLoc, #[.mkInvariantEntry rtLoc ⟨rtLoc, "lambda self: P"⟩
        ⟨rtLoc, "self"⟩ ⟨rtLoc, none⟩]⟩)
      (snapshots := ⟨rtLoc, none⟩) (modifiesClause := ⟨rtLoc, none⟩) (ghosts := ⟨rtLoc, none⟩)
  match misplaced.fromDDM with
  | .error (_, msg) =>
    unless msg == "An invariant among the postconditions of 'f'" do
      throw <| IO.userError s!"unexpected read error: {msg}"
  | .ok _ => throw <| IO.userError "an invariant entry among the postconditions must be a read error"

/-- Through Ion bytes: `writeDDM` states the format version, and `readDDMVersioned` reads it
    with the signatures, a class field's literal value and the positions of fields and class
    variables included; a file without the format command reads with no version; an invariant
    entry of an old file reads with the binder `self` and no source text. -/
private def ionFileTest : IO Unit := do
  let d : FunctionDecl := {
    loc := rtLoc, nameLoc := rtLoc, name := "f", args := { args := #[], kwonly := #[] }
    returnType := SpecType.ident rtLoc .typingAny, isOverload := false
    preconditions := #[], postconditions := #[]
    dropped := #[{ kind := .modifies, source := "x.y()" }] }
  let intTy := SpecType.ident rtLoc .builtinsInt
  let fields : Array ClassField := #[
    { name := "x", type := intTy, source := .body (some (.intLit (-1) rtLoc)),
      loc := { start := ⟨3⟩, stop := ⟨9⟩ } },
    { name := "b", type := intTy, source := .body (some (.boolLit true rtLoc)) },
    { name := "f", type := intTy, source := .body (some (.floatLit "-2.5" rtLoc)) },
    { name := "n", type := intTy, source := .body (some (.noneLit rtLoc)) },
    { name := "y", type := intTy, source := .init "_H()" }, { name := "z", type := intTy }]
  let classVars : Array ClassVariable :=
    #[{ name := "K", value := "int", loc := { start := ⟨12⟩, stop := ⟨19⟩ } }]
  let c : ClassDef := { loc := rtLoc, name := "C", methods := #[], fields, classVars, invariants :=
    #[{ source := "lambda s: s.x", binder := "s", formula := none }] }
  IO.FS.withTempDir fun dir => do
    let file := dir / "m.pyspec.st.ion"
    writeDDM file #[.functionDecl d, .classDef c]
    let (version, sigs) ← IO.ofExcept (← (readDDMVersioned file).toBaseIO)
    unless version == some formatVersion && sigs.size == 2 do
      throw <| IO.userError s!"expected version {formatVersion} and 2 signatures, got {version}, {sigs.size}"
    match sigs[0]!, sigs[1]! with
    | .functionDecl d', .classDef c' =>
      unless d'.dropped.map (·.source) == #["x.y()"] && c'.invariants.map (·.binder) == #["s"] do
        throw <| IO.userError "the dropped clause or the invariant changed through Ion"
      let fields := c'.fields.map fun f => (f.name, match f.source with
        | .body (some (.intLit i _)) => s!"int {i}"
        | .body (some (.boolLit b _)) => s!"bool {b}"
        | .body (some (.floatLit v _)) => s!"float {v}"
        | .body (some (.noneLit _)) => "None"
        | .body (some _) => "other"
        | .body none => "none"
        | .init c => s!"init {c}")
      unless fields == #[("x", "int -1"), ("b", "bool true"), ("f", "float -2.5"), ("n", "None"),
          ("y", "init _H()"), ("z", "none")] do
        throw <| IO.userError s!"the fields changed through Ion: {fields}"
      let locs := c'.fields.map (·.loc.start.byteIdx) ++
        c'.classVars.map (·.loc.start.byteIdx)
      unless locs == #[3, 0, 0, 0, 0, 0, 12] do
        throw <| IO.userError s!"the positions of the fields and class variables changed through Ion: {locs}"
    | _, _ => throw <| IO.userError "the signatures changed kind through Ion"
    -- A file without the format command, as an older PySpec wrote it.
    let old := dir / "old.pyspec.st.ion"
    let legacyInv : DDM.ClassDecl SourceRange :=
      .mkClassDecl rtLoc ⟨rtLoc, "C"⟩ ⟨rtLoc, #[]⟩ ⟨rtLoc, #[]⟩ ⟨rtLoc, #[]⟩ ⟨rtLoc, #[]⟩
        ⟨rtLoc, #[]⟩ ⟨rtLoc, false⟩ ⟨rtLoc, some (.mkInvariantsClause rtLoc
          ⟨rtLoc, #[.mkPostconditionEntry rtLoc (SpecExpr.var "inv" rtLoc).toDDM]⟩)⟩
    let pgm : StrataDDM.Program := .create DDM.PythonSpecs_map DDM.PythonSpecs.name
      #[(DDM.Command.classDef rtLoc legacyInv).toAst]
    IO.FS.writeBinFile old pgm.toIon
    let (version, sigs) ← IO.ofExcept (← (readDDMVersioned old).toBaseIO)
    unless version == none do throw <| IO.userError "a file without a format command has no version"
    match (sigs[0]? : Option Signature) with
    | some (Signature.classDef c') =>
      unless c'.invariants.map (fun i => (i.binder, i.source, i.formula.isSome)) ==
          #[("self", "", true)] do
        throw <| IO.userError "an old invariant entry must read with binder self and no source"
    | _ => throw <| IO.userError "expected the old class"

/-- A dropped entry with an unknown kind, or in the invariants or modifies clause, is a read
    error. -/
private def droppedEntryReadErrorTest : IO Unit := do
  let mkFun (posts : Array (DDM.PostconditionEntry SourceRange))
      (mods : Array (DDM.PostconditionEntry SourceRange)) : DDM.FunDecl SourceRange :=
    .mkFunDecl rtLoc (name := ⟨rtLoc, "f"⟩) (args := ⟨rtLoc, #[]⟩) (kwonly := ⟨rtLoc, #[]⟩)
      (kwargs := ⟨rtLoc, none⟩) (returnType := (SpecType.ident rtLoc .typingAny).toDDM)
      (isOverload := ⟨rtLoc, false⟩) (preconditions := ⟨rtLoc, #[]⟩)
      (postconditions := ⟨rtLoc, posts⟩) (snapshots := ⟨rtLoc, none⟩)
      (modifiesClause := ⟨rtLoc, if mods.isEmpty then none else some (.mkModifiesClause rtLoc ⟨rtLoc, mods⟩)⟩)
      (ghosts := ⟨rtLoc, none⟩)
  let dropped (tag : String) : DDM.PostconditionEntry SourceRange :=
    .mkDroppedEntry rtLoc ⟨rtLoc, tag⟩ ⟨rtLoc, "src"⟩
  let expectError {α : Type} (what : String) (r : FromDDM α) (msg : String) : IO Unit :=
    match r with
    | .error (_, m) => unless m == msg do throw <| IO.userError s!"{what}: unexpected error {m}"
    | .ok _ => throw <| IO.userError s!"{what}: expected a read error"
  expectError "unknown kind" (mkFun #[dropped "nope"] #[]).fromDDM
    "Unknown kind of dropped clause: 'nope'"
  expectError "dropped in modifies" (mkFun #[] #[dropped "assert"]).fromDDM
    "A modifies target of 'f' that is not a plain entry"
  let cls : DDM.ClassDecl SourceRange :=
    .mkClassDecl rtLoc ⟨rtLoc, "C"⟩ ⟨rtLoc, #[]⟩ ⟨rtLoc, #[]⟩ ⟨rtLoc, #[]⟩ ⟨rtLoc, #[]⟩
      ⟨rtLoc, #[]⟩ ⟨rtLoc, false⟩ ⟨rtLoc, some (.mkInvariantsClause rtLoc ⟨rtLoc, #[dropped "assert"]⟩)⟩
  expectError "dropped in invariants" cls.fromDDM "An invariant of 'C' that is not an invariant entry"

def specExprRoundTripExtraTest : IO Unit := do
  pcmpOpRoundTripTest
  nestedRoundTripTest
  unknownPcmpTagFallbackTest
  funcDeclAdmittedRoundTripTest
  misplacedEntryReadErrorTest
  droppedAndKwargsRoundTripTest
  ionFileTest
  droppedEntryReadErrorTest

#guard_msgs in
#eval specExprRoundTripExtraTest
end
