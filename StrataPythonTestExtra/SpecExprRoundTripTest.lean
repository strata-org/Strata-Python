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
    `fromDDM` preserves the invalid shape as a placeholder instead of silently
    reinterpreting its expression as an ordinary frame target or invariant. -/
private def admittedEntryOutsidePostconditionsFallbackTest : IO Unit := do
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
  | .error (_, msg) => throw <| IO.userError s!"malformed FunctionDecl read failed: {msg}"
  | .ok d =>
    unless d.modifies.size == 1 && d.modifies[0]!.softBEq (.placeholder rtLoc) do
      throw <| IO.userError "admitted modifies entry must map to a placeholder"
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
  | .error (_, msg) => throw <| IO.userError s!"malformed ClassDecl read failed: {msg}"
  | .ok d =>
    unless d.invariants.size == 1 && d.invariants[0]!.softBEq (.placeholder rtLoc) do
      throw <| IO.userError "admitted invariant entry must map to a placeholder"

def specExprRoundTripExtraTest : IO Unit := do
  pcmpOpRoundTripTest
  nestedRoundTripTest
  unknownPcmpTagFallbackTest
  funcDeclAdmittedRoundTripTest
  admittedEntryOutsidePostconditionsFallbackTest

#guard_msgs in
#eval specExprRoundTripExtraTest
end
