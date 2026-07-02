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
  [.lt, .gt, .eq, .ne, .isIn, .notIn]

-- `PCmpOp.ofTag?` inverts `PCmpOp.tag` for every variant.
#guard allPCmpOps.all (fun op => PCmpOp.ofTag? op.tag == some op)

-- An unknown tag string is not parsed back into a `PCmpOp`.
#guard PCmpOp.ofTag? "definitely-not-a-tag" == none
#guard PCmpOp.ofTag? "" == none
#guard PCmpOp.ofTag? "isIn" == none

/-- Every `PCmpOp` variant survives a `pcmp` round-trip (the existing test only covers `.isIn`). -/
def pcmpOpRoundTripTest : IO Unit := do
  let x := SpecExpr.var "x" rtLoc
  let y := SpecExpr.var "y" rtLoc
  for op in allPCmpOps do
    let e := SpecExpr.pcmp op x y rtLoc
    let e' := rtSpecExpr e
    unless e'.softBEq e do
      throw <| IO.userError s!"pcmp round-trip mismatch for op '{op.tag}': {e} -> {e'}"

/-- Nested `SpecExpr` trees survive round-trip; guards the recursive `toDDM`/`fromDDM`. -/
def nestedRoundTripTest : IO Unit := do
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
        .neg (.neg (.neg x rtLoc) rtLoc) rtLoc) ]
  for (name, e) in samples do
    let e' := rtSpecExpr e
    unless e'.softBEq e do
      throw <| IO.userError s!"nested round-trip mismatch for '{name}': {e} -> {e'}"

/-- A `pcmpExpr` whose tag string is not a known `PCmpOp` falls back to
    `.placeholder` in `fromDDM` (the `PCmpOp.ofTag? = none` branch at DDM.lean
    ~485). This exercises the actual `fromDDM` fallback, not `ofTag?` alone. -/
def unknownPcmpTagFallbackTest : IO Unit := do
  let lhs := (SpecExpr.var "x" rtLoc).toDDM
  let rhs := (SpecExpr.var "y" rtLoc).toDDM
  let bogus : DDM.SpecExprDecl SourceRange :=
    .pcmpExpr rtLoc ⟨rtLoc, "bogus"⟩ lhs rhs
  let result := bogus.fromDDM
  unless result.softBEq (.placeholder rtLoc) do
    throw <| IO.userError s!"unknown pcmp tag expected placeholder, got {result}"

def specExprRoundTripExtraTest : IO Unit := do
  pcmpOpRoundTripTest
  nestedRoundTripTest
  unknownPcmpTagFallbackTest

#guard_msgs in
#eval specExprRoundTripExtraTest
end
