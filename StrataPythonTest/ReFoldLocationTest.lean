/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataPython.PyFactory

meta section

namespace StrataPython.ToCore.Tests

open Strata Lambda

/-- A fold tags its whole result with the call-site location it is given: folding
    `f` at `callLoc` with `args` yields a result whose every node carries
    `callLoc`, so re-stamping `callLoc` across it leaves it unchanged. Returns
    `false` if `f` does not fold these args. -/
private def foldsAllAt (callLoc : ExprSourceLoc) (f : LFunc Core.CoreLParams)
    (args : List Core.Expression.Expr) : Bool :=
  match f.concreteEval with
  | some fold =>
    match fold callLoc none args with
    | some out => out == out.replaceMetadata (fun _ => callLoc)
    | none => false
  | none => false

/-! The regex folds thread the call-site location through their result, so an
    obligation inside a folded `re.match`/`re.fullmatch`/`re.search` or
    `re_pattern_*` term points at the Python call site rather than a synthesized
    location. Each changed fold, applied to a literal pattern at `callLoc`,
    produces an all-`callLoc` result; if a fold stopped threading the location
    (reverting to the synthesized `regex`/`python-factory` locations) its result
    would differ and this check would fail. -/
#guard
  let callLoc : ExprSourceLoc := ExprSourceLoc.synthesized "call-site"
  let pat : Core.Expression.Expr := .strConst callLoc "a*"
  let s : Core.Expression.Expr := .fvar callLoc "s" none
  -- `mkModeBoolFunc` folds take the pattern and the subject string.
  foldsAllAt callLoc reMatchBoolFunc [pat, s]
    && foldsAllAt callLoc reFullmatchBoolFunc [pat, s]
    && foldsAllAt callLoc reSearchBoolFunc [pat, s]
  -- `mkRePatternFunc` folds take the pattern alone.
    && foldsAllAt callLoc rePatternIsErrorFunc [pat]
    && foldsAllAt callLoc rePatternErrorMsgFunc [pat]

end StrataPython.ToCore.Tests
