/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Programs
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
-- `#guard` links, validates and runs as compiled code.
meta import StrataDynTest.Exec.Programs
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Block scopes

A block's scope is what is in scope at its entry and live there.  `ifs n` is `n` ifs in a
row, each a header that reads the parameter, two arms and a join; each scope holds at most the
parameter.  `join` defines a value in its entry, branches, and reads the value only at the
join, so both arms carry it to the join.
-/

namespace Strata.Dyn.ExecTest.LinkScopeTest

open Strata.Dyn.ExecTest.Programs
open Strata.Dyn.Exec

/-- If `i` of `ifs`: header `h{i}` compares `%0` with `i`, and arms `t{i}` and `f{i}` meet at
`h{i+1}`, or at `done` after the last. -/
def ifBlocks (n i : Nat) : List (Block E Unit) :=
  let next := if i + 1 = n then "done" else s!"h{i + 1}"
  [blk s!"h{i}" [] [cst (1 + 2 * i) intT (.int i),
        app (2 + 2 * i) boolT Ex.lt.ref ⟨#[], rfl⟩ [0, 1 + 2 * i]]
      (br (2 + 2 * i) (to s!"t{i}") (to s!"f{i}")),
    blk s!"t{i}" [] [] (goto (to next)),
    blk s!"f{i}" [] [] (goto (to next))]

/-- `ifs n (x) = x`, after `n` ifs in a row. -/
def ifs (n : Nat) : Func E Unit := fn "ifs" intT (
  [blk "entry" [d 0 intT] [] (goto (to "h0"))] ++
    (List.range n).flatMap (ifBlocks n) ++ [blk "done" [] [] (ret 0)])

/-- `join(x) = x + 1` by a branch on `x < 0` whose arms meet at a join that reads the `1` the
entry defines. -/
def join : Func E Unit := fn "join" intT [
  blk "entry" [d 0 intT] [cst 1 intT (.int 0), cst 2 intT (.int 1),
      app 3 boolT Ex.lt.ref ⟨#[], rfl⟩ [0, 1]]
    (br 3 (to "neg") (to "pos")),
  blk "neg" [] [] (goto (to "meet")),
  blk "pos" [] [] (goto (to "meet")),
  blk "meet" [] [app 4 intT Ex.add.ref ⟨#[], rfl⟩ [0, 2]] (ret 4)]

/-- Each block's label and scope, by id, in function `f` of the linked and validated module of
`fs`, or `none` if it does not link and validate. -/
def scopes (fs : List (Func E Unit)) (f : String) : Option (List (String × List Nat)) :=
  match mod fs with
  | .error _ => none
  | .ok m => match prepare ExSem.model m (nm f) with
    | .error _ => none
    | .ok ⟨lm, _, i⟩ => lm.funcs[i]?.map fun b =>
      b.blocks.toList.map fun lb => (nameStr lb.label.name, lb.scope.map (·.1))

/-- The `Int` that function `f` of `fs` returns on `x`, if any. -/
def runInt (fs : List (Func E Unit)) (f : String) (x : Int) : Option Int :=
  match mod fs with
  | .ok m => (runModule ExSem.model m (nm f) #[ExSem.model.arg x] 100000).read? Int
  | .error _ => none

-- 200 ifs link, validate and run, and no block's scope holds more than the parameter.
#guard runInt [ifs 200] "ifs" 7 == some 7
#guard (scopes [ifs 200] "ifs").map (·.all (·.2.length ≤ 1)) == some true
#guard (scopes [ifs 200] "ifs").map (·.length) == some 602

-- The join reads `%0` and `%2` from the entry, so both arms carry them, the latest first, and
-- no block carries `%1`, which only the entry reads.
#guard runInt [join] "join" 5 == some 6
#guard runInt [join] "join" (-5) == some (-4)
#guard scopes [join] "join" ==
  some [("entry", []), ("neg", [2, 0]), ("pos", [2, 0]), ("meet", [2, 0])]

end Strata.Dyn.ExecTest.LinkScopeTest
