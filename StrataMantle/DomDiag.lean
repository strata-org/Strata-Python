/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR
import StrataMantle.DDM
public import Std.Data.HashMap
import Std.Data.HashSet
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Why a function is not reachable and scoped

`Func.scopeDiagnostics` explains why a function fails `Func.Reachable` or `Func.Scopable`
(`StrataMantle/Dom.lean`), one message per problem, for a reader or producer to report.  It
names each block its body's entry does not reach, and each use out of scope.  For a use out of
scope it names the value, where it is defined, and a path from the body's entry to the use that
avoids the definition:

    `%t.0` (defined in `entry.0`) is used in `join.0`, reachable via
    `entry.0 → rhs.0 → join.0` without it

In a reachable body a use is in scope under some tree exactly when no such path exists, so the
messages name no tree.  The module only explains, and carries no proof: `Func.WF`'s instance
makes the decision.
-/

namespace Strata.Mantle

open Std (HashMap HashSet)

variable {env : Env Unit} {α : Type}

namespace DomDiag

/-- A label as printed, quoted. -/
public def labelText (l : Label) : String := "`" ++ ToDDM.nameText l.name ++ "`"

/-- A value as printed. -/
def valText (names : Array Name) (x : ValId) : String :=
  "%" ++ ((names[x.id]?.map ToDDM.nameText).getD s!"?{x.id}")

/-- A point, as its block and its instruction count. -/
public def pointText (p : Point) : String := s!"{labelText p.label} after {p.count} instructions"

/-- The values used by an instruction or terminator: its operands and successor arguments. -/
def uses (args : Array ValId) (succs : Array BlockValue) : Array ValId :=
  args ++ succs.flatMap (·.args)

/-- The transfers out of block `b`: the count each leaves from, and its target. -/
public def edges (b : Block env α) : Array (Nat × Label) := Id.run do
  let mut out := #[]
  for h : k in [:b.instrs.size] do
    for s in b.instrs[k].succs do out := out.push (k, s.target)
  for s in b.term.succs do out := out.push (b.instrs.size, s.target)
  return out

/-- A path from the entry `e` to the point `y` that avoids the point `d`, as the blocks it
passes, if there is one.  A path through block `d.label` avoids `d` only by leaving before
it. -/
public def avoidingPath (bs : HashMap Label (Block env α)) (e : Label) (d y : Point) :
    Option (List Label) := Id.run do
  -- The last count of a block a path entering it at its start reaches without passing `d`.
  let limit (l : Label) (n : Nat) : Option Nat :=
    if l = d.label then (if d.count = 0 then none else some (d.count - 1)) else some n
  let some _ := limit e 0 | return none
  let mut prev : HashMap Label Label := {}
  let mut seen : HashSet Label := ({} : HashSet Label).insert e
  let mut queue := #[e]
  let mut i := 0
  for _ in [:bs.size + 1] do
    if h : i < queue.size then
      let l := queue[i]
      i := i + 1
      let some b := bs[l]? | continue
      let some lim := limit l b.instrs.size | continue
      if l = y.label && y.count ≤ lim then
        let mut path := [l]
        let mut cur := l
        for _ in [:bs.size] do
          match prev[cur]? with
          | some p => path := p :: path; cur := p
          | none => break
        return some path
      for (k, t) in edges b do
        if k ≤ lim && !seen.contains t && bs.contains t && (limit t 0).isSome then
          seen := seen.insert t
          prev := prev.insert t l
          queue := queue.push t
  return none

/-- The points after the entry of a path through the blocks `path` to `y` that avoids `d`:
each block up to its first transfer to the next, which leaves before `d` in `d`'s block. -/
def pathPoints (bs : HashMap Label (Block env α)) (d y : Point) :
    List Label → Option (List Point)
  | [] => none
  | [l] => some ((List.range y.count).map fun k => ⟨l, k + 1⟩)
  | l :: m :: rest => do
    let b ← bs[l]?
    let lim := if l = d.label then d.count - 1 else b.instrs.size
    let (k, _) ← (edges b).find? fun (k, t) => k ≤ lim && t = m
    let ps ← pathPoints bs d y (m :: rest)
    some ((List.range k).map (fun j => ⟨l, j + 1⟩) ++ ⟨m, 0⟩ :: ps)

/-- A path from the entry `e` to `y` that avoids `d`, as the points after the entry it passes,
as `Body.pathB` (`StrataMantle/DomComplete.lean`) checks it. -/
public def avoidingPoints (bs : HashMap Label (Block env α)) (e : Label) (d y : Point) :
    Option (List Point) :=
  (avoidingPath bs e d y).bind (pathPoints bs d y)

/-- The labels of the blocks a path from the entry `e` reaches. -/
def reachedFrom (bs : HashMap Label (Block env α)) (e : Label) : HashSet Label := Id.run do
  let mut seen : HashSet Label := ({} : HashSet Label).insert e
  let mut queue := #[e]
  let mut i := 0
  for _ in [:bs.size + 1] do
    if h : i < queue.size then
      let l := queue[i]
      i := i + 1
      let some b := bs[l]? | continue
      for (_, t) in edges b do
        if !seen.contains t && bs.contains t then
          seen := seen.insert t
          queue := queue.push t
  return seen

/-- The problems of a body entered where `vis` is visible, appended to `out`. -/
partial def body (names : Array Name) (vis : HashSet ValId) (blocks : Array (Block env α))
    (out : Array String) : Array String := Id.run do
  let mut out := out
  let some e := blocks[0]? | return out
  let bs : HashMap Label (Block env α) :=
    blocks.foldl (fun m b => m.insert b.label b) {}
  let reached := reachedFrom bs e.label
  for b in blocks do
    unless reached.contains b.label do
      out := out.push s!"block {labelText b.label} is unreachable from the entry"
  -- Where each value of the body is defined.
  let mut defAt : HashMap ValId Point := {}
  for b in blocks do
    for d in b.params do defAt := defAt.insert d.id ⟨b.label, 0⟩
    for h : k in [:b.instrs.size] do
      defAt := defAt.insert b.instrs[k].result.id ⟨b.label, k + 1⟩
  -- A value is in scope where no path from the entry avoids its definition.
  let inScopeAt (x : ValId) (l : Label) (k : Nat) : Bool :=
    vis.contains x || (defAt[x]?.any fun d => (avoidingPath bs e.label d ⟨l, k⟩).isNone)
  let report (x : ValId) (l : Label) (k : Nat) : String :=
    let use := s!"`{valText names x}`"
    match defAt[x]? with
    | none => s!"{use} is used in {labelText l} but is not in scope there: it is not defined \
        in this body, nor visible where the body is entered"
    | some d =>
      match avoidingPath bs e.label d ⟨l, k⟩ with
      | some path => s!"{use} (defined in {labelText d.label}) is used in {labelText l}, \
          reachable via `{" → ".intercalate (path.map (ToDDM.nameText ·.name))}` without it"
      | none => s!"{use} (defined in {labelText d.label}) is used in {labelText l}"
  for b in blocks do
    let n := b.instrs.size
    let regionVis (k : Nat) : HashSet ValId := Id.run do
      let mut v := vis
      for (x, _) in defAt.toList do
        if inScopeAt x b.label k then v := v.insert x
      return v
    for h : k in [:n] do
      let i := b.instrs[k]
      for x in uses i.args i.succs do
        unless inScopeAt x b.label k do out := out.push (report x b.label k)
      unless i.regions.isEmpty do
        let v := regionVis k
        for r in i.regions do out := body names v r.blocks out
    for x in uses b.term.args b.term.succs do
      unless inScopeAt x b.label n do out := out.push (report x b.label n)
    unless b.term.regions.isEmpty do
      let v := regionVis n
      for r in b.term.regions do out := body names v r.blocks out
  return out

end DomDiag

/-- Why the function is not reachable and scoped: one message per block its body's entry does
not reach, and per use out of scope.  Empty for a function that is both. -/
public def Func.scopeDiagnostics (fn : Func env α) : Array String :=
  DomDiag.body fn.names {} fn.blocks #[]

end Strata.Mantle
