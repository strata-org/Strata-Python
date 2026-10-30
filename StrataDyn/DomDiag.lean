/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
import StrataDyn.IRProps
import all StrataDyn.Util.List
import Std.Data.HashMap.Lemmas
import Std.Data.HashSet.Lemmas
import StrataDyn.DDM
public import Std.Data.HashMap
import Std.Data.HashSet
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Why a function is not reachable and scoped

`Func.scopeDiagnostics` explains why a function fails `Func.Reachable` or `Func.Scopable`
(`StrataDyn/Dom.lean`), one message per problem, for a reader or producer to report.  It
names each block its body's entry does not reach, and each use out of scope.  For a use out of
scope it names the value, where it is defined, and a path from the body's entry to the use that
avoids the definition:

    `%t.0` (defined in `entry.0`) is used in `join.0`, reachable via
    `entry.0 → rhs.0 → join.0` without it

In a reachable body a use is in scope under some tree exactly when no such path exists, so the
messages name no tree.  The module only explains, and proves nothing about its messages:
`Func.WF`'s instance makes the decision.
-/

namespace Strata.Dyn

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
def uses (args : Array ValId) (succs : Array Target.Raw) : Array ValId :=
  args ++ succs.flatMap (·.args)

/-- The transfers out of block `b`: the count each leaves from, and its target. -/
public def edges (b : Block env α) : Array (Nat × Label) := Id.run do
  let mut out := #[]
  for h : k in [:b.instrs.size] do
    for s in b.instrs[k].succs do out := out.push (k, s.label)
  for s in b.term.succs do out := out.push (b.instrs.size, s.label)
  return out

/-- The number of keys of `bs` that are not in `seen`: how many blocks a search over `bs` has
left to see. -/
def unseenKeys (bs : HashMap Label (Block env α)) (seen : HashSet Label) : Nat :=
  bs.keys.countP (!seen.contains ·)

/-- Adding to `seen` a key of `bs` that is not in `seen` yet lowers the number of unseen keys. -/
private theorem unseenKeys_insert_lt {bs : HashMap Label (Block env α)} {seen : HashSet Label}
    {t : Label} (ht : bs.contains t = true) (hs : seen.contains t = false) :
    unseenKeys bs (seen.insert t) < unseenKeys bs seen := by
  unfold unseenKeys
  refine List.countP_lt_countP (fun x _ hx => ?_) t ?_ ?_ ?_
  · simp only [Bool.not_eq_true', HashSet.contains_insert, Bool.or_eq_false_iff] at hx ⊢
    exact hx.2
  · exact HashMap.mem_keys.mpr (by simpa using ht)
  · simp
  · simpa using hs

/-- Go through the labels of `ts` in order.  Keep each one that `ok` accepts, that is a key of
`bs`, and that is not in `seen` yet, so a repeated label is kept once.  Each kept label goes into
`seen`, and `mk` of it goes at the end of `queue`. -/
def enqueue {β : Type} (bs : HashMap Label (Block env α)) (ok : Label → Bool) (mk : Label → β) :
    List Label → HashSet Label → Array β → HashSet Label × Array β
  | [], seen, queue => (seen, queue)
  | t :: ts, seen, queue =>
    if ok t && !seen.contains t && bs.contains t then
      enqueue bs ok mk ts (seen.insert t) (queue.push (mk t))
    else enqueue bs ok mk ts seen queue

/-- `enqueue` only grows the queue, and each label it adds uses up one unseen key of `bs`. -/
private theorem enqueue_le {β : Type} (bs : HashMap Label (Block env α)) (ok : Label → Bool)
    (mk : Label → β) : ∀ (ts : List Label) (seen : HashSet Label) (queue : Array β),
      queue.size ≤ (enqueue bs ok mk ts seen queue).2.size ∧
      unseenKeys bs (enqueue bs ok mk ts seen queue).1 + (enqueue bs ok mk ts seen queue).2.size ≤
        unseenKeys bs seen + queue.size
  | [], _, _ => by simp [enqueue]
  | t :: ts, seen, queue => by
    simp only [enqueue]
    split
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      have hlt := unseenKeys_insert_lt hc.2 hc.1.2
      have ih := enqueue_le bs ok mk ts (seen.insert t) (queue.push (mk t))
      simp only [Array.size_push] at ih
      omega
    · exact enqueue_le bs ok mk ts seen queue

/-- The last count of block `l` that a path entering `l` at its start reaches without passing
the point `d`, where `n` is the last count of `l`.  It is `none` if `d` is the start of `l`. -/
def limitAt (d : Point) (l : Label) (n : Nat) : Option Nat :=
  if l = d.label then (if d.count = 0 then none else some (d.count - 1)) else some n

/-- The targets of the transfers out of block `b`, in order. -/
def targets (b : Block env α) : List Label := (edges b).toList.map (·.2)

/-- The targets of the transfers out of block `b` that leave from count `lim` or before, in
order. -/
def targetsWithin (b : Block env α) (lim : Nat) : List Label :=
  ((edges b).toList.filter (·.1 ≤ lim)).map (·.2)

/-- The labels from the search's start to entry `j` of `queue`, followed by `acc`.  Each entry's
parent is the index of the entry it was queued from, which comes before it, and the start is its
own parent. -/
def pathTo (queue : Array (Label × Nat)) (j : Nat) (acc : List Label := []) : List Label :=
  if h : j < queue.size then
    if queue[j].2 < j then pathTo queue queue[j].2 (queue[j].1 :: acc) else queue[j].1 :: acc
  else acc
termination_by j

/-- A path from the entry `e` to the point `y` that avoids the point `d`, as the blocks it
passes, if there is one.  A path through block `d.label` avoids `d` only by leaving before
it.  A breadth-first search: each queue entry is a label and its parent's index. -/
public def avoidingPath (bs : HashMap Label (Block env α)) (e : Label) (d y : Point) :
    Option (List Label) :=
  match limitAt d e 0 with
  | none => none
  | some _ => go (({} : HashSet Label).insert e) #[(e, 0)] 0
where
  /-- The search from entry `i` of `queue` on. -/
  go (seen : HashSet Label) (queue : Array (Label × Nat)) (i : Nat) : Option (List Label) :=
    if h : i < queue.size then
      let l := queue[i].1
      match bs[l]? with
      | none => go seen queue (i + 1)
      | some b =>
        match limitAt d l b.instrs.size with
        | none => go seen queue (i + 1)
        | some lim =>
          if l = y.label && y.count ≤ lim then some (pathTo queue i)
          else
            let r := enqueue bs (limitAt d · 0 |>.isSome) (·, i) (targetsWithin b lim) seen queue
            have hr := enqueue_le bs (limitAt d · 0 |>.isSome) (·, i) (targetsWithin b lim) seen queue
            go r.1 r.2 (i + 1)
    else none
  termination_by unseenKeys bs seen + (queue.size - i)
  decreasing_by all_goals omega

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
as `Body.pathB` (`StrataDyn/DomComplete.lean`) checks it. -/
public def avoidingPoints (bs : HashMap Label (Block env α)) (e : Label) (d y : Point) :
    Option (List Point) :=
  (avoidingPath bs e d y).bind (pathPoints bs d y)

/-- The labels of the blocks a path from the entry `e` reaches, by a breadth-first search. -/
def reachedFrom (bs : HashMap Label (Block env α)) (e : Label) : HashSet Label :=
  go (({} : HashSet Label).insert e) #[e] 0
where
  /-- The search from entry `i` of `queue` on. -/
  go (seen : HashSet Label) (queue : Array Label) (i : Nat) : HashSet Label :=
    if h : i < queue.size then
      match bs[queue[i]]? with
      | none => go seen queue (i + 1)
      | some b =>
        let r := enqueue bs (fun _ => true) id (targets b) seen queue
        have hr := enqueue_le bs (fun _ => true) id (targets b) seen queue
        go r.1 r.2 (i + 1)
    else seen
  termination_by unseenKeys bs seen + (queue.size - i)
  decreasing_by all_goals omega

/-- The problems of a body entered where `vis` is visible, appended to `out`. -/
def body (names : Array Name) (vis : HashSet ValId) (blocks : Array (Block env α))
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
  for hb : b in blocks do
    have hbLt := Array.sizeOf_lt_of_mem hb
    let n := b.instrs.size
    let regionVis (k : Nat) : HashSet ValId := Id.run do
      let mut v := vis
      for (x, _) in defAt.toList do
        if inScopeAt x b.label k then v := v.insert x
      return v
    for h : k in [:n] do
      let i := b.instrs[k]
      have hiLt : sizeOf i < sizeOf b.instrs := Array.sizeOf_getElem b.instrs k (by get_elem_tactic)
      for x in uses i.args i.succs do
        unless inScopeAt x b.label k do out := out.push (report x b.label k)
      unless i.regions.isEmpty do
        let v := regionVis k
        for hr : r in i.regions do
          have hrLt := Instruction.sizeOf_lt_of_mem_regions hr
          have hbsLt := Region.sizeOf_blocks_lt r
          have hinsLt := Block.sizeOf_instrs_lt b
          out := body names v r.blocks out
    for x in uses b.term.args b.term.succs do
      unless inScopeAt x b.label n do out := out.push (report x b.label n)
    unless b.term.regions.isEmpty do
      let v := regionVis n
      for hr : r in b.term.regions do
        have hrLt := Terminator.sizeOf_lt_of_mem_regions hr
        have hbsLt := Region.sizeOf_blocks_lt r
        have htLt := Block.sizeOf_term_lt b
        out := body names v r.blocks out
  return out
termination_by sizeOf blocks
decreasing_by all_goals omega

end DomDiag

/-- Why the function is not reachable and scoped: one message per block its body's entry does
not reach, and per use out of scope.  Empty for a function that is both. -/
public def Func.scopeDiagnostics (fn : Func env α) : Array String :=
  DomDiag.body fn.names {} fn.blocks #[]

/-- Why the region, entered where only the values `visible` are visible, is not reachable and
scoped: one message per block its entry does not reach, and per use out of scope.  `names` are
the names of the values of the function or ghost it belongs to.  Empty for a region that is
both. -/
public def Region.scopeDiagnostics (r : Region env α) (names : Array Name)
    (visible : Array ValId := #[]) : Array String :=
  DomDiag.body names (visible.foldl (·.insert ·) {}) r.blocks #[]

end Strata.Dyn
