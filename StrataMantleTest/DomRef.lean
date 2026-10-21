/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR
public import Std.Data.HashMap
public import Std.Data.HashSet
import StrataMantle.DomFast
import StrataMantle.DomDiag
import StrataMantle.DDM
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Dominators, independently

A reference for testing `Body.domTree?`: the dominators of each block's start by the iterative
set-intersection algorithm, as a map from each dominating block to the last of its points that
dominates, `⟨l, 0⟩` up to `⟨l, c⟩`.  A block the entry does not reach has no dominators, and a
transfer from it constrains nothing.  `Func.WF` asks every block to be reachable, so
`idomMismatches` reports such a block.
-/

namespace Strata.Mantle.DomRef

public section

open Std (HashMap) in
/-- The immediate dominator of each block of the body but the entry, by the iterative
set-intersection algorithm. -/
def expectedIdoms {env : Strata.Mantle.Env Unit} {α : Type}
    (bs : Array (Strata.Mantle.Block env α)) : HashMap Strata.Mantle.Label Strata.Mantle.Point :=
  Id.run do
  let some e := bs[0]? | return {}
  let byLabel : HashMap Strata.Mantle.Label (Strata.Mantle.Block env α) :=
    bs.foldl (fun m b => m.insert b.label b) {}
  let mut preds : HashMap Strata.Mantle.Label (Array Strata.Mantle.Point) := {}
  for b in bs do
    for (k, t) in Strata.Mantle.DomDiag.edges b do
      if byLabel.contains t then
        preds := preds.insert t ((preds.getD t #[]).push ⟨b.label, k⟩)
  -- Reachability from the entry.
  let mut reached : Std.HashSet Strata.Mantle.Label := ({} : Std.HashSet _).insert e.label
  let mut work := #[e.label]
  while h : work.size > 0 do
    let l := work.back
    work := work.pop
    for (_, t) in (byLabel.get? l).map Strata.Mantle.DomDiag.edges |>.getD #[] do
      if byLabel.contains t && !reached.contains t then
        reached := reached.insert t
        work := work.push t
  let mut dom : HashMap Strata.Mantle.Label (HashMap Strata.Mantle.Label Nat) :=
    ({} : HashMap _ _).insert e.label (({} : HashMap _ _).insert e.label 0)
  let atPoint (dom : HashMap Strata.Mantle.Label (HashMap Strata.Mantle.Label Nat))
      (p : Strata.Mantle.Point) : Option (HashMap Strata.Mantle.Label Nat) :=
    if reached.contains p.label then (dom.get? p.label).map (·.insert p.label p.count)
    else none
  let meet (a b : HashMap Strata.Mantle.Label Nat) : HashMap Strata.Mantle.Label Nat :=
    a.fold (init := {}) fun m l c => match b.get? l with
      | some c₂ => m.insert l (min c c₂)
      | none => m
  let mut changed := true
  while changed do
    changed := false
    for b in bs.toList.drop 1 do
      unless reached.contains b.label do continue
      let mut new : Option (HashMap Strata.Mantle.Label Nat) := none
      for p in preds.getD b.label #[] do
        if let some dp := atPoint dom p then
          new := some (match new with | none => dp | some n => meet n dp)
      if let some n := new then
        let n := n.insert b.label 0
        if (dom.get? b.label).map (·.toList.length) != some n.size ||
            !((dom.get? b.label).all fun o => n.toList.all fun (l, c) => o.get? l == some c) then
          dom := dom.insert b.label n
          changed := true
  let mut out : HashMap Strata.Mantle.Label Strata.Mantle.Point := {}
  for b in bs.toList.drop 1 do
    if !reached.contains b.label then
      continue
    else if let some ds := dom.get? b.label then
      -- The deepest strict dominator: the one with the most dominators.
      let mut best : Option (Nat × Strata.Mantle.Point) := none
      for (l, c) in ds.toList do
        if l == b.label then continue
        let depth := ((dom.get? l).map (·.size)).getD 0
        if best.all (·.1 < depth) then best := some (depth, ⟨l, c⟩)
      if let some (_, p) := best then out := out.insert b.label p
  return out

/-- The blocks of `bs`, at every region depth, whose parent in the tree `Body.domTree?` computes
is not `expectedIdoms`'. -/
partial def idomMismatches {env : Strata.Mantle.Env Unit} {α : Type}
    (bs : Array (Strata.Mantle.Block env α)) : Array String := Id.run do
  let exp := expectedIdoms bs
  let mut out := #[]
  let some t := Strata.Mantle.Body.domTree? bs.toList
    | return #["the computed order does not check out"]
  for b in bs.toList.drop 1 do
    if (exp.get? b.label).isNone then
      out := out.push s!"{Strata.Mantle.ToDDM.nameText b.label.name}: the entry does not reach it"
    else if t b.label != exp.get? b.label then
      out := out.push s!"{Strata.Mantle.ToDDM.nameText b.label.name}: computed \
        {(t b.label).map Strata.Mantle.DomDiag.pointText}, expected \
        {(exp.get? b.label).map Strata.Mantle.DomDiag.pointText}"
  for b in bs do
    for i in b.instrs do
      for r in i.regions do out := out ++ idomMismatches r.blocks
    for r in b.term.regions do out := out ++ idomMismatches r.blocks
  return out

end

end Strata.Mantle.DomRef
