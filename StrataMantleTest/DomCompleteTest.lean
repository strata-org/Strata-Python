/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.DomComplete
public import StrataMantle.DomDecide
public import StrataMantle.DomFast
public import StrataMantleTest.DSLTest
import StrataMantle.Env.WF
import StrataMantle.DomCheck
import StrataMantle.DomDiag
import StrataMantle.DomCompute
-- The checks below run the computation, the checker and the path search as compiled code.
meta import StrataMantle.Env.WF
meta import StrataMantle.WF
meta import StrataMantle.DomProps
meta import StrataMantle.DomComplete
meta import StrataMantle.DomDecide
meta import StrataMantle.DomFast
meta import StrataMantle.DomCompute
meta import StrataMantle.DomDiag
meta import StrataMantle.Build
meta import StrataMantleTest.DSLTest

set_option autoImplicit false

/-!
# Scoping by some tree

`Body.Scopable` (`StrataMantle/Dom.lean`) on hand-written control-flow graphs: a
diamond, a loop, an irreducible loop, a loop entered twice, exception edges, and regions through
the builder.

For each, under the tree `Body.domTree?` computes, and for every pair of nodes `d` and `y`, the
diagnostics' path search (`DomDiag.avoidingPoints`) finds a path from the entry to `y` that
avoids `d` exactly when the tree does not put `d` above `y`, and `Body.pathB` accepts the path it
finds.  So on these shapes the computed tree is the exact one `Body.exists_exact` describes, and
the search is complete.

`Body.domTree?` takes the computed tree on all of these, and an order whose join comes before
its arms shows why it checks the order first.

Then the tests refute a use out of scope: `Body.pathB` checks the search's path, and
`Func.not_scopable_of_refutes` turns the check into a proof that no tree scopes the function.
The flat tree of the diamond leaves a use out of scope that the computed tree has in scope, and
the search finds no path there: the use is in scope under some tree, just not under that one.
-/

namespace Strata.Mantle.DomCompleteTest

open Strata.Mantle.DSLTest
open Strata.Mantle.Build (freshVal freshLabel startBlock startFreshBlock emitApply finishBlock
  region goto build FailedFunc)

private abbrev E := Demo.env



private def d (n : Nat) : ValDecl E := ⟨⟨n⟩, Demo.Value⟩

private def lbl (s : String) : Label := ⟨.str .base s⟩

/-- Block `s` after `k` instructions. -/
private def pt (s : String) (k : Nat) : Point := ⟨lbl s, k⟩

/-- `%r = add %a %b ^h()`. -/
private def add (r a b : Nat) (h : String) : Instruction E Unit :=
  .apply () (d r) Demo.add ⟨#[], rfl⟩ #[⟨a⟩, ⟨b⟩] #[⟨lbl h, #[]⟩] #[]

/-- `ret %x`. -/
private def ret (x : Nat) : Terminator E Unit := .ret () ⟨x⟩

/-- `jump ^s()`. -/
private def jump (s : String) : Terminator E Unit := .jump () ⟨lbl s, #[]⟩

/-- `br %c ^t() ^f()`. -/
private def br (c : Nat) (t f : String) : Terminator E Unit :=
  .apply () Demo.br ⟨#[], rfl⟩ #[⟨c⟩] #[⟨lbl t, #[]⟩, ⟨lbl f, #[]⟩] #[]

/-- Block `s` with parameters `ps` (ids), instructions `is` and terminator `t`. -/
private def blk (s : String) (ps : Array Nat) (is : Array (Instruction E Unit))
    (t : Terminator E Unit) : Block E Unit :=
  { label := lbl s, params := (ps.toList.map d).toArray, instrs := is, term := t, info := () }

/-- The function of the blocks. -/
private def fnOf (bs : List (Block E Unit)) : Func E Unit :=
  { name := .str .base "f", retType := Demo.Value, blocks := bs.toArray, names := #[], info := () }

/-- Whether the function is reachable and scopable, as `Func.WF` asks. -/
private def rule (fn : Func E Unit) : Bool := decide (fn.Reachable ∧ fn.Scopable)

/-! ## The search, the checker and the computed tree -/

/-- The path the diagnostics find from the entry to `y` that avoids `d`. -/
private def find (bs : List (Block E Unit)) (d y : Point) : Option (List Point) :=
  DomDiag.avoidingPoints (bs.foldl (fun m b => m.insert b.label b) {})
    ((bs.head?.map (·.label)).getD default) d y

/-- Whether the tree `t` of the blocks puts `d` at or above `y`. -/
private def anc (bs : List (Block E Unit)) (t : Body.Tree) (d y : Point) : Bool :=
  match Body.tree? bs with
  | none => false
  | some tm =>
    match tm.find? y.label with
    | none => false
    | some b => Body.above (Body.chain tm t bs.length b y.count) d

/-- The nodes of the body. -/
private def nodes (bs : List (Block E Unit)) : List Point :=
  bs.flatMap fun b => (List.range (b.instrs.size + 1)).map (⟨b.label, ·⟩)

/-- Under the computed tree, for every pair of nodes, the search finds a path avoiding `d` to
`y` exactly when the tree does not put `d` above `y`, and the checker accepts it. -/
private def exact (bs : List (Block E Unit)) : Bool :=
  match Body.domTree? bs with
  | none => false
  | some t =>
    (nodes bs).all fun d => (nodes bs).all fun y =>
      match find bs d y with
      | some ps => !anc bs t d y && Body.pathB bs d y ps
      | none => anc bs t d y

/-- `exact` for the body and every region nested in it. -/
private partial def exactAll (bs : List (Block E Unit)) : Bool :=
  exact bs && bs.all fun b =>
    (b.instrs.toList.flatMap (·.regions.toList) ++ b.term.regions.toList).all
      (exactAll ·.blocks.toList)

/-! ## Shapes -/

/-- `entry` computes `%1` and branches to `l` and `r`, which both jump to `j`. -/
private def diamond : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h"] (br 0 "l" "r"),
   blk "l" #[] #[] (jump "j"), blk "r" #[] #[add 2 1 1 "h"] (jump "j"),
   blk "j" #[] #[] (ret 1), blk "h" #[3] #[] (ret 3)]

#guard exact diamond
#guard rule (fnOf diamond)

private def loop : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h"] (jump "head"),
   blk "head" #[] #[add 2 1 1 "h"] (br 0 "body" "exit"),
   blk "body" #[] #[add 3 2 2 "h"] (jump "head"),
   blk "exit" #[] #[] (ret 2), blk "h" #[4] #[] (ret 4)]

#guard exact loop
#guard rule (fnOf loop)

/-- Two loops, one inside the other. -/
private def nested : List (Block E Unit) :=
  [blk "entry" #[0] #[] (jump "outer"),
   blk "outer" #[] #[add 1 0 0 "h"] (br 0 "inner" "exit"),
   blk "inner" #[] #[add 2 1 1 "h"] (br 0 "inner" "latch"),
   blk "latch" #[] #[] (jump "outer"),
   blk "exit" #[] #[] (ret 1), blk "h" #[4] #[] (ret 4)]

#guard exact nested
#guard rule (fnOf nested)

/-- `a` and `b` jump to each other, and the entry enters both. -/
private def irreducible : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h"] (br 0 "a" "b"),
   blk "a" #[] #[add 2 1 1 "h"] (br 0 "b" "x"), blk "b" #[] #[] (br 0 "a" "x"),
   blk "x" #[] #[] (ret 1), blk "h" #[3] #[] (ret 3)]

#guard exact irreducible
#guard rule (fnOf irreducible)

/-- A loop of `b` and `c` that `a` enters at `b` and the entry at `c`. -/
private def twice : List (Block E Unit) :=
  [blk "entry" #[0] #[] (br 0 "a" "c"), blk "a" #[] #[] (br 0 "b" "w"),
   blk "b" #[] #[] (br 0 "c" "w"), blk "w" #[] #[] (ret 0), blk "c" #[] #[] (jump "b")]

#guard exact twice
#guard rule (fnOf twice)

/-- Exception edges leave before their instruction. -/
private def raising : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h", add 2 1 1 "h2"] (jump "b"),
   blk "b" #[] #[add 3 2 2 "h2"] (ret 3),
   blk "h" #[4] #[] (ret 4), blk "h2" #[5] #[] (ret 1)]

#guard exact raising
#guard rule (fnOf raising)

/-! ## The computed tree's order

`Body.domTree?` takes the computed tree only when the depth-first search's order lists every
block, the entry first, each entered from an earlier one (`Body.EarlierPred`).  It does on every
shape above.  The order matters: in its own order, `joinFirst`'s join `j` comes before the arms
that enter it, so the first pass gives `j` the start of the entry, and the later passes only
move parents up.  `j` keeps a parent above its immediate dominator, `d` after its `add`. -/

#guard [diamond, loop, nested, irreducible, twice, raising].all (Body.domTree? · |>.isSome)

private def joinFirst : List (Block E Unit) :=
  [blk "entry" #[0] #[] (jump "d"), blk "d" #[] #[add 1 0 0 "h"] (br 0 "q1" "q2"),
   blk "j" #[] #[] (ret 1), blk "q1" #[] #[] (jump "j"), blk "q2" #[] #[] (jump "j"),
   blk "h" #[3] #[] (ret 3)]

#guard !Body.earlierPredB joinFirst
#guard (Body.computeTree joinFirst).find? (lbl "j") = some (pt "entry" 0)
#guard (Body.domTree? joinFirst).bind (· (lbl "j")) = some (pt "d" 1)

/-! ## Regions, through the builder -/

private def withRegion : Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF} :=
  build (.str .base "f") Demo.Value () do
    let x ← freshVal (.str .base "x") Demo.Value
    let c ← freshVal (.str .base "c") Base.Bool
    let _ ← startFreshBlock #[x, c] "entry"
    let thn := region #[] (base := "t") do
      let t2 ← freshLabel "t2"
      let _ ← emitApply (.str .base "s") Demo.Value Demo.add #[x.id, x.id] #[goto t2]
      finishBlock (.jump () (goto t2 #[x.id]))
      let v ← freshVal (.str .base "v") Demo.Value
      startBlock t2 #[v]
      finishBlock (.ret () v.id)
    let els := region #[] (finishBlock (.ret () x.id)) "e"
    let r ← emitApply (.str .base "r") Demo.Value Demo.«if» #[c.id] (regions := #[thn, els])
    finishBlock (.ret () r)

#guard match withRegion with
  | .ok f => exactAll f.1.blocks.toList && rule f.1
  | .error _ => false

/-! ## A use one tree misses, but another tree has

Under the flat tree every block is under the entry before its first transfer, the `add`, so `j`
does not see `%1`.  The computed tree has `j` under the branch, which every path to `j` passes
after `%1`: the search finds no path to `j` avoiding `%1`'s definition, and the function is
scopable. -/

/-- The flat tree: every block but the entry under the entry before its first transfer. -/
private def flatTree (bs : List (Block E Unit)) : Body.Tree := fun l =>
  match bs.head? with
  | none => none
  | some e =>
    if l = e.label then none else some ⟨e.label, e.instrs.toList.findIdx (!·.succs.isEmpty)⟩

#guard !Body.checkScopedBy (fun _ => false) diamond (flatTree diamond)
#guard (Body.domTree? diamond).any (Body.checkScopedBy (fun _ => false) diamond ·)
#guard rule (fnOf diamond)
#guard find diamond (pt "entry" 1) (pt "j" 0) = none

/-! ## A use no tree has

`j` returns `%2`, which only `r` defines.  The search finds the path through `l`, the checker
accepts it, and so no tree scopes the function. -/

private def badDiamond : List (Block E Unit) :=
  [blk "entry" #[0] #[add 1 0 0 "h"] (br 0 "l" "r"),
   blk "l" #[] #[] (jump "j"), blk "r" #[] #[add 2 1 1 "h"] (jump "j"),
   blk "j" #[] #[] (br 2 "x" "x"), blk "x" #[] #[] (ret 1), blk "h" #[3] #[] (ret 3)]

#guard !rule (fnOf badDiamond)
#guard find badDiamond (pt "r" 1) (pt "j" 0) = some [pt "entry" 1, pt "l" 0, pt "j" 0]
#guard Body.refutes (fun d => (find badDiamond d (pt "j" 0)).getD []) badDiamond ⟨2⟩ (pt "j" 0)

/-- No tree scopes `badDiamond`: the path `entry → l → j` avoids `%2`'s only definition. -/
example : ¬ (fnOf badDiamond).Scopable :=
  Func.not_scopable_of_refutes (fn := fnOf badDiamond) (x := ⟨2⟩) (y := pt "j" 0)
    (find := fun _ => [pt "entry" 1, pt "l" 0, pt "j" 0])
    (.term (b := blk "j" #[] #[] (br 2 "x" "x"))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self)))
      (.inl ⟨List.mem_cons_self⟩))
    (by decide +kernel)

/-! ## Unreachable blocks

The entry does not reach `u`, which jumps to both `v` and `w`.  `v` uses `%1`, which `a`
defines, and `w` uses `%2`, which `b` defines.  Every path from the entry to `v` passes `a`'s
`add`, and every path to `w` passes `b`'s, so the function is dominance-correct.  But (L3) puts
the parents of `v` and `w` above `u`'s terminator, and the points above one point form a chain,
so no legal tree has `a` after its `add` above `v` and `b` after its `add` above `w`: no tree
scopes the function, though both uses are in blocks that run.  That is why `Func.WF` asks that
the entry reach every block.  The builder drops `u`, after which the function is reachable and
scopable.

As the function is not reachable, only the uses' check shows it dominance-correct: `availB`
needs only distinct labels. -/

private def unreached : List (Block E Unit) :=
  [blk "entry" #[0] #[] (br 0 "a" "b"),
   blk "a" #[] #[add 1 0 0 "h"] (jump "v"), blk "b" #[] #[add 2 0 0 "h"] (jump "w"),
   blk "v" #[] #[] (ret 1), blk "w" #[] #[] (ret 2),
   blk "u" #[] #[] (br 0 "v" "w"), blk "h" #[3] #[] (ret 3)]

#guard Block.domOKList (Body.availB unreached fun _ => false) unreached
#guard !rule (fnOf unreached)
#guard (Body.dropUnreached unreached).length = 6
#guard rule (fnOf (Body.dropUnreached unreached))

end Strata.Mantle.DomCompleteTest
