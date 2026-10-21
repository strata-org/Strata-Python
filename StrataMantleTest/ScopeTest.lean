/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.DomDiag
public import StrataMantleTest.DSLTest
public import StrataMantleTest.RegionTest
import StrataMantle.Env.WF
import all StrataMantleTest.RegionTest
meta import StrataMantle.WF
meta import StrataMantle.DomProps
meta import StrataMantle.DomFast
meta import StrataMantle.DomDiag
meta import StrataMantle.Build
meta import StrataMantleTest.DSLTest
meta import StrataMantleTest.RegionTest

set_option autoImplicit false

/-!
# Scoping

Functions written as blocks, whose cases check that the rule says what it should.  First
`Body.checkScopedBy` checks a given tree against `Body.ScopedBy`: what a block sees through its
parent, which trees are legal, and the block-local rule.  Then the rule itself, `Func.WF`'s
`reachable` and `scoping`, which asks only that some tree exist: siblings, a long chain, and
regions.  Each of these rejections has an accepted twin.  Then the tree the check computes for
a built function, and a build with a use out of scope, which fails with an explanation.
-/

namespace Strata.Mantle.ScopeTest

open Strata.Mantle.DSLTest
open Strata.Mantle.Build (freshVal freshLabel startBlock startBlockWith startFreshBlock
  emitApply finishBlock terminate goto build FailedFunc)

private abbrev E := Demo.env

private def valT : TypeExpr E := Demo.Value.ty

private def d (n : Nat) : ValDecl E := ⟨⟨n⟩, valT⟩

private def lbl (s : String) : Label := ⟨.str .base s⟩

/-- Block `s` after `k` instructions. -/
private def pt (s : String) (k : Nat) : Point := ⟨lbl s, k⟩

/-- `%r = add %a %b ^h()`. -/
private def add (r a b : Nat) (h : String) (hargs : Array ValId := #[]) : Instruction E Unit :=
  .apply () (d r) Demo.add ⟨#[], rfl⟩ #[⟨a⟩, ⟨b⟩] #[⟨lbl h, hargs⟩] #[]

/-- Block `s` with parameters `ps` (ids), instructions `is` and terminator `t`. -/
private def blk (s : String) (ps : Array Nat) (is : Array (Instruction E Unit))
    (t : Terminator E Unit) : Block E Unit :=
  { label := lbl s, params := ps.map d, instrs := is, term := t, info := () }

/-- The tree that gives block `s` the parent `p` for each `(s, p)`, and no other block one. -/
private def tr (ps : List (String × Point)) : Body.Tree :=
  fun l => (ps.find? fun (s, _) => decide (lbl s = l)).map (·.2)

/-- Whether the tree `t` scopes the function's top-level body: `Body.ScopedBy`, decided. -/
private def scopedBy (fn : Func E Unit) (t : Body.Tree) : Bool :=
  Body.checkScopedBy (fun _ => false) fn.blocks.toList t

/-- Whether the function is reachable and scopable, as `Func.WF` asks. -/
private def rule {env : Env Unit} (fn : Func env Unit) : Bool := decide (fn.Reachable ∧ fn.Scopable)

private def fn (bs : Array (Block E Unit)) : Func E Unit :=
  { name := .str .base "f", retType := valT, blocks := bs, names := #[], info := () }

/-- `ret %x`. -/
private def ret (x : Nat) : Terminator E Unit := .ret () ⟨x⟩

/-- `jump ^s()`. -/
private def jump (s : String) : Terminator E Unit := .jump () ⟨lbl s, #[]⟩

/-! ## The running example

    entry(%0):
      %1 = add %0 %0 ^h()
      %2 = add %1 %1 ^h()
      jump ^b()
    b:                 -- returns `%x`, the `x` given to `ex`
      ret %x
    h(%3):
      ret %3

The entry may first leave at `⟨entry, 0⟩`, which the flat tree puts `b` and `h` under.  `b`
is entered only from the entry's end, so `⟨entry, 2⟩` may be its parent too. -/

private def ex (x : Nat) : Func E Unit :=
  fn #[blk "entry" #[0] #[add 1 0 0 "h", add 2 1 1 "h"] (jump "b"),
    blk "b" #[] #[] (ret x), blk "h" #[3] #[] (ret 3)]

/-- The flat tree of `ex`: `b` and `h` under `⟨entry, 0⟩`. -/
private def exFlat : Body.Tree := tr [("b", pt "entry" 0), ("h", pt "entry" 0)]

-- Under the flat tree, `b` sees the entry's parameter, not its results.
#guard scopedBy (ex 0) exFlat
#guard !scopedBy (ex 2) exFlat

-- Under the precise tree, `b` sees both results.
#guard scopedBy (ex 2) (tr [("b", pt "entry" 2), ("h", pt "entry" 0)])
#guard scopedBy (ex 1) (tr [("b", pt "entry" 2), ("h", pt "entry" 0)])

-- The rule asks only that some tree exist, so `b` may use the results; `h`'s parameter is in
-- scope under no tree.
#guard rule (ex 2)
#guard !rule (ex 3)

/-! ## Legal trees -/

-- (L3) `h` is entered from `⟨entry, 0⟩`, above `⟨entry, 1⟩`.
#guard !scopedBy (ex 0) (tr [("b", pt "entry" 0), ("h", pt "entry" 1)])

-- (L1) The entry has no parent.
#guard !scopedBy (fn #[blk "entry" #[0] #[] (ret 0)]) (tr [("entry", pt "entry" 0)])
#guard scopedBy (fn #[blk "entry" #[0] #[] (ret 0)]) (tr [])

-- (L2) Every other block has one, a node of the body.
#guard !scopedBy (ex 0) (tr [("h", pt "entry" 0)])
#guard !scopedBy (ex 0) (tr [("b", pt "nowhere" 0), ("h", pt "entry" 0)])
#guard !scopedBy (ex 0) (tr [("b", pt "entry" 3), ("h", pt "entry" 0)])
#guard scopedBy (ex 0) (tr [("b", pt "entry" 2), ("h", pt "entry" 0)])

/-- Two unreachable blocks `u` and `w`, which `u` jumps to. -/
private def cyc (x : Nat) : Func E Unit :=
  fn #[blk "entry" #[0] #[] (ret 0), blk "u" #[] #[add 1 0 0 "w"] (jump "w"),
    blk "w" #[4] #[] (ret x)]

-- (L2) A chain reaches the root, unreachable code included, so no value can depend on itself.
#guard !scopedBy (cyc 0) (tr [("u", pt "w" 0), ("w", pt "u" 0)])
#guard !scopedBy (cyc 0) (tr [("u", pt "u" 0), ("w", pt "w" 0)])
#guard scopedBy (cyc 0) (tr [("u", pt "entry" 0), ("w", pt "u" 0)])
#guard scopedBy (cyc 4) (tr [("u", pt "entry" 0), ("w", pt "entry" 0)])

-- But the rule asks that every block be reachable.
#guard !rule (cyc 0)
#guard rule (fn #[blk "entry" #[0] #[] (jump "u"), blk "u" #[] #[add 1 0 0 "w"] (jump "w"),
    blk "w" #[4] #[] (ret 0)])

/-- The blocks labelled `ls` all have entries in the ancestor map of the function's blocks under
the tree `t`. -/
private def mapped (f : Func E Unit) (t : Body.Tree) (ls : List Label) : Bool :=
  let bs := f.blocks.toList
  match Body.tree? bs with
  | some tm => let m := Body.ancs tm t bs; ls.all fun l => (m.find? l).isSome
  | none => false

-- The ancestor map has an entry for a block exactly when the block's chain reaches the root;
-- for a block without one, the checker walks its chain.
#guard !mapped (cyc 0) (tr [("u", pt "w" 0), ("w", pt "u" 0)]) [lbl "u"]
#guard mapped (cyc 0) (tr [("u", pt "entry" 0), ("w", pt "u" 0)]) [lbl "u", lbl "w"]

/-! ## Within a block

The rule is the same under any tree here: a handler is entered from inside the block. -/

/-- The tree that puts `h` under the entry's start. -/
private def hTree : Body.Tree := tr [("h", pt "entry" 0)]

-- A handler does not see the result of the operation that failed.
#guard !scopedBy (fn #[blk "entry" #[0] #[add 1 0 0 "h"] (ret 1), blk "h" #[3] #[] (ret 1)])
  hTree
#guard scopedBy (fn #[blk "entry" #[0] #[add 1 0 0 "h"] (ret 1), blk "h" #[3] #[] (ret 0)])
  hTree
#guard !rule (fn #[blk "entry" #[0] #[add 1 0 0 "h"] (ret 1), blk "h" #[3] #[] (ret 1)])
#guard rule (fn #[blk "entry" #[0] #[add 1 0 0 "h"] (ret 1), blk "h" #[3] #[] (ret 0)])

-- Nor may a successor pass it.
#guard !scopedBy (fn #[blk "entry" #[0] #[add 1 0 0 "h" #[⟨1⟩]] (ret 1),
    blk "h" #[2, 3] #[] (ret 2)]) hTree
#guard scopedBy (fn #[blk "entry" #[0] #[add 1 0 0 "h" #[⟨0⟩]] (ret 1),
    blk "h" #[2, 3] #[] (ret 2)]) hTree

-- No use of an instruction's own result, nor of a later one.
#guard !scopedBy (fn #[blk "entry" #[0] #[add 1 1 0 "h"] (ret 1), blk "h" #[3] #[] (ret 0)])
  hTree
#guard !scopedBy (fn #[blk "entry" #[0] #[add 1 2 0 "h", add 2 0 0 "h"] (ret 1),
    blk "h" #[3] #[] (ret 0)]) hTree
#guard scopedBy (fn #[blk "entry" #[0] #[add 1 0 0 "h", add 2 1 0 "h"] (ret 2),
    blk "h" #[3] #[] (ret 0)]) hTree

/-! ## Siblings

`entry` branches to `l` and `r`; `l` returns and `r` jumps to `j`.  Neither side sees the
other's values, and `j`, entered from `r` alone, sees `r`'s and not `l`'s. -/

private def diamond (lUse jUse : Nat) : Func E Unit :=
  fn #[blk "entry" #[0, 5] #[]
      (.apply () Demo.br ⟨#[], rfl⟩ #[⟨5⟩] #[⟨lbl "l", #[]⟩, ⟨lbl "r", #[]⟩] #[]),
    blk "l" #[] #[add 1 0 0 "h"] (.ret () ⟨lUse⟩),
    blk "r" #[] #[add 2 0 0 "h"] (jump "j"),
    blk "j" #[] #[] (ret jUse),
    blk "h" #[3] #[] (ret 3)]

#guard rule (diamond 1 0)
#guard !rule (diamond 2 0)
#guard rule (diamond 1 2)
#guard !rule (diamond 1 1)

/-! ## A value defined twice

A tree puts a use in scope if some definition is above it, so a value that `l` and `r` both
define is in scope in each of them, and not in `j`.  Well-formedness rejects such a function for
other reasons; the checker still keeps every point that defines a value. -/

private def twice (lUse jUse : Nat) : Func E Unit :=
  fn #[blk "entry" #[0, 5] #[]
      (.apply () Demo.br ⟨#[], rfl⟩ #[⟨5⟩] #[⟨lbl "l", #[]⟩, ⟨lbl "r", #[]⟩] #[]),
    blk "l" #[] #[add 1 0 0 "h"] (.ret () ⟨lUse⟩),
    blk "r" #[] #[add 1 0 0 "h"] (ret 1),
    blk "j" #[] #[] (ret jUse),
    blk "h" #[3] #[] (ret 3)]

/-- The flat tree of `twice`. -/
private def twiceFlat : Body.Tree :=
  tr [("l", pt "entry" 0), ("r", pt "entry" 0), ("j", pt "entry" 0), ("h", pt "entry" 0)]

#guard scopedBy (twice 1 0) twiceFlat
#guard !scopedBy (twice 1 1) twiceFlat

/-! ## A long chain

Block `b.i` of the chain computes `%(i+1)` from the entry's parameter `%0` and from `%i`, the
value of the block before it, under which it lies, and jumps to the next block; the last
returns `%x`.  Each use is of a value defined up to `n` blocks above it.  The checker builds
each block's ancestors and each value's definitions once, so the chain of 10,000 blocks checks
in time linear in its size, up to the maps' logarithms; looking along each use's chain would
take time quadratic in it.  The rule's check computes the tree first, and then checks the same
way.  On this shape, where every block may fail to `h`, computing the tree takes time quadratic
in the chain's length, so the test checks the rule on a chain of 1,000 blocks. -/

/-- Block `b.i` of the chain. -/
private def bl (i : Nat) : Label := ⟨.num (.str .base "b") i⟩

/-- Block `i` of a chain of `n` blocks, the last returning `%x`. -/
private def link (n x i : Nat) : Block E Unit :=
  { label := bl i, params := if i = 0 then #[d 0] else #[], info := ()
    instrs := #[.apply () (d (i + 1)) Demo.add ⟨#[], rfl⟩ #[⟨0⟩, ⟨i⟩] #[⟨lbl "h", #[]⟩] #[]]
    term := if i + 1 = n then ret x else .jump () ⟨bl (i + 1), #[]⟩ }

/-- A chain of `n` blocks returning `%x`, and a handler under the entry's start that every
block's instruction may fail to. -/
private def longChain (n x : Nat) : Func E Unit :=
  fn (((List.range n).map (link n x)).toArray.push
    (blk "h" #[n + 1] #[] (ret (n + 1))))

/-- The chain's tree, as a map, built once: block `b.i` under its predecessor's instruction, and
the handler under the entry's start. -/
private def chainTree (n : Nat) : LabelMap Point :=
  (List.range n).foldl (init := (∅ : LabelMap Point).insert (lbl "h") ⟨bl 0, 0⟩)
    fun m i => if i = 0 then m else m.insert (bl i) ⟨bl (i - 1), 1⟩

-- The entry's parameter, 10,000 blocks up, and the last block's own result.
#guard scopedBy (longChain 10000 0) (chainTree 10000).find?
#guard scopedBy (longChain 10000 10000) (chainTree 10000).find?
#guard rule (longChain 1000 1000)
-- The handler's parameter is not in scope in the chain.
#guard !scopedBy (longChain 10000 10001) (chainTree 10000).find?
#guard !rule (longChain 1000 1001)
-- Every block of the chain is in the ancestor map, so the checker walks no chain.
#guard mapped (longChain 10000 0) (chainTree 10000).find?
  ((longChain 10000 0).blocks.toList.map (·.label))

/-! ## Regions

`reg.if` runs one of two regions.  A region sees what is in scope at the instruction that owns
it, not that instruction's result; what it defines is visible only in it and in the regions
nested in it. -/

section Regions

open Strata.Mantle.RegionTest

private def intT : TypeExpr Reg.env := Base.Int.ty
private def boolT : TypeExpr Reg.env := Base.Bool.ty

/-- `%r = reg.if[Int] %c { then } { else }`, with `%c` id 0. -/
private def ifI (r : Nat) (thn els : Array (Block Reg.env Unit)) : Instruction Reg.env Unit :=
  .apply () ⟨⟨r⟩, intT⟩ Reg.«if» ⟨#[.ty intT], rfl⟩ #[⟨0⟩] #[] #[⟨thn⟩, ⟨els⟩]

/-- A region body returning `%x`, after defining `%y` as `1`. -/
private def body (s : String) (x y : Nat) : Array (Block Reg.env Unit) :=
  #[{ label := lbl s, params := #[], instrs := #[.const () ⟨⟨y⟩, intT⟩ (.int 1)],
      term := .ret () ⟨x⟩, info := () }]

/-- `f(%0 : Bool, %1 : Int)` whose entry runs `is` and returns `%x`. -/
private def rfn (is : Array (Instruction Reg.env Unit)) (x : Nat) : Func Reg.env Unit :=
  { name := .str .base "f", retType := intT, names := #[], info := ()
    blocks := #[{ label := lbl "entry", params := #[⟨⟨0⟩, boolT⟩, ⟨⟨1⟩, intT⟩], instrs := is,
                  term := .ret () ⟨x⟩, info := () }] }

-- A region sees the function's values, and its own.
#guard rule (rfn #[ifI 2 (body "t" 1 3) (body "e" 4 4)] 2)
-- Not its owner's result.
#guard !rule (rfn #[ifI 2 (body "t" 2 3) (body "e" 4 4)] 2)
-- Nor a sibling region's values, nor do they escape.
#guard !rule (rfn #[ifI 2 (body "t" 4 3) (body "e" 4 4)] 2)
#guard !rule (rfn #[ifI 2 (body "t" 1 3) (body "e" 4 4)] 3)
-- A nested region sees what its enclosing one defines before it.
#guard rule (rfn #[ifI 2
    #[{ label := lbl "t", params := #[], info := ()
        instrs := #[.const () ⟨⟨3⟩, intT⟩ (.int 1), ifI 4 (body "tt" 3 5) (body "te" 1 6)]
        term := .ret () ⟨4⟩ }]
    (body "e" 1 7)] 2)

/-- A region body of two blocks, `t` jumping to `t2`, which returns `%1`. -/
private def twoBlocks : List (Block Reg.env Unit) :=
  [{ label := lbl "t", params := #[], instrs := #[], term := .jump () ⟨lbl "t2", #[]⟩,
      info := () },
    { label := lbl "t2", params := #[], instrs := #[], term := .ret () ⟨1⟩, info := () }]

-- A region's tree is its own: its blocks are under its entry, not under the function's.
#guard !Body.checkScopedBy (· == ⟨1⟩) twoBlocks (tr [("t2", pt "entry" 0)])
#guard Body.checkScopedBy (· == ⟨1⟩) twoBlocks (tr [("t2", pt "t" 0)])
-- A region's blocks must be reachable from its entry too.
#guard rule (rfn #[ifI 2 twoBlocks.toArray (body "e" 1 7)] 2)
#guard !rule (rfn #[ifI 2 twoBlocks.reverse.toArray (body "e" 1 7)] 2)

end Regions

/-! ## The computed tree

`f(%x)` computes `%a = add %x %x` in the entry, then jumps to `b`, which computes `%s` and jumps
to `c`; `c` returns `%a` or `%s`.  Both `add`s may fail to `h`.  The check computes each block's
immediate dominator: `b` is under the entry's jump, `c` under `b`'s, and `h` under the entry
before `%a`, where the first `add` leaves to it.  So `c` sees both. -/

private def builtBody (useS : Bool) : BuildM E Unit Unit := do
  let x ← freshVal (.str .base "x") valT
  let _ ← startFreshBlock #[x] "entry"
  let h ← freshLabel "h"
  let a ← emitApply (.str .base "a") valT Demo.add #[x.id, x.id] #[goto h]
  let b ← freshLabel "b"
  let c ← freshLabel "c"
  finishBlock (.jump () (goto b))
  startBlock b
  let s ← emitApply (.str .base "s") valT Demo.add #[a, a] #[goto h]
  finishBlock (.jump () (goto c))
  startBlock c
  finishBlock (.ret () (if useS then s else a))
  let e ← startBlockWith h (.str .base "e") valT
  finishBlock (.ret () e)

private def built (useS : Bool) : Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF} :=
  build (.str .base "f") valT () (builtBody useS)

/-- Block `s.0` after `k` instructions, as the builder names it. -/
private def bpt (s : String) (k : Nat) : Point := ⟨⟨.num (.str .base s) 0⟩, k⟩

-- The builds succeed, so both functions are well formed, and the check computes this tree.
#guard match built true with
  | .ok f => match Body.domTree? f.1.blocks.toList with
    | some t => decide (f.1.blocks.map (t ·.label) =
        #[none, bpt "entry" 1, bpt "b" 1, bpt "entry" 0])
    | none => false
  | .error _ => false
#guard (built false).isOk

/-! A use that no tree puts in scope, as its definition does not dominate it: `%t` is defined in
`l` only, and `j` is also entered from `r`.  The `add` defining `%t` may fail to `h`.  Its twin
returns `%x` instead. -/

private def joinBody (useT : Bool) : BuildM E Unit Unit := do
  let x ← freshVal (.str .base "x") valT
  let c ← freshVal (.str .base "c") Base.Bool.ty
  let _ ← startFreshBlock #[x, c] "entry"
  let l ← freshLabel "l"
  let r ← freshLabel "r"
  let j ← freshLabel "j"
  let h ← freshLabel "h"
  terminate Demo.br #[c.id] #[goto l, goto r]
  startBlock l
  let t ← emitApply (.str .base "t") valT Demo.add #[x.id, x.id] #[goto h]
  finishBlock (.jump () (goto j))
  startBlock r
  finishBlock (.jump () (goto j))
  startBlock j
  finishBlock (.ret () (if useT then t else x.id))
  let e ← startBlockWith h (.str .base "e") valT
  finishBlock (.ret () e)

private def broken : Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF} :=
  build (.str .base "f") valT () (joinBody true)

-- The build fails with no misuse: the function is not well formed.
#guard match broken with
  | .error e => e.misuses.isEmpty
  | .ok _ => false

/-- info: f is not well formed -/
#guard_msgs in
#eval match broken with
  | .ok _ => IO.println "well formed"
  | .error e => IO.println (toString e)

-- The `FailedFunc` holds the function as emitted, whose diagnostics say why.
/-- info: `%t.0` (defined in `l.0`) is used in `j.0`, reachable via `entry.0 → r.0 → j.0` without it -/
#guard_msgs in
#eval match broken with
  | .ok _ => IO.println "well formed"
  | .error e => for m in e.func.scopeDiagnostics do IO.println m

-- The twin builds, and its function has no diagnostics.
#guard match build (.str .base "f") valT () (joinBody false) with
  | .ok f => f.1.scopeDiagnostics.isEmpty
  | .error _ => false

end Strata.Mantle.ScopeTest
