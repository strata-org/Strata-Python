/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.RefToReg
public import Std.Data.HashMap
public import StrataDyn.DDM

set_option autoImplicit false

/-!
# Running a function and its promoted form side by side

A property test of ref-to-reg, until its correctness is proved.
`sameRuns` runs a function and the function `Plan.apply` made from it along the same paths, in
step, and reports the first point where they differ.  The random paths take the edges of the
operations that have successors more or less often, so that both early exits and long runs are
tried.  Then one path per edge of the top-level blocks takes that edge, if its step budget
reaches it: a script of choices leads it there along a shortest path, and it goes on at random.

Values are symbols.  Every kept operation other than the cell operations gives its result a
fresh symbol, the same in both runs, and the two runs must pass it the same operands.  The
original run also performs the removed reads and writes of the promoted cells, on its own heap;
the promoted run doesn't.  At
each operation with successors, a random choice takes an edge or goes on; the values an
operation supplies to its successor (its payload) are fresh symbols.  An operation with regions
runs 0 to 3 times a region it picks at random each time, from a copy of the frame.  A cell
*escapes* when it is given to an operation that is no cell operation, stored in a cell, or left
by an exit.  An operation (before, between and after its region runs), and a caller at an
exit, may read every escaped cell, so each must hold the same in both runs; after each of
these points, each may hold anything, the same fresh symbol
in both (the locality rule, H1).  A call is an operation like any other.  A cell made outside the
function (a parameter, or an operation's result) is a symbol, and a read of it gives a fresh
symbol.  Randomness comes from a fixed seed, so runs are reproducible.
-/

namespace Strata.Dyn.RefToRegSim

open Strata.Dyn.RefToReg
open Std (HashMap)

public section

variable {env : Env Unit} [base ≼ env] {α : Type}

/-- A value: a symbol, or a cell, by its location. -/
inductive Val where
  | sym (n : Nat)
  | cell (loc : Nat)
deriving DecidableEq

/-- `#n` for a symbol, `cell n` for a cell. -/
instance : ToString Val := ⟨fun | .sym n => s!"#{n}" | .cell l => s!"cell {l}"⟩

/-- A place where a run chooses an edge: an instruction with successors, by its result, or a
block's terminator, by the block's label. -/
inductive Site where
  | instr (result : ValId)
  | term (block : Label)
deriving DecidableEq

/-- A choice made in advance at a site: at an instruction, `0` goes on and `j + 1` takes its
successor `j`; at a terminator, `j` takes its successor `j`. -/
structure Choice where
  site : Site
  pick : Nat

/-- The state of both runs: the random seed, the next symbol, both heaps, and the steps left. -/
structure St where
  seed : Nat
  next : Nat := 0
  heapO : Array Val := #[]
  heapP : Array Val := #[]
  /-- The cells that escaped: given to an operation that is no cell operation, stored in a
  cell, or left by an exit. -/
  escaped : List Nat := []
  fuel : Nat
  /-- One operation in this many takes one of its edges. -/
  errRate : Nat := 3
  /-- Choices to make, in order, before choosing at random: each is used when the run reaches
  its site. -/
  script : List Choice := []

/-- The simulation's monad: it stops with the first difference. -/
abbrev M := StateT St (Except String)

/-- A random number below `n`, or `0`. -/
def rand (n : Nat) : M Nat := do
  let s ← get
  let seed := (s.seed * 1103515245 + 12345) % 2147483648
  set { s with seed }
  return if n == 0 then 0 else (seed / 65536) % n

/-- The next choice of the script, if it is for `site`; it is used up. -/
def scripted (site : Site) : M (Option Nat) := do
  let s ← get
  match s.script with
  | c :: rest =>
    if c.site == site then
      set { s with script := rest }
      return some c.pick
    else return none
  | [] => return none

/-- A fresh symbol. -/
def fresh : M Val := do
  let s ← get
  set { s with next := s.next + 1 }
  return .sym s.next

/-- One step of fuel, or `false` if none is left. -/
def tick : M Bool := do
  let s ← get
  if s.fuel == 0 then return false
  set { s with fuel := s.fuel - 1 }
  return true

/-- Both runs' frames. -/
abbrev Env2 := HashMap ValId Val × HashMap ValId Val

/-- The value of `v` in a frame; an unbound value is a difference too. -/
def look (e : HashMap ValId Val) (v : ValId) (what : String) : M Val :=
  match e.get? v with
  | some x => pure x
  | none => throw s!"{what}: %{v.id} is not bound"

/-- The operands of both instructions, which must be the same values. -/
def sameArgs (e : Env2) (as bs : Array ValId) (what : String) : M (List Val) := do
  unless as.size == bs.size do throw s!"{what}: {as.size} operands against {bs.size}"
  let mut out := []
  for (a, b) in as.toList.zip bs.toList do
    let x ← look e.1 a what
    let y ← look e.2 b what
    unless x == y do throw s!"{what}: operand %{a.id} is {x}, but %{b.id} is {y}"
    out := out ++ [x]
  return out

/-- The cells among `vs` escape. -/
def escape (vs : List Val) : M Unit :=
  for v in vs do
    if let .cell l := v then
      modify fun s => if s.escaped.contains l then s else { s with escaped := l :: s.escaped }

/-- An operation or a caller may read every escaped cell: each must hold the same in both
runs. -/
def sameEscaped (what : String) : M Unit := do
  let s ← get
  for l in s.escaped do
    let x := s.heapO[l]?.getD (.sym 0)
    let y := s.heapP[l]?.getD (.sym 0)
    unless x == y do throw s!"{what}: escaped cell {l} holds {x} and {y}"

/-- An operation given the cells `vs` may read and write them, and every cell that escaped
before: they escape, must hold the same, and then each may hold anything, the same in both
runs (the locality rule, H1). -/
def operate (vs : List Val) (what : String) : M Unit := do
  escape vs
  sameEscaped what
  for l in (← get).escaped do
    let x ← fresh
    modify fun s =>
      { s with heapO := s.heapO.setIfInBounds l x, heapP := s.heapP.setIfInBounds l x }

/-- The block labelled `l` of a body. -/
def blockOf (bs : List (Block env α)) (l : Label) : Option (Block env α) :=
  bs.find? (·.label == l)

/-- An operation's name, for comparing and reporting. -/
def opName : Instruction env α → String
  | .const .. => "const"
  | .apply _ _ r .. => ToDDM.nameText r.name

/-- Bind the parameters of both target blocks from the edges `kO`, `kP`: their arguments, then
the payload, the same fresh symbols for both. -/
def enter (e : Env2) (bO bP : Block env α) (kO kP : Target.Raw) (what : String) :
    M Env2 := do
  let argsO ← kO.args.toList.mapM (look e.1 · what)
  let argsP ← kP.args.toList.mapM (look e.2 · what)
  let nO := bO.params.size - argsO.length
  let nP := bP.params.size - argsP.length
  unless nO == nP do throw s!"{what}: payloads of {nO} and {nP} values"
  let payload ← (List.range nO).mapM fun _ => fresh
  let eO := (bO.params.toList.zip (argsO ++ payload)).foldl (fun m (p, v) => m.insert p.id v) e.1
  let eP := (bP.params.toList.zip (argsP ++ payload)).foldl (fun m (p, v) => m.insert p.id v) e.2
  return (eO, eP)

/-- How a body's run ended: it left by its exit with these values, or ran out of fuel. -/
inductive Exit where
  | value (o p : Val)
  | out

mutual

/-- Run both bodies from their blocks `bO`, `bP`, with frames `e`, at most `n` blocks deep. -/
def runBlocks (P : Plan env) (bsO bsP : List (Block env α)) :
    Nat → Block env α → Block env α → Env2 → M Exit
  | 0, _, _, _ => pure .out
  | n + 1, bO, bP, e => do
    match ← runInstrs P bsO bsP n bO.instrs.toList bP.instrs.toList e with
    | .inl (kO, kP, e) => follow P bsO bsP n kO kP e
    | .inr none => pure .out
    | .inr (some e) =>
      let tO := bO.term
      let tP := bP.term
      let what := s!"the terminator of {ToDDM.nameText bO.label.name}"
      let vs ← sameArgs e tO.args tP.args what
      unless tO.regions.size == tP.regions.size do throw s!"{what}: different regions"
      escape vs
      sameEscaped what
      for _ in [0:← rand 4] do
        if tO.regions.size > 0 then
          let j ← rand tO.regions.size
          if let (some rO, some rP) := (tO.regions[j]?, tP.regions[j]?) then
            if let .out ← runRegion P n rO rP e then return .out
            operate vs what
      operate vs what
      -- A terminator with no successor, such as `unreachable`, ends the path.
      if tO.succs.size == 0 then return .out
      let j ← match ← scripted (.term bO.label) with
        | some j => pure j
        | none => rand tO.succs.size
      match tO.succs[j]?, tP.succs[j]? with
      | some kO, some kP => follow P bsO bsP n kO kP e
      | _, _ => throw s!"{what}: no successor {j}"

/-- Take the edges `kO`, `kP`: leave the body by its exit, or go on in the target blocks. -/
def follow (P : Plan env) (bsO bsP : List (Block env α)) :
    Nat → Target.Raw → Target.Raw → Env2 → M Exit
  | 0, _, _, _ => pure .out
  | n + 1, kO, kP, e => do
    unless kO.label == kP.label do throw "two edges to different blocks"
    if kO.label == Label.exit then
      let vs ← sameArgs e kO.args kP.args "an exit"
      escape vs
      sameEscaped "an exit"
      match vs with
      | [v] => pure (.value v v)
      | _ => throw "an exit without one value"
    else
      match blockOf bsO kO.label, blockOf bsP kP.label with
      | some bO, some bP =>
        let e ← enter e bO bP kO kP s!"the edge to {ToDDM.nameText kO.label.name}"
        runBlocks P bsO bsP n bO bP e
      | _, _ => throw s!"no block {ToDDM.nameText kO.label.name}"

/-- Run a region of both, from copies of the frames, with the same fresh arguments. -/
def runRegion (P : Plan env) : Nat → Region env α → Region env α → Env2 → M Exit
  | 0, _, _, _ => pure .out
  | n + 1, rO, rP, e => do
    match rO.blocks.toList, rP.blocks.toList with
    | bO :: _, bP :: _ =>
      let args ← (List.range bO.params.size).mapM fun _ => fresh
      unless bO.params.size == bP.params.size do throw "regions with different parameters"
      let eO := (bO.params.toList.zip args).foldl (fun m (p, v) => m.insert p.id v) e.1
      let eP := (bP.params.toList.zip args).foldl (fun m (p, v) => m.insert p.id v) e.2
      runBlocks P rO.blocks.toList rP.blocks.toList n bO bP (eO, eP)
    | _, _ => throw "a region without blocks"

/-- Run both blocks' instructions: the original's removed reads and writes on its own, and
every other instruction in step.  It ends with an edge taken, the frames at the terminator, or
no fuel. -/
def runInstrs (P : Plan env) (bsO bsP : List (Block env α)) :
    Nat → List (Instruction env α) → List (Instruction env α) → Env2 →
      M ((Target.Raw × Target.Raw × Env2) ⊕ Option Env2)
  | 0, _, _, _ => pure (.inr none)
  | _ + 1, [], [], e => pure (.inr (some e))
  | n + 1, iO :: isO, isP, e => do
    unless ← tick do return .inr none
    if P.drops iO then
      match cellOp? iO with
      | some (.get r c) =>
        let x ← look e.1 c "a removed read"
        let .cell l := x | throw "a removed read of a value that is not a cell"
        let v := (← get).heapO[l]?.getD (.sym 0)
        runInstrs P bsO bsP n isO isP (e.1.insert r v, e.2)
      | some (.set _ c v) =>
        let .cell l ← look e.1 c "a removed write"
          | throw "a removed write to a value that is not a cell"
        let x ← look e.1 v "a removed write"
        modify fun s => { s with heapO := s.heapO.setIfInBounds l x }
        runInstrs P bsO bsP n isO isP e
      | _ => throw "a removed instruction that is no read or write"
    else
    match isP with
    | [] => throw s!"the promoted block ends before {opName iO}"
    | iP :: isP => do
      let what := s!"{opName iO} defining %{iO.result.id.id}"
      unless opName iO == opName iP do throw s!"{what}: against {opName iP}"
      let vs ← sameArgs e iO.args iP.args what
      let e ← match cellOp? iO with
        | some (.new c _) =>
          escape vs
          let s ← get
          let l := s.heapO.size
          set { s with heapO := s.heapO.push (vs.headD (.sym 0)),
                       heapP := s.heapP.push (vs.headD (.sym 0)) }
          pure (e.1.insert c (.cell l), e.2.insert iP.result.id (.cell l))
        | some (.get r _) =>
          match vs.headD (.sym 0) with
          | .cell l =>
            let s ← get
            let x := s.heapO[l]?.getD (.sym 0)
            let y := s.heapP[l]?.getD (.sym 0)
            unless x == y do throw s!"{what}: the cell holds {x} and {y}"
            pure (e.1.insert r x, e.2.insert iP.result.id y)
          | .sym _ =>
            -- A cell made outside the function (a parameter, or an operation's result): its
            -- content may be anything, the same in both runs.
            let x ← fresh
            pure (e.1.insert r x, e.2.insert iP.result.id x)
        | some (.set _ _ _) =>
          escape (vs.drop 1)
          if let .cell l := vs.headD (.sym 0) then
            let x := vs.getD 1 (.sym 0)
            modify fun s => { s with heapO := s.heapO.setIfInBounds l x,
                                     heapP := s.heapP.setIfInBounds l x }
          let x ← fresh
          pure (e.1.insert iO.result.id x, e.2.insert iP.result.id x)
        | none => do
          unless iO.regions.size == iP.regions.size do throw s!"{what}: different regions"
          escape vs
          sameEscaped what
          for _ in [0:← rand 4] do
            if iO.regions.size > 0 then
              let j ← rand iO.regions.size
              if let (some rO, some rP) := (iO.regions[j]?, iP.regions[j]?) then
                if let .out ← runRegion P n rO rP e then return .inr none
                operate vs what
          operate vs what
          let x ← fresh
          pure (e.1.insert iO.result.id x, e.2.insert iP.result.id x)
      -- Take one of the operation's edges as the script says, or one time in `errRate`.  The
      -- roll is drawn at every instruction, so the random paths don't depend on the script.
      let roll ← rand (← get).errRate
      let pick ← if iO.succs.size == 0 then pure none else
        match ← scripted (.instr iO.result.id) with
        | some 0 => pure none
        | some (j + 1) => pure (some j)
        | none => if roll == 0 then pure (some (← rand iO.succs.size)) else pure none
      if let some j := pick then
        match iO.succs[j]?, iP.succs[j]? with
        | some kO, some kP => return .inl (kO, kP, e)
        | _, _ => throw s!"{what}: no successor {j}"
      runInstrs P bsO bsP n isO isP e
  | _ + 1, [], _ :: _, _ => throw "the promoted block has more instructions"

end

/-- The choices of the block `b` that take one of its edges, each with the edge's target. -/
def edgeChoices (b : Block env α) : List (Choice × Label) :=
  b.instrs.toList.flatMap (fun i =>
    i.succs.toList.zipIdx.map fun (k, j) => (⟨.instr i.result.id, j + 1⟩, k.label)) ++
  b.term.succs.toList.zipIdx.map fun (k, j) => (⟨.term b.label, j⟩, k.label)

/-- One script per edge of `fn`'s top-level blocks: the choices along a shortest path from the
entry to the edge's block, then the edge. -/
def coveringScripts (fn : Func env α) : List (List Choice) := Id.run do
  let bs := fn.blocks.toList
  let some entry := bs.head? | return []
  -- The choices that reach each block, found level by level.
  let mut reach : HashMap Label (List Choice) :=
    ({} : HashMap Label (List Choice)).insert entry.label []
  let mut frontier := [entry]
  for _ in [0:bs.length] do
    let mut next := []
    for b in frontier do
      let path := reach.getD b.label []
      for (c, t) in edgeChoices b do
        if !reach.contains t then
          if let some tb := bs.find? (·.label == t) then
            reach := reach.insert t (path ++ [c])
            next := next ++ [tb]
    frontier := next
  return bs.flatMap fun b =>
    match reach.get? b.label with
    | some path => (edgeChoices b).map fun (c, _) => path ++ [c]
    | none => []

/-- Run `fn` and `fn'` side by side once, with the error rate `errRate` and the script
`script`. -/
def onePath (P : Plan env) (fn fn' : Func env α) (steps errRate : Nat) (script : List Choice) :
    M Unit := do
  modify fun s =>
    { s with heapO := #[], heapP := #[], escaped := [], fuel := steps, errRate, script }
  match fn.blocks.toList, fn'.blocks.toList with
  | bO :: _, bP :: _ =>
    let args ← (List.range bO.params.size).mapM fun _ => fresh
    unless bO.params.size == bP.params.size do throw "the functions take different parameters"
    let e : Env2 := ((bO.params.toList.zip args).foldl (fun m (p, v) => m.insert p.id v) {},
      (bP.params.toList.zip args).foldl (fun m (p, v) => m.insert p.id v) {})
    let _ ← runBlocks P fn.blocks.toList fn'.blocks.toList steps bO bP e
  | _, _ => pure ()

/-- Run `fn` and `fn'` side by side along `paths` random paths from `seed`, each at most
`steps` steps, then along one path per edge of `fn`'s top-level blocks that takes that edge
(`coveringScripts`); the first difference, or `none`.  `P` says which instructions of `fn` are
removed in `fn'`. -/
def sameRuns (P : Plan env) (fn fn' : Func env α) (seed paths steps : Nat) : Option String :=
  let go : M Unit := do
    for k in [0:paths] do
      -- One path in three takes an operation's edges a third of the time, the others one time
      -- in thirty.
      onePath P fn fn' steps (if k % 3 == 0 then 3 else 30) []
    -- A covering path takes no edge but those of its script, as far as it goes.
    for script in coveringScripts fn do
      onePath P fn fn' steps 1000000 script
  match go.run { seed, fuel := steps } with
  | .ok _ => none
  | .error e => some e

/-- The first place where the start maps `S` go wrong, or `none`: an edge of the walk whose
content map lacks, or has another value for, an entry of its target's start map other than a
carried cell; or a start map with an entry, other than a carried cell's, whose value is one of
the block's own parameters.  The check doesn't test these: it relies on the changed sets, and
this tests that they are right. -/
def edgesAgree (P : Plan env) (S : Starts) (fn : Func env α) : Option String :=
  let carried (l : Label) := (P.block l).carried.map (·.1)
  let params := blockParams fn
  let fromEdges := (walk P S.maps fn).findSome? fun e =>
    match e with
    | .edge m k =>
      match S.maps.get? k.label with
      | none => none
      | some st =>
        st.toList.findSome? fun (c, u) =>
          if (carried k.label).contains c || m.get? c == some u then none
          else some s!"the edge to {ToDDM.nameText k.label.name} passes \
            {(m.get? c).map (·.id)} for %{c.id}, but the block starts with %{u.id}"
    | _ => none
  fromEdges.orElse fun _ => S.maps.toList.findSome? fun (l, st) =>
    let own := (params.getD l #[]).toList.map (·.id) ++ (P.block l).carried.map (·.2.id)
    st.toList.findSome? fun (c, u) =>
      if !(carried l).contains c && own.contains u then
        some s!"{ToDDM.nameText l.name} starts with its own parameter %{u.id} for %{c.id}"
      else none

end

end Strata.Dyn.RefToRegSim
