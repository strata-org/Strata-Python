/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Programs
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
-- `#eval` runs the engine and the programs as compiled code.
meta import StrataDynTest.Exec.Programs
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Differential tests: `runFused` against iterating `step`

What `runFused_eq` and its corollaries say, checked on runs as well as proved, so that a
statement that is true but not what was meant would show:

* both engines end with the same outcome, heap, world and number of choices;
* each fused step's configuration is the step loop's at the matching `exec` or `again` one;
* at every fuel `k`, `runFused k` ends as `runFrames t` does for some `t ≥ k`, a run that
  `runFrames k` finishes `runFused k` finishes, and a fused timeout is a step-loop timeout;
* the same, from the step loop's configurations in every mode, not only from the start;
* a hook that stops the run after `k` steps, resumed with `runFused`, ends as the run does;
* a hook that only observes runs as `runFrames` does.
-/

namespace Strata.Dyn.ExecTest.FusedDiffTest

open Strata.Dyn.ExecTest.Programs
open Strata.Dyn.Exec


/-! ## Fingerprints -/

section

/-- `d` as an `α`, shown by `f`, if it is one. -/
def dynAt? (d : Dyn (ExSem.model.interp Run)) (α : Type) [@TagOf Run _ (ExSem.model.decode Run) α]
    (f : α → String) : Option String :=
  (ExSem.model.read? (.ok d) α).map f

/-- A value, by the Lean types the programs use. -/
def dynStr (d : Dyn (ExSem.model.interp Run)) : String :=
  (dynAt? d Int toString) <|> (dynAt? d Bool toString) <|>
    (dynAt? d (Except Int Int) fun x => match x with
      | .ok v => s!"ok {v}" | .error e => s!"error {e}") <|>
    (dynAt? d (Ref Run Int) fun l => s!"@{l.loc}") <|>
    (dynAt? d (FnRef Run [Int] Int) fun f => s!"&{f.idx}@{f.captured}") <|>
    (dynAt? d (Array Int) toString) |>.getD "()"

def frameFP (f : Frame ExSem.model.at) : String :=
  let env := f.env.toList.zipIdx.map fun (d, v) => s!"{v}={dynStr d}"
  s!"{nameStr f.func.name}:{f.block}:{f.pc}:{f.code.length}{env}"

def coreFP (c : Core ExSem.model.at) (drawn : Nat) : String :=
  let waits := c.conts.map fun
    | .rule f p => s!"{frameFP f}/{nameStr p.inst.op}"
    | .call f dst _ => s!"{frameFP f}/%{dst}"
  s!"{frameFP c.top} | {waits} | heap {c.heap.cells.toList.map dynStr} \
    {c.heap.caps.toList.map (·.map dynStr)} | \
    {c.world.out.items} {c.world.ticks.n} | drawn {drawn}"

def modeName : Mode ExSem.model.at → String
  | .exec => "exec" | .jump .. => "jump" | .call .. => "call" | .ret .. => "ret"
  | .request .. => "request" | .again .. => "again" | .done .. => "done"

/-- The values of `xs`. -/
def argsDyn {I : Ty → Type} : {ts : List Ty} → Args I ts → List (Dyn I)
  | [], .nil => []
  | _ :: _, .cons x xs => ⟨_, x⟩ :: argsDyn xs

/-- The successor an exit takes, by position, and its payload. -/
def exitFP {I : Ty → Type} : {ps : List (List Ty)} → Exit I ps → Nat × List (Dyn I)
  | _, .here xs => (0, argsDyn xs)
  | _, .there e => let (k, xs) := exitFP e; (k + 1, xs)

/-- The head of a rule's tree: its result, its stop, or its request with what the request
holds. -/
def treeFP (i : Inst ExSem.model.at) : i.Tree → String
  | .ret v => s!"ret {dynStr (resDyn i.ret v)}"
  | .stop (.jump (.exit e)) => let (k, xs) := exitFP e; s!"exit {k} {xs.map dynStr}"
  | .stop (.jump (.again _)) => "again"
  | .stop (.fault f) => s!"fault {repr f}"
  | .choose _ => "choose"
  | .update _ => "update"
  | .vis (.region j xs) _ => s!"region {j} {(argsDyn xs).map dynStr}"
  | .vis (.call _ idx captured _) _ => s!"call {idx}@{captured}"
  | .vis (.new t v) _ => s!"new {dynStr ⟨t, v⟩}"
  | .vis (.get _ l) _ => s!"get @{l}"
  | .vis (.set t l v) _ => s!"set @{l} {dynStr ⟨t, v⟩}"
  | .vis (.modify _ l _) _ => s!"modify @{l}"
  | .vis (.bind t v _ idx captured) _ => s!"bind {idx}@{captured} {dynStr ⟨t, v⟩}"

/-- Decide `Typed env vs ts`. -/
def decTyped (env : Array (Dyn (ExSem.model.interp Run))) :
    (vs : List Nat) → (ts : List Ty) → Decidable (Typed (M := ExSem.model.at) env vs ts)
  | [], [] => isTrue trivial
  | v :: vs, t :: ts =>
    if h : v < env.size then
      if ht : (env[v]'h).1 = t then
        match decTyped env vs ts with
        | isTrue h₁ => isTrue ⟨⟨h, fun _ => ht⟩, h₁⟩
        | isFalse h₁ => isFalse fun h₂ => h₁ h₂.2
      else isFalse fun h₂ => ht (h₂.1.2 h)
    else isFalse fun h₂ => h h₂.1.1
  | [], _ :: _ => isFalse id
  | _ :: _, [] => isFalse id

/-- What a mode holds that the core does not.  A rule's state is a value of the rule's own Lean
type, with no tag and no `Repr`, so a rule about to run again is shown by the head of the tree
it runs again with that state: what it returns, where it jumps or what it asks for first. -/
def modeFP (c : Core ExSem.model.at) : Mode ExSem.model.at → String
  | .again r =>
    match decTyped c.top.env r.inst.rerun.args r.inst.rerun.ts with
    | isTrue h => s!" | again {treeFP r.inst (r.inst.again c.top.env h r.st)}"
    | isFalse _ => " | again on operands of other tags"
  | _ => ""

def stateFP (s : State ExSem.model.at) : String × String :=
  (modeName s.mode, coreFP s.core s.drawn ++ modeFP s.core s.mode)

def resultStr : Result (ExSem.model.interp Run) → String
  | .ok d => s!"ok {dynStr d}"
  | .fault f => s!"fault {repr f}"

end

/-! ## One case -/

section
variable {m : LModule ExSem.model.at} (hw : WF m) (oracle : Nat → Nat) {B : Ty}

/-- A heap, fingerprinted. -/
def heapFP (hp : Heap ExSem.model.at) : String :=
  s!"heap {hp.cells.toList.map dynStr} {hp.caps.toList.map (·.map dynStr)}"

/-- A run's end, fingerprinted. -/
def endFP : RunEnd m B → String
  | .done r ⟨hp, w⟩ d l => s!"done {resultStr r} {w.out.items} \
      {w.ticks.n} drawn {d} left {l} {heapFP hp}"
  | .timeout s _ => s!"timeout {stateFP s}"

/-- The configuration before each step of the step loop, and its end. -/
def trace : Nat → (s : State ExSem.model.at) → StateOK m B s → Array (String × String) →
    Array (String × String) × Option String
  | 0, _, _, acc => (acc, none)
  | n + 1, s, h, acc => match step hw oracle s h with
    | .next _ s₁ h₁ => trace n s₁ h₁ (acc.push (stateFP s))
    | .final r hp w d => (acc.push (stateFP s), some s!"done {resultStr r} \
        {w.out.items} {w.ticks.n} drawn {d} {heapFP hp}")

/-- A hook that stops the run after its `k`-th step. -/
def stopAfter (k : Nat) : Hook m B Nat := fun c _ _ =>
  if c + 1 = k then .stop (c + 1) else .continue (c + 1)

/-- A hook that only counts. -/
def countAll : Hook m B Nat := fun c _ _ => .continue (c + 1)

/-- The fuels to check of a run of `n` steps: all of them, or a sample with the ends. -/
def fuelsFor (n : Nat) : List Nat :=
  if n ≤ 120 then List.range (n + 3)
  else ((List.range 20) ++ (List.range 21).map (· * (n / 20)) ++
    (List.range 6).map (n + 2 - ·)).eraseDups

/-- The claims about `runFused`, at `fuels`, from `s`, whose step loop visits `tr` and ends
after `N` steps: the problems found, and how many fuels were checked. -/
def claims (s : State ExSem.model.at) (h : StateOK m B s) (tr : Array (String × String)) (N : Nat)
    (fuels : List Nat) : Array String := Id.run do
  let mut bad := #[]
  for k in fuels do
    let fu := runFused hw oracle k s h
    let fr := runFrames hw oracle k s h
    match fu with
    | .done _ _ _ l =>
      if endFP (runFrames hw oracle (N + l) s h) != endFP fu || N + l < k then
        bad := bad.push s!"claim 1 at {k}"
    | .timeout s₁ _ =>
      let hit := (List.range (tr.size - min k tr.size)).find? fun i => tr[i + k]? == some (stateFP s₁)
      match hit with
      | none => bad := bad.push s!"claim 1 at {k}: the fused timeout is no later configuration"
      | some i =>
        if endFP (runFrames hw oracle (i + k) s h) != endFP fu then
          bad := bad.push s!"claim 1 at {k}: runFrames {i + k}"
    match fr, fu with
    | .done r sn d l, .done r₁ sn₁ d₁ l₁ =>
      if endFP (m := m) (B := B) (.done r sn d 0) != endFP (m := m) (B := B) (.done r₁ sn₁ d₁ 0) ||
          l₁ < l then
        bad := bad.push s!"claim 2 at {k}"
    | .done .., .timeout .. => bad := bad.push s!"claim 2 at {k}: the fused run timed out"
    | .timeout .., .done .. => pure ()
    | .timeout .., .timeout .. => pure ()
  return bad

/-- Compare the engines from `s`, an `exec` configuration: the problems found, the step
counts, the outcome, and how many claims were checked.  A fused step ends where the step loop
is about to run an instruction or to run a rule again. -/
def compare (s : State ExSem.model.at) (h : StateOK m B s) (fuel : Nat) :
    Array String × Nat × Nat × String × Nat := Id.run do
  let mut bad := #[]
  let (tr, fend) := trace hw oracle fuel s h #[]
  let N := tr.size
  let pos := (List.range N).filter fun i =>
    (tr[i]?.map (·.1)) == some "exec" || (tr[i]?.map (·.1)) == some "again"
  -- The fused run's configurations, fused step by fused step.
  let mut n := 0
  for j in [0:pos.length + 1] do
    match runFused hw oracle j s h with
    | .timeout s₁ _ =>
      n := j + 1
      if (pos[j]?.bind (tr[·]?)) != some (stateFP s₁) then
        bad := bad.push s!"fused step {j}: not the step loop's configuration"
    | .done .. => pure ()
  match fend, runFused hw oracle (N + 5) s h with
  | some e, .done r ⟨hp, w⟩ d _ =>
    if e != s!"done {resultStr r} {w.out.items} \
        {w.ticks.n} drawn {d} {heapFP hp}" then
      bad := bad.push "the engines end differently"
  | _, _ => bad := bad.push "a run did not end"
  -- The claims, from the start and from configurations in every mode.
  let firsts := ["jump", "call", "ret", "request", "again", "done"].filterMap fun k =>
    (List.range N).find? fun i => (tr[i]?.map (·.1)) == some k
  let starts := (if N ≤ 30 then List.range N else (List.range 10) ++
    (List.range 10).map (· * (N / 10)) ++ firsts ++ [N - 1]).eraseDups.filter (· < N)
  let mut checked := 0
  for j in starts do
    match runFrames hw oracle j s h with
    | .timeout sj hj =>
      let fuels := fuelsFor (N - j)
      checked := checked + fuels.length
      bad := bad ++ (claims hw oracle sj hj (tr.extract j N) (N - j) fuels).map
        (s!"from step {j}: " ++ ·)
    | .done .. => pure ()
  -- Stop after `k` steps, then resume fused.
  for k in (fuelsFor N).filter (fun k => k != 0 && k < N) do
    checked := checked + 1
    match runHooked hw oracle (stopAfter k) (N + 5) 0 s h with
    | (.stopped s₁ h₁ _, _) =>
      match runFused hw oracle (N + 5) s₁ h₁, fend with
      | .done r ⟨hp, w⟩ d _, some e =>
        if e != s!"done {resultStr r} {w.out.items} \
            {w.ticks.n} drawn {d} {heapFP hp}" then
          bad := bad.push s!"stop after {k}: resumed differently"
      | _, _ => bad := bad.push s!"stop after {k}: no end"
    | _ => bad := bad.push s!"stop after {k}: did not stop"
  -- An observer.
  match runHooked hw oracle countAll (N + 5) 0 s h with
  | (e, c) =>
    if (e.toRunEnd.map endFP) != some (endFP (runFrames hw oracle (N + 5) s h)) || c + 1 != N then
      bad := bad.push "observer"
  return (bad, n, N, fend.getD "timeout", checked)

end

/-- A case: functions, an entry, arguments and an oracle. -/
structure Case where
  fs : List (Func E Unit)
  entry : String
  args : Array Int
  oracle : Nat → Nat := fun _ => 0

/-- Link, validate, start and compare: the problems and the number of claims checked. -/
def checkCase (c : Case) : Array String × Nat :=
  match mod c.fs >>= link ExSem.model with
  | .error _ => (#["link"], 0)
  | .ok lm => match hw : checkModule lm with
    | .error _ => (#["invalid"], 0)
    | .ok () => match lm.funcIndex (nm c.entry) with
      | none => (#["no function"], 0)
      | some i =>
        let args := c.args.map fun n => (⟨ExSem.T.base.Int, n⟩ : Dyn (ExSem.model.interp Run))
        match start hw i args.toList with
        | .error _ => (#["start"], 0)
        | .ok ⟨_, s, h⟩ =>
          let (bad, _, _, _, k) := compare hw c.oracle s h 100000
          (bad.map (s!"{c.entry} {c.args}: " ++ ·), k)

/-- Pseudo-random oracles. -/
def lcg (seed i : Nat) : Nat := ((i + 1) * 1103515245 + seed * 12345 + 977) / 65536 % 32768

def oracles : List (Nat → Nat) :=
  [fun _ => 0, fun _ => 1, fun _ => 7, fun i => i, lcg 1, lcg 2]

def cases : List Case :=
  [⟨[arith], "arith", #[3, 4], fun _ => 0⟩, ⟨[sum], "sum", #[10], fun _ => 0⟩,
   ⟨[safeDiv], "safeDiv", #[7, 2], fun _ => 0⟩, ⟨[safeDiv], "safeDiv", #[7, 0], fun _ => 0⟩,
   ⟨[inc, fail, chain], "chain", #[5], fun _ => 0⟩, ⟨[fib], "fib", #[6], fun _ => 0⟩,
   ⟨[count], "count", #[4], fun _ => 0⟩,
   ⟨[addRef, closure], "closure", #[5], fun _ => 0⟩, ⟨[addRef, callsClo], "callsClo", #[3], fun _ => 0⟩,
   ⟨[genericCells], "genericCells", #[3], fun _ => 0⟩, ⟨[boxes], "boxes", #[4], fun _ => 0⟩,
   ⟨[swapped], "swapped", #[4], fun _ => 0⟩, ⟨[boxed], "boxed", #[4], fun _ => 0⟩,
   ⟨[gapAfter], "gapAfter", #[2], fun _ => 0⟩, ⟨[halts], "halts", #[], fun _ => 0⟩,
   ⟨[fibC], "fibC", #[6], fun _ => 0⟩, ⟨[incI, twice, useTwice], "useTwice", #[5], fun _ => 0⟩,
   ⟨[incI, viaCell], "viaCell", #[5], fun _ => 0⟩,
   ⟨[mkRef, useRef], "useRef", #[5], fun _ => 0⟩, ⟨[mkRef, useRef], "useRef", #[0], fun _ => 0⟩,
   ⟨[slotRead], "slotRead", #[6], fun _ => 0⟩, ⟨[bump], "bump", #[41], fun _ => 0⟩,
   ⟨[regionCell], "regionCell", #[4], fun _ => 0⟩, ⟨[incI, cloCall], "cloCall", #[9], fun _ => 0⟩,
   ⟨[squares], "squares", #[4, -1], fun _ => 0⟩, ⟨[squares], "squares", #[0, -1], fun _ => 0⟩,
   ⟨[squares], "squares", #[5, 2], fun _ => 0⟩, ⟨[squaresR], "squaresR", #[4, -1], fun _ => 0⟩,
   ⟨[squaresR], "squaresR", #[0, -1], fun _ => 0⟩, ⟨[squaresR], "squaresR", #[5, 2], fun _ => 0⟩,
   ⟨[tables], "tables", #[3], fun _ => 0⟩, ⟨[powAbove], "powAbove", #[100], fun _ => 0⟩,
   ⟨[powAbove], "powAbove", #[1], fun _ => 0⟩] ++
  oracles.flatMap fun o => [⟨[noisy], "noisy", #[5], o⟩, ⟨[coins], "coins", #[], o⟩]

/-- info: 45 cases, 15495 claims checked, no disagreement -/
#guard_msgs in
#eval
  let rs := cases.map checkCase
  let bad := rs.flatMap fun (b, _) => b.toList
  let n := rs.foldl (· + ·.2) 0
  IO.println (if bad.isEmpty then s!"{cases.length} cases, {n} claims checked, no disagreement"
    else "\n".intercalate (bad.take 10))

end Strata.Dyn.ExecTest.FusedDiffTest
