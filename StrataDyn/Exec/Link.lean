/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Sem
public import StrataDyn.WF
public import Std.Data.HashSet
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Models, linked modules and linking

Linking turns a `Module` into an `LModule` over a `Model` at the machine's token, in which every
name is resolved.  It first computes the module's signatures, each function's parameters' tags
and its result's.  Then it links every function at `M.at`:

* each operation to its wrapper, applied to its type arguments' tags, with its variadic
  operands collected, so that a step looks nothing up and compares no strings, and, for a rule
  that loops, to its wrapper on a state too, which a jump to its `Again` re-enters;
* `base.refNew`, `refGet` and `refSet` to the machine's heap instructions, at their contents'
  tag, and `base.callCode` to the machine's call, at its signature;
* each type to its tag, each label to its block's index in its body or to the body's exit, and
  each function constant to a code pointer, a closure with no captures, which must be at its
  function's signature;
* each region to a body of the module's `regions`.

Linking also records each function's **slots**: one more than the largest value id it or any of
its regions defines.  The machine stores a frame's values in an array of that many slots, by
id, so a dense numbering, as the builder and the reader make, wastes none.  A region's values
share its function's slots, and so does every region body.

Operation and type names are looked up in the model's `NameMap`s, 2-3 trees on `Name.key`
that the table generator builds, so a link computes the keys of the names its module uses and
compares `Nat`s.  An operation the model lacks is a missing rule; linking reports all of them
at once.

Linking also records each block's **scope**: the values defined outside the block that are
bound, with their tags, whenever it is entered.  A block's scope is what is in scope at its
entry under the body's dominator tree, computed as `Func.WF` computes it (`Body.domTree?`, or
`Body.computeTree` if that fails), and live there (`liveIns`): some path from the block's entry
reads it, with a region's reads counted at its instruction.  What is in scope at a block's
entry under the tree is what is in scope at its parent point: its parent block's scope,
parameters and the results of the instructions before the point.  A function's entry block
sees nothing, and a region's entry block what its instruction sees and the region reads.  So
the blocks may come in any order.  Validation (`Check.lean`) checks every scope on every edge
into its block.

TODO: prove `link_wf`, that linking a module without extern functions that `Module.WF` accepts
gives one that `WF` accepts.  Nothing proves it yet; a run validates the linked module and
rejects it otherwise.  A module with an extern function does not run yet: an extern has no
blocks, so linking rejects it.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-! ## Curried functions -/

section
variable {I : Ty → Type}

/-- `g` after the curried function `f`. -/
def Fn.map {R S : Type} (g : R → S) : {ts : List Ty} → Fn I R ts → Fn I S ts
  | [], f => g f
  | _ :: _, f => fun x => Fn.map g (f x)

/-- A function of `ts` and then `us`, uncurried at the join. -/
def Fn.append {X : Type} {us : List Ty} : {ts : List Ty} → Fn I (Fn I X us) ts → Fn I X (ts ++ us)
  | [], f => f
  | _ :: _, f => fun x => Fn.append (f x)

/-- `k` of the `n` operands that follow, collected after `acc` into an array. -/
def Fn.collect {X : Type} (v : Ty) (acc : Array (I v)) :
    (n : Nat) → (Array (I v) → X) → Fn I X (List.replicate n v)
  | 0, k => k acc
  | n + 1, k => fun x => Fn.collect v (acc.push x) n k

/-- The curried function of one operand per tag in `ts` that ignores them and returns `x`. -/
def Fn.const {R : Type} (x : R) : (ts : List Ty) → Fn I R ts
  | [] => x
  | _ :: ts => fun _ => Fn.const x ts

/-- A wrapper on `argc` operands, curried in all of them: its declared operands, then the
variadic's, or `none` if the count does not fit. -/
def uncurry {X : Type} (args : List Ty) :
    (variadic : Option Ty) → Fn I (VarFn I variadic X) args → Nat → Option ((ts : List Ty) × Fn I X ts)
  | none, f, argc => if argc = args.length then some ⟨args, f⟩ else none
  | some v, f, argc =>
    if args.length ≤ argc then
      some ⟨args ++ List.replicate (argc - args.length) v,
        Fn.append (Fn.map (Fn.collect v #[] (argc - args.length)) f)⟩
    else none

end

/-! ## Linked modules -/

section
variable (M : RunModel)

/-- Where a transfer goes: a block of its body, by index, or the body's exit. -/
inductive LTarget where
  | block (i : Nat)
  | exit
  deriving Repr, DecidableEq

/-- A transfer, with the leading arguments it binds. -/
structure LSite where
  target : LTarget
  args : List Nat

/-- What a rule's instruction runs on, fixed by linking: its operands `args`, of tags `ts`, its
rule's state type `M.St key`, by the operation's position in the table and its type arguments'
tags, and `tree`, its rule's tree on the operands with a state, which a jump to its `Again`
runs.  One object, so that running the rule copies one field. -/
structure Rerun (rs : List (List Ty × Ty)) (ps : List (List Ty)) (R : Type) where
  key : Nat × Array Ty
  ts : List Ty
  args : List Nat
  tree : Fn M.interp (M.St key → Tree M.interp Run M.W rs ps (M.St key) R) ts

/-- A linked instruction.  Values are by their ids. -/
inductive LInsn where
  | const (dst : Nat) (v : Dyn M.interp)
  /-- A pure rule or a constructor, on operands of tags `ts`. -/
  | pure (dst : Nat) (ts : List Ty) (r : Ty) (f : Fn M.interp (M.interp r) ts) (args : List Nat)
  /-- A rule's tree, on the operands of `re`, with the module's regions `regs`. -/
  | sem (op : Name) (dst : Nat) (rs : List (List Ty × Ty)) (r : Ty) (ps : List (List Ty))
    (re : Rerun M rs ps (M.interp r))
    (f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) (M.interp r)) re.ts)
    (regs : List Nat) (succs : List LSite)
  /-- The machine's heap instructions, on cells holding values of tag `t`. -/
  | refNew (dst : Nat) (t : Ty) (v : Nat)
  | refGet (dst : Nat) (t : Ty) (cell : Nat)
  | refSet (dst : Nat) (t : Ty) (cell v : Nat)
  /-- The machine's call of the typed code pointer `f` on `args`, of tags `ts`, returning
  code `r`. -/
  | callCode (dst : Nat) (ts : List Ty) (r : Ty) (f : Nat) (args : List Nat)

/-- A linked terminator. -/
inductive LTerm where
  /-- A case instruction, or another pure terminal wrapper. -/
  | case (ts : List Ty) (ps : List (List Ty)) (f : Fn M.interp (Exit M.interp ps) ts)
    (args : List Nat) (succs : List LSite)
  /-- A terminal rule's tree, on the operands of `re`. -/
  | sem (op : Name) (rs : List (List Ty × Ty)) (ps : List (List Ty)) (re : Rerun M rs ps Empty)
    (f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) Empty) re.ts)
    (regs : List Nat) (succs : List LSite)

/-- A block.  `scope` lists the values of other blocks it reads, with their tags. -/
structure LBlock where
  label : Label
  params : List (Nat × Ty)
  scope : List (Nat × Ty)
  insns : List (LInsn M)
  term : LTerm M

/-- A body: a function's blocks, or a region's.  A transfer to its exit leaves it with a value
of tag `ret`, and its values are ids below `slots`. -/
structure LBody where
  name : Name
  ret : Ty
  blocks : Array (LBlock M)
  slots : Nat := 0
  region : Bool := false
  /-- A function's entry parameters' tags, which a call must pass.  Linking computes them,
  and validation checks them against the entry block and the module's signatures. -/
  params : List Ty := []

/-- A module: its functions, and every function's regions, at every depth. -/
structure LModule where
  funcs : Array (LBody M)
  regions : Array (LBody M)

end

section
variable {M : RunModel}

/-- The value an instruction defines. -/
def LInsn.dst : LInsn M → Nat
  | .const d _ | .pure d .. | .sem _ d .. | .refNew d .. | .refGet d .. | .refSet d ..
  | .callCode d .. => d

/-- The parameters' tags. -/
def LBlock.paramTys (b : LBlock M) : List Ty := b.params.map (·.2)

/-- Every instruction of the block satisfies `insn`, and its terminator satisfies `term`. -/
def LBlock.All (b : LBlock M) (insn : LInsn M → Prop) (term : LTerm M → Prop) : Prop :=
  (∀ i ∈ b.insns, insn i) ∧ term b.term

/-- Every instruction of the body's blocks satisfies `insn`, and every terminator `term`. -/
def LBody.All (g : LBody M) (insn : LInsn M → Prop) (term : LTerm M → Prop) : Prop :=
  ∀ b ∈ g.blocks, b.All insn term

/-- Every instruction of every function and region of the module satisfies `insn`, and every
terminator `term`. -/
def LModule.All (m : LModule M) (insn : LInsn M → Prop) (term : LTerm M → Prop) : Prop :=
  (∀ g ∈ m.funcs, g.All insn term) ∧ ∀ g ∈ m.regions, g.All insn term

end

/-! ## Linking -/

section
variable (M : Model)

/-- What linking reads besides the model: the module's functions, by name, their signatures,
and the slots of the function being linked. -/
structure LinkCtx where
  funcs : NameMap Nat
  sigs : Array (List Ty × Ty) := #[]
  slots : Nat := 0

/-- What linking accumulates: the module's regions so far, and the operations the model
lacks. -/
structure LinkState where
  regions : Array (LBody M.at) := #[]
  missing : Array Name := #[]

/-- Linking's monad. -/
abbrev LinkM := ReaderT LinkCtx (StateT (LinkState M) (Except Fault))

variable {M}

/-- Fail with `Fault.invalid msg`. -/
def linkError {α : Type} (msg : String) : LinkM M α := throw (.invalid msg)

variable (M) in
/-- The code of a declared type applied to codes. -/
def appCode (h : Dyn.Name) (as : Array (Option Ty)) : Option Ty := do
  some (Ty.app (← M.typeIndex.find? h) (← as.toList.mapM id))

/-- The code of a list of tags. -/
def listOf (es : Array (Option Ty)) : Option Ty := do some (Ty.list (← es.toList.mapM id))

variable (M) in
/-- The tag of a closed type, if the model has one. -/
def codeOf {env : Env Unit} {k : Kind} (t : TypeExpr env #[] k) : Option Ty :=
  t.toRaw.fold (fun _ => none) (appCode M) listOf

/-- The tag of a closed type. -/
def tyCode {env : Env Unit} {k : Kind} (t : TypeExpr env #[] k) : LinkM M Ty :=
  match codeOf M t with
  | some c => pure c
  | none => linkError "a type with no tag in the model"

/-- A target, resolved in a body whose labels are `labels`. -/
def linkSite (labels : LabelMap Nat) (k : Target.Raw) : LinkM M LSite := do
  let args := k.args.toList.map (·.id)
  if k.label = Label.exit then return ⟨.exit, args⟩
  match labels.find? k.label with
  | some i => return ⟨.block i, args⟩
  | none => linkError "a transfer to a block that is not in its body"

/-- Record `op` as missing, unless it is already. -/
def addMissing (op : Name) : LinkM M Unit :=
  modify fun s => if s.missing.contains op then s else { s with missing := s.missing.push op }

/-- The codes of an application's type arguments, for a wrapper of `n` of them. -/
def typeArgCodes {env : Env Unit} {params : Array Kind} (typeArgs : TypeArgs env params)
    (n : Nat) : LinkM M (Vector Ty n) := do
  let cs ← typeArgs.args.toList.mapM fun a => tyCode a.val
  if h : cs.length = n then return ⟨cs.toArray, h⟩
  linkError "an application with the wrong number of type arguments"

/-- The tree on a state of a rule that does not loop, which never runs. -/
def noAgain {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S R : Type} :
    S → Tree M.at.interp Run M.at.W rs ps S R :=
  fun _ => semanticFailure "a rule that does not loop ran again"

/-- `dst = o args`, whose rule's state type is `M.St key`, with its successors and the module's
regions `regs`. -/
def linkApp (op : Name) (dst : Nat) (key : Nat × Array Ty) (args : List Nat) (succs : List LSite)
    (regs : List Nat) : (s : Shape) → Impl Run M.at.interp M.at.W s (M.at.St key) →
      LinkM M (LInsn M.at)
  | ⟨as, var, some r, [], []⟩, .pure f => do
    let some ⟨ts, g⟩ := uncurry as var f args.length | linkError s!"{nameStr op}: wrong operand count"
    unless succs.isEmpty && regs.isEmpty do linkError s!"{nameStr op}: takes no successors or regions"
    return .pure dst ts r g args
  | ⟨as, var, some r, ps, rs⟩, .sem f => do
    let some ⟨ts, g⟩ := uncurry as var f args.length | linkError s!"{nameStr op}: wrong operand count"
    return .sem op dst rs r ps ⟨key, ts, args, Fn.const noAgain ts⟩ g regs succs
  | ⟨as, var, some r, ps, rs⟩, .loop f again => do
    let some ⟨ts, g⟩ := uncurry as var f args.length | linkError s!"{nameStr op}: wrong operand count"
    let some ⟨ts₁, g₁⟩ := uncurry as var again args.length |
      linkError s!"{nameStr op}: wrong operand count"
    if h : ts₁ = ts then
      return .sem op dst rs r ps ⟨key, ts, args, cast (congrArg (Fn M.at.interp _) h) g₁⟩ g regs
        succs
    else linkError s!"{nameStr op}: wrong operand count"
  | _, _ => linkError s!"{nameStr op}: not an instruction that falls through"

/-- The terminator `o args`, whose rule's state type is `M.St key`. -/
def linkTermApp (op : Name) (key : Nat × Array Ty) (args : List Nat) (succs : List LSite)
    (regs : List Nat) : (s : Shape) → Impl Run M.at.interp M.at.W s (M.at.St key) →
      LinkM M (LTerm M.at)
  | ⟨as, var, none, ps, []⟩, .pure f => do
    let some ⟨ts, g⟩ := uncurry as var f args.length | linkError s!"{nameStr op}: wrong operand count"
    unless regs.isEmpty do linkError s!"{nameStr op}: takes no regions"
    return .case ts ps g args succs
  | ⟨as, var, none, ps, rs⟩, .sem f => do
    let some ⟨ts, g⟩ := uncurry as var f args.length | linkError s!"{nameStr op}: wrong operand count"
    return .sem op rs ps ⟨key, ts, args, Fn.const noAgain ts⟩ g regs succs
  | ⟨as, var, none, ps, rs⟩, .loop f again => do
    let some ⟨ts, g⟩ := uncurry as var f args.length | linkError s!"{nameStr op}: wrong operand count"
    let some ⟨ts₁, g₁⟩ := uncurry as var again args.length |
      linkError s!"{nameStr op}: wrong operand count"
    if h : ts₁ = ts then
      return .sem op rs ps ⟨key, ts, args, cast (congrArg (Fn M.at.interp _) h) g₁⟩ g regs succs
    else linkError s!"{nameStr op}: wrong operand count"
  | _, _ => linkError s!"{nameStr op}: not a terminal instruction"

/-- The constant `dst = c`, declared at type `type`.  A function constant is a code pointer, a
closure with no captures, which must be at its function's signature.  A ghost reference may occur
only in a contract, which linking does not reach, so one here is an error. -/
def linkConst {env : Env Unit} (dst : Nat) (type : TypeExpr env) :
    Const → LinkM M (LInsn M.at)
  | .func f => do
    let some i := (← read).funcs.find? f | throw (.noFunction f)
    match ← tyCode type with
    | .app 1 [.list ts, r] =>
      if (← read).sigs[i]? = some (ts, r) then
        return .const dst ⟨Ty.fn ts r, M.at.fnAt ts r i⟩
      else linkError s!"{nameStr f}: a code pointer at another signature than its function's"
    | _ => linkError s!"{nameStr f}: a function constant whose type is not a code pointer"
  | .unit => return .const dst ⟨M.unit, M.unitVal Run⟩
  | .bool b => return .const dst ⟨M.bool, M.ofBool Run b⟩
  | .int i => return .const dst ⟨M.int, M.ofInt Run i⟩
  | .float x => return .const dst ⟨M.float, M.ofFloat Run x⟩
  | .str x => return .const dst ⟨M.str, M.ofStr Run x⟩
  | .ghost g => linkError s!"{nameStr g}: a ghost reference outside a contract"

end

/-- A typing context: values by id, with their tags, the latest first.  Linking builds
one per block from the dominator tree; validation checks against it. -/
abbrev Ctx := List (Nat × Ty)

section
variable {M : RunModel}

/-- What an instruction adds to the context. -/
def LInsn.resTy : LInsn M → Ty
  | .const _ v => v.1
  | .pure _ _ r .. | .sem _ _ _ r .. => r
  | .refNew _ t _ => Ty.ref t
  | .refGet _ t _ => t
  | .refSet .. => M.unit
  | .callCode _ _ r _ _ => r

/-- A terminator that stands for a missing rule; the module never runs. -/
def missingTerm (op : Name) : LTerm M :=
  .sem op [] [] ⟨(0, #[]), [], [], fun _ => semanticGap s!"{nameStr op}: no rule"⟩
    (semanticGap s!"{nameStr op}: no rule") [] []

end

section
variable {M : Model} {env : Env Unit} [base ≼ env] {α : Type}

/-- The ids a target passes. -/
def siteIds (succs : Array Target.Raw) : List Nat := succs.toList.flatMap (·.args.toList.map (·.id))

/-- The ids `blocks` define, at any depth: their parameters and their instructions' results. -/
def definedIds (blocks : List (Block env α)) : Std.HashSet Nat :=
  (Block.withNestedList blocks).foldl (init := {}) fun s b =>
    b.instrs.foldl (fun s i => s.insert i.result.id.id) (b.params.foldl (·.insert ·.id.id) s)

/-- The ids `blocks` read, at any depth, that they do not define: what a region reads from the
code around it. -/
def freeIds (blocks : List (Block env α)) : List Nat :=
  let defs := definedIds blocks
  let reads := (Block.withNestedList blocks).flatMap fun b =>
    let insnIds := b.instrs.toList.flatMap fun
      | .const .. => []
      | .apply _ _ _ _ args succs _ => args.toList.map (·.id) ++ siteIds succs
    let termIds := match b.term with
      | .apply _ _ _ args succs _ => args.toList.map (·.id) ++ siteIds succs
    insnIds ++ termIds
  reads.filter (!defs.contains ·)

/-- What block `b` reads at its own level, its regions' free ids included, and the blocks of its
body, whose labels are `labels`, that it may transfer to. -/
def blockUses (labels : LabelMap Nat) (b : Block env α) : List Nat × List Nat :=
  let regionIds (rs : List (Dyn.Region env α)) : List Nat :=
    rs.flatMap fun r => freeIds r.blocks.toList
  let targets (succs : Array Target.Raw) : List Nat :=
    succs.toList.filterMap fun k => labels.find? k.label
  let (rd, ts) := b.instrs.foldl (init := ([], [])) fun (rd, ts) i => match i with
    | .const .. => (rd, ts)
    | .apply _ _ _ _ args succs ⟨rs⟩ =>
      (args.toList.map (·.id) ++ siteIds succs ++ regionIds rs ++ rd, targets succs ++ ts)
  match b.term with
  | .apply _ _ _ args succs ⟨rs⟩ =>
    (args.toList.map (·.id) ++ siteIds succs ++ regionIds rs ++ rd, targets succs ++ ts)

/-- `s` after rounds of `round` until a round changes nothing, which takes at most `rounds`
rounds.  A fault names the pass `what` if the last round still changes something. -/
def fixpoint {σ : Type} (rounds : Nat) (what : String) (round : σ → Except Fault (σ × Bool))
    (s : σ) : Except Fault σ := do
  let mut s := s
  for _ in [0:rounds] do
    let (s₁, changed) ← round s
    s := s₁
    if !changed then return s
  throw (.invalid s!"{what}: no fixpoint after {rounds} rounds")

/-- The values live at the entry of each of a body's blocks, whose labels are `labels`: those
that some path from the entry reads before the path defines them.  A region's free ids count as
read at its instruction.  A backward dataflow: each round adds to each block what its
successors read and it does not define, and it stops after a round that adds nothing.  A fact
travels one block per round at least, so `n + 1` rounds suffice; a fault reports a last round
that still adds something, and a successor whose index is beyond the blocks. -/
def liveIns {n : Nat} (labels : LabelMap Nat) (blocks : Vector (Block env α) n) :
    Except Fault (Vector (Std.HashSet Nat) n) := do
  let info ← blocks.mapM fun b => do
    let defs : Std.HashSet Nat := b.instrs.foldl (fun s i => s.insert i.result.id.id)
      (b.params.foldl (·.insert ·.id.id) {})
    let (reads, succs) := blockUses labels b
    let succs ← succs.mapM fun k =>
      if h : k < n then pure (⟨k, h⟩ : Fin n)
      else throw (.invalid s!"liveness: a successor {k} beyond the {n} blocks")
    return (defs, reads, succs)
  let live : Vector (Std.HashSet Nat) n := info.map fun (defs, reads, _) =>
    reads.foldl (fun s v => if defs.contains v then s else s.insert v) {}
  fixpoint (n + 1) s!"liveness over {n} blocks" (s := live) fun live => do
    let mut live := live
    let mut changed := false
    for j in (List.finRange n).reverse do
      let (defs, _, succs) := info[j]
      let cur := live[j]
      let next := succs.foldl (init := cur) fun s k =>
        live[k].fold (init := s) fun s v => if defs.contains v then s else s.insert v
      if next.size != cur.size then
        live := live.set j next
        changed := true
    return (live, changed)

/-- One more than the largest id that `blocks` define, at any depth. -/
def slotsOf (blocks : List (Block env α)) : Nat :=
  let fit (n : Nat) (d : ValDecl env) := max n (d.id.id + 1)
  (Block.withNestedList blocks).foldl (init := 0) fun n b =>
    b.instrs.toList.foldl (fun n i => fit n i.result) (b.params.toList.foldl fit n)

/-- Each block's index, by label. -/
def labelsOf (blocks : List (Block env α)) : LabelMap Nat :=
  (blocks.foldl (fun (m, i) b => (m.insert b.label i, i + 1)) ((∅ : LabelMap Nat), 0)).1

/-- The parameters, by id, with their tags. -/
def linkParams (ps : List (ValDecl env)) : LinkM M Ctx :=
  ps.mapM fun d => return (d.id.id, ← tyCode d.type)

/-- `Γ` with each of `ps` added, in order. -/
def ctxOf (Γ : Ctx) : Ctx → Ctx
  | [] => Γ
  | p :: ps => ctxOf (p :: Γ) ps

/-- What a block defines, in order, at their declared codes: its parameters, then its
instructions' results. -/
def blockDefs (b : Block env α) : LinkM M Ctx := do
  let ps ← linkParams b.params.toList
  let rs ← b.instrs.toList.mapM fun i => return (i.result.id.id, ← tyCode i.result.type)
  return ps ++ rs

/-- What is in scope at each block's entry under a body's dominator tree, with
`parents[j]` block `j`'s parent and `defs[j]` its parameter count and definitions: `outer` at
the entry, and at another block what is in scope at its parent point `⟨l, k⟩`, the scope of
`l`, its parameters and its first `k` results.  `none` for a block whose chain of parents does
not reach the entry.  A parent may come after its block, so each round fills in the blocks
whose parents are known, until a round fills in none.  Each round but the last fills in a
block, so `n + 1` rounds suffice; a fault reports a last round that still fills one in, and a
parent that is not one of the blocks. -/
def treeScopes {n : Nat} (labels : LabelMap Nat) (parents : Vector (Option Point) n)
    (defs : Vector (Nat × Ctx) n) (outer : Ctx) : Except Fault (Vector (Option Ctx) n) := do
  let known : Vector (Option Ctx) n := Vector.ofFn fun j => if j.1 = 0 then some outer else none
  fixpoint (n + 1) s!"scopes over {n} blocks" (s := known) fun known => do
    let mut known := known
    let mut changed := false
    for j in List.finRange n do
      if j.1 = 0 || known[j].isSome then continue
      let some ⟨l, k⟩ := parents[j] | continue
      let some i := labels.find? l
        | throw (.invalid s!"scopes: a parent {nameStr l.name} that is not one of the blocks")
      if h : i < n then
        -- The parent's scope may not be known yet in this round.
        let some c := known[i] | continue
        let (np, ds) := defs[i]
        known := known.set j (some (ctxOf c (ds.take (np + k))))
        changed := true
      else throw (.invalid s!"scopes: a parent {i} beyond the {n} blocks")
    return (known, changed)

/-- The scope of each of a body's blocks, whose labels are `labels`: what is in scope at its
entry under the body's computed dominator tree, its entry seeing `outer`, and live there
(`liveIns`).  A block whose parents do not reach the entry sees nothing. -/
def bodyScopes (labels : LabelMap Nat) (blocks : List (Block env α)) (outer : Ctx) :
    LinkM M (Vector Ctx blocks.length) := do
  let bs : Vector (Block env α) blocks.length := ⟨blocks.toArray, by simp⟩
  let defs ← bs.mapM fun b => return (b.params.size, ← blockDefs b)
  let t := (Body.domTree? blocks).getD (Body.computeTree blocks).find?
  let scopes ← (treeScopes labels (bs.map (t ·.label)) defs outer : Except Fault _)
  let live ← (liveIns labels bs : Except Fault _)
  return Vector.zipWith (fun sc lv => (sc.getD []).filter fun p => lv.contains p.1) scopes live

/-- The parameters' tags of the entry block of the function `name`, whose linked blocks are
`lbs`.  `Func.WF.externIff` gives a defined function blocks. -/
def entryParams (name : Name) : List (LBlock M.at) → LinkM M (List Ty)
  | b :: _ => pure b.paramTys
  | [] => linkError s!"{nameStr name}: no entry block"

mutual

/-- Link one region, whose entry block sees `scope`, into the module's regions; its index. -/
def linkRegion (fname : Name) (scope : Ctx) (retTy : Ty) :
    Dyn.Region env α → LinkM M Nat
  | ⟨⟨blocks⟩⟩ => do
    let labels := labelsOf blocks
    let scopes ← bodyScopes labels blocks scope
    let lbs ← linkBlocks labels blocks scopes.toList (by simp)
    let st ← get
    let k := st.regions.size
    let body : LBody M.at :=
      { name := .num fname k, ret := retTy, blocks := ⟨lbs⟩, slots := (← read).slots,
        region := true }
    set { st with regions := st.regions.push body }
    return k

/-- Link an instruction's regions, at the signatures `sigs`, each of whose entry blocks sees
`Γ`. -/
def linkRegions (fname : Name) (Γ : Ctx) :
    List (Dyn.Region env α) → List (List Ty × Ty) → LinkM M (List Nat)
  | [], [] => pure []
  | r :: rs, sig :: sigs => do
    let k ← linkRegion fname Γ sig.2 r
    return k :: (← linkRegions fname Γ rs sigs)
  | _, _ => linkError s!"{nameStr fname}: the wrong number of regions"

/-- Link a body's blocks, each with its scope in `scopes`, one per block, as `bodyScopes` gives
them. -/
def linkBlocks (labels : LabelMap Nat) :
    (bs : List (Block env α)) → (scopes : List Ctx) → bs.length = scopes.length →
      LinkM M (List (LBlock M.at))
  | [], _, _ => pure []
  | ⟨label, params, ⟨instrs⟩, term, _⟩ :: bs, sc :: scopes, h => do
    let params ← linkParams params.toList
    let (insns, Γ) ← linkInsns labels (ctxOf sc params) instrs
    let term ← linkTerm labels Γ term
    let lb : LBlock M.at := { label, params, scope := sc, insns, term }
    return lb :: (← linkBlocks labels bs scopes (by simpa using h))
  | _ :: _, [], h => absurd h (by simp)

/-- Link instructions in context `Γ`, and the context after them. -/
def linkInsns (labels : LabelMap Nat) (Γ : Ctx) :
    List (Instruction env α) → LinkM M (List (LInsn M.at) × Ctx)
  | [] => pure ([], Γ)
  | ins :: is => do
    let li ← linkInsn labels Γ ins
    let (lis, Γ) ← linkInsns labels ((li.dst, li.resTy) :: Γ) is
    return (li :: lis, Γ)

/-- Link an instruction in context `Γ`, which its regions see. -/
def linkInsn (labels : LabelMap Nat) (Γ : Ctx) :
    Instruction env α → LinkM M (LInsn M.at)
  | .const _ d c => linkConst d.id.id d.type c
  | .apply _ d r typeArgs args succs ⟨regions⟩ => do
    let args := args.toList.map (·.id)
    let succs ← succs.toList.mapM (linkSite labels)
    match M.index.find? r.name with
    | none => do
      addMissing r.name
      return .const d.id.id ⟨M.unit, M.unitVal Run⟩
    | some (.impl k) => do
      match hk : M.ops[k]? with
      | none => linkError s!"{nameStr r.name}: no operation {k} in the table"
      | some (_, o) =>
        let targs ← typeArgCodes typeArgs o.typeArgc
        let s := o.shape targs
        let regs ← linkRegions r.name Γ regions s.regions
        linkApp r.name d.id.id (k, targs.toArray) args succs regs s
          (cast (congrArg (Impl Run M.at.interp M.at.W s) (M.stateOf_eq Run hk targs).symm)
            (o.fn Run targs))
    | some k => do
      unless succs.isEmpty && regions.isEmpty do
        linkError s!"{nameStr r.name}: takes no successors or regions"
      match k, args with
      | .refNew, [v] => return .refNew d.id.id (← typeArgCodes typeArgs 1)[0] v
      | .refGet, [c] => return .refGet d.id.id (← typeArgCodes typeArgs 1)[0] c
      | .refSet, [c, v] => return .refSet d.id.id (← typeArgCodes typeArgs 1)[0] c v
      -- `callCode [(as : list) r]`: the list of argument codes, then the result's.
      | .callCode, f :: as => do
        let targs ← typeArgCodes typeArgs 2
        match targs[0] with
        | .list ts => return .callCode d.id.id ts targs[1] f as
        | .app .. => linkError s!"{nameStr r.name}: a type where a list of types belongs"
      | _, _ => linkError s!"{nameStr r.name}: the wrong number of operands"

/-- Link a terminator in context `Γ`, which its regions see. -/
def linkTerm (labels : LabelMap Nat) (Γ : Ctx) :
    Terminator env α → LinkM M (LTerm M.at)
  | .apply _ r typeArgs args succs ⟨regions⟩ => do
    let args := args.toList.map (·.id)
    let succs ← succs.toList.mapM (linkSite labels)
    match M.index.find? r.name with
    | some (.impl k) => do
      match hk : M.ops[k]? with
      | none => linkError s!"{nameStr r.name}: no operation {k} in the table"
      | some (_, o) =>
        let targs ← typeArgCodes typeArgs o.typeArgc
        let s := o.shape targs
        let regs ← linkRegions r.name Γ regions s.regions
        linkTermApp r.name (k, targs.toArray) args succs regs s
          (cast (congrArg (Impl Run M.at.interp M.at.W s) (M.stateOf_eq Run hk targs).symm)
            (o.fn Run targs))
    | some _ => linkError s!"{nameStr r.name}: not a terminal instruction"
    | none => do
      addMissing r.name
      return missingTerm r.name

end

/-- Link a function. -/
def linkFunc (f : Func env α) : LinkM M (LBody M.at) :=
  if f.extern then linkError s!"{nameStr f.name}: an extern function does not run yet"
  else do
    let blocks := f.blocks.toList
    let slots := slotsOf blocks
    let labels := labelsOf blocks
    let lbs ← withReader ({ · with slots }) do
      let scopes ← bodyScopes labels blocks []
      linkBlocks labels blocks scopes.toList (by simp)
    let params ← entryParams f.name lbs
    return { name := f.name, ret := ← tyCode f.retType, blocks := ⟨lbs⟩, slots, params }

end

/-- The signature of `f`: its parameters' tags, and its result's tag.  A defined function's
entry block takes exactly its parameters (`Func.WF.entryParams`). -/
def sigOf (M : Model) {env : Env Unit} {α : Type} (f : Func env α) : Except Fault (List Ty × Ty) := do
  let ps := f.params.toList
  let some ts := ps.mapM fun d => codeOf M d.type |
    .error (.invalid s!"{nameStr f.name}: a parameter type with no tag in the model")
  let some r := codeOf M f.retType |
    .error (.invalid s!"{nameStr f.name}: a result type with no tag in the model")
  return (ts, r)

/-- Link `m` against the model `M` at the machine's token, reporting every missing rule at once,
in order of first use. -/
def link (M : Model) {env : Env Unit} [base ≼ env] {α : Type} (m : Module env α) :
    Except Fault (LModule M.at) := do
  let m := m.raw
  let some funcs := NameMap.ofArray? (m.funcs.toList.zipIdx.map fun (f, i) => (f.name, i)).toArray |
    .error (.invalid "a function named twice")
  let sigs ← m.funcs.mapM (sigOf M)
  let (fs, st) ← (m.funcs.toList.mapM (linkFunc (M := M))).run { funcs, sigs } |>.run {}
  unless st.missing.isEmpty do .error (.missingRules st.missing)
  return { funcs := ⟨fs⟩, regions := st.regions }

end

end Strata.Dyn.Exec
