/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
public import StrataDyn.WF
public import StrataDyn.DomCompute
public import StrataDyn.Util.NameMap
public import StrataDyn.KindedTypeArgs
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF
import all StrataDyn.Util.LabelMapProps

set_option autoImplicit false

/-!
# Emitting a function

A builder emits a function's instructions in order.  Blocks are named by `Label`, so a
transfer can name a block before it is built.  A function's blocks carry the labels they were
allocated, in the order they were finished.

When the builder finishes a body, the function's or a region's, it drops the blocks the
body's entry does not reach (`Body.dropUnreached`, `StrataDyn/DomCompute.lean`), as
`Func.WF` asks every block to be reachable.  `Func.WF` also asks that some tree of each body put
every use in scope, and its check computes that tree, whatever order the blocks were finished
in.  So a producer leaves dominance to the check.

A fresh label is `base.n`, `bb.n` by default, with `n` counted per `base` across the whole
function, regions included, so labels are unique, as `Func.WF` demands.  The suffixes are
numbered again when the function is finished, as values are, so a fresh label whose base its
caller did not choose can be renamed (`renameLabel`) without leaving a gap.  A misuse the
builder records names a block by the label the finished function gives it.

A value is named after a stem, `x.n`, with `n` counted per stem when the function is finished,
so that two `x`es are `x.0` and `x.1`.  A value whose stem its emitter chose itself, a typed
emitter's default, can be renamed (`rename`), and the numbering leaves no gaps.

Ids count from `0` in allocation order.  They follow the printed order of definitions
(`Func.Canonical`) if each block's parameters, a region's included, are allocated just before
the block opens.

The operations:

* `withInfo`: set the annotation given to what is emitted;
* `freshVal`, `rename`: a fresh value, and a new stem for one;
* `emitConst`, `emitFunc`, `emitApply`, `emitApplyWith`, `emitApplyNamed`: emit an
  instruction, `emitApplyWith` with regions built in any monad `BuildM` lifts into, and
  `emitApplyNamed` named after the instruction unless given a name;
* `checkTypeArgs`: type arguments given as data, checked against an instruction's kinds;
* `goto`: a transfer to a block;
* `freshLabel`, `renameLabel`, `startBlock`, `startBlockWith`, `startFreshBlock`: allocate,
  rename and open blocks;
* `finishBlock`, `terminate`, `jump`, `branch`, `ret`, `unreachable`: close the open block
  with a terminator: any terminal operation, a datatype's `case` among them, or the base's
  control flow;
* `region`, `regionWith`: emit an operation's nested body, `regionWith` from any monad
  `BuildM` lifts into;
* `run`, `build`: run a builder and check the function it emitted;
* `stub`: a checked function whose body is `unreachable`, to stand in for one whose build
  failed.

An application's type arguments, `typeArgs` of `emitApply`, `emitApplyWith` and `terminate`,
are a `TypeArgsOf` the instruction.  Written `(typeArgs := ta[…])`, as in
`emitApply n Base.Unit Base.refSet.ref #[cell, v] (typeArgs := ta[Py.Value])`, Lean checks their
count and kinds at the call.  Left out, they are inferred from the result type when the code is
compiled, or, if it does not fix them all, when the builder runs, from the operands' types and
the result type: the builder keeps each value's type for this.  Arguments that neither fixes,
or that a list splicing two parameters leaves ambiguous, are an error that says to write them,
when the code is compiled if the signature alone shows it.

Types are written as handles (`StrataDyn.Env.Handle`): `Base.Int`, `Py.Value`,
`Base.Except Base.Int Base.Bool`, `Base.Fn [Base.Int] Base.Bool`, each coerced to the
`TypeExpr` or `TypeArg` the builder takes.

`StrataDyn.Build.Typed` adds a typed emitter per instruction, `o`, whose Lean type is
the instruction's signature: Lean checks its operands, successors and result type at the call,
and infers its type arguments.

The builder records each misuse as an error: an instruction emitted with no block open, a
block opened while another is open or under a label already used, a block finished when none
is open, a region or function body that ends with a block open, and a function that ends
with a region still being emitted, as when a region's body throws.  A build succeeds when it
records no misuse and the function is well formed (`Func.WF`), and then gives the checked
function.  Otherwise it gives a `FailedFunc`, which holds the misuses and the function as
emitted.

The builder is language-neutral.
-/

namespace Strata.Dyn

public section

namespace Build

-- The builder's maps are association lists and 2-3 trees (`NameMap`), which the kernel reduces.
/-- A map from strings, as an association list, latest entry first. -/
structure StrMap (β : Type) where
  entries : List (String × β) := []

namespace StrMap

variable {β : Type}

instance : EmptyCollection (StrMap β) := ⟨⟨[]⟩⟩

/-- The value at `k`, if any. -/
@[expose] def find? (m : StrMap β) (k : String) : Option β :=
  (m.entries.find? (·.1 == k)).map (·.2)

/-- The value at `k`, or `d`. -/
@[expose] def getD (m : StrMap β) (k : String) (d : β) : β := (m.find? k).getD d

/-- `m` with `k` mapped to `x`. -/
@[expose] def insert (m : StrMap β) (k : String) (x : β) : StrMap β := ⟨(k, x) :: m.entries⟩

end StrMap

/-- The blocks being emitted: the open block, if any, and the blocks finished so far, in the
order they were finished, so the *first block finished is the entry*.  A region swaps it for
an empty one while its own blocks are emitted. -/
structure Body (env : Env Unit) (α : Type) where
  /-- The block being built, if one is open. -/
  label : Option Label := none
  params : Array (ValDecl env) := #[]
  instrs : Array (Instruction env α) := #[]
  blocks : Array (Block env α) := #[]

/-- A label `freshLabel` allocated. -/
structure FreshLabel where
  /-- The name it was allocated. -/
  name : Name
  /-- Its base, which the function numbers again when it is finished. -/
  base : Name
  /-- Whether its caller gave the base.  `renameLabel` replaces only a base that was not. -/
  given : Bool

/-- A piece of a misuse's message: text, or a label, which the message gives its final name. -/
inductive MsgPart where
  | text (s : String)
  | label (l : Label)

/-- What a function under construction consists of: its `body`, and what counts across the
function, regions included. -/
structure State (env : Env Unit) (α : Type) where
  /-- The annotation an instruction or block gets when its emitter is given none. -/
  info : α
  nextVal : Nat := 0
  /-- The stem of each value's name, by id, and whether its emitter's caller gave it.  The
  function numbers the stems when it is finished, so that two `x`es are `x.0` and `x.1`.
  `rename` replaces only a stem that was not given. -/
  stems : Array (Name × Bool) := #[]
  /-- The type of each value, by id. -/
  types : Array (TypeExpr env) := #[]
  /-- Next suffix per label base, so that two `bb`s are allocated `bb.0` and `bb.1`. -/
  labelSuffixes : StrMap Nat := ∅
  /-- The fresh labels, in allocation order. -/
  freshLabels : Array FreshLabel := #[]
  /-- The labels of the blocks opened so far, regions included. -/
  labels : NameSet := ∅
  body : Body env α := {}
  /-- The entry labels of the regions being emitted, innermost last. -/
  regions : Array Label := #[]
  /-- The misuses recorded so far, in order, each a message whose labels are given their final
  names when the function is finished. -/
  errors : Array (Array MsgPart) := #[]

end Build

/-- Emitting into one function. -/
abbrev BuildM (env : Env Unit) (α : Type) := StateM (Build.State env α)

namespace Build

variable {env : Env Unit} {α : Type}

/-- The empty state, annotating with `info` by default. -/
def State.init (info : α) : State env α := { info }

/-! ## Errors -/

/-- Record the error `msg`. -/
def error (msg : String) : BuildM env α Unit :=
  modify fun s => { s with errors := s.errors.push #[.text msg] }

/-- Record the error whose message is `parts`, its labels named as in the finished function. -/
def errorParts (parts : Array MsgPart) : BuildM env α Unit :=
  modify fun s => { s with errors := s.errors.push parts }

/-- `n`, dotted, for an error message. -/
def nameText : Name → String
  | .base => "_"
  | .str .base s => s
  | .num .base i => toString i
  | .str p s => s!"{nameText p}.{s}"
  | .num p i => s!"{nameText p}.{i}"

/-- Record an error if a block is still open when `what` ends. -/
def checkClosed (what : String) : BuildM env α Unit := do
  if let some l := (← get).body.label then
    errorParts #[.text s!"{what} ends with block ", .label l, .text " open"]

/-! ## Annotations -/

/-- The annotation to use: `info` if given, the current default otherwise. -/
def resolveInfo (info : Option α) : BuildM env α α := do
  return info.getD (← get).info

/-- Run `m` with `info` as the default annotation, restoring the old one afterwards. -/
def withInfo {β : Type} (info : α) (m : BuildM env α β) : BuildM env α β := do
  let saved := (← get).info
  modify ({ · with info })
  let r ← m
  modify ({ · with info := saved })
  return r

/-! ## Values -/

/-- A fresh value of type `t`, named `stem.n`, with `n` the number of values named after
`stem` before it in the finished function.  `stem` is structured: `x.cell` is the segments `x`
and `cell`, never one segment with a `.` in it.  `given` is false for a stem the emitter chose
itself, which `rename` may replace. -/
def freshVal (stem : Name) (t : TypeExpr env) (given : Bool := true) :
    BuildM env α (ValDecl env) := do
  let s ← get
  set { s with
    nextVal := s.nextVal + 1
    stems := s.stems.push (stem, given)
    types := s.types.push t }
  return ⟨⟨s.nextVal⟩, t⟩

/-- Name `v` after `stem`, if it is `start` or later and its emitter chose its stem itself.
Its stem is then given, so an enclosing `rename` keeps it. -/
def rename (start : Nat) (stem : Name) (v : ValId) : BuildM env α Unit :=
  modify fun s =>
    if h : start ≤ v.id ∧ v.id < s.stems.size then
      if s.stems[v.id].2 then s else { s with stems := s.stems.set v.id (stem, true) }
    else s

/-- The values' names: each stem numbered by how many values before it have it. -/
def numberStems (stems : Array Name) : Array Name :=
  (stems.foldl (init := (#[], (∅ : NameMap Nat))) fun (out, next) stem =>
    let k := (next.find? stem).getD 0
    (out.push (.num stem k), next.insert stem (k + 1))).1

/-! ## Instructions -/

/-- Emit `instr`, whose result is `d`, into the open block.  With no block open, it is
an error, and `instr` is not emitted. -/
def emit (d : ValDecl env) (instr : Instruction env α) : BuildM env α ValId := do
  if (← get).body.label.isNone then
    error s!"instruction %{d.id.id} emitted with no block open"
  else
    modify fun s => { s with body.instrs := s.body.instrs.push instr }
  return d.id

/-- Emit a literal, named after `name`, at the type the base gives it.  A function reference
takes its type from `emitFunc`; given one, it is an error, and nothing is emitted. -/
def emitConst [base ⊑ env] (name : Name) (c : Const) (info : Option α := none) :
    BuildM env α ValId := do
  match c.typeOf? (env := env) with
  | some t =>
    let d ← freshVal name t
    emit d (.const (← resolveInfo info) d c)
  | none =>
    let d ← freshVal name Base.Unit
    error s!"%{d.id.id}: a function reference emitted as a literal, with no type; use emitFunc"
    return d.id

/-- Emit a code pointer to `target`, a function of the module, at `ty`, the target's code
type, `base.Fn` of its parameter types and its return type.  The module checks it, so the
target may be built after the reference. -/
def emitFunc [base ⊑ env] (target : Name) (ty : TypeExpr env) (info : Option α := none) :
    BuildM env α ValId := do
  let d ← freshVal (.str .base "code") ty
  emit d (.const (← resolveInfo info) d (.func target))

/-- The type arguments `typeArgs` of an application of `r`, checked against its kinds, or
`none` with an error recorded if their count or a kind is wrong.  It is for a caller that has
them as data rather than writing `ta[…]`. -/
def checkTypeArgs {isig : InsnSig env} (r : InsnRef env isig) {type : Option (TypeExpr env)}
    (typeArgs : Array (TypeArg env)) : BuildM env α (Option (KindedTypeArgsFor r type)) := do
  match KindedTypeArgs.check? isig.scope.toList typeArgs with
  | .ok ta => return some ta
  | .error msg => error s!"{nameText r.name}: {msg}"; return none

/-- The type arguments of an application of `r` to `args`, whose result has type `type`, `none`
for a terminal instruction: as given, or inferred from the operands' types and `type`.  If they
cannot be inferred, `none`, with an error recorded. -/
def resolveTypeArgs {isig : InsnSig env} (r : InsnRef env isig) {type : Option (TypeExpr env)}
    (args : Array ValId) : TypeArgsOf r type → BuildM env α (Option (TypeArgs env isig.scope))
  | .given k => return some k.toTypeArgs
  | .infer => do
    let types := (← get).types
    let some ops := args.mapM (types[·.id]?)
      | error s!"{nameText r.name}: an operand is not a value of this function"; return none
    match isig.inferTypeArgs? type ops with
    | .ok a => return some a
    | .error e => error (e.text (nameText r.name)); return none

/-- `emitApply`, with regions built in any monad `BuildM` lifts into, such as a front end's
builder.  Its type arguments are `emitApply`'s.  `given` is false for a `name` the caller did
not choose, which `rename` may replace. -/
def emitApplyWith {m : Type → Type} [Monad m] [MonadLiftT (BuildM env α) m] {isig : InsnSig env}
    (name : Name) (type : TypeExpr env) (r : InsnRef env isig) (args : Array ValId)
    (succs : Array Target.Raw := #[]) (regions : Array (m (Region env α)) := #[])
    (info : Option α := none) (typeArgs : TypeArgsOf r (some type) := by infer_type_args)
    (given : Bool := true) : m ValId := do
  let d ← (freshVal name type given : BuildM env α (ValDecl env))
  let rs ← regions.mapM id
  (do
    let some ta ← resolveTypeArgs r args typeArgs | return d.id
    emit d (.apply (← resolveInfo info) d r ta args succs rs) : BuildM env α ValId)

/-- `emitApplyWith`, its result named after `result` if given, and otherwise after `stem`, a
name `rename` may replace: what a typed emitter applies. -/
def emitApplyNamed {m : Type → Type} [Monad m] [MonadLiftT (BuildM env α) m]
    {isig : InsnSig env} (result : Option Name) (stem : String) (type : TypeExpr env)
    (r : InsnRef env isig) (args : Array ValId) (succs : Array Target.Raw)
    (regions : Array (m (Region env α))) (info : Option α) (typeArgs : TypeArgsOf r (some type)) :
    m ValId :=
  emitApplyWith (result.getD (.str .base stem)) type r args succs regions info typeArgs
    result.isSome

/-- Emit an application of an operation, a datatype's constructor included.  `type` is the
result's type, the operation's return type at `typeArgs`.  `succs` are the blocks it may
transfer to, one per declared successor, and `regions` emit its nested bodies, each a
`region`.  They run after the result is allocated, so ids follow the printed order: the
result, then what the regions define.

`typeArgs`, written `ta[…]`, has one argument per type parameter, each of its kind, checked by
Lean.  Left out, it is inferred from `type` by `infer_type_args`, or else from the operands'
types and `type` when the builder runs.  If that fails, nothing is emitted, and the error is
recorded. -/
def emitApply {isig : InsnSig env} (name : Name) (type : TypeExpr env)
    (r : InsnRef env isig) (args : Array ValId) (succs : Array Target.Raw := #[])
    (regions : Array (BuildM env α (Region env α)) := #[]) (info : Option α := none)
    (typeArgs : TypeArgsOf r (some type) := by infer_type_args) :
    BuildM env α ValId := do
  emitApplyWith name type r args succs regions info typeArgs

/-! ## Blocks -/

/-- A target at `label`, binding `args`. -/
def goto (label : Label) (args : Array ValId := #[]) : Target.Raw := ⟨label, args⟩

/-- The default base of a label: `bb`. -/
def blockBase : String := "bb"

/-- A label for a block not yet built, which a transfer can name: `base.n`, with `n` the
next suffix for `base`.  `given` is false for a base the caller did not choose, which
`renameLabel` may replace. -/
def freshLabel (base : String := blockBase) (given : Bool := true) : BuildM env α Label := do
  let s ← get
  let suffix := s.labelSuffixes.getD base 0
  let name := .num (.str .base base) suffix
  set { s with
    labelSuffixes := s.labelSuffixes.insert base (suffix + 1)
    freshLabels := s.freshLabels.push { name, base := .str .base base, given } }
  return ⟨name⟩

/-- Give `l` the base `base`, if it is the `start`th fresh label or a later one and its caller
did not choose its base.  Its base is then given, so an enclosing `renameLabel` keeps it. -/
def renameLabel (start : Nat) (base : String) (l : Label) : BuildM env α Unit :=
  modify fun s => Id.run do
    for h : i in [start:s.freshLabels.size] do
      let f := s.freshLabels[i]
      if f.name == l.name then
        if f.given then return s
        return { s with
          freshLabels := s.freshLabels.set i { f with base := .str .base base, given := true } }
    return s

/-- Open the block called `label`, taking `params`.  It is an error to open a block while
another is open, which loses the other block, or under a label already used in the function or
any region of it. -/
def startBlock (label : Label) (params : Array (ValDecl env) := #[]) :
    BuildM env α Unit := do
  let s ← get
  if let some l := s.body.label then
    errorParts #[.text "block ", .label label, .text " opened while block ", .label l,
      .text " is open"]
  if label.name ∈ s.labels then
    errorParts #[.text "block ", .label label, .text " opened twice: its label is already used"]
  modify fun s =>
    { s with
      labels := s.labels.insert label.name ()
      body := { s.body with label := some label, params, instrs := #[] } }

/-- Open the block called `label`, taking one fresh value of type `t` named after `name`, and
return that value. -/
def startBlockWith (label : Label) (name : Name) (t : TypeExpr env) :
    BuildM env α ValId := do
  let v ← freshVal name t
  startBlock label #[v]
  return v.id

/-- Open a fresh block and hand back its label. -/
def startFreshBlock (params : Array (ValDecl env) := #[]) (base : String := blockBase) :
    BuildM env α Label := do
  let l ← freshLabel base
  startBlock l params
  return l

/-- Close the open block with `term`.  With no block open, it is an error. -/
def finishBlock (term : Terminator env α) (info : Option α := none) : BuildM env α Unit := do
  let info ← resolveInfo info
  let s ← get
  match s.body.label with
  | none => error "a block finished with no block open"
  | some l =>
    let b : Block env α :=
      { label := l, params := s.body.params, instrs := s.body.instrs, term, info }
    set { s with body := { blocks := s.body.blocks.push b } }

/-- Close the open block by applying the terminal operation `r`.  Its type arguments are
`emitApply`'s; with no result, they are inferred from the operands' types.  If that fails, the
block is dropped, and the error is recorded. -/
def terminate {isig : InsnSig env} (r : InsnRef env isig) (args : Array ValId := #[])
    (succs : Array Target.Raw := #[]) (regions : Array (BuildM env α (Region env α)) := #[])
    (info : Option α := none) (typeArgs : TypeArgsOf r none := by infer_type_args) :
    BuildM env α Unit := do
  let i ← resolveInfo info
  let rs ← regions.mapM id
  match ← resolveTypeArgs r args typeArgs with
  | some ta => finishBlock (.apply i r ta args succs rs) (some i)
  | none => modify fun s => { s with body := { s.body with label := none } }

/-- Close the open block with `jump k`. -/
def jump [base ⊑ env] (k : Target.Raw) (info : Option α := none) : BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.jump i k) (some i)

/-- Close the open block with `branch cond t f`. -/
def branch [base ⊑ env] (cond : ValId) (t f : Target.Raw) (info : Option α := none) :
    BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.branch i cond t f) (some i)

/-- Close the open block by leaving the enclosing body with `v`: a jump to `Label.exit`. -/
def ret [base ⊑ env] (v : ValId) (info : Option α := none) : BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.ret i v) (some i)

/-- Close the open block with `unreachable`. -/
def unreachable [base ⊑ env] (info : Option α := none) : BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.unreachable i) (some i)

/-! ## Regions -/

/-- Emit a region: open its entry block, labelled `base.n` and taking `params`, run `body`, and
take the blocks it finished that its entry reaches, entry first, and `body`'s result.  The
builder sets the enclosing body aside meanwhile, and restores it with the default annotation
afterwards, so a region can be emitted in the middle of a block.  Ids and labels keep counting
across the region.

`body` runs in any monad `BuildM` lifts into, such as a front end's builder.  It must finish
every block it opens.  While it runs, the region is the innermost open one, named by its entry
label.  A body that throws leaves the region open, which `run` records as a misuse. -/
def regionWith {m : Type → Type} {β : Type} [Monad m] [MonadLiftT (BuildM env α) m]
    (params : Array (ValDecl env)) (body : m β) (base : String := "region") :
    m (Region env α × β) := do
  let saved ← (modifyGet fun s => (s.body, { s with body := {} }) : BuildM env α (Body env α))
  let info := (← (get : BuildM env α (State env α))).info
  let entry ← (startFreshBlock params base : BuildM env α Label)
  (modify fun s => { s with regions := s.regions.push entry } : BuildM env α Unit)
  let r ← body
  (checkClosed s!"region {base}" : BuildM env α Unit)
  let inner ← (modifyGet fun s =>
      (s.body, { s with body := saved, info, regions := s.regions.pop }) :
    BuildM env α (Body env α))
  return (⟨(Body.dropUnreached inner.blocks.toList).toArray⟩, r)

/-- `regionWith` in `BuildM` itself, for a body with no result. -/
def region (params : Array (ValDecl env)) (body : BuildM env α Unit)
    (base : String := "region") : BuildM env α (Region env α) :=
  Prod.fst <$> regionWith params body base

/-! ## Finishing -/

mutual

/-- The terminator, with the labels of its targets and of its regions' blocks renamed by `f`. -/
private def relabelTerm (f : Label → Label) : Terminator env α → Terminator env α
  | .apply i r ta args succs ⟨rs⟩ =>
    .apply i r ta args (succs.map fun k => { k with label := f k.label }) ⟨relabelRegions f rs⟩

/-- `relabelTerm`, for an instruction. -/
private def relabelInstr (f : Label → Label) : Instruction env α → Instruction env α
  | .const i d c => .const i d c
  | .apply i d r ta args succs ⟨rs⟩ =>
    .apply i d r ta args (succs.map fun k => { k with label := f k.label }) ⟨relabelRegions f rs⟩

/-- `relabelInstr` on each. -/
private def relabelInstrs (f : Label → Label) :
    List (Instruction env α) → List (Instruction env α)
  | [] => []
  | i :: is => relabelInstr f i :: relabelInstrs f is

/-- The block, with its label renamed by `f`, and its instructions and terminator relabelled. -/
private def relabelBlock (f : Label → Label) : Block env α → Block env α
  | ⟨l, ps, ⟨is⟩, term, info⟩ => ⟨f l, ps, ⟨relabelInstrs f is⟩, relabelTerm f term, info⟩

/-- `relabelBlock` on each. -/
private def relabelBlocks (f : Label → Label) : List (Block env α) → List (Block env α)
  | [] => []
  | b :: bs => relabelBlock f b :: relabelBlocks f bs

/-- `relabelBlocks` on each region's blocks. -/
private def relabelRegions (f : Label → Label) : List (Region env α) → List (Region env α)
  | [] => []
  | ⟨⟨bs⟩⟩ :: rs => ⟨⟨relabelBlocks f bs⟩⟩ :: relabelRegions f rs

end

/-- The fresh labels of `s` whose final name differs from the one they were allocated, mapped
to it: its base, numbered by how many fresh labels before it have that base. -/
private def labelRenames (s : State env α) : Option (NameMap Name) :=
  let moved := (s.freshLabels.map (·.name) |>.zip (numberStems (s.freshLabels.map (·.base))))
    |>.filter fun (a, b) => a != b
  if moved.isEmpty then none
  else some (moved.foldl (init := ∅) fun r (a, b) => r.insert a b)

/-- `blocks`, with each fresh label of `s` given its final name. -/
private def numberLabels (s : State env α) (blocks : Array (Block env α)) :
    Array (Block env α) :=
  match labelRenames s with
  | none => blocks
  | some renames =>
    (relabelBlocks (fun l => ⟨(renames.find? l.name).getD l.name⟩) blocks.toList).toArray

/-- The misuses `s` recorded, each label given the name it has in the function `s` describes. -/
def State.misuses (s : State env α) : Array String :=
  let final : Label → Name := match labelRenames s with
    | none => (·.name)
    | some renames => fun l => (renames.find? l.name).getD l.name
  s.errors.map fun parts => parts.foldl (init := "") fun acc p => match p with
    | .text t => acc ++ t
    | .label l => acc ++ nameText (final l)

/-- The function the state describes, less the blocks its entry does not reach.  The first
block finished is the entry. -/
private def toFunc (s : State env α) (name : Name) (retType : TypeExpr env) (info : α) :
    Func env α :=
  { name, retType, blocks := numberLabels s (Body.dropUnreached s.body.blocks.toList).toArray,
    names := numberStems (s.stems.map (·.1)), info }

/-- A function the builder could not finish as a well-formed function. -/
structure FailedFunc (env : Env Unit) (α β : Type) where
  /-- What the builder returned. -/
  value : β
  /-- The misuses, in order; empty when the only fault is that `func` is not well formed. -/
  misuses : Array String
  /-- The function as emitted. -/
  func : Func env α

/-- The misuses, a line each, or that the function is not well formed. -/
instance {β : Type} : ToString (FailedFunc env α β) :=
  ⟨fun e => if e.misuses.isEmpty then s!"{nameText e.func.name} is not well formed"
    else "\n".intercalate e.misuses.toList⟩

/-- Decide `Func.WF` of the function `toFunc` gives. -/
private def decWF [base ⊑ env] (s : State env α) (name : Name) (retType : TypeExpr env)
    (info : α) : Decidable (toFunc s name retType info).WF :=
  inferInstance

/-- Record an error for each region still being emitted when the function ends. -/
def checkRegionsClosed : BuildM env α Unit := do
  for l in (← get).regions do
    errorParts #[.text "region ", .label l,
      .text " is still open when the function ends: its body did not return"]

/-- Run a builder for the function `name` and check the function it emitted.  The result is
the checked function and what the builder returned, or a `FailedFunc` when the builder recorded
a misuse, such as a block left open at the end, or the function is not well formed.  `info`
annotates the function, and is the default annotation for everything in it. -/
def run [base ⊑ env] {β : Type} (name : Name) (retType : TypeExpr env) (info : α)
    (m : BuildM env α β) : Except (FailedFunc env α β) ({fn : Func env α // fn.WF} × β) :=
  let (r, s) := (do
    let r ← m
    checkRegionsClosed
    checkClosed "the function"
    return r) (State.init info)
  let fn := toFunc s name retType info
  if !s.errors.isEmpty then .error ⟨r, s.misuses, fn⟩
  else match decWF s name retType info with
    | isTrue h => .ok (⟨fn, h⟩, r)
    | isFalse _ => .error ⟨r, #[], fn⟩

/-- `run`, for a builder that returns nothing: the checked function, or a `FailedFunc`. -/
def build [base ⊑ env] (name : Name) (retType : TypeExpr env) (info : α)
    (m : BuildM env α Unit) : Except (FailedFunc env α Unit) {fn : Func env α // fn.WF} :=
  Prod.fst <$> run name retType info m

/-! ## Stubs

A front end puts a stub in place of a function whose build failed, so that its module can
still be checked. -/

/-- Values with distinct ids, none defined in `ctx`, can all be defined. -/
private theorem foldlM_define_isSome : ∀ (ds : List (ValDecl env)) (ctx : Ctx env),
    (ds.map (·.id.id)).Nodup → (∀ d ∈ ds, ctx.types.find? d.id.id = none) →
      (ds.foldlM Ctx.define? ctx).isSome
  | [], _, _, _ => rfl
  | d :: ds, ctx, hnd, hfree => by
    have hd : ctx.define? d = some ⟨ctx.types.insert d.id.id d.type⟩ := by
      simp [Ctx.define?, hfree d List.mem_cons_self]
    rw [List.foldlM_cons, hd]
    refine foldlM_define_isSome ds _ (List.nodup_cons.mp hnd).2 fun e he => ?_
    have hne : e.id.id ≠ d.id.id := fun h =>
      (List.nodup_cons.mp hnd).1 (List.mem_map.mpr ⟨e, he, h⟩)
    rw [NatTrie.find?_insert, ite_eq_right hne]
    exact hfree e (List.mem_cons_of_mem d he)

/-- The number a name ends in, or `0`. -/
private def numSuffix : Name → Nat
  | .num _ i => i
  | _ => 0

/-- A list whose keys are `0, 1, …` in order has no repeats. -/
private theorem nodup_of_map_eq_range {β : Type} (l : List β) (k : β → Nat)
    (h : l.map k = List.range l.length) : l.Nodup :=
  List.Pairwise.of_map k (fun _ _ hk he => hk (congrArg k he)) (h ▸ List.nodup_range)

/-- `unreachable` is well formed anywhere. -/
private theorem unreachable_wf [base ⊑ env] (ctx : Ctx env) (bs : BlockSigs env) (i : α) :
    Terminator.WF ctx bs (Terminator.unreachable (env := env) i) := by
  simp [Terminator.unreachable, Terminator.WF, InsnSig.callWF, Target.Raw.AllWF, Agrees,
    OptHolds, Ctx.typesOf?, InsnSig.operandTypes?, InsnSig.succTypes, InsnSig.regionTypes,
    Region.WFList, Base.unreachable.sig]

/-- The stub's parameters: parameter `i` is value `i`. -/
private def stubParams (params : Array (Name × TypeExpr env)) : Array (ValDecl env) :=
  params.mapIdx fun i p => ⟨⟨i⟩, p.2⟩

/-- The function `stub` gives. -/
private def stubFunc [base ⊑ env] (name : Name) (params : Array (Name × TypeExpr env))
    (retType : TypeExpr env) (info : α) : Func env α :=
  { name, retType, info
    blocks := #[{ label := ⟨.num (.str .base "entry") 0⟩, params := stubParams params,
                  instrs := #[], term := .unreachable info, info }]
    names := params.mapIdx fun i p => .num p.1 i }

/-- A body of one block, with no instruction and a terminator with no region, is reachable. -/
private theorem reachable_single (b : Block env α) (hi : b.instrs = #[])
    (hr : b.term.regions = #[]) : Body.Reachable [b] := by
  refine .mk (fun c hc => ?_) (fun y r h => ?_)
  · rw [List.mem_singleton.mp hc]
    exact .root
  · cases h with
    | instr hc h _ =>
      rw [List.mem_singleton.mp hc, hi] at h
      simp at h
    | term hc h =>
      rw [List.mem_singleton.mp hc, hr] at h
      simp at h

/-- A body of one block, with no instruction, ending in a terminator with no operand,
successor or region, is scopable, by the tree that gives no block a parent. -/
private theorem scopable_single {Λ : ValId → Prop} (b : Block env α) (hi : b.instrs = #[])
    (ha : b.term.args = #[]) (hs : b.term.succs = #[]) (hr : b.term.regions = #[]) :
    Body.Scopable Λ [b] := by
  have hmem : ∀ {c}, c ∈ [b] → c = b := List.mem_singleton.mp
  have hk : ∀ {c : Block env α} {k : Nat} {i : Instruction env α}, c ∈ [b] →
      c.instrs[k]? ≠ some i := by
    intro c k i hc h
    rw [hmem hc, hi] at h
    simp at h
  refine .mk (fun _ => none) ⟨⟨List.pairwise_singleton _ _, fun _ _ => rfl, ?_, ?_, ?_⟩, ?_⟩ ?_
  · intro c hc
    simp at hc
  · intro c hc
    rw [hmem hc]
    exact .refl _
  · intro u v p hj
    cases hj with
    | instr hc h => exact absurd h (hk hc)
    | term hc h =>
      rw [hmem hc, hs] at h
      simp at h
  · intro x y hu
    cases hu with
    | instr hc h => exact absurd h (hk hc)
    | term hc h =>
      rw [hmem hc] at h
      rcases h with h | ⟨s, h, -⟩ <;> simp [ha, hs] at h
  · intro y r hy
    cases hy with
    | instr hc h => exact absurd h (hk hc)
    | term hc h =>
      rw [hmem hc, hr] at h
      simp at h

private theorem stubFunc_wf [base ⊑ env] (name : Name) (params : Array (Name × TypeExpr env))
    (retType : TypeExpr env) (info : α) : (stubFunc name params retType info).WF := by
  have hdefs : (stubFunc name params retType info).defs = (stubParams params).toList := by
    simp [stubFunc, Func.defs, Block.defsList, Instruction.defsList, Terminator.defs,
      Terminator.unreachable, Region.defsList]
  have hids : (stubParams params).toList.map (·.id.id) = List.range params.size :=
    List.ext_getElem (by simp [stubParams]) (by simp [stubParams])
  refine ⟨by simp [stubFunc], ?_, ?_, ?_, ?_, reachable_single _ rfl rfl,
    scopable_single _ rfl rfl rfl rfl⟩
  · show Label.Distinct [Label.exit, ⟨.num (.str .base "entry") 0⟩]
    decide
  · refine nodup_of_map_eq_range _ numSuffix (List.ext_getElem (by simp [stubFunc]) ?_)
    simp [stubFunc, numSuffix]
  · rw [hdefs, ValDecl.idBound_le_iff]
    intro d hd
    have : d.id.id ∈ List.range params.size := hids ▸ List.mem_map_of_mem hd
    simpa [stubFunc] using this
  · obtain ⟨ctx, hctx⟩ := Option.isSome_iff_exists.mp
      (foldlM_define_isSome (stubParams params).toList ∅ (hids ▸ List.nodup_range)
        fun _ _ => rfl)
    refine ⟨ctx, by rw [Func.ctx?, hdefs]; exact hctx, fun b hb => ?_⟩
    obtain rfl : b = _ := by simpa [stubFunc] using hb
    exact ⟨trivial, unreachable_wf ctx _ info⟩

/-- The stub of the function `name`, which takes `params` and returns `retType`: one block,
`entry.0`, taking the parameters and ending in `unreachable`.  Parameter `i` is value `i`,
named `x.i` for its name `x`.  A stub is always well formed. -/
def stub [base ⊑ env] (name : Name) (params : Array (Name × TypeExpr env))
    (retType : TypeExpr env) (info : α) : {fn : Func env α // fn.WF} :=
  ⟨stubFunc name params retType info, stubFunc_wf name params retType info⟩

end Build

end

end Strata.Dyn
