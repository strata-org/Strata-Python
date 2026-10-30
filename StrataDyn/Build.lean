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

Ids count from `0` in allocation order.  They follow the order of `Func.defs`
(`Func.Canonical`) if each block's parameters, a region's included, are allocated just before
the block opens, and the contract is emitted after the body, its clauses in the order they
print.

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
* `requires`, `ensures`, `reads`, `writes`: emit a clause of the function's contract, a frame's
  regions included;
* `withFailureBlock`, `withPropagatingBlock`: run a body with the label of a block for its
  failure successors, and emit that block after the body's blocks;
* `old`: emit an application of `base.old`, which an `ensures` clause applies to read the state
  at the call;
* `emitGhost`: emit the cell of a ghost of the module, which only a contract may name;
* `ghost`: emit a ghost of the module, its initializer and its invariant, and check it;
* `run`, `build`: run a builder and check the function it emitted;
* `buildExtern`: emit an extern function, a signature and a contract with no blocks, and check
  it;
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
  /-- The contract's clauses emitted so far. -/
  contract : Contract env α := {}
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
takes its type from `emitFunc`, and a ghost reference from `emitGhost`; given either, it is an
error, and nothing is emitted. -/
def emitConst [base ≼ env] (name : Name) (c : Const) (info : Option α := none) :
    BuildM env α ValId := do
  match c.typeOf? (env := env) with
  | some t =>
    let d ← freshVal name t
    emit d (.const (← resolveInfo info) d c)
  | none =>
    let d ← freshVal name Base.Unit
    let (what, emitter) := match c with
      | .ghost _ => ("a ghost", "emitGhost")
      | _ => ("a function", "emitFunc")
    error s!"%{d.id.id}: {what} reference emitted as a literal, with no type; use {emitter}"
    return d.id

/-- Emit a code pointer to `target`, a function of the module, at `ty`, the target's code
type, `base.Fn` of its parameter types and its return type.  The module checks it, so the
target may be built after the reference. -/
def emitFunc [base ≼ env] (target : Name) (ty : TypeExpr env) (info : Option α := none) :
    BuildM env α ValId := do
  let d ← freshVal (.str .base "code") ty
  emit d (.const (← resolveInfo info) d (.func target))

/-- Emit the cell of the ghost `target` of the module, which holds a `type`: a value of type
`base.Ref(type)`.  The module checks it, so the ghost may be built after the reference.  Only a
contract may name a ghost. -/
def emitGhost [base ≼ env] (target : Name) (type : TypeExpr env) (info : Option α := none) :
    BuildM env α ValId := do
  let d ← freshVal (.str .base "ghost") (Base.Ref type)
  emit d (.const (← resolveInfo info) d (.ghost target))

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
def jump [base ≼ env] (k : Target.Raw) (info : Option α := none) : BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.jump i k) (some i)

/-- Close the open block with `branch cond t f`. -/
def branch [base ≼ env] (cond : ValId) (t f : Target.Raw) (info : Option α := none) :
    BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.branch i cond t f) (some i)

/-- Close the open block by leaving the enclosing body with `v`: a jump to `Label.exit`. -/
def ret [base ≼ env] (v : ValId) (info : Option α := none) : BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.ret i v) (some i)

/-- Close the open block with `unreachable`. -/
def unreachable [base ≼ env] (info : Option α := none) : BuildM env α Unit := do
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
label.  A body that throws leaves the region open, which `run`, `buildExtern` and `ghost` record
as a misuse. -/
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

/-! ## Contracts -/

/-- Whether the contract emitted so far has a frame. -/
private def hasFrame : BuildM env α Bool := do
  let c := (← get).contract
  return c.reads.isSome || c.writes.isSome

/-- Emit a `requires` clause of the function's contract: a region with no arguments, labelled
`pre.n`, whose `body` returns a `base.Bool`, named in diagnostics by `message`.  One after an
`ensures` clause or a frame is a misuse, since the `requires` clauses come first. -/
def requires (body : BuildM env α Unit) (message : Option String := none) :
    BuildM env α Unit := do
  if !(← get).contract.ensures.isEmpty then error "a requires clause after an ensures clause"
  else if ← hasFrame then error "a requires clause after a frame"
  let r ← region #[] body "pre"
  modify fun s => { s with contract.requires := s.contract.requires.push { region := r, message } }

/-- Emit an `ensures` clause of the function's contract: a region labelled `post.n`, taking a
fresh value of type `t`, the function's result, named after `name`.  `body`, given that value,
returns a `base.Bool`.  The clause is `free`, assumed and never checked, if `free` is set: an
extern's `ensures` clauses are free, and a defined function's are not.  `message` names it in
diagnostics.  One after a frame is a misuse, since the frames come last. -/
def ensures (name : Name) (t : TypeExpr env) (body : ValId → BuildM env α Unit)
    (free : Bool := false) (message : Option String := none) : BuildM env α Unit := do
  if ← hasFrame then error "an ensures clause after a frame"
  let result ← freshVal name t
  let r ← region #[result] (body result.id) "post"
  modify fun s =>
    { s with contract.ensures := s.contract.ensures.push { region := r, free, message } }

/-- An entry of a frame, as `reads` and `writes` take it: a cell among the function's parameters,
or the `body` of a frame region, which returns a `base.Loc`, the set of locations it names. -/
inductive FrameItem (env : Env Unit) (α : Type) where
  | cell (v : ValId)
  | region (body : BuildM env α Unit)

/-- The entries of a frame, in order: each cell as it is, and each region emitted by running its
body, as a region with no arguments labelled `loc.n`.  A failure in a frame region must go to a
block that ends in `unreachable`: `withFailureBlock` with no value gives the block. -/
private def frameEntries (items : Array (FrameItem env α)) :
    BuildM env α (Array (FrameEntry env α)) :=
  items.mapM fun
    | .cell v => pure (.cell v)
    | .region body => FrameEntry.region <$> region #[] body "loc"

/-- Emit the function's `reads` clause: the locations it may read.  It runs the body of each
frame region itself, in the order of the entries, so a frame region cannot be emitted out of
order or left unused.  A second one, or one after the `writes` clause, is a misuse, and then
no region is emitted. -/
def reads (items : Array (FrameItem env α)) : BuildM env α Unit := do
  let c := (← get).contract
  if c.reads.isSome then error "a second reads clause"
  else if c.writes.isSome then error "a reads clause after the writes clause"
  else
    let entries ← frameEntries items
    modify fun s => { s with contract.reads := some entries }

/-- Emit the function's `writes` clause: the locations it may change.  It runs the body of each
frame region itself, as `reads` does.  A second one is a misuse, and then no region is
emitted. -/
def writes (items : Array (FrameItem env α)) : BuildM env α Unit := do
  if (← get).contract.writes.isSome then error "a second writes clause"
  else
    let entries ← frameEntries items
    modify fun s => { s with contract.writes := some entries }

/-! ## Failure blocks

A failure successor of a contract region names a failure block or a propagating block of its
region.  These builders give the body its label first, and emit the block after the body,
when no block is open, and only if a block of the body transfers to it.  So its values get ids
after the body's, in the order of `Func.defs`, and a block that nothing uses takes no id. -/

/-- Whether a block finished in the open body transfers to `l`. -/
private def targeted (l : Label) : BuildM env α Bool :=
  return (← get).body.blocks.any fun b => (Body.edges b).any (·.2 == l)

/-- Run `body` with the label of a *failure block*, `fail.n`, and then emit the block after the
blocks `body` finished, if one of them transfers to it.  The block takes one parameter `%e.n` per
type of `payload`, so that a failure successor whose payload is `payload` can name it.  It
returns the constant `c` when `value` is `some c`, and is `unreachable` when `value` is `none`.
A failure in a `requires` clause or a checked `ensures` clause gives `false`, and one in a `free
ensures` clause gives `true`.  `body` must finish every block it opens. -/
def withFailureBlock [base ≼ env] {β : Type} (payload : Array (TypeExpr env))
    (value : Option Bool) (body : Label → BuildM env α β) (info : Option α := none) :
    BuildM env α β := do
  let l ← freshLabel "fail"
  let i ← resolveInfo info
  let r ← body l
  if ← targeted l then
    startBlock l (← payload.mapM (freshVal (.str .base "e")))
    match value with
    | some c => ret (← emitConst (.str .base "value") (.bool c) (some i)) (some i)
    | none => unreachable (some i)
  return r

/-- Run `body` with the label of a *propagating block*, `propagate.n`, and then emit the block
after the blocks `body` finished, if one of them transfers to it.  The block takes the failure
`%exc.n : e`, and returns it as `base.error[e, a](%exc.n)`, so that a nested region whose result
is a `base.Except(e, a)` passes the failure on to the operation that owns it.  `body` must finish
every block it opens. -/
def withPropagatingBlock [base ≼ env] {β : Type} (e a : TypeExpr env)
    (body : Label → BuildM env α β) (info : Option α := none) : BuildM env α β := do
  let l ← freshLabel "propagate"
  let i ← resolveInfo info
  let r ← body l
  if ← targeted l then
    let exc ← startBlockWith l (.str .base "exc") e
    ret (← emitApply (.str .base "err") (Base.Except e a) Base.Except.error.ref #[exc]
      (info := some i) (typeArgs := ta[e, a])) (some i)
  return r

/-! ## `old` -/

/-- Emit `base.old[e, a]`, named after `name`, whose failure goes to `err`: its region, labelled
`old.n`, runs `body` in the state at the call.  `body` gets the label of a propagating block for
the failure successors in the region, which is emitted, after its blocks, only if one of them
transfers to it.  `body` finishes every block it opens, each returning a `base.Except(e, a)`.
Only an `ensures` clause may apply `base.old`. -/
def old [base ≼ env] (name : Name) (e a : TypeExpr env) (err : Label)
    (body : Label → BuildM env α Unit) (info : Option α := none) : BuildM env α ValId :=
  emitApply name a Base.old.ref #[] (succs := #[goto err])
    (regions := #[region #[] (withPropagatingBlock e a body info) "old"]) (info := info)
    (typeArgs := ta[e, a])

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

/-- `r`, with the labels of its blocks renamed by `f`. -/
private def relabelRegion (f : Label → Label) (r : Region env α) : Region env α :=
  ⟨(relabelBlocks f r.blocks.toList).toArray⟩

/-- `c`, with the labels of its regions' blocks renamed by `f`. -/
private def relabelContract (f : Label → Label) (c : Contract env α) : Contract env α :=
  let entry : FrameEntry env α → FrameEntry env α := fun
    | .cell v => .cell v
    | .region r => .region (relabelRegion f r)
  { requires := c.requires.map fun cl => { cl with region := relabelRegion f cl.region }
    ensures := c.ensures.map fun cl => { cl with region := relabelRegion f cl.region }
    reads := c.reads.map (·.map entry)
    writes := c.writes.map (·.map entry) }

/-- The renaming that gives each fresh label of `s` its final name, or `none` if every fresh
label keeps the name it was allocated. -/
private def finalLabel? (s : State env α) : Option (Label → Label) :=
  (labelRenames s).map fun renames l => ⟨(renames.find? l.name).getD l.name⟩

/-- `blocks`, with each fresh label of `s` given its final name. -/
private def numberLabels (s : State env α) (blocks : Array (Block env α)) :
    Array (Block env α) :=
  match finalLabel? s with
  | none => blocks
  | some f => (relabelBlocks f blocks.toList).toArray

/-- `c`, with each fresh label of `s` given its final name. -/
private def numberContractLabels (s : State env α) (c : Contract env α) : Contract env α :=
  match finalLabel? s with
  | none => c
  | some f => relabelContract f c

/-- `r`, with each fresh label of `s` given its final name. -/
private def numberRegionLabels (s : State env α) (r : Region env α) : Region env α :=
  match finalLabel? s with
  | none => r
  | some f => relabelRegion f r

/-- The misuses `s` recorded, each label given the name it has in the function `s` describes. -/
def State.misuses (s : State env α) : Array String :=
  let final : Label → Name := match labelRenames s with
    | none => (·.name)
    | some renames => fun l => (renames.find? l.name).getD l.name
  s.errors.map fun parts => parts.foldl (init := "") fun acc p => match p with
    | .text t => acc ++ t
    | .label l => acc ++ nameText (final l)

/-- The defined function the state describes, less the blocks its entry does not reach.  The
first block finished is the entry, and its parameters are the function's. -/
private def toFunc (s : State env α) (name : Name) (retType : TypeExpr env) (info : α) :
    Func env α :=
  let blocks := numberLabels s (Body.dropUnreached s.body.blocks.toList).toArray
  { name, params := (blocks[0]?.map (·.params)).getD #[], retType, blocks,
    contract := numberContractLabels s s.contract, names := numberStems (s.stems.map (·.1)),
    info }

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

/-- Decide `Func.WF` of a function the builder emitted. -/
private def decWF [base ≼ env] (fn : Func env α) : Decidable fn.WF :=
  inferInstance

/-- `fn`, checked, with `r`, what the builder returned; or a `FailedFunc` if the builder
recorded the misuses `errors` or `fn` is not well formed. -/
private def finish [base ≼ env] {β : Type} (r : β) (errors : Array String) (fn : Func env α) :
    Except (FailedFunc env α β) ({fn : Func env α // fn.WF} × β) :=
  if !errors.isEmpty then .error ⟨r, errors, fn⟩
  else match decWF fn with
    | isTrue h => .ok (⟨fn, h⟩, r)
    | isFalse _ => .error ⟨r, #[], fn⟩

/-- Record an error for each region still being emitted when `what` ends. -/
def checkRegionsClosed (what : String) : BuildM env α Unit := do
  for l in (← get).regions do
    errorParts #[.text "region ", .label l,
      .text s!" is still open when {what} ends: its body did not return"]

/-- Run a builder for the function `name` and check the function it emitted.  The result is
the checked function and what the builder returned, or a `FailedFunc` when the builder recorded
a misuse, such as a block left open at the end, or the function is not well formed.  `info`
annotates the function, and is the default annotation for everything in it. -/
def run [base ≼ env] {β : Type} (name : Name) (retType : TypeExpr env) (info : α)
    (m : BuildM env α β) : Except (FailedFunc env α β) ({fn : Func env α // fn.WF} × β) :=
  let (r, s) := (do
    let r ← m
    checkRegionsClosed "the function"
    checkClosed "the function"
    return r) (State.init info)
  finish r s.misuses (toFunc s name retType info)

/-- `run`, for a builder that returns nothing: the checked function, or a `FailedFunc`. -/
def build [base ≼ env] (name : Name) (retType : TypeExpr env) (info : α)
    (m : BuildM env α Unit) : Except (FailedFunc env α Unit) {fn : Func env α // fn.WF} :=
  Prod.fst <$> run name retType info m

/-- Emit the extern function `name`, which takes `params` and returns `retType`, and check it:
the checked function, or a `FailedFunc`.  Its parameters get the first ids, in order, and
`contract`, given those ids, emits its clauses.  An extern has no blocks, so a block that
`contract` opens outside a clause makes it ill formed.  `info` annotates the function, and is the default
annotation for everything in it. -/
def buildExtern [base ≼ env] (name : Name) (params : Array (Name × TypeExpr env))
    (retType : TypeExpr env) (info : α) (contract : Array ValId → BuildM env α Unit) :
    Except (FailedFunc env α Unit) {fn : Func env α // fn.WF} :=
  let emit : BuildM env α (Array (ValDecl env)) := do
    let ps ← params.mapM fun (n, t) => freshVal n t
    contract (ps.map (·.id))
    checkRegionsClosed "the function"
    checkClosed "the function"
    return ps
  let (ps, s) := emit (State.init info)
  Prod.fst <$> finish () s.misuses
    { toFunc s name retType info with params := ps, extern := true }

/-! ## Ghosts -/

/-- A ghost the builder could not finish as a well-formed ghost. -/
structure FailedGhost (env : Env Unit) (α : Type) where
  /-- The misuses, in order; empty when the only fault is that `ghost` is not well formed. -/
  misuses : Array String
  /-- The ghost as emitted. -/
  ghost : Ghost env α

/-- The misuses, a line each, or that the ghost is not well formed. -/
instance : ToString (FailedGhost env α) :=
  ⟨fun e => if e.misuses.isEmpty then s!"ghost {nameText e.ghost.name} is not well formed"
    else "\n".intercalate e.misuses.toList⟩

/-- Emit the ghost `name`, which holds a `type`, and check it: the checked ghost, or a
`FailedGhost`.  `init` emits the body of its initializer, a region with no arguments labelled
`init.n` that returns the first contents, and `invariant`, given the contents `%v.n`, the body of
its invariant, a region labelled `inv.n` that returns a `base.Bool`.  The values are numbered
from `0`, the initializer's first, as `Ghost.defs` lists them.  A failure in either region must
go to a block that ends in `unreachable`: `withFailureBlock` with no value gives the block.
`info` annotates the ghost, and is the default annotation for everything in it.  That the ghosts
and functions it names exist is checked with its module. -/
def ghost [base ≼ env] (name : Name) (type : TypeExpr env) (init : Option (BuildM env α Unit))
    (invariant : Option (ValId → BuildM env α Unit)) (info : α) :
    Except (FailedGhost env α) {g : Ghost env α // g.WF} :=
  let emit : BuildM env α (Option (Region env α) × Option (Region env α)) := do
    let i ← init.mapM fun body => region #[] body "init"
    let v ← invariant.mapM fun body => do
      let v ← freshVal (.str .base "v") type
      region #[v] (body v.id) "inv"
    checkRegionsClosed "the ghost"
    checkClosed "the ghost"
    return (i, v)
  let ((i, v), s) := emit (State.init info)
  let g : Ghost env α :=
    { name, type, init := i.map (numberRegionLabels s), invariant := v.map (numberRegionLabels s),
      names := numberStems (s.stems.map (·.1)), info }
  if !s.errors.isEmpty then .error ⟨s.misuses, g⟩
  else if h : g.WF then .ok ⟨g, h⟩
  else .error ⟨#[], g⟩

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
private theorem unreachable_wf [base ≼ env] (ctx : Ctx env) (bs : BlockSigs env) (i : α) :
    Terminator.WF ctx bs (Terminator.unreachable (env := env) i) := by
  simp [Terminator.unreachable, Terminator.WF, InsnSig.callWF, Target.Raw.AllWF, Agrees,
    OptHolds, Ctx.typesOf?, InsnSig.operandTypes?, InsnSig.succTypes, InsnSig.regionTypes,
    Region.WFList, Base.unreachable.sig]

/-- The stub's parameters: parameter `i` is value `i`. -/
private def stubParams (params : Array (Name × TypeExpr env)) : Array (ValDecl env) :=
  params.mapIdx fun i p => ⟨⟨i⟩, p.2⟩

/-- The function `stub` gives. -/
private def stubFunc [base ≼ env] (name : Name) (params : Array (Name × TypeExpr env))
    (retType : TypeExpr env) (info : α) : Func env α :=
  { name, params := stubParams params, retType, info
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

private theorem stubFunc_wf [base ≼ env] (name : Name) (params : Array (Name × TypeExpr env))
    (retType : TypeExpr env) (info : α) : (stubFunc name params retType info).WF := by
  have hdefs : (stubFunc name params retType info).defs = (stubParams params).toList := by
    simp [stubFunc, Func.defs, Block.defsList, Instruction.defsList, Terminator.defs,
      Terminator.unreachable, Region.defsList, Contract.regions, Contract.frameRegions,
      FrameEntry.regionsOf]
  have hids : (stubParams params).toList.map (·.id.id) = List.range params.size :=
    List.ext_getElem (by simp [stubParams]) (by simp [stubParams])
  obtain ⟨ctx, hctx⟩ := Option.isSome_iff_exists.mp
    (foldlM_define_isSome (stubParams params).toList ∅ (hids ▸ List.nodup_range) fun _ _ => rfl)
  have hctx' : (stubFunc name params retType info).ctx? = some ctx := by
    rw [Func.ctx?, hdefs]; exact hctx
  refine ⟨by simp [stubFunc], by simp [stubFunc], ?_, ?_, ?_, ?_, reachable_single _ rfl rfl,
    scopable_single _ rfl rfl rfl rfl,
    ⟨ctx, hctx', by
      simp [Func.ContractWFIn, Func.FrameWF, FrameEntry.cellsOf, FrameEntry.regionsOf, stubFunc]⟩,
    by simp [Func.ClauseModesWF, stubFunc], ?_, ?_, ?_⟩
  · show Label.Distinct [Label.exit, ⟨.num (.str .base "entry") 0⟩]
    decide
  · refine nodup_of_map_eq_range _ numSuffix (List.ext_getElem (by simp [stubFunc]) ?_)
    simp [stubFunc, numSuffix]
  · rw [hdefs, ValDecl.idBound_le_iff]
    intro d hd
    have : d.id.id ∈ List.range params.size := hids ▸ List.mem_map_of_mem hd
    simpa [stubFunc] using this
  · refine ⟨ctx, hctx', fun b hb => ?_⟩
    obtain rfl : b = _ := by simpa [stubFunc] using hb
    exact ⟨trivial, unreachable_wf ctx _ info⟩
  · simp [Func.ContractRegionsWF, Func.ClauseFailuresWF, Region.Propagates, Region.nestedList,
      Region.EndsInControl, Region.Acyclic, Region.allList, Region.withNestedList,
      Contract.regions, Contract.frameRegions, FrameEntry.regionsOf, stubFunc]
  · simp [Func.OldWF, Func.OldPlaced, Func.OldScoped, Region.NoOld, Region.allList,
      Region.withNestedList, Block.nestedRegionsList, Instruction.regionsWithNestedList,
      Terminator.regionsWithNested, Terminator.unreachable, Contract.frameRegions,
      FrameEntry.regionsOf, stubFunc]
  · simp [Func.GhostsInContract, Block.withNestedList, Instruction.nestedBlocksList,
      Terminator.nestedBlocks, Terminator.unreachable, Region.blocksList, stubFunc]

/-- The stub of the function `name`, which takes `params` and returns `retType`: one block,
`entry.0`, taking the parameters and ending in `unreachable`.  Parameter `i` is value `i`,
named `x.i` for its name `x`.  A stub is always well formed. -/
def stub [base ≼ env] (name : Name) (params : Array (Name × TypeExpr env))
    (retType : TypeExpr env) (info : α) : {fn : Func env α // fn.WF} :=
  ⟨stubFunc name params retType info, stubFunc_wf name params retType info⟩

end Build

end

end Strata.Dyn
