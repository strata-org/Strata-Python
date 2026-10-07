/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# Emitting a function

A builder emits a function's instructions in order.  Blocks are named by `Label`, so a
transfer can name a block before it is built.  A function's blocks carry the labels they were
allocated, in the order they were finished.

A label is `base.n`, `bb.n` by default, with `n` counting per `base` across the whole
function, regions included, so labels are unique function-wide as `Func.WF` demands.

The operations:

* `withInfo`: set the annotation given to what is emitted;
* `freshVal`: a fresh value;
* `emitConst`, `emitApply`: emit an instruction;
* `freshLabel`, `startBlock`, `startBlockWith`, `startFreshBlock`: allocate and open blocks;
* `finishBlock`, `terminate`, `jump`, `branch`, `ret`, `unreachable`: close the open block
  with a terminator: any terminal operation, a datatype's `case` among them, or the base's
  control flow;
* `region`: emit an operation's nested body;
* `run`: run a builder, taking the function it emitted and the errors it recorded;
* `build`: the function, or the `Errors` if any was recorded;
* `Holds`: a property of a build's function, false if the build failed.

Misuse is an error, recorded in the state: an instruction emitted with no block open, a block
opened while another is open, a block finished when none is open, and a region or function
body that ends with a block open.  `build` succeeds only if there is none.

The builder is language-neutral.  Its maps are association lists (`StrMap`), so a function it
builds reduces in the kernel.
-/

namespace Strata.Mantle

public section

namespace Build

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

/-- What a function under construction consists of.

`blocks` holds the finished blocks of the function, or of the region being emitted, in the
order they were finished: the *first block finished is the entry*. -/
structure State (env : Env Unit) (α : Type) where
  /-- The annotation an instruction or block gets when its emitter is given none. -/
  info : α
  nextVal : Nat := 0
  names : Array ValName := #[]
  /-- Next suffix per readable name, so that two `x`es are `x.0` and `x.1`. -/
  suffixes : StrMap Nat := ∅
  /-- Next suffix per label base, so that two `bb`s are `bb.0` and `bb.1`. -/
  labelSuffixes : StrMap Nat := ∅
  /-- The block being built, if one is open. -/
  label : Option Label := none
  params : Array (ValDecl env) := #[]
  instrs : Array (Instruction env α) := #[]
  blocks : Array (Block env α) := #[]
  /-- The misuses recorded so far, in order. -/
  errors : Array String := #[]

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
  modify fun s => { s with errors := s.errors.push msg }

/-- `n`, dotted, for an error message. -/
def nameText : Name → String
  | .base => "_"
  | .str .base s => s
  | .num .base i => toString i
  | .str p s => s!"{nameText p}.{s}"
  | .num p i => s!"{nameText p}.{i}"

/-- Record an error if a block is still open when `what` ends. -/
def checkClosed (what : String) : BuildM env α Unit := do
  if let some l := (← get).label then
    error s!"{what} ends with block {nameText l.name} open"

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

/-- A fresh value of type `t`, named after `base` with a disambiguating suffix. -/
def freshVal (base : String) (t : TypeExpr env 0) : BuildM env α (ValDecl env) := do
  let s ← get
  let suffix := s.suffixes.getD base 0
  set { s with
    nextVal := s.nextVal + 1
    names := s.names.push ⟨base, suffix⟩
    suffixes := s.suffixes.insert base (suffix + 1) }
  return ⟨⟨s.nextVal⟩, t⟩

/-! ## Instructions -/

/-- Emit `instr`, whose result is `d`, into the open block.  With no block open, it is
an error, and `instr` is not emitted. -/
def emit (d : ValDecl env) (instr : Instruction env α) : BuildM env α ValId := do
  if (← get).label.isNone then
    error s!"instruction %{d.id.id} emitted with no block open"
  else
    modify fun s => { s with instrs := s.instrs.push instr }
  return d.id

/-- Emit a constant.  Its type is what the base gives it, so the caller supplies
only a name to read it by. -/
def emitConst [base ⊑ env] (name : String) (c : Const) (info : Option α := none) :
    BuildM env α ValId := do
  let d ← freshVal name c.typeOf
  emit d (.const (← resolveInfo info) d c)

/-- Emit a code pointer to `target`, a function of the module: the constant `.func target`. -/
def emitFunc [base ⊑ env] (target : Name) (info : Option α := none) :
    BuildM env α ValId :=
  emitConst "code" (.func target) info

/-- Emit an application of an operation, a datatype's constructor included.  `type` is the
result's type, the operation's return type at `typeArgs`.  `succs` are the blocks it may
transfer to, one per declared successor, and `regions` are its nested bodies, each emitted
with `region`. -/
def emitApply {isig : InsnSig env} (name : String) (type : TypeExpr env 0)
    (r : InsnRef env isig) (typeArgs : Vector (TypeExpr env 0) isig.typeArgc)
    (args : Array ValId) (succs : Array BlockValue := #[])
    (regions : Array (Region env α) := #[]) (info : Option α := none) :
    BuildM env α ValId := do
  let d ← freshVal name type
  emit d (.apply (← resolveInfo info) d r typeArgs args succs regions)

/-! ## Blocks -/

/-- A transfer to `label`, pre-binding `args`. -/
def goto (label : Label) (args : Array ValId := #[]) : BlockValue := ⟨label, args⟩

/-- The default base of a label: `bb`. -/
def blockBase : String := "bb"

/-- A label for a block not yet built, which a transfer can name: `base.n`, with `n` the
next suffix for `base`. -/
def freshLabel (base : String := blockBase) : BuildM env α Label := do
  let s ← get
  let suffix := s.labelSuffixes.getD base 0
  set { s with labelSuffixes := s.labelSuffixes.insert base (suffix + 1) }
  return ⟨.num (.str .base base) suffix⟩

/-- Open the block called `label`, taking `params`.  Opening a block while another is open
is an error, and the other block is lost. -/
def startBlock (label : Label) (params : Array (ValDecl env) := #[]) :
    BuildM env α Unit := do
  if let some l := (← get).label then
    error s!"block {nameText label.name} opened while block {nameText l.name} is open"
  modify fun s => { s with label := some label, params, instrs := #[] }

/--
Open the block called `label`, taking one fresh value with base `name` of type type `t`, and
return that value.
-/
def startBlockWith (label : Label) (name : String) (t : TypeExpr env 0) :
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

/-- Close the open block with `term`.  Throws error is no block is open. -/
def finishBlock (term : Terminator env α) (info : Option α := none) : BuildM env α Unit := do
  let info ← resolveInfo info
  let s ← get
  match s.label with
  | none => error "a block finished with no block open"
  | some l =>
    let b : Block env α := { label := l, params := s.params, instrs := s.instrs, term, info }
    set { s with
      blocks := s.blocks.push b
      label := none
      params := #[]
      instrs := #[] }

/-- Close the open block by applying the terminal operation `r`. -/
def terminate {isig : InsnSig env} (r : InsnRef env isig)
    (typeArgs : Vector (TypeExpr env 0) isig.typeArgc) (args : Array ValId := #[])
    (succs : Array BlockValue := #[]) (regions : Array (Region env α) := #[])
    (info : Option α := none) : BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.apply i r typeArgs args succs regions) (some i)

/-- Close the open block with `jump k`. -/
def jump [base ⊑ env] (k : BlockValue) (info : Option α := none) : BuildM env α Unit := do
  let i ← resolveInfo info
  finishBlock (.jump i k) (some i)

/-- Close the open block with `branch cond t f`. -/
def branch [base ⊑ env] (cond : ValId) (t f : BlockValue) (info : Option α := none) :
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

/-- Emit a region: open its entry block, labelled `base.n` and taking `params`, run `body`,
and take the blocks it finished, entry first.  The open block and the blocks finished so
far are restored afterwards, so a region can be emitted in the middle of a block.  Value ids,
readable names and labels keep counting across it.

`body` must finish every block it opens, the entry included: ending with a block open is
an error.  `ret` leaves the region.  A transfer from the body to a block outside the region is
emitted as written, and `Func.WF` rejects it. -/
def region (params : Array (ValDecl env)) (body : BuildM env α Unit)
    (base : String := "region") : BuildM env α (Region env α) := do
  let saved ← get
  set ({ saved with label := none, params := #[], instrs := #[], blocks := #[] } : State env α)
  let _ ← startFreshBlock params base
  body
  checkClosed s!"region {base}"
  let inner ← get
  set ({ inner with
    info := saved.info, label := saved.label, params := saved.params,
    instrs := saved.instrs, blocks := saved.blocks } : State env α)
  return ⟨inner.blocks⟩

/-! ## Finishing -/

/-- The function the state describes.  The first block finished is the entry, so its
parameters are the function's. -/
def toFunc (s : State env α) (name : Name) (retType : TypeExpr env 0) (info : α) :
    Func env α :=
  { name, retType, blocks := s.blocks, names := s.names, info }

/-- The errors a failed build recorded: at least one message. -/
structure Errors where
  /-- The messages, in the order they were recorded. -/
  toArray : Array String
  nonempty : toArray.size ≠ 0

/-- The messages, a line each. -/
instance : ToString Errors := ⟨fun e => "\n".intercalate e.toArray.toList⟩

/-- What running a builder gives: `value`, and the errors recorded on the way. -/
structure Built (β : Type) where
  value : β
  errors : Array String

/-- `value` if no error was recorded, and the errors otherwise. -/
def Built.toExcept {β : Type} (b : Built β) : Except Errors β :=
  if h : b.errors.size = 0 then .ok b.value else .error ⟨b.errors, h⟩

/--
Run a builder for the function `name` and take the function it emitted, what the
builder returned, and the errors recorded, a block left open at the end among them.  `info`
annotates the function, and is the default annotation for everything in it. -/
def run {β : Type} (name : Name) (retType : TypeExpr env 0) (info : α)
    (m : BuildM env α β) : Built (Func env α × β) :=
  let (r, s) := (do let r ← m; checkClosed "the function"; return r) (State.init info)
  ⟨(toFunc s name retType info, r), s.errors⟩

/-- Run a builder and take the function it emitted, or the errors if any was recorded. -/
def build (name : Name) (retType : TypeExpr env 0) (info : α)
    (m : BuildM env α Unit) : Except Errors (Func env α) :=
  Prod.fst <$> (run name retType info m).toExcept

/-! ## Checking a result -/

/-- `p` holds of the result: false for an error, so both `Holds p` and `Holds (¬ p ·)` fail
on a failed build.  Decidable, for `decide +kernel` over a build. -/
@[expose] def Holds {ε β : Type} (p : β → Prop) : Except ε β → Prop
  | .ok x => p x
  | .error _ => False

instance {ε β : Type} (p : β → Prop) [DecidablePred p] : (e : Except ε β) → Decidable (Holds p e)
  | .ok x => inferInstanceAs (Decidable (p x))
  | .error _ => isFalse id

end Build

end

end Strata.Mantle
