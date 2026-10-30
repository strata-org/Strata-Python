/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Build
public import StrataDyn.Typed
-- Instruction values embed the signature representation, needed at code-generation time.
import StrataDyn.Env.WF
-- `dyn_emitters`.  `StrataDyn.DSL` imports this module, so this one imports the command alone.
import StrataDyn.DSL.Core

set_option autoImplicit false

/-!
# Typed emitters

`Build.emitApply` takes an instruction, its result type and its operands as an
`Array ValId`, so Lean checks none of them against the instruction's signature: a front end
learns of a wrong operand when `Build.run` checks the function.  The pieces here let each
instruction have an emitter whose Lean type is its signature, which the `environment` command
generates under the instruction's own name (`StrataDyn.DSL.Emit`); `o.ref` is the
instruction itself:

```lean
Base.refNew (value : Val env a) (result : Option Name := none) : m (Val env (Base.Ref a))
Base.callCode (f : Val env (Base.Fn as r)) (args : Vals env as) (result : Option Name := none) :
  m (Val env r)
Base.Except.case (scrutinee : Val env (Base.Except e a)) (ok : Target env [a])
  (error : Target env [e]) : m Unit
```

A value's Lean type carries the function's environment and its Dyn type, a type expression
of that environment, so Lean infers the type arguments by unifying the operands' types with the
signature, and computes the result's.  The type is a phantom: `Build.run`'s check is still what
guarantees the function is well formed.

* `Val` and `Vals`, the typed values (`StrataDyn.Typed`).
* `BlockRef env ps`, a block whose parameters have the types `ps`, which `Emit.freshLabel`
  makes.
* `Target env ps`, what fills a successor whose payload is `ps`: a block with a prefix of its
  arguments bound, that still expects `ps`.  `BlockRef.goto`, `Target.bind` and
  `Target.bindAll` make one, and a region's body is given its exit as one, which knows its
  region.  `Target.raw` is the untyped target.  Their constructors are private, so a block or a
  target comes from these operations, or from the escape `Target.ofRaw`.
* `MonadBuild env α m`: a monad that emits into a function over `env`, `BuildM` or a front
  end's builder over it.  The emitters run in any of them.
* `freshLabel`, `startBlock`, `startBlock₁`, `param`, `int`, `bool`, `str`, `float`, `unit`,
  `code`, `ret`: the builder's operations at typed values.
* `Build.named` and `let%`: a value or a block named after the Lean binder it is bound to.

## Names

An emitter's result is named after `result` if it is given, and otherwise after the
instruction.  A block from `freshLabel` is labelled after `base` if it is given, and otherwise
`bb`, and `startBlock₁`'s parameter after `stem`, and otherwise `v`.  Where
`Strata.Dyn.Emit` is open, `let% x ← e` binds `x` as `let x ← e` does, and names the value or
block `e` returns `x`, if `e` made it and nothing gave it a name:

```lean
let% cell ← Base.refNew zero                       -- %cell.0
let% r ← Base.refGet (← Base.refNew zero)          -- %refNew.0, then %r.0
let% x ← Base.refGet cell (result := n "read")     -- %read.0
let% ok ← Emit.freshLabel [Base.Int]               -- ^ok.0
let% err ← Emit.freshLabel [Base.Int] "fail"       -- ^fail.0
let% x ← Emit.startBlock₁ ok                       -- %x.0, the parameter of ^ok.0
```

So in a helper that emits several values, only the one it returns takes the name, and a name
the helper gave it wins.  A result that is neither a value nor a block is bound and not
named.  `let%` takes an identifier, with `mut` or a type as `let` does; a pattern, a
reassignment and a nested `(← e)` name nothing.  `let%` in a monad that does not emit into a
function is an error at the statement.

## Exits

Every region's exit is the same label, `Label.exit`, which leaves the innermost body being
emitted.  So the builder keeps the open regions, and the exit a region's body is given names
its region.  An instruction given the exit of a region other than the innermost open one, an
enclosing region's or one that has ended, is recorded as a misuse, and `Build.run` rejects the
function.

## Escapes

`Val.ofId`, `Val.cast` and `Target.ofRaw` give a value or a target whatever type they
are told, for a type known only when the builder runs or a value kept untyped by a front end.
Lean checks nothing about them, and `Emit.ret` does not check its value against the function's
result type: these are checked by `Build.run` only, which rejects the function if the claimed
type is wrong.  `Val.id` and `Target.raw` go back to the untyped builder.
-/

namespace Strata.Dyn

public section

/-! ## Typed blocks and targets -/

/-- A block, over `env`, whose parameters have the types `ps`.  `Emit.freshLabel` makes one. -/
structure BlockRef (env : Env Unit) (ps : List (TypeExpr env)) where
  private mk ::
  /-- The block's label. -/
  label : Label

/-- What fills a successor with payload `ps`: a block, with a prefix of its arguments bound, that
still expects values of the types `ps`.  `ps` is a phantom.  The bound arguments come first,
and the operation's payload fills the block's remaining parameters, in order.  (MLIR's
`SuccessorOperands` puts the values the operation produces first instead.)  `BlockRef.goto`,
`Target.bind`, `Target.bindAll` and `Build.withExit` make one, and `Target.ofRaw` is the escape. -/
structure Target (env : Env Unit) (ps : List (TypeExpr env)) where
  private mk ::
  /-- The target, as the builder takes it. -/
  raw : Target.Raw
  /-- The entry label of the region this is the exit of, if it is one. -/
  exitOf : Option Label := none

namespace BlockRef

variable {env : Env Unit}

/-- A target at `l`, binding none of its arguments. -/
@[inline] def goto {ps : List (TypeExpr env)} (l : BlockRef env ps) : Target env ps :=
  ⟨⟨l.label, #[]⟩, none⟩

end BlockRef

namespace Target

variable {env : Env Unit}

/-- `k`, with its next argument bound to `v`. -/
@[inline] def bind {t : TypeExpr env} {ps : List (TypeExpr env)} (k : Target env (t :: ps))
    (v : Val env t) : Target env ps :=
  { k with raw := k.raw.bind v.id }

/-- `k`, with all its arguments bound to `vs`. -/
@[inline] def bindAll {ps : List (TypeExpr env)} (k : Target env ps) (vs : Vals env ps) :
    Target env [] :=
  { k with raw := { k.raw with args := vs.idsTo k.raw.args } }

/-- `r`, as a target expecting `ps`, not the exit of any region.  Lean does not check `ps`. -/
@[inline] def ofRaw (ps : List (TypeExpr env)) (r : Target.Raw) : Target env ps := ⟨r, none⟩

end Target

/-! ## Monads that emit -/

/-- A monad that emits into one function over `env` annotated with `α`: `BuildM env α`, or a
front end's builder over it.  `env` and `α` are found from the monad, so an emitter called in
it needs neither. -/
class MonadBuild (env : outParam (Env Unit)) (α : outParam Type) (m : Type → Type) where
  /-- Run a `BuildM` action. -/
  liftBuild {β : Type} : BuildM env α β → m β

export MonadBuild (liftBuild)

instance {env : Env Unit} {α : Type} : MonadBuild env α (BuildM env α) := ⟨id⟩

instance {env : Env Unit} {α σ : Type} {m : Type → Type} [Monad m] [MonadBuild env α m] :
    MonadBuild env α (StateT σ m) :=
  ⟨fun x s => do return (← liftBuild x, s)⟩

instance {env : Env Unit} {α ρ : Type} {m : Type → Type} [MonadBuild env α m] :
    MonadBuild env α (ReaderT ρ m) :=
  ⟨fun x _ => liftBuild x⟩

instance {env : Env Unit} {α ε : Type} {m : Type → Type} [Monad m] [MonadBuild env α m] :
    MonadBuild env α (ExceptT ε m) :=
  ⟨fun x => ExceptT.lift (liftBuild x)⟩

namespace Build

variable {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]

/-- `liftBuild`, packaged as a `MonadLiftT` instance. -/
@[reducible] def liftOf (env : Env Unit) (α : Type) (m : Type → Type) [MonadBuild env α m] :
    MonadLiftT (BuildM env α) m :=
  ⟨liftBuild⟩

/-- Record a misuse for each of `exits`, the regions whose exits an instruction is given, that
is not the innermost open region: an enclosing one, which the exit would not leave, or one that
has ended. -/
def checkExits (exits : Array (Option Label)) : BuildM env α Unit := do
  let regions := (← get).regions
  for e in exits do
    let some r := e | continue
    if regions.back? == some r then continue
    -- The innermost open region, if the exit's region encloses it.
    match regions.back?.filter fun _ => regions.contains r with
    | some inner =>
      errorParts #[.text "the exit of region ", .label r, .text " is used inside region ",
        .label inner, .text ", which it does not leave"]
    | none =>
      errorParts #[.text "the exit of region ", .label r, .text " is used after the region ends"]

/-- `body`, given the exit of the innermost open region, which leaves it with an `r`. -/
def withExit {β : Type} (r : TypeExpr env) (body : Target env [r] → m β) : m β := do
  let inner ← liftBuild (do return (← get).regions.back? : BuildM env α (Option Label))
  body ⟨⟨Label.exit, #[]⟩, inner⟩

/-- `terminate`, with regions built in any monad that emits into the function. -/
def terminateWith {isig : InsnSig env} (r : InsnRef env isig) (args : Array ValId)
    (succs : Array Target.Raw) (regions : Array (m (Region env α))) (info : Option α)
    (typeArgs : TypeArgsOf r none) : m Unit := do
  let rs ← regions.mapM id
  liftBuild do
    let i ← resolveInfo info
    match ← resolveTypeArgs r args typeArgs with
    | some ta => finishBlock (.apply i r ta args succs rs) (some i)
    | none => modify fun s => { s with body := { s.body with label := none } }

/-- Where a statement starts emitting: the next value's id, and the number of fresh labels. -/
structure Mark where
  /-- The id of the next value. -/
  vals : Nat
  /-- The number of fresh labels allocated so far. -/
  labels : Nat

/-- What `named` names in a result of type `β`: a value, a block's label, or nothing. -/
class NameResult (env : Env Unit) (β : Type) where
  /-- Name `b` after `stem`, if it was made since `start` and nothing named it. -/
  name {α : Type} (start : Mark) (stem : String) (b : β) : BuildM env α Unit

instance {t : TypeExpr env} : NameResult env (Val env t) :=
  ⟨fun start stem v => rename start.vals (.str .base stem) v.id⟩

instance {ps : List (TypeExpr env)} : NameResult env (BlockRef env ps) :=
  ⟨fun start stem l => renameLabel start.labels stem l.label⟩

instance (priority := low) {β : Type} : NameResult env β := ⟨fun _ _ _ => pure ()⟩

/-- `x`, with what it returns named after `stem` if `x` made it and nothing gave it a name:
neither its emitter's caller nor an inner `named`.  A value takes the name `stem.n`, and a
block the label `stem.n`; anything else is returned as it is.  `let% v ← x` is
`let v ← named "v" x`. -/
def named {β : Type} [NameResult env β] (stem : String) (x : m β) : m β := do
  let start ← liftBuild (do
    let s ← get
    return ⟨s.nextVal, s.freshLabels.size⟩ : BuildM env α Mark)
  let b ← x
  liftBuild (NameResult.name start stem b : BuildM env α Unit)
  return b

end Build

/-! ## The builder's operations, at typed values -/

namespace Emit

open Build

variable {env : Env Unit} {α : Type} {m : Type → Type} [Monad m] [MonadBuild env α m]

/-- A fresh block taking values of types `ps`, not yet opened: `base.n`.  Without `base`, it is
`bb.n`, and `let%` may rename it. -/
def freshLabel (ps : List (TypeExpr env)) (base : Option String := none) :
    m (BlockRef env ps) :=
  liftBuild (do return ⟨← Build.freshLabel (base.getD blockBase) base.isSome⟩ :
    BuildM env α (BlockRef env ps))

/-- Fresh values of types `ts`, each named after `stem`. -/
def freshVals (stem : Name) : (ts : List (TypeExpr env)) →
    BuildM env α (Array (ValDecl env) × Vals env ts)
  | [] => return (#[], .nil)
  | t :: ts => do
    let d ← freshVal stem t
    let (ds, vs) ← freshVals stem ts
    return (#[d] ++ ds, .cons ⟨d.id⟩ vs)

/-- Open the block `l`, taking fresh values of its parameters' types, each named after
`stem`, and return them. -/
def startBlock {ps : List (TypeExpr env)} (l : BlockRef env ps) (stem : Name := .str .base "v") :
    m (Vals env ps) :=
  liftBuild do
    let (ds, vs) ← freshVals stem ps
    Build.startBlock l.label ds
    return vs

/-- Open the block `l`, which takes one value, and return it.  The value is named after `stem`
if it is given, and otherwise `v`, which `let%` may rename. -/
def startBlock₁ {t : TypeExpr env} (l : BlockRef env [t]) (stem : Option Name := none) :
    m (Val env t) :=
  liftBuild do
    let d ← freshVal (stem.getD (.str .base "v")) t stem.isSome
    Build.startBlock l.label #[d]
    return ⟨d.id⟩

/-- A fresh value of type `t` named after `stem`, as a block's or a function's parameter. -/
def param (stem : Name) (t : TypeExpr env) : m (ValDecl env × Val env t) :=
  liftBuild do
    let d ← freshVal stem t
    return (d, ⟨d.id⟩)

/-- Close the open block by leaving the enclosing body with `v`.  Lean does not check `t`
against the body's result type; a region's body has its exit as a `Target [r]`, which it does. -/
def ret [base ⊑ env] {t : TypeExpr env} (v : Val env t) (info : Option α := none) : m Unit :=
  liftBuild (Build.ret v.id info)

/-- The integer constant `i`. -/
def int [base ⊑ env] (stem : Name) (i : Int) (info : Option α := none) :
    m (Val env Base.Int) :=
  liftBuild (Val.mk <$> emitConst stem (.int i) info)

/-- The Boolean constant `b`. -/
def bool [base ⊑ env] (stem : Name) (b : Bool) (info : Option α := none) :
    m (Val env Base.Bool) :=
  liftBuild (Val.mk <$> emitConst stem (.bool b) info)

/-- The string constant `s`. -/
def str [base ⊑ env] (stem : Name) (s : String) (info : Option α := none) :
    m (Val env Base.String) :=
  liftBuild (Val.mk <$> emitConst stem (.str s) info)

/-- The float constant `f`. -/
def float [base ⊑ env] (stem : Name) (f : Float) (info : Option α := none) :
    m (Val env Base.Float64) :=
  liftBuild (Val.mk <$> emitConst stem (.float f) info)

/-- The unit constant. -/
def unit [base ⊑ env] (stem : Name) (info : Option α := none) :
    m (Val env Base.Unit) :=
  liftBuild (Val.mk <$> emitConst stem .unit info)

/-- A code pointer to `target`, at the untyped `base.Code`. -/
def code [base ⊑ env] (target : Name) (info : Option α := none) :
    m (Val env Base.Code) :=
  liftBuild (Val.mk <$> emitFunc target Base.Code info)

/-- `let% x ← e`: `let x ← e`, with the value or block `e` returns named after `x` if `e` made
it and nothing named it (`Build.named`).  `let% mut x ← e` and `let% x : T ← e` are `let`'s. -/
scoped syntax (name := letNamed) "let% " ("mut ")? ident (" : " term)? " ← " term : doElem

macro_rules
  | `(doElem| let% $[mut%$mut?]? $x:ident $[: $t?]? ← $e) => do
    let stem := x.getId.eraseMacroScopes.toString (escape := false)
    let e ← `(Strata.Dyn.Build.named $(Lean.quote stem) $e)
    match mut? with
    | some _ => `(doElem| let mut $x:ident $[: $t?]? ← $e:term)
    | none => `(doElem| let $x:ident $[: $t?]? ← $e:term)

end Emit

end

/-! ## The base's emitters

`Base` is declared below the builder, so its emitters are generated here, from the record
its `environment` command left. -/

dyn_emitters Base

end Strata.Dyn
