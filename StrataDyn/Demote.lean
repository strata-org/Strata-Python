/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Shape
public import StrataDyn.RefToReg

set_option autoImplicit false

/-!
# Demoting block parameters to private cells

`demote` gives every parameter `%p : τ` of every block but a function's entry a cell, so that
no other block takes parameters.  The entry block makes the cell, holding the default value
that the caller gives for `τ`; each jump to the block writes its argument to the cell and
passes nothing; and the block reads the cell where it starts, as `%p`, so the parameter's uses
stay as they are.  The writes of a jump pass values, not cells, so a jump that permutes
parameters needs no temporary.  Contracts, extern functions and ghosts stay as they are.

A default (`Demote.Default`) is a literal or a pure operation applied to defaults.  No run
reads it, but the instructions that compute it run in the entry block; that they do not fault
is the caller's obligation.

The input shape (`Demotable`) is plain control with bare branches, which case lowering
provides (`demotable_cased`).  The pass takes the proof and does not decide it: with it, the
writes of an edge go before the edge's jump, and the result has the input's blocks.  The result
(`Demoted`) is in plain control without block parameters by construction.  That every cell is
private (`PrivateCells`) and that the result is well formed are decided on what the pass
built.  The first is meant to fail only for a reference that the input already had and that is
not a private cell, or that a default makes; the second only for a default that is not of its
type.  Neither is proved.

**What is proved.** `StrataDyn/DemoteSound/` proves, by ref-to-reg's theorems and under their
hypotheses, that a linked module with a certificate of demotion (`DemotionOK`) shows the
behaviour of its *padded original*: the input with the cells' defaults and `refNew`s added to
its functions' entry blocks.  It is not proved that the pass's output, linked, has the
certificate, nor that the padded original runs as the input, whose cells are numbered
differently.  `docs/Dyn.md` §8 says what the certificate asks and what the theorems assume.

The cost grows with the instructions and edges, with a default built for each cell, and with the
closing checks of private cells and well-formedness; lookups are hash maps.
-/

namespace Strata.Dyn

public section

namespace Demote

/-- A value that reads no state: a literal, or a `pure` operation applied to defaults, each with
its type, such as a datatype's constructor applied to defaults of its fields:
`base.error[e, a]` of a default of `e` for `base.Except(e, a)`.  The instructions that compute
it run in the entry block of each function that needs it, so they must not be seen to run:
the constructor takes the proof that the operation is `pure`, and the caller answers for an
operation that can fault. -/
inductive Default (env : Env Unit) where
  | const (c : Const)
  | apply {isig : InsnSig env} (r : InsnRef env isig) (typeArgs : TypeArgs env isig.scope)
      (pure : isig.effect = .pure) (args : List (TypeExpr env × Default env))

/-- A default value for each type that has one: what a cell of that type holds until its first
write.  The value given for a type must be of that type; `demote` rejects a function that gets
one that is not (`Error.illFormed`). -/
abbrev Defaults (env : Env Unit) := TypeExpr env → Option (Default env)

/-- The defaults every environment has, the literals: `()`, `false`, `0`, `0.0` and `""`. -/
def Defaults.literals {env : Env Unit} [base ≼ env] : Defaults env := fun τ =>
  ([.unit, .bool false, .int 0, .float 0, .str ""] : List Const).find? (·.typeOf? = some τ)
    |>.map .const

/-- Why `demote` rejects a function. -/
inductive Error where
  /-- The type of the parameter named `param`, of the block `block`, has no default value. -/
  | noDefault (param : Name) (block : Label)
  /-- A reference of the function is not a private cell (`Func.PrivateCells`). -/
  | notPrivate
  /-- The demoted function is not well formed: a default value is not of its type. -/
  | illFormed
deriving DecidableEq

end Demote

/-- The shape `demote` assumes: plain control, and no arguments on the arms of branches. -/
@[expose] def Demotable {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α) : Prop :=
  PlainControl m ∧ BareBranches m

instance {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α) :
    Decidable (Demotable m) :=
  inferInstanceAs (Decidable (PlainControl m ∧ BareBranches m))

section
variable {env : Env Unit} [base ≼ env] {α : Type}

/-! ## Private cells

Every `base.Ref` value is a *private cell*: the result of a `refNew` in the entry block, used
only as the cell operand of `refGet` and `refSet`, never passed as an operand, stored, returned
or passed on an edge (`RefToReg.escapingUses`, `RefToReg.termUses`).  Such a cell is a local
variable of the function.  No function takes a reference as a parameter, an extern function
included.  The instances are for compiled code: the kernel does not reduce the test of a type's
head. -/

/-- The cells of the function: the results of the `refNew`s of its entry block. -/
@[expose] def Func.entryCells (fn : Func env α) : List ValId :=
  match fn.blocks[0]? with
  | some entry => entry.instrs.toList.filterMap fun i =>
      match RefToReg.cellOp? i with
      | some (.new c _) => some c
      | _ => none
  | none => []

/-- The block keeps the cells that `isCell` holds of private: none of its parameters is a
reference, every reference it defines (`TypeExpr.isRef`) is one of the cells, and no cell
escapes through an instruction's operands or edges or through the terminator. -/
@[expose] def Block.PrivateCellsIn (isCell : ValId → Bool) (b : Block env α) : Prop :=
  (∀ p ∈ b.params, p.type.isRef = false) ∧
  (∀ i ∈ b.instrs, i.result.type.isRef = true → isCell i.result.id = true) ∧
  (∀ i ∈ b.instrs, ∀ u ∈ RefToReg.escapingUses i, isCell u = false) ∧
  (∀ u ∈ RefToReg.termUses b.term, isCell u = false)

instance (isCell : ValId → Bool) (b : Block env α) : Decidable (b.PrivateCellsIn isCell) :=
  inferInstanceAs (Decidable ((∀ p ∈ b.params, p.type.isRef = false) ∧
    (∀ i ∈ b.instrs, i.result.type.isRef = true → isCell i.result.id = true) ∧
    (∀ i ∈ b.instrs, ∀ u ∈ RefToReg.escapingUses i, isCell u = false) ∧
    (∀ u ∈ RefToReg.termUses b.term, isCell u = false)))

/-- Every reference of the function is a private cell: no parameter is a reference, also of a
function without a body, and every block keeps the function's cells private
(`Block.PrivateCellsIn`).  This asks less than ref-to-reg does of a cell it promotes
(`RefToReg.candidates`), which also needs the result of each write unused; no lemma relates
the two. -/
@[expose] def Func.PrivateCells (fn : Func env α) : Prop :=
  (∀ p ∈ fn.params, p.type.isRef = false) ∧
    ∀ b ∈ fn.blocks, b.PrivateCellsIn fn.entryCells.contains

/-- Decided with the cells in a hash set, so that the cost does not grow with their number
times the body's size. -/
instance (fn : Func env α) : Decidable fn.PrivateCells :=
  let cells : Std.HashSet ValId := .ofList fn.entryCells
  decidable_of_iff ((∀ p ∈ fn.params, p.type.isRef = false) ∧
      ∀ b ∈ fn.blocks, b.PrivateCellsIn cells.contains) (by
    rw [show cells.contains = fn.entryCells.contains from
      funext fun _ => Std.HashSet.contains_ofList]
    exact Iff.rfl)

/-- Every reference of every function's body is a private cell. -/
@[expose] def PrivateCells (m : Module.Raw env α) : Prop := ∀ fn ∈ m.funcs, fn.PrivateCells

instance (m : Module.Raw env α) : Decidable (PrivateCells m) :=
  inferInstanceAs (Decidable (∀ fn ∈ m.funcs, fn.PrivateCells))

end

/-- The shape `demote` establishes: plain control, parameters only on entry blocks, and every
reference a private cell. -/
@[expose] def Demoted {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α) : Prop :=
  PlainControl m ∧ NoBlockParams m ∧ PrivateCells m

instance {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α) :
    Decidable (Demoted m) :=
  inferInstanceAs (Decidable (PlainControl m ∧ NoBlockParams m ∧ PrivateCells m))

namespace Demote

variable {env : Env Unit} [base ≼ env] {α : Type}

/-- The pass's monad: the names of the function's values, to which it adds, and a rejection. -/
private abbrev M := StateT ValueNames (Except Error)

/-- A new value, named `stem.k`. -/
private def fresh (stem : Name) : M ValId := modifyGet (·.fresh stem)

/-- An instruction that falls through. -/
private abbrev Plain (env : Env Unit) (α : Type) := { i : Instruction env α // i.Plain }

mutual

/-- Append the definition of `d` as the default `v` to `pre`: each operand's definition first,
then `d`'s own, preserving the evaluation and fresh-name order. -/
private def defaultOf (info : α) (d : ValDecl env) (pre : Array (Plain env α)) :
    Default env → M (Array (Plain env α))
  | .const c => return pre.push ⟨.const info d c, rfl, rfl⟩
  | .apply r typeArgs _ args => do
    let (pre, operands) ← defaultsOf info pre #[] args
    return pre.push ⟨.apply info d r typeArgs operands #[] #[], rfl, rfl⟩

/-- Accumulate the definitions and operands of `vs` in order. Forward-growing buffers avoid
copying the remaining suffix at each argument of a wide default. -/
private def defaultsOf (info : α) (pre : Array (Plain env α)) (operands : Array ValId) :
    List (TypeExpr env × Default env) → M (Array (Plain env α) × Array ValId)
  | [] => return (pre, operands)
  | (τ, v) :: vs => do
    let x ← fresh (.str .base "default")
    let pre ← defaultOf info ⟨x, τ⟩ pre v
    defaultsOf info pre (operands.push x) vs

end

/-- `cell := base.refNew[τ](v)`. -/
private def newCell (info : α) (cell : ValId) (τ : TypeExpr env) (v : ValId) : Plain env α :=
  ⟨.apply info ⟨cell, Base.Ref τ⟩ Base.refNew.ref ⟨#[.ty τ], rfl⟩ #[v] #[] #[], rfl, rfl⟩

/-- `p := base.refGet[τ](cell)`. -/
private def readCell (info : α) (p : ValDecl env) (cell : ValId) : Plain env α :=
  ⟨.apply info p Base.refGet.ref ⟨#[.ty p.type], rfl⟩ #[cell] #[] #[], rfl, rfl⟩

/-- `u := base.refSet[τ](cell, v)`. -/
private def writeCell (info : α) (u : ValId) (τ : TypeExpr env) (cell v : ValId) : Plain env α :=
  ⟨.apply info ⟨u, Base.Unit⟩ Base.refSet.ref ⟨#[.ty τ], rfl⟩ #[cell, v] #[] #[], rfl, rfl⟩

/-- A block parameter and its cell. -/
private structure Slot (env : Env Unit) where
  param : ValDecl env
  cell : ValId

/-- The cells of each block that is not the entry, by its label, in parameter order. -/
private abbrev Cells (env : Env Unit) := Std.HashMap Label (Array (Slot env))

/-- The name of the value `v` of `fn`. -/
private def nameOf (fn : Func env α) (v : ValId) : Name := fn.names[v.id]?.getD .base

/-- A cell for each parameter of `b`, named after the parameter: `x.cell.k` for `x.n`. -/
private def slots (fn : Func env α) (b : Block env α) : M (Array (Slot env)) :=
  b.params.mapM fun d => return ⟨d, ← fresh (.str (nameOf fn d.id).splitNum.1 "cell")⟩

/-- The instructions that make the cell of `s`, a parameter of the block `owner`, holding its
type's default value. -/
private def alloc (defaults : Defaults env) (fn : Func env α) (info : α) (owner : Label)
    (s : Slot env) : M (Array (Plain env α)) := do
  let some v := defaults s.param.type | throw (.noDefault (nameOf fn s.param.id) owner)
  let d ← fresh (.str .base "default")
  return (← defaultOf info ⟨d, s.param.type⟩ #[] v).push (newCell info s.cell s.param.type d)

/-- The writes of the edge of `t`, which is in plain control, and `t` without the arguments
written: a jump to a block with cells writes each argument to its parameter's cell, and every
other terminator stays. -/
private def edge (cells : Cells env) (t : Terminator env α) (ht : t.PlainControl) :
    M (Array (Plain env α) × { t' : Terminator env α // t'.PlainControl }) :=
  match t.plain? with
  | some (.jump k) =>
    match cells[k.label]? with
    | some ss => do
      let writes ← (ss.zip k.args).mapM fun (s, a) =>
        return writeCell t.info (← fresh (.str .base "set")) s.param.type s.cell a
      return (writes, ⟨.jump t.info ⟨k.label, #[]⟩,
        by simp [Terminator.PlainControl, Terminator.plain?_jump]⟩)
    | none => return (#[], ⟨t, ht⟩)
  | _ => return (#[], ⟨t, ht⟩)

/-- `b`, in plain control, with the parameters `params`, the instructions `pre` before its own
and the writes of its edge after them. -/
private def block (cells : Cells env) (params : Array (ValDecl env)) (pre : Array (Plain env α))
    (b : Block env α) (hb : b.PlainControl) :
    M { b' : Block env α // b'.PlainControl ∧ b'.params = params } := do
  let (post, t) ← edge cells b.term hb.2
  return ⟨{ b with params, instrs := pre.map (·.val) ++ b.instrs ++ post.map (·.val), term := t },
    ⟨fun i hi => by
      simp only [Array.mem_append, Array.mem_map] at hi
      obtain (⟨p, -, rfl⟩ | hi) | ⟨p, -, rfl⟩ := hi
      · exact p.property
      · exact hb.1 i hi
      · exact p.property, t.property⟩, rfl⟩

/-- A function in the shape that `demote` establishes. -/
private abbrev Out (env : Env Unit) [base ≼ env] (α : Type) :=
  { fn' : Func env α // fn'.PlainControl ∧ fn'.NoBlockParams ∧ fn'.PrivateCells }

/-- `fn`, if every reference of it is a private cell. -/
private def check (fn : Func env α) (h : fn.PlainControl ∧ fn.NoBlockParams) :
    Except Error (Out env α) :=
  if hc : fn.PrivateCells then .ok ⟨fn, h.1, h.2, hc⟩ else .error .notPrivate

/-- `fn`, in plain control, demoted. -/
private def func (defaults : Defaults env) (fn : Func env α) (hfn : fn.PlainControl) :
    Except Error (Out env α) :=
  match hbs : fn.blocks.toList with
  | [] => check fn ⟨hfn, by simp [Func.NoBlockParams, hbs]⟩
  | entry :: rest => do
    have hin : ∀ b ∈ entry :: rest, b.PlainControl := fun b hb =>
      hfn b (Array.mem_toList_iff.mp (hbs ▸ hb))
    let demoted : M _ := do
      let owned ← rest.mapM fun b => return (b.label, ← slots fn b)
      let cells : Cells env := .ofList owned
      let allocs ← owned.toArray.flatMapM fun (owner, ss) =>
        ss.flatMapM (alloc defaults fn entry.info owner)
      let entry' ← block cells entry.params allocs entry (hin entry (.head _))
      let rest' ← rest.attach.mapM fun ⟨b, hb⟩ =>
        block cells #[] ((cells.getD b.label #[]).map fun s => readCell b.info s.param s.cell) b
          (hin b (.tail _ hb))
      return (entry', rest')
    let ((entry', rest'), s) ← demoted.run (.of fn.names)
    check { fn with blocks := (entry'.val :: rest'.map (·.val)).toArray, names := s.names }
      ⟨fun b hb => by
        simp only [List.mem_toArray, List.mem_cons, List.mem_map] at hb
        obtain rfl | ⟨r, -, rfl⟩ := hb
        · exact entry'.property.1
        · exact r.property.1,
       fun b hb => by
        simp only [List.drop_succ_cons, List.drop_zero, List.mem_map] at hb
        obtain ⟨r, -, rfl⟩ := hb
        simp [r.property.2]⟩

end Demote

/-- **Demotion**: the module `m`, which is `Demotable`, with every parameter of every block but a
function's entry demoted to a private cell that first holds its type's default value; or each
function concerned with the reason (`Demote.Error`).  The module's name, ghosts and annotation
stay. -/
def demote {env : Env Unit} [base ≼ env] {α : Type} (defaults : Demote.Defaults env)
    (m : Module env α) (h : Demotable m.raw) :
    Except (Array (Name × Demote.Error)) { m' : Module env α // Demoted m'.raw } :=
  let results := m.raw.funcs.attach.map fun ⟨fn, hfn⟩ =>
    (fn.name, Demote.func defaults fn (h.1 fn hfn))
  let errs := results.filterMap fun
    | (n, .error e) => some (n, e)
    | _ => none
  if !errs.isEmpty then .error errs else
  let funcs := results.filterMap fun
    | (_, .ok fn) => some fn
    | _ => none
  match hc : Module.Raw.check { m.raw with funcs := funcs.map (·.val) } with
  | .ok m' =>
    have hm' : ∀ fn ∈ m'.raw.funcs, fn.PlainControl ∧ fn.NoBlockParams ∧ fn.PrivateCells :=
      fun fn hfn => by
        rw [Module.Raw.raw_of_check hc] at hfn
        obtain ⟨g, -, rfl⟩ := Array.mem_map.mp hfn
        exact g.property
    .ok ⟨m', fun fn hfn => (hm' fn hfn).1, fun fn hfn => (hm' fn hfn).2.1,
      fun fn hfn => (hm' fn hfn).2.2⟩
  | .error names => .error (names.map (·, .illFormed))

end

end Strata.Dyn
