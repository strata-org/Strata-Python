/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Base
import StrataMantle.Env.WF

set_option autoImplicit false

/-!
# An environment-driven SSA IR

Control and data flow for any language whose operations and types come from an `Env`.
`StrataMantle/WF.lean` states its well-formedness.  A `Module.Raw` is a module as built; a
`Module` (`StrataMantle/WF.lean`) is one with its well-formedness proof.

Every level carries an annotation type `α`, as the DDM-generated AST does: a front end
instantiates it at `SourceRange`, a test at `Unit`, and `map` moves between them.
Well-formedness does not mention it.

An operation may carry *regions*: nested bodies of blocks, MLIR-style, that its signature
declares, and *successors*: blocks it may transfer to.  A raising operation declares an `err`
successor, so where a failure goes is an ordinary transfer.  A *terminal* operation ends its
block: every block ends with one, a `Terminator`.  Control flow is terminal operations like
any other: the base declares `jump`, `branch` and `unreachable`, and each datatype `T` a
`T.case` that eliminates it.  Returning is a `jump` to `Label.exit`.  A datatype's constructor
is an operation too, applied at explicit type arguments through its `InsnRef`.
`Instruction`, `Terminator`, `Block` and `Region` are one nested inductive.  A block
is named by its `Label`, not its position, so emitting, reordering or dropping blocks never
rewrites a transfer.
-/

namespace Strata.Mantle

public section

/-! ## Values -/

-- Exposed, so that the kernel decides equality of ids, labels and points in other modules.
@[expose] section

/-- An SSA value reference.  Ids are unique within a function. -/
structure ValId where
  id : Nat
deriving Inhabited, Repr, BEq, Hashable, DecidableEq

/-- `ValId`'s derived `==` is equality. -/
instance : LawfulBEq ValId where
  eq_of_beq {a b} h := by
    cases a; cases b
    simp only [BEq.beq, instBEqValId.beq, decide_eq_true_eq] at h
    rw [h]
  rfl {a} := by cases a; simp [BEq.beq, instBEqValId.beq]

/-- A definition site: an id and the type of what it defines. -/
structure ValDecl (env : Env Unit) where
  id   : ValId
  type : TypeExpr env

/-! ## Control transfers -/

/-- A block's name.  Unique within a function, counting every region's blocks, and never
renumbered. -/
structure Label where
  name : Name
deriving DecidableEq, Hashable

/-- A point of a body: the block `label` after its first `count` instructions.
`⟨l, 0⟩` is where the block starts, and its instruction `k` runs at `⟨l, k⟩`, its terminator at
`⟨l, n⟩` for `n` instructions. -/
structure Point where
  label : Label
  count : Nat
deriving DecidableEq

end

instance : Inhabited Label := ⟨⟨.base⟩⟩

/-- The exit of a function or region body: a jump to it leaves the body, with the body's
result as its one argument.  No block carries it. -/
@[expose] def Label.exit : Label := ⟨.base⟩

/-- Where to go and what to pass: a block label with a prefix of its arguments already
bound.  What the target still expects is what the operation taking the transfer supplies: its
successor's declared payload. -/
structure BlockValue where
  target : Label
  args   : Array ValId
deriving Inhabited, BEq

/-! ## Instructions -/

/-- The builtin constants.  Their types come from the base, so a literal needs no
declaration in the environment. -/
inductive Const where
  | unit
  | bool  (b : Bool)
  | int   (i : Int)
  | float (f : Float)
  | str   (s : String)
  /-- A code pointer to the function `target` of the enclosing module. -/
  | func  (target : Name)
deriving Inhabited, Repr

/-- The type the base gives a constant, in an environment that refines the base: a literal's
type, and for a function reference the untyped `base.Code`.  A function reference may instead
have its target's `Func.codeType`, which the module decides (`Module.Raw.WF`). -/
@[expose] def Const.typeOf {env : Env Unit} [base ⊑ env] : Const → TypeExpr env
  | .unit    => Base.Unit.ty
  | .bool _  => Base.Bool.ty
  | .int _   => Base.Int.ty
  | .float _ => Base.Float64.ty
  | .str _   => Base.String.ty
  | .func _  => Base.Code.ty

mutual

/-- A literal, or an application of an operation the signature declares, a datatype's
constructor included.  Each names its result; an operation with nothing to return returns
`Unit`.

`succs` are where the operation may transfer instead of falling through, one per successor
its signature declares and in that order; each receives that successor's declared values.
A raising operation's `err` successor is its handler, and its result is what it returns on
success.

`regions` are the operation's nested bodies, one per region its signature declares and in
that order.

`typeArgs` are the operation's type arguments, one per type parameter of its signature, each of
the parameter's kind: a type, or a list of types.

A terminal operation is not an `Instruction` but a `Terminator`. -/
inductive Instruction (env : Env Unit) (α : Type) where
  | const (info : α) (result : ValDecl env) (c : Const)
  | apply (info : α) (result : ValDecl env)
          {isig : InsnSig env} (r : InsnRef env isig)
          (typeArgs : TypeArgs env isig.scope)
          (args : Array ValId)
          (succs : Array BlockValue)
          (regions : Array (Region env α))

/-- How a block ends: an application of a terminal operation, one its signature marks
`terminal`.  It never falls through, so it defines no result, and it leaves by one of its
successors, each receiving that successor's declared values.  Its operands, successors and
regions are as for `Instruction.apply`. -/
inductive Terminator (env : Env Unit) (α : Type) where
  | apply (info : α) {isig : InsnSig env} (r : InsnRef env isig)
          (typeArgs : TypeArgs env isig.scope)
          (args : Array ValId)
          (succs : Array BlockValue)
          (regions : Array (Region env α))

/-- A basic block: one entry, and every exit named by the terminator. -/
structure Block (env : Env Unit) (α : Type) where
  label  : Label
  params : Array (ValDecl env)
  instrs : Array (Instruction env α)
  term   : Terminator env α
  info   : α

/-- An operation's nested body: blocks, `blocks[0]` the entry, whose parameters are the
region's arguments.

Control stays inside: a transfer names a block of the same region, or the region's own
`Label.exit`, which leaves it with the value passed.  Values in scope at the owning
instruction are visible inside, and value ids are unique across the whole function. -/
structure Region (env : Env Unit) (α : Type) where
  blocks : Array (Block env α)

end

/-- The value an instruction defines.  Every instruction defines one.  Values its regions
define are not included. -/
@[expose] def Instruction.result {env : Env Unit} {α : Type} : Instruction env α → ValDecl env
  | .const _ d _ => d
  | .apply _ d .. => d

/-- An instruction's operands. -/
@[expose] def Instruction.args {env : Env Unit} {α : Type} : Instruction env α → Array ValId
  | .const .. => #[]
  | .apply _ _ _ _ args _ _ => args

/-- Where an instruction may transfer instead of falling through. -/
@[expose] def Instruction.succs {env : Env Unit} {α : Type} :
    Instruction env α → Array BlockValue
  | .const .. => #[]
  | .apply _ _ _ _ _ succs _ => succs

/-- An instruction's regions. -/
@[expose] def Instruction.regions {env : Env Unit} {α : Type} :
    Instruction env α → Array (Region env α)
  | .const .. => #[]
  | .apply _ _ _ _ _ _ regions => regions

/-- A terminator's operands. -/
@[expose] def Terminator.args {env : Env Unit} {α : Type} : Terminator env α → Array ValId
  | .apply _ _ _ args _ _ => args

/-- Where a terminator may transfer. -/
@[expose] def Terminator.succs {env : Env Unit} {α : Type} :
    Terminator env α → Array BlockValue
  | .apply _ _ _ _ succs _ => succs

/-- A terminator's regions. -/
@[expose] def Terminator.regions {env : Env Unit} {α : Type} :
    Terminator env α → Array (Region env α)
  | .apply _ _ _ _ _ regions => regions

/-! ## Control flow

The base's terminal operations, as terminators.  A `T.case` is applied as any other terminal
operation is. -/

/-- `jump k`: continue at `k`. -/
@[expose] def Terminator.jump {env : Env Unit} [base ⊑ env] {α : Type} (info : α)
    (k : BlockValue) : Terminator env α :=
  .apply info Base.jump ⟨#[], rfl⟩ #[] #[k] #[]

/-- `branch cond t f`: continue at `t` if `cond` holds, else at `f`. -/
@[expose] def Terminator.branch {env : Env Unit} [base ⊑ env] {α : Type} (info : α)
    (cond : ValId) (t f : BlockValue) : Terminator env α :=
  .apply info Base.branch ⟨#[], rfl⟩ #[cond] #[t, f] #[]

/-- `unreachable`: control never gets here. -/
@[expose] def Terminator.unreachable {env : Env Unit} [base ⊑ env] {α : Type} (info : α) :
    Terminator env α :=
  .apply info Base.unreachable ⟨#[], rfl⟩ #[] #[] #[]

/-- `ret v`: leave the enclosing body with `v`, a jump to `Label.exit`. -/
@[expose] def Terminator.ret {env : Env Unit} [base ⊑ env] {α : Type} (info : α) (v : ValId) :
    Terminator env α :=
  .jump info ⟨Label.exit, #[v]⟩

/-- A function.  `blocks[0]` is the entry, and its parameters are the function's.  Its
top-level blocks are a region in all but name: transfers stay among them, and a jump to
`Label.exit` returns from the function.

`names[i]` is the name value `i` prints as, `%x.1`.  A well-formed function names every value
it defines, no two alike. -/
structure Func (env : Env Unit) (α : Type) where
  name    : Name
  retType : TypeExpr env
  blocks  : Array (Block env α)
  names   : Array Name
  info    : α

/-- The type of a code pointer to `fn`: `base.Fn` of its entry block's parameter types and
its return type.  A function with no entry block takes nothing. -/
@[expose] def Func.codeType {env : Env Unit} [base ⊑ env] {α : Type} (fn : Func env α) :
    TypeExpr env :=
  Base.Fn.ty (.ofTypes ((fn.blocks[0]?.map (·.params.map (·.type))).getD #[])) fn.retType

/-- An unchecked module, typed against one environment that refines the base.  A `Module` is
one with its well-formedness proof. -/
structure Module.Raw (env : Env Unit) [base ⊑ env] (α : Type) where
  name  : Name
  funcs : Array (Func env α)
  info  : α

/-! ## Annotations

`map` changes the annotation type and touches nothing else.  It descends into regions;
`Block.map_instrs` and `Region.map_blocks` state it per field. -/

mutual

@[expose] def Terminator.map {env : Env Unit} {α β : Type} (f : α → β) :
    Terminator env α → Terminator env β
  | .apply info r typeArgs args succs ⟨regions⟩ =>
    .apply (f info) r typeArgs args succs ⟨Region.mapList f regions⟩

@[expose] def Instruction.map {env : Env Unit} {α β : Type} (f : α → β) :
    Instruction env α → Instruction env β
  | .const info result c => .const (f info) result c
  | .apply info result r typeArgs args succs ⟨regions⟩ =>
    .apply (f info) result r typeArgs args succs ⟨Region.mapList f regions⟩

/-- `Instruction.map` on each. -/
@[expose] def Instruction.mapList {env : Env Unit} {α β : Type} (f : α → β) :
    List (Instruction env α) → List (Instruction env β)
  | [] => []
  | i :: is => i.map f :: Instruction.mapList f is

@[expose] def Block.map {env : Env Unit} {α β : Type} (f : α → β) :
    Block env α → Block env β
  | ⟨label, params, ⟨instrs⟩, term, info⟩ =>
    ⟨label, params, ⟨Instruction.mapList f instrs⟩, term.map f, f info⟩

/-- `Block.map` on each. -/
@[expose] def Block.mapList {env : Env Unit} {α β : Type} (f : α → β) :
    List (Block env α) → List (Block env β)
  | [] => []
  | b :: bs => b.map f :: Block.mapList f bs

@[expose] def Region.map {env : Env Unit} {α β : Type} (f : α → β) :
    Region env α → Region env β
  | ⟨⟨blocks⟩⟩ => ⟨⟨Block.mapList f blocks⟩⟩

/-- `Region.map` on each. -/
@[expose] def Region.mapList {env : Env Unit} {α β : Type} (f : α → β) :
    List (Region env α) → List (Region env β)
  | [] => []
  | r :: rs => r.map f :: Region.mapList f rs

end

/-- `Instruction.mapList` is `List.map`. -/
@[simp] theorem Instruction.mapList_eq {env : Env Unit} {α β : Type} (f : α → β)
    (l : List (Instruction env α)) : Instruction.mapList f l = l.map (Instruction.map f) := by
  induction l <;> simp_all [Instruction.mapList]

/-- `Block.mapList` is `List.map`. -/
@[simp] theorem Block.mapList_eq {env : Env Unit} {α β : Type} (f : α → β)
    (l : List (Block env α)) : Block.mapList f l = l.map (Block.map f) := by
  induction l <;> simp_all [Block.mapList]

/-- `Region.mapList` is `List.map`. -/
@[simp] theorem Region.mapList_eq {env : Env Unit} {α β : Type} (f : α → β)
    (l : List (Region env α)) : Region.mapList f l = l.map (Region.map f) := by
  induction l <;> simp_all [Region.mapList]

/-- Mapping a block maps each of its instructions. -/
@[simp] theorem Block.map_instrs {env : Env Unit} {α β : Type} (f : α → β) (b : Block env α) :
    (b.map f).instrs = b.instrs.map (Instruction.map f) := by
  obtain ⟨_, _, ⟨_⟩, _, _⟩ := b
  simp [Block.map]

/-- Mapping a region maps each of its blocks. -/
@[simp] theorem Region.map_blocks {env : Env Unit} {α β : Type} (f : α → β) (r : Region env α) :
    (r.map f).blocks = r.blocks.map (Block.map f) := by
  obtain ⟨⟨_⟩⟩ := r
  simp [Region.map]

@[expose] def Func.map {env : Env Unit} {α β : Type} (f : α → β) (fn : Func env α) :
    Func env β where
  name    := fn.name
  retType := fn.retType
  blocks  := fn.blocks.map (Block.map f)
  names   := fn.names
  info    := f fn.info

@[expose] def Module.Raw.map {env : Env Unit} [base ⊑ env] {α β : Type} (f : α → β)
    (m : Module.Raw env α) : Module.Raw env β where
  name  := m.name
  funcs := m.funcs.map (Func.map f)
  info  := f m.info

end

end Strata.Mantle
