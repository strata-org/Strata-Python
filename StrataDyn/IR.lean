/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# An environment-driven SSA IR

Control and data flow for any language whose operations and types come from an `Env`.
`StrataDyn/WF.lean` states its well-formedness.  A `Module.Raw` is a module as built; a
`Module` (`StrataDyn/WF.lean`) is one with its well-formedness proof.

A module also has *ghosts* (`Ghost`): cells that only contracts can name, each with an optional
initializer and invariant, which are regions too.

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

namespace Strata.Dyn

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
deriving DecidableEq

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

/-- What fills one of an operation's successors: a block label with a prefix of its arguments
already bound.  The operation supplies the rest, its successor's declared payload: the bound
arguments come first, and the payload fills the block's remaining parameters, in order.  (MLIR's
`SuccessorOperands` puts the values the operation produces first instead.) -/
structure Target.Raw where
  label : Label
  args  : Array ValId
deriving Inhabited, BEq

/-- `k`, with its next argument bound to `v`. -/
@[inline] def Target.Raw.bind (k : Target.Raw) (v : ValId) : Target.Raw :=
  { k with args := k.args.push v }

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
  /-- The cell of the ghost `name` of the enclosing module (`Ghost`): a `base.Ref` of the
  ghost's type.  Only a contract may use it. -/
  | ghost (name : Name)
deriving Inhabited, Repr

/-- The type the base gives a literal, in an environment that refines the base.  A function
reference has none: it has its target's `Func.codeType`, which the module decides
(`Module.Raw.WF`).  A ghost reference has none either: it has the type of its ghost's cell,
which the module decides too. -/
@[expose] def Const.typeOf? {env : Env Unit} [base ≼ env] : Const → Option (TypeExpr env)
  | .unit    => some Base.Unit
  | .bool _  => some Base.Bool
  | .int _   => some Base.Int
  | .float _ => some Base.Float64
  | .str _   => some Base.String
  | .func _  => none
  | .ghost _ => none

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
          (succs : Array Target.Raw)
          (regions : Array (Region env α))

/-- How a block ends: an application of a terminal operation, one its signature marks
`terminal`.  It never falls through, so it defines no result, and it leaves by one of its
successors, each receiving that successor's declared values.  Its operands, successors and
regions are as for `Instruction.apply`. -/
inductive Terminator (env : Env Unit) (α : Type) where
  | apply (info : α) {isig : InsnSig env} (r : InsnRef env isig)
          (typeArgs : TypeArgs env isig.scope)
          (args : Array ValId)
          (succs : Array Target.Raw)
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
    Instruction env α → Array Target.Raw
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
    Terminator env α → Array Target.Raw
  | .apply _ _ _ _ succs _ => succs

/-- A terminator's regions. -/
@[expose] def Terminator.regions {env : Env Unit} {α : Type} :
    Terminator env α → Array (Region env α)
  | .apply _ _ _ _ _ regions => regions

/-! ## Control flow

The base's terminal operations, as terminators.  A `T.case` is applied as any other terminal
operation is. -/

/-- `jump k`: continue at `k`. -/
@[expose] def Terminator.jump {env : Env Unit} [base ≼ env] {α : Type} (info : α)
    (k : Target.Raw) : Terminator env α :=
  .apply info Base.jump.ref ⟨#[], rfl⟩ #[] #[k] #[]

/-- `branch cond t f`: continue at `t` if `cond` holds, else at `f`. -/
@[expose] def Terminator.branch {env : Env Unit} [base ≼ env] {α : Type} (info : α)
    (cond : ValId) (t f : Target.Raw) : Terminator env α :=
  .apply info Base.branch.ref ⟨#[], rfl⟩ #[cond] #[t, f] #[]

/-- `unreachable`: control never gets here. -/
@[expose] def Terminator.unreachable {env : Env Unit} [base ≼ env] {α : Type} (info : α) :
    Terminator env α :=
  .apply info Base.unreachable.ref ⟨#[], rfl⟩ #[] #[] #[]

/-- `ret v`: leave the enclosing body with `v`, a jump to `Label.exit`. -/
@[expose] def Terminator.ret {env : Env Unit} [base ≼ env] {α : Type} (info : α) (v : ValId) :
    Terminator env α :=
  .jump info ⟨Label.exit, #[v]⟩

/-- A `requires` or `ensures` clause of a contract: a region that returns a `base.Bool`.  A
`free` clause is assumed and never checked; only an extern function's `ensures` clauses are
free.  `message` names the clause in diagnostics, and for a free clause says where the trust
comes from, such as "admitted postcondition of 'f'". -/
structure Clause (env : Env Unit) (α : Type) where
  region  : Region env α
  free    : Bool := false
  message : Option String := none

/-- An entry of a `reads` or `writes` frame: a set of locations.  A `cell` names a parameter of
type `base.Ref`, and stands for the contents of that cell.  A `region` is a *frame region*: it
takes no arguments, sees the function's parameters as a clause does, and returns a `base.Loc`. -/
inductive FrameEntry (env : Env Unit) (α : Type) where
  | cell (v : ValId)
  | region (r : Region env α)

/-- The cell the entry names, if it is a `cell`. -/
@[expose] def FrameEntry.cell? {env : Env Unit} {α : Type} : FrameEntry env α → Option ValId
  | .cell v => some v
  | .region _ => none

/-- The entry's region, if it is a `region`. -/
@[expose] def FrameEntry.region? {env : Env Unit} {α : Type} :
    FrameEntry env α → Option (Region env α)
  | .cell _ => none
  | .region r => some r

/-- A function's contract: what a caller must establish before a call, and what the function
establishes when it returns.  Most functions have none.

A `requires` or `ensures` clause is a region that returns a `base.Bool` and sees the function's
parameters: a `requires` clause takes no arguments, and an `ensures` clause takes the function's
result.  A `requires` clause is a condition that the caller establishes at each call, in the
state at the call.  An `ensures` clause, in the state at return, is a promise that holds at every
exit of a defined function; a `free` one is assumed after every call and never checked.  Only an
`ensures` clause applies `base.old`, which reads the state at the call.  No clause changes the
state.  The clauses are evaluated in order, the `requires` clauses at the call and the `ensures`
clauses at an exit, each only when every earlier clause returned true.  A failure in a clause
gives `false`, or `true` in a `free` one, so a failure never makes a clause hold, nor a free
clause assume anything.

A `reads` or `writes` clause is a frame: the union of its entries' sets of locations, each entry a
cell among the parameters or a frame region (`FrameEntry`).  A frame region runs in the state at
the call, after the `requires` clauses returned true, so the set is fixed at the call.  Each
failure in it goes to a block that ends in `unreachable`.  At a call where it fails, the frame is
not well defined and states nothing.  At every exit, each location that existed at the call and
is outside the `writes` frame holds the value it held at the call.  Every read that the call
makes of a location that existed at the call is of a location in the `reads` frame.  State
allocated during the call is not constrained.  Without a `writes` frame, the function may change
any location, and without a `reads` frame, it may read any.  An extern function's frames are
trusted. -/
structure Contract (env : Env Unit) (α : Type) where
  requires : Array (Clause env α) := #[]
  ensures  : Array (Clause env α) := #[]
  reads    : Option (Array (FrameEntry env α)) := none
  writes   : Option (Array (FrameEntry env α)) := none

/-- The cells a frame names, in order. -/
@[expose] def FrameEntry.cellsOf {env : Env Unit} {α : Type}
    (frame : Option (Array (FrameEntry env α))) : List ValId :=
  (frame.getD #[]).toList.filterMap FrameEntry.cell?

/-- The regions of a frame, in order. -/
@[expose] def FrameEntry.regionsOf {env : Env Unit} {α : Type}
    (frame : Option (Array (FrameEntry env α))) : List (Region env α) :=
  (frame.getD #[]).toList.filterMap FrameEntry.region?

/-- The regions of a contract's frames, in the order they print: the `reads` frame's, then the
`writes` frame's. -/
@[expose] def Contract.frameRegions {env : Env Unit} {α : Type} (c : Contract env α) :
    List (Region env α) :=
  FrameEntry.regionsOf c.reads ++ FrameEntry.regionsOf c.writes

/-- The regions of a contract, in the order they print: those of its `requires` and `ensures`
clauses, then its frame regions. -/
@[expose] def Contract.regions {env : Env Unit} {α : Type} (c : Contract env α) :
    List (Region env α) :=
  c.requires.toList.map (·.region) ++ c.ensures.toList.map (·.region) ++ c.frameRegions

/-- A function: its signature, its contract and, unless it is `extern`, its body.

A defined function's `blocks[0]` is the entry, and its parameters are the function's `params`.
Its top-level blocks are a region in all but name: transfers stay among them, and a jump to
`Label.exit` returns from the function.  An extern function has a signature and a contract, and
no blocks: the signature and the contract are all that a caller knows of it.  Its parameters
get the first ids, `0, 1, …`, in the order they are declared.

`names[i]` is the name value `i` prints as, `%x.1`.  A well-formed function names every value
it defines, no two alike, its contract's included. -/
structure Func (env : Env Unit) (α : Type) where
  name     : Name
  params   : Array (ValDecl env)
  retType  : TypeExpr env
  extern   : Bool := false
  blocks   : Array (Block env α)
  contract : Contract env α := {}
  names    : Array Name
  info     : α

/-- The type of a code pointer to `fn`: `base.Fn` of its parameters' types and its return
type. -/
@[expose] def Func.codeType {env : Env Unit} [base ≼ env] {α : Type} (fn : Func env α) :
    TypeExpr env :=
  Base.Fn (TypeList.ofTypes (fn.params.map (·.type))) fn.retType

/-- A ghost: a cell of the module that only contracts can name.  `type` is the type of its
contents, and `const ghost` (`Const.ghost`) names its cell, a `base.Ref(type)`.

* `init`, the *initializer*, takes no arguments and returns the first contents.  The
  initializers run once, before any function, in the order the ghosts are declared.  A ghost
  without one starts with some value that satisfies its invariant.
* `invariant` takes the contents and returns a `base.Bool`: it holds in every state.  It is
  trusted, so an initializer whose value does not satisfy it makes the module's trusted
  assumptions contradict themselves.

Each of these regions is a contract region, sees only its own values, and refers to no function.
An initializer names only the ghosts declared before its own, and an invariant names no ghost.  A
ghost changes only at a call whose `writes` frame covers its cell, or that has no `writes`
frame.

`names[i]` is the name value `i` of the ghost's regions prints as.  The values of the
initializer come first. -/
structure Ghost (env : Env Unit) (α : Type) where
  name      : Name
  type      : TypeExpr env
  init      : Option (Region env α) := none
  invariant : Option (Region env α) := none
  names     : Array Name := #[]
  info      : α

/-- The regions of a ghost, in the order they print: its initializer, then its invariant. -/
@[expose] def Ghost.regions {env : Env Unit} {α : Type} (g : Ghost env α) : List (Region env α) :=
  g.init.toList ++ g.invariant.toList

/-- An unchecked module, typed against one environment that refines the base.  A `Module` is
one with its well-formedness proof.  Its ghosts come first, as they print. -/
structure Module.Raw (env : Env Unit) [base ≼ env] (α : Type) where
  name   : Name
  ghosts : Array (Ghost env α) := #[]
  funcs  : Array (Func env α)
  info   : α

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

/-- `Region.map` on the clause's region. -/
@[expose] def Clause.map {env : Env Unit} {α β : Type} (f : α → β) (c : Clause env α) :
    Clause env β where
  region  := c.region.map f
  free    := c.free
  message := c.message

/-- `Region.map` on the entry's region, if it has one. -/
@[expose] def FrameEntry.map {env : Env Unit} {α β : Type} (f : α → β) :
    FrameEntry env α → FrameEntry env β
  | .cell v => .cell v
  | .region r => .region (r.map f)

@[expose] def Func.map {env : Env Unit} {α β : Type} (f : α → β) (fn : Func env α) :
    Func env β where
  name     := fn.name
  params   := fn.params
  retType  := fn.retType
  extern   := fn.extern
  blocks   := fn.blocks.map (Block.map f)
  contract := { requires := fn.contract.requires.map (Clause.map f)
                ensures  := fn.contract.ensures.map (Clause.map f)
                reads    := fn.contract.reads.map (·.map (FrameEntry.map f))
                writes   := fn.contract.writes.map (·.map (FrameEntry.map f)) }
  names    := fn.names
  info     := f fn.info

@[expose] def Ghost.map {env : Env Unit} {α β : Type} (f : α → β) (g : Ghost env α) :
    Ghost env β where
  name      := g.name
  type      := g.type
  init      := g.init.map (Region.map f)
  invariant := g.invariant.map (Region.map f)
  names     := g.names
  info      := f g.info

@[expose] def Module.Raw.map {env : Env Unit} [base ≼ env] {α β : Type} (f : α → β)
    (m : Module.Raw env α) : Module.Raw env β where
  name   := m.name
  ghosts := m.ghosts.map (Ghost.map f)
  funcs  := m.funcs.map (Func.map f)
  info   := f m.info

end

end Strata.Dyn
