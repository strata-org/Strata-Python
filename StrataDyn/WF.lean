/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.IR
public import StrataDyn.Util.NameMap
public import StrataDyn.Util.LabelMap
public import StrataDyn.DomProps
public import StrataDyn.DomDecide
public import StrataDyn.Util.Array
public import StrataDyn.ContractRegion
public import StrataDyn.ContractRegionProps
-- The instances evaluate the environment representation at code-generation time.
import StrataDyn.Env.WF
import all StrataDyn.Util.LabelMapProps

set_option autoImplicit false

/-!
# Well-formedness of the IR

One predicate per level, each stated as an equation between what a site supplies and
what the thing it names demands:

* an `Instruction`'s operands have the types its signature demands at the type
  arguments it supplies, and its result is what that signature returns, a constructor's
  as any other operation's.  A constant has its literal's type, and a function reference a
  `base.Fn` type.  An operation is not terminal, and supplies exactly the successors and regions its signature declares: each successor is a non-entry block of
  its own region, or the region's exit, and receives exactly the parameters it declares;
  each region is well formed at the signature's region types;
* a `Terminator` is checked as an instruction's operation is, but must be terminal and
  defines no result;
* a `Block`'s instructions and terminator are well formed;
* a `Region`'s entry block takes the declared parameters, and every block is well formed
  against the region's own blocks and its exit, `Label.exit`, which takes the region's
  result;
* a `Func` is extern exactly when it has no blocks, and a defined function's entry block takes
  exactly its parameters.  It uses no label twice nor `Label.exit` at all, defines no value
  twice and names every value it defines, no two alike, counting every region and its
  contract's, and every block is well formed in the context those definitions give, its exit
  taking the function's return type; every block of every body is reachable from the body's
  entry, and some legal tree of each body puts every use in scope;
* a `Func`'s `requires` and `ensures` clauses are regions returning a `base.Bool`, a
  `requires` clause taking no arguments and an `ensures` clause the function's result.  A `reads`
  or `writes` frame names distinct parameters of type `base.Ref`, and frame regions, which take
  no arguments and return a `base.Loc`.  Each clause and frame region is well formed in the
  function's context, and is checked as a body entered where only the function's parameters are
  visible: it sees only the parameters and its own values, and the body sees none of them.  No
  instruction or terminator of a contract region (a clause, a frame region, or a region nested in
  one at any depth) applies an operation declared `writes`.  No `requires` clause is `free`; an
  extern's `ensures` clauses are all `free`, and a defined function's all checked.  A failure
  successor of a clause's own blocks goes to a failure block, which returns the clause's failure
  value, `false`, or `true` in a `free` clause, or ends in `unreachable`; one of a frame region's
  own blocks goes to a block that ends in `unreachable`; one of a region nested in a contract
  region goes to a block that ends in `unreachable` or, if the region may propagate, passes the
  failure on with `base.error`.  Every block of a contract region ends in control flow, and the
  blocks of every contract region form an acyclic graph.  Only an `ensures` clause applies
  `base.old`, at any depth, and each outermost `old` region, entered where only the parameters,
  the clause's constants and the parameters of the regions that enclose it are visible, is shaped
  and dominance-correct.  The body names no ghost, at any depth;
* a `Ghost`'s initializer takes no arguments and returns the ghost's type, and its invariant takes
  the ghost's contents and returns a `base.Bool`.  Each is well formed in the ghost's context, is
  checked as a body entered where nothing is visible, and follows the rules for a frame region:
  no operation declared `writes`, failures that go to blocks that end in `unreachable`, blocks
  that end in control flow and form an acyclic graph, and no `base.old`.  The invariant names no
  ghost, and neither region refers to a function, at any depth.  The ghost's labels and value
  names are distinct, and every value is named;
* a `Module.Raw` names no function twice, nor a ghost twice or like a function, its functions and
  ghosts are all well formed, and every function reference names one of its functions, at that
  function's code type.  Every ghost reference names one of its ghosts, at the type of the
  ghost's cell, and an initializer names only the ghosts declared before its own.

A function's rules depend on the function alone, and a ghost's on the ghost alone, so each can
be checked before its module is assembled.

A `Module` is a `Module.Raw` with its proof.  `Module.Raw.check` gives one by running the
checker, and `Module.ofChecked` gives one from checked functions and ghosts, deciding only the
module's own rules (`Module.Raw.OwnWFIn`).

`Decidable` instances decide every predicate, so `decide` is the checker.

An operand has the type its definition gives it, wherever in the function that is.  Where a
value may be used is the separate rule `Func.Scopable` (`StrataDyn/Dom.lean`): for each body
some legal dominator tree puts every use in scope, defined above it in that tree or in scope
where the enclosing region's owner runs.  The IR stores no tree; the checker computes one
(`StrataDyn/DomDecide.lean`).  So the rules reject a use before its definition, a use of a
value outside the region that defines it, and a handler's use of the result of the operation
that failed.  Every block must also be reachable from its body's entry (`Func.Reachable`).

The rules do not check:

* **Reordering.** `Ref` makes instruction order observable, and these rules say nothing about
  reordering instructions.  Effects are checked only in contract regions.

Nothing here mentions the annotation type `α`.
-/

namespace Strata.Dyn

public section

/-! ## Two combinators -/

/-- `o` succeeds, and what it yields satisfies `p`. -/
@[expose] def OptHolds {α : Type} (o : Option α) (p : α → Prop) : Prop :=
  ∃ x, o = some x ∧ p x

instance {α : Type} (o : Option α) (p : α → Prop) [DecidablePred p] :
    Decidable (OptHolds o p) :=
  match o with
  | none => .isFalse (by simp [OptHolds])
  | some x => decidable_of_iff (p x) (by simp [OptHolds])

/-- Two lookups succeed and agree.  Unlike `a = b`, it fails when neither exists. -/
@[expose] def Agrees {α : Type} (a b : Option α) : Prop := OptHolds a (fun x => b = some x)

instance {α : Type} [DecidableEq α] (a b : Option α) : Decidable (Agrees a b) :=
  inferInstanceAs (Decidable (OptHolds a (fun x => b = some x)))

/-! ## Maps the kernel reduces

The checker's maps are tries and trees, so `decide +kernel` evaluates it:

* `NatTrie` and `LabelMap` (`StrataDyn.Util.LabelMap`): maps from `Nat` and from labels;
* `Label.Distinct`: no label occurs twice, decided through a `LabelMap`;
* `NameMap` and `NameSet` (`StrataDyn.Util.NameMap`): a map and a set of names, as a 2-3
  tree on `Name.key`.  A `NameMap` holds a module's functions' code types: deciding
  `Module.Raw.WF` builds it once and looks every function reference up in it. -/

/-- No label occurs twice in `ls`. -/
@[expose] def Label.Distinct (ls : List Label) : Prop := (LabelMap.ofDistinct? ls).isSome

instance (ls : List Label) : Decidable (Label.Distinct ls) :=
  inferInstanceAs (Decidable ((LabelMap.ofDistinct? ls).isSome = true))

/-! ## The typing context

The context maps each value id to the type fixed at its definition site.  `Func.ctx?` builds
it, and fails on a repeated id.  It is function-wide: a value defined outside a region is
visible inside it. -/

/-- The type of every value a function defines, by id. -/
structure Ctx (env : Env Unit) where
  types : NatTrie (TypeExpr env)

namespace Ctx

/-- No value defined yet. -/
@[expose] def empty {env : Env Unit} : Ctx env := ⟨.leaf⟩

instance {env : Env Unit} : EmptyCollection (Ctx env) := ⟨empty⟩

/-- Record a definition, or fail if the id already has one. -/
@[expose] def define? {env : Env Unit} (ctx : Ctx env) (d : ValDecl env) : Option (Ctx env) :=
  if (ctx.types.find? d.id.id).isSome then none else some ⟨ctx.types.insert d.id.id d.type⟩

/-- The type of a value, if it is defined. -/
@[expose] def typeOf? {env : Env Unit} (ctx : Ctx env) (v : ValId) : Option (TypeExpr env) :=
  ctx.types.find? v.id

/-- The types of an operand list, if every operand is defined. -/
@[expose] def typesOf? {env : Env Unit} (ctx : Ctx env) (vs : Array ValId) :
    Option (Array (TypeExpr env)) :=
  vs.mapM ctx.typeOf?

end Ctx

/-! ## Transfers

A transfer names a block and pre-binds a prefix of its arguments; what the block
still expects is what the operation taking the transfer supplies: its successor's declared
values. -/

/-- The parameter types of the blocks a transfer may name: those of one region, or of the
function's top level, other than its entry, and the exit. -/
abbrev BlockSigs (env : Env Unit) := LabelMap (Array (TypeExpr env))

/-- The transfer targets of a body: `Label.exit`, taking the body's result `result`, and
each of `blocks` but the head, which is the entry. -/
@[expose] def BlockSigs.of {env : Env Unit} {α : Type} (blocks : List (Block env α))
    (result : TypeExpr env) : BlockSigs env :=
  (blocks.drop 1).foldl (init := (∅ : BlockSigs env).insert Label.exit #[result])
    fun m b => m.insert b.label (b.params.map (·.type))

/-- The parameter types the target `k` implies for its block: what it binds, then what it
leaves for the operation. -/
@[expose] def Target.Raw.implies? {env : Env Unit} (ctx : Ctx env) (k : Target.Raw)
    (expects : Array (TypeExpr env)) : Option (Array (TypeExpr env)) :=
  (ctx.typesOf? k.args).map (· ++ expects)

/-- A target is well formed when its label is a block of `bs` that declares exactly the
parameters the target implies. -/
@[expose, reducible] def Target.Raw.WF {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env)
    (k : Target.Raw) (expects : Array (TypeExpr env)) : Prop :=
  Agrees (bs.find? k.label) (k.implies? ctx expects)

/-- Each target of `ks` is well formed at the corresponding entry of `expects`: one per
entry, in order, as an operation's successors against their declared values. -/
@[expose, reducible] def Target.Raw.AllWF {env : Env Unit} (ctx : Ctx env)
    (bs : BlockSigs env) (ks : Array Target.Raw)
    (expects : Array (Array (TypeExpr env))) : Prop :=
  ks.size = expects.size ∧ ∀ p ∈ ks.zip expects, Target.Raw.WF ctx bs p.1 p.2

instance {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env) (ks : Array Target.Raw)
    (expects : Array (Array (TypeExpr env))) :
    Decidable (Target.Raw.AllWF ctx bs ks expects) :=
  inferInstanceAs (Decidable (ks.size = expects.size ∧
    ∀ p ∈ ks.zip expects, Target.Raw.WF ctx bs p.1 p.2))

/-! ## Operations -/

/-- What an operation's successors receive at its type arguments: per successor, in order, the
types its payload entries stand for, a spread's list one per element. -/
@[expose] def InsnSig.succTypes {env : Env Unit} (isig : InsnSig env)
    (typeArgs : TypeArgs env isig.scope) : Array (Array (TypeExpr env)) :=
  isig.succs.map fun p => p.type.flatMap (·.typesAt typeArgs)

/-- An operation's operands and successors, wherever it sits: its operands have the types
its signature demands at `typeArgs`, and it names one block of `bs` per declared successor,
each receiving that successor's declared values after what the site pre-binds. -/
@[expose, reducible] def InsnSig.callWF {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env)
    (isig : InsnSig env) (typeArgs : TypeArgs env isig.scope)
    (args : Array ValId) (succs : Array Target.Raw) : Prop :=
  Agrees (ctx.typesOf? args) (isig.operandTypes? typeArgs args.size) ∧
    Target.Raw.AllWF ctx bs succs (isig.succTypes typeArgs)

/-- What a region must be: its entry block's parameter types, and the type its exit takes. -/
abbrev RegionType (env : Env Unit) := Array (TypeExpr env) × TypeExpr env

/-- What each region of an operation must be, at its type arguments. -/
@[expose] def InsnSig.regionTypes {env : Env Unit} (isig : InsnSig env)
    (typeArgs : TypeArgs env isig.scope) : List (RegionType env) :=
  isig.regions.toList.map fun p =>
    (p.type.params.map (·.type.instantiate typeArgs),
      p.type.returnType.instantiate typeArgs)

/-- A region's entry block exists and takes exactly `params`. -/
@[expose, reducible] def Region.entryWF {env : Env Unit} {α : Type}
    (params : Array (TypeExpr env)) (blocks : List (Block env α)) : Prop :=
  blocks.head?.map (fun b => b.params.map (·.type)) = some params

/-! ## Instructions, terminators, blocks and regions -/

/-- Whether the raw type is an application of the type `n`. -/
@[expose] def TypeExpr.Raw.isAppOf (n : Name) : TypeExpr.Raw → Bool
  | .app m _ => m == n
  | _ => false

/-- A constant's rule, at the type `t` of the value it defines: a literal has the type the
base gives it, and a function reference is a code pointer, of a `base.Fn` type.  Which `Fn`
its target allows is the module's rule, `Module.Raw.WF`.  A ghost reference may have any type
here: which type its ghost allows is the module's rule too. -/
@[expose] def Const.WF {env : Env Unit} [base ≼ env] (t : TypeExpr env) : Const → Prop
  | .func _ => t.toRaw.isAppOf Base.Fn.name = true
  | .ghost _ => True
  | c => c.typeOf? = some t

instance {env : Env Unit} [base ≼ env] (t : TypeExpr env) : (c : Const) → Decidable (c.WF t)
  | .func _ => inferInstanceAs (Decidable (_ = true))
  | .ghost _ => inferInstanceAs (Decidable True)
  | .unit | .bool _ | .int _ | .float _ | .str _ => inferInstanceAs (Decidable (_ = some t))

mutual

/-- An instruction's rule, in the context `ctx`, with `bs` the blocks its successors may name.

* A constant satisfies `Const.WF` at the type of the value it defines.  A function
  reference's type is a `base.Fn` type.  Whether a function or ghost reference names a
  function or a ghost of the module, and at which type, is `Module.Raw.WF`'s rule.
* An application has a return type, which its result has at the type arguments, satisfies
  `InsnSig.callWF`, and supplies one region per declared region, each well formed at the
  declared types.  A constructor is applied as any operation is: its signature is the one
  `Env.addData` derived from its datatype. -/
@[expose] def Instruction.WF {env : Env Unit} {α : Type} [base ≼ env]
    (ctx : Ctx env) (bs : BlockSigs env) : Instruction env α → Prop
  | .const _ d c => c.WF d.type
  | @Instruction.apply _ _ _ d isig _ typeArgs args succs ⟨regions⟩ =>
    isig.returnType.map (·.instantiate typeArgs) = some d.type ∧
      isig.callWF ctx bs typeArgs args succs ∧
      Region.WFList ctx (isig.regionTypes typeArgs) regions

/-- `Instruction.WF` of each. -/
@[expose] def Instruction.WFList {env : Env Unit} {α : Type} [base ≼ env]
    (ctx : Ctx env) (bs : BlockSigs env) :
    List (Instruction env α) → Prop
  | [] => True
  | i :: is => Instruction.WF ctx bs i ∧ Instruction.WFList ctx bs is

/-- A terminator's rule: a terminal operation, one with no return type, satisfying
`InsnSig.callWF`, that supplies its regions as `Instruction.apply` does.  Any successor may be
taken and any region run. -/
@[expose] def Terminator.WF {env : Env Unit} {α : Type} [base ≼ env]
    (ctx : Ctx env) (bs : BlockSigs env) : Terminator env α → Prop
  | @Terminator.apply _ _ _ isig _ typeArgs args succs ⟨regions⟩ =>
    isig.returnType = none ∧ isig.callWF ctx bs typeArgs args succs ∧
      Region.WFList ctx (isig.regionTypes typeArgs) regions

/-- A block is well formed when its instructions and its terminator are, against the
blocks `bs` of its region.  `Func.ctx?` checks its parameters. -/
@[expose] def Block.WF {env : Env Unit} {α : Type} [base ≼ env]
    (ctx : Ctx env) (bs : BlockSigs env) : Block env α → Prop
  | ⟨_, _, ⟨instrs⟩, term, _⟩ =>
    Instruction.WFList ctx bs instrs ∧ Terminator.WF ctx bs term

/-- `Block.WF` of each. -/
@[expose] def Block.WFList {env : Env Unit} {α : Type} [base ≼ env]
    (ctx : Ctx env) (bs : BlockSigs env) : List (Block env α) → Prop
  | [] => True
  | b :: l => Block.WF ctx bs b ∧ Block.WFList ctx bs l

/-- A region is well formed at `sig` when its entry block takes `sig`'s parameters and
every block is well formed against the region's own blocks and its exit, taking `sig`'s
result.  So control leaves the region only through its exit, with a value of the declared
type. -/
@[expose] def Region.WF {env : Env Unit} {α : Type} [base ≼ env]
    (ctx : Ctx env) (sig : RegionType env) : Region env α → Prop
  | ⟨⟨blocks⟩⟩ =>
    Region.entryWF sig.1 blocks ∧ Block.WFList ctx (BlockSigs.of blocks sig.2) blocks

/-- One region per signature, each well formed at it: the same number, in the same order. -/
@[expose] def Region.WFList {env : Env Unit} {α : Type} [base ≼ env]
    (ctx : Ctx env) :
    List (RegionType env) → List (Region env α) → Prop
  | [], [] => True
  | s :: ss, r :: rs => Region.WF ctx s r ∧ Region.WFList ctx ss rs
  | _, _ => False

end

section Decide

variable {env : Env Unit} {α : Type} [base ≼ env] (ctx : Ctx env)

mutual

/-- Deciding `Instruction.WF`. -/
def Instruction.decWF (bs : BlockSigs env) :
    (i : Instruction env α) → Decidable (Instruction.WF ctx bs i)
  | .const _ d c => inferInstanceAs (Decidable (c.WF d.type))
  | @Instruction.apply _ _ _ d isig _ typeArgs args succs ⟨regions⟩ =>
    have := Region.decWFList (isig.regionTypes typeArgs) regions
    inferInstanceAs (Decidable
      (isig.returnType.map (·.instantiate typeArgs) = some d.type ∧
        isig.callWF ctx bs typeArgs args succs ∧
        Region.WFList ctx (isig.regionTypes typeArgs) regions))

/-- Deciding `Instruction.WFList`. -/
def Instruction.decWFList (bs : BlockSigs env) :
    (is : List (Instruction env α)) → Decidable (Instruction.WFList ctx bs is)
  | [] => inferInstanceAs (Decidable True)
  | i :: is =>
    have := Instruction.decWF bs i
    have := Instruction.decWFList bs is
    inferInstanceAs
      (Decidable (Instruction.WF ctx bs i ∧ Instruction.WFList ctx bs is))

/-- Deciding `Terminator.WF`. -/
def Terminator.decWF (bs : BlockSigs env) :
    (t : Terminator env α) → Decidable (Terminator.WF ctx bs t)
  | @Terminator.apply _ _ _ isig _ typeArgs args succs ⟨regions⟩ =>
    have := Region.decWFList (isig.regionTypes typeArgs) regions
    inferInstanceAs (Decidable
      (isig.returnType = none ∧ isig.callWF ctx bs typeArgs args succs ∧
        Region.WFList ctx (isig.regionTypes typeArgs) regions))

/-- Deciding `Block.WF`. -/
def Block.decWF (bs : BlockSigs env) :
    (b : Block env α) → Decidable (Block.WF ctx bs b)
  | ⟨_, _, ⟨instrs⟩, term, _⟩ =>
    have := Instruction.decWFList bs instrs
    have := Terminator.decWF bs term
    inferInstanceAs (Decidable (Instruction.WFList ctx bs instrs ∧
      Terminator.WF ctx bs term))

/-- Deciding `Block.WFList`. -/
def Block.decWFList (bs : BlockSigs env) :
    (l : List (Block env α)) → Decidable (Block.WFList ctx bs l)
  | [] => inferInstanceAs (Decidable True)
  | b :: l =>
    have := Block.decWF bs b
    have := Block.decWFList bs l
    inferInstanceAs (Decidable (Block.WF ctx bs b ∧ Block.WFList ctx bs l))

/-- Deciding `Region.WF`. -/
def Region.decWF (sig : RegionType env) :
    (r : Region env α) → Decidable (Region.WF ctx sig r)
  | ⟨⟨blocks⟩⟩ =>
    have := Block.decWFList (BlockSigs.of blocks sig.2) blocks
    inferInstanceAs (Decidable (Region.entryWF sig.1 blocks ∧
      Block.WFList ctx (BlockSigs.of blocks sig.2) blocks))

/-- Deciding `Region.WFList`. -/
def Region.decWFList :
    (sigs : List (RegionType env)) → (rs : List (Region env α)) →
      Decidable (Region.WFList ctx sigs rs)
  | [], [] => inferInstanceAs (Decidable True)
  | s :: ss, r :: rs =>
    have := Region.decWF s r
    have := Region.decWFList ss rs
    inferInstanceAs (Decidable (Region.WF ctx s r ∧ Region.WFList ctx ss rs))
  | [], _ :: _ => inferInstanceAs (Decidable False)
  | _ :: _, [] => inferInstanceAs (Decidable False)

end

instance (bs : BlockSigs env) (i : Instruction env α) :
    Decidable (Instruction.WF ctx bs i) := Instruction.decWF ctx bs i

instance (bs : BlockSigs env) (t : Terminator env α) :
    Decidable (Terminator.WF ctx bs t) := Terminator.decWF ctx bs t

instance (bs : BlockSigs env) (b : Block env α) :
    Decidable (Block.WF ctx bs b) := Block.decWF ctx bs b

instance (sig : RegionType env) (r : Region env α) :
    Decidable (Region.WF ctx sig r) := Region.decWF ctx sig r

end Decide

/-! ## Functions and modules -/

mutual

/-- Every block nested in an instruction's regions, at any depth. -/
@[expose] def Instruction.nestedBlocks {env : Env Unit} {α : Type} :
    Instruction env α → List (Block env α)
  | .apply _ _ _ _ _ _ ⟨regions⟩ => Region.blocksList regions
  | .const .. => []

/-- Every block nested in a terminal operation's regions, at any depth. -/
@[expose] def Terminator.nestedBlocks {env : Env Unit} {α : Type} :
    Terminator env α → List (Block env α)
  | .apply _ _ _ _ _ ⟨regions⟩ => Region.blocksList regions

/-- `Instruction.nestedBlocks` of each. -/
@[expose] def Instruction.nestedBlocksList {env : Env Unit} {α : Type} :
    List (Instruction env α) → List (Block env α)
  | [] => []
  | i :: is => i.nestedBlocks ++ Instruction.nestedBlocksList is

/-- Each block, followed by every block nested in its instructions' and its terminator's
regions. -/
@[expose] def Block.withNestedList {env : Env Unit} {α : Type} :
    List (Block env α) → List (Block env α)
  | [] => []
  | ⟨l, ps, ⟨instrs⟩, t, i⟩ :: bs =>
    ⟨l, ps, ⟨instrs⟩, t, i⟩ ::
      (Instruction.nestedBlocksList instrs ++ Terminator.nestedBlocks t ++
        Block.withNestedList bs)

/-- Every block of the regions, at any depth. -/
@[expose] def Region.blocksList {env : Env Unit} {α : Type} :
    List (Region env α) → List (Block env α)
  | [] => []
  | ⟨⟨blocks⟩⟩ :: rs => Block.withNestedList blocks ++ Region.blocksList rs

end

/-- Every block of the function: its own and those of every region, at any depth, then its
contract's. -/
@[expose] def Func.allBlocks {env : Env Unit} {α : Type} (fn : Func env α) :
    List (Block env α) :=
  Block.withNestedList fn.blocks.toList ++ Region.blocksList fn.contract.regions

mutual

/-- What an instruction defines, in the order it is written: its result, then what its
regions define. -/
@[expose] def Instruction.defs {env : Env Unit} {α : Type} :
    Instruction env α → List (ValDecl env)
  | .const _ d _ => [d]
  | .apply _ d _ _ _ _ ⟨regions⟩ => d :: Region.defsList regions

/-- `Instruction.defs` of each. -/
@[expose] def Instruction.defsList {env : Env Unit} {α : Type} :
    List (Instruction env α) → List (ValDecl env)
  | [] => []
  | i :: is => i.defs ++ Instruction.defsList is

/-- What a terminator's regions define. -/
@[expose] def Terminator.defs {env : Env Unit} {α : Type} :
    Terminator env α → List (ValDecl env)
  | .apply _ _ _ _ _ ⟨regions⟩ => Region.defsList regions

/-- What blocks define, in the order it is written: each block's parameters, then what its
instructions and terminator define. -/
@[expose] def Block.defsList {env : Env Unit} {α : Type} :
    List (Block env α) → List (ValDecl env)
  | [] => []
  | ⟨_, params, ⟨instrs⟩, t, _⟩ :: bs =>
    params.toList ++ Instruction.defsList instrs ++ t.defs ++ Block.defsList bs

/-- What regions define, in order. -/
@[expose] def Region.defsList {env : Env Unit} {α : Type} :
    List (Region env α) → List (ValDecl env)
  | [] => []
  | ⟨⟨blocks⟩⟩ :: rs => Block.defsList blocks ++ Region.defsList rs

end

/-- Every value the function defines: an extern's parameters; then those of its body, in the
order the printed form writes the definitions, each block's parameters (the entry block's are
the function's own), then each instruction's result followed by what its regions define, then
what the terminator's regions define; then its contract's, clause by clause.  The contract
prints before the body, but its values come last, so that a contract leaves the body's ids as
they are. -/
@[expose] def Func.defs {env : Env Unit} {α : Type} (fn : Func env α) : List (ValDecl env) :=
  (if fn.extern then fn.params.toList else []) ++ Block.defsList fn.blocks.toList ++
    Region.defsList fn.contract.regions

/-- The ids are `0, 1, …` in the order `Func.defs` lists the definitions, and each value has
one name: what reading a printed function gives. -/
@[expose] def Func.Canonical {env : Env Unit} {α : Type} (fn : Func env α) : Prop :=
  fn.defs.map (·.id.id) = List.range fn.defs.length ∧ fn.names.size = fn.defs.length

instance {env : Env Unit} {α : Type} (fn : Func env α) : Decidable fn.Canonical :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The type of every value the function defines, its contract's included, or `none` if some
id is defined twice. -/
@[expose] def Func.ctx? {env : Env Unit} {α : Type} (fn : Func env α) : Option (Ctx env) :=
  fn.defs.foldlM (init := (∅ : Ctx env)) Ctx.define?

/-- The label of every block of the function, regions included. -/
@[expose] def Func.labels {env : Env Unit} {α : Type} (fn : Func env α) : List Label :=
  fn.allBlocks.map (·.label)

/-- The blocks a transfer at the function's top level may name, and its exit, taking
`retType`. -/
@[expose] def Func.blockSigs {env : Env Unit} {α : Type} (fn : Func env α) : BlockSigs env :=
  BlockSigs.of fn.blocks.toList fn.retType

-- One bound for every id, which the kernel computes once where `∀ d ∈ ds, d.id.id < n` would
-- recompute `n` per value.
/-- One more than the largest id of `ds`, or `0`. -/
@[expose] def ValDecl.idBound {env : Env Unit} (ds : List (ValDecl env)) : Nat :=
  ds.foldl (fun m d => max m (d.id.id + 1)) 0

/-- The bound folded from `m` is at most `n` iff `m` is and every id of `ds` is below `n`. -/
theorem ValDecl.foldl_le_iff {env : Env Unit} (n : Nat) :
    ∀ (ds : List (ValDecl env)) (m : Nat),
      ds.foldl (fun m d => max m (d.id.id + 1)) m ≤ n ↔ m ≤ n ∧ ∀ d ∈ ds, d.id.id < n
  | [], m => by simp
  | d :: ds, m => by
    simp [ValDecl.foldl_le_iff n ds, Nat.max_le, Nat.succ_le_iff, and_assoc]

/-- `ValDecl.idBound ds` is at most `n` iff every id of `ds` is below `n`. -/
theorem ValDecl.idBound_le_iff {env : Env Unit} (ds : List (ValDecl env)) (n : Nat) :
    ValDecl.idBound ds ≤ n ↔ ∀ d ∈ ds, d.id.id < n := by
  simp [ValDecl.idBound, ValDecl.foldl_le_iff]

-- Through a `NameSet`, which the kernel reduces faster than the list's own `Nodup` check.
/-- Deciding that no name occurs twice in `ns`. -/
@[expose] def Name.decNodup (ns : Array Name) : Decidable ns.toList.Nodup :=
  decidable_of_iff _ NameSet.of?_isSome_iff

/-- The rule for a function's blocks: no value is defined twice, regions and contract included,
and every top-level block is well formed, in the context those definitions give, against the
top-level blocks and the exit.  No transfer names an entry block, the function's or a region's:
`BlockSigs.of` leaves entries out. -/
-- Over the list of the blocks: deciding a quantifier over an array's members takes time quadratic
-- in its size.
@[expose, reducible] def Func.BodyWF {env : Env Unit} {α : Type} [base ≼ env]
    (fn : Func env α) : Prop :=
  OptHolds fn.ctx? fun ctx => ∀ b ∈ fn.blocks.toList, Block.WF ctx fn.blockSigs b

/-! ### Contracts -/

/-- Whether `x` is one of the function's parameters: what a contract clause sees on entry. -/
@[expose] def Func.isParam {env : Env Unit} {α : Type} (fn : Func env α) (x : ValId) : Bool :=
  fn.params.any (·.id == x)

/-- The effect of the operation the instruction applies: its signature's.  A constant's is
`pure`. -/
@[expose] def Instruction.effect {env : Env Unit} {α : Type} : Instruction env α → Effect
  | @Instruction.apply _ _ _ _ isig .. => isig.effect
  | .const .. => .pure

/-- The effect of the operation the terminator applies: its signature's. -/
@[expose] def Terminator.effect {env : Env Unit} {α : Type} : Terminator env α → Effect
  | @Terminator.apply _ _ _ isig .. => isig.effect

/-- What a `requires` clause must be: no arguments, and a `base.Bool` result. -/
@[expose] def Func.requiresType {env : Env Unit} [base ≼ env] : RegionType env :=
  (#[], Base.Bool)

/-- What an `ensures` clause must be: the function's result as its argument, and a
`base.Bool` result. -/
@[expose] def Func.ensuresType {env : Env Unit} {α : Type} [base ≼ env] (fn : Func env α) :
    RegionType env :=
  (#[fn.retType], Base.Bool)

/-- No instruction or terminator of the regions, at any depth, applies an operation declared
`writes`: what the checker asks of a contract region, which must not change state. -/
@[expose, reducible] def Region.NoWrites {env : Env Unit} {α : Type} (rs : List (Region env α)) :
    Prop :=
  ∀ b ∈ Region.blocksList rs, (∀ i ∈ b.instrs.toList, i.effect ≠ .writes) ∧ b.term.effect ≠ .writes

/-- What a frame region must be: no arguments, and a `base.Loc` result, the set of locations
that it names. -/
@[expose] def Func.frameType {env : Env Unit} [base ≼ env] : RegionType env :=
  (#[], Base.Loc)

/-- The region `r` of a clause or a frame is well formed at `sig`, in the function's context
`ctx`; it is shaped and dominance-correct as a body entered where only the parameters are visible
(`Region.domOK_iff`), so it uses only the parameters and its own values; and it applies no
operation declared `writes`, at any depth. -/
@[expose, reducible] def Func.ClauseWF {env : Env Unit} {α : Type} [base ≼ env]
    (fn : Func env α) (ctx : Ctx env) (sig : RegionType env) (r : Region env α) : Prop :=
  Region.WF ctx sig r ∧ r.domOK fn.isParam = true ∧ Region.NoWrites [r]

/-- Whether `t` is a cell's type, a `base.Ref`. -/
@[expose] def TypeExpr.isRef {env : Env Unit} (t : TypeExpr env) : Bool :=
  t.fold (fun _ _ => false) (fun n _ => n == bn "Ref") (fun _ => false)

/-- A frame is well formed, in the function's context `ctx`, when each cell it names is a
parameter of type `base.Ref`, it names no cell twice, and each of its regions is well formed at
`Func.frameType`, as a clause is at its type. -/
@[expose] def Func.FrameWF {env : Env Unit} {α : Type} [base ≼ env] (fn : Func env α)
    (ctx : Ctx env) (frame : Option (Array (FrameEntry env α))) : Prop :=
  (∀ v ∈ FrameEntry.cellsOf frame, ∃ d ∈ fn.params.toList, d.id = v ∧ d.type.isRef = true) ∧
    (FrameEntry.cellsOf frame).Nodup ∧
    ∀ r ∈ FrameEntry.regionsOf frame, fn.ClauseWF ctx Func.frameType r

/-! ### Deciding the cells of a frame

`Func.FrameWF` is decided in time linear in the parameters and the cells: each cell is looked up
in the set of the ids of the parameters of type `base.Ref`, and the cells' ids are added, one by
one, to a set of the ids met so far. -/

/-- One step of `ValId.distinctB`: fail on an id that `seen` holds, or add it. -/
@[expose] def ValId.distinctStep (seen : NatTrie Unit) (v : ValId) : Option (NatTrie Unit) :=
  if (seen.find? v.id).isSome then none else some (seen.insert v.id ())

/-- Whether no value occurs twice in `vs`, decided through the set of the ids met so far. -/
@[expose] def ValId.distinctB (vs : List ValId) : Bool :=
  (vs.foldlM ValId.distinctStep .leaf).isSome

/-- Adding the ids of `vs` to `seen`, one by one, never meets an id that is already there exactly
when `vs` has no repeats and `seen` holds none of its ids. -/
private theorem ValId.foldlM_distinctStep_isSome :
    ∀ (vs : List ValId) (seen : NatTrie Unit),
      (vs.foldlM ValId.distinctStep seen).isSome = true ↔
        vs.Nodup ∧ ∀ v ∈ vs, seen.find? v.id = none
  | [], _ => by simp
  | v :: vs, seen => by
    rw [List.foldlM_cons]
    by_cases h : (seen.find? v.id).isSome = true
    · have hs : ValId.distinctStep seen v = none := by simp [ValId.distinctStep, h]
      rw [hs]
      constructor
      · intro hc
        simp at hc
      · intro ⟨_, hall⟩
        have hv := hall v List.mem_cons_self
        simp [hv] at h
    · have hs : ValId.distinctStep seen v = some (seen.insert v.id ()) := by
        simp [ValId.distinctStep, h]
      have hv : seen.find? v.id = none := by simpa using h
      rw [hs]
      show (vs.foldlM ValId.distinctStep (seen.insert v.id ())).isSome = true ↔ _
      rw [ValId.foldlM_distinctStep_isSome vs]
      simp only [NatTrie.find?_insert, List.nodup_cons, List.forall_mem_cons]
      constructor
      · rintro ⟨hnd, hall⟩
        refine ⟨⟨fun hm => ?_, hnd⟩, hv, fun w hw => ?_⟩
        · have hvv := hall v hm
          simp at hvv
        · have hww := hall w hw
          by_cases hwv : w.id = v.id
          · simp [hwv] at hww
          · simpa [hwv] using hww
      · rintro ⟨⟨hnot, hnd⟩, -, hall⟩
        refine ⟨hnd, fun w hw => ?_⟩
        have hne : w.id ≠ v.id := fun he => hnot (by cases w; cases v; simp_all)
        simp [hne, hall w hw]

/-- `ValId.distinctB` decides that a list of values has no repeats. -/
theorem ValId.distinctB_iff (vs : List ValId) : ValId.distinctB vs = true ↔ vs.Nodup := by
  simpa [ValId.distinctB] using ValId.foldlM_distinctStep_isSome vs .leaf

/-- The ids of the function's parameters of type `base.Ref`, as a set. -/
@[expose] def Func.refParamIds {env : Env Unit} {α : Type} (fn : Func env α) : NatTrie Unit :=
  fn.params.toList.foldl (fun m d => if d.type.isRef then m.insert d.id.id () else m) .leaf

/-- Adding to `m` the ids of the declarations of `ds` of type `base.Ref` gives a set that holds
exactly the ids of `m` and those. -/
private theorem foldl_refIds_isSome {env : Env Unit} :
    ∀ (ds : List (ValDecl env)) (m : NatTrie Unit) (k : Nat),
      ((ds.foldl (fun m d => if d.type.isRef then m.insert d.id.id () else m) m).find?
          k).isSome = true ↔
        (m.find? k).isSome = true ∨ ∃ d ∈ ds, d.id.id = k ∧ d.type.isRef = true
  | [], _, _ => by simp
  | d :: ds, m, k => by
    rw [List.foldl_cons, foldl_refIds_isSome ds]
    by_cases hr : d.type.isRef = true
    · by_cases hk : k = d.id.id
      · subst hk
        simp [hr, NatTrie.find?_insert]
      · simp [hr, NatTrie.find?_insert, hk, Ne.symm hk]
    · simp [hr]

/-- `Func.refParamIds` holds the id of `v` exactly when a parameter of type `base.Ref` is `v`. -/
theorem Func.refParamIds_iff {env : Env Unit} {α : Type} (fn : Func env α) (v : ValId) :
    (fn.refParamIds.find? v.id).isSome = true ↔
      ∃ d ∈ fn.params.toList, d.id = v ∧ d.type.isRef = true := by
  rw [Func.refParamIds, foldl_refIds_isSome]
  simp only [NatTrie.find?_leaf, Option.isSome_none, Bool.false_eq_true, false_or]
  constructor
  · rintro ⟨d, hd, hid, hr⟩
    have hdv : d.id = v := by
      obtain ⟨j⟩ := v
      revert hid
      obtain ⟨i⟩ := d.id
      simp
    exact ⟨d, hd, hdv, hr⟩
  · rintro ⟨d, hd, rfl, hr⟩
    exact ⟨d, hd, rfl, hr⟩

-- `Func.FrameWF` is not reducible, so that instance search uses this instance.
/-- Deciding `Func.FrameWF` in linear time: each cell is looked up in `Func.refParamIds`, which
is built once, and `ValId.distinctB` decides that no cell repeats. -/
instance {env : Env Unit} {α : Type} [base ≼ env] (fn : Func env α) (ctx : Ctx env)
    (frame : Option (Array (FrameEntry env α))) : Decidable (fn.FrameWF ctx frame) :=
  let refs := fn.refParamIds
  decidable_of_iff ((FrameEntry.cellsOf frame).all (fun v => (refs.find? v.id).isSome) = true ∧
      ValId.distinctB (FrameEntry.cellsOf frame) = true ∧
      ∀ r ∈ FrameEntry.regionsOf frame, fn.ClauseWF ctx Func.frameType r) (by
    simp only [Func.FrameWF, List.all_eq_true, ValId.distinctB_iff, refs, Func.refParamIds_iff])

/-- The rule for a function's contract, in the function's context `ctx`: each `requires` clause
is well formed at `Func.requiresType`, each `ensures` clause at `Func.ensuresType`, and each frame
names only distinct cells among the parameters, and regions well formed at `Func.frameType`. -/
@[expose] def Func.ContractWFIn {env : Env Unit} {α : Type} [base ≼ env]
    (fn : Func env α) (ctx : Ctx env) : Prop :=
  (∀ c ∈ fn.contract.requires.toList, fn.ClauseWF ctx Func.requiresType c.region) ∧
    (∀ c ∈ fn.contract.ensures.toList, fn.ClauseWF ctx fn.ensuresType c.region) ∧
    fn.FrameWF ctx fn.contract.reads ∧ fn.FrameWF ctx fn.contract.writes

-- `Func.ContractWFIn` is not reducible, so that instance search uses this instance.  Unfolded, the
-- search goes past its size limit where the function is a let-bound term.
instance {env : Env Unit} {α : Type} [base ≼ env] (fn : Func env α) (ctx : Ctx env) :
    Decidable (fn.ContractWFIn ctx) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The rule for a function's contract: `Func.ContractWFIn`, in the context of all the function's
values, which is computed once for the whole contract. -/
@[expose, reducible] def Func.ContractWF {env : Env Unit} {α : Type} [base ≼ env]
    (fn : Func env α) : Prop :=
  OptHolds fn.ctx? fn.ContractWFIn

/-- Which clauses may be `free`: no `requires` clause is, an extern's `ensures` clauses all
are, and a defined function's are all checked. -/
@[expose, reducible] def Func.ClauseModesWF {env : Env Unit} {α : Type} (fn : Func env α) :
    Prop :=
  (∀ c ∈ fn.contract.requires.toList, c.free = false) ∧
    ∀ c ∈ fn.contract.ensures.toList, c.free = fn.extern

/-! ### Failures and cycles in contract regions

The predicates are stated in `StrataDyn/ContractRegion.lean`, and decided fast by
`StrataDyn/ContractRegionProps.lean`. -/

/-- How a function's clauses and frame regions handle the failures of their own blocks: in a
clause, a failure successor goes to a failure block of the clause that gives `false`, or `true` in
a `free ensures` clause, or that ends in `unreachable`; in a frame region, it goes to a block of
the region that ends in `unreachable`. -/
@[expose, reducible] def Func.ClauseFailuresWF {env : Env Unit} {α : Type} (fn : Func env α) :
    Prop :=
  (∀ c ∈ fn.contract.requires.toList, c.region.FailsWith (some false)) ∧
    (∀ c ∈ fn.contract.ensures.toList, c.region.FailsWith (some c.free)) ∧
    ∀ r ∈ fn.contract.frameRegions, r.FailsWith none

/-- The rule for a function's contract regions: its clauses and frame regions handle their
failures as `Func.ClauseFailuresWF` asks, the regions nested in them pass their failures on, every
block of them ends in control flow, and none of them has a cycle. -/
@[expose] def Func.ContractRegionsWF {env : Env Unit} {α : Type} (fn : Func env α) : Prop :=
  fn.ClauseFailuresWF ∧ Region.Propagates fn.contract.regions ∧
    Region.EndsInControl fn.contract.regions ∧ Region.Acyclic fn.contract.regions

instance {env : Env Unit} {α : Type} (fn : Func env α) : Decidable fn.ContractRegionsWF :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ### `old` in `ensures` clauses

The predicates are stated in `StrataDyn/ContractRegion.lean`. -/

/-- `base.old` appears only in an `ensures` clause: no instruction of the body, of a `requires`
clause or of a frame region applies it, at any depth. -/
@[expose, reducible] def Func.OldPlaced {env : Env Unit} {α : Type} (fn : Func env α) : Prop :=
  Region.NoOld (⟨fn.blocks⟩ :: fn.contract.requires.toList.map (·.region) ++
    fn.contract.frameRegions)

/-- Each outermost `old` region of an `ensures` clause sees, from outside it, only the parameters,
the clause's constants, and the parameters of the regions nested in the clause that enclose it,
never the result or another value that the clause defines outside the `old` region
(`Region.OldScoped`). -/
@[expose, reducible] def Func.OldScoped {env : Env Unit} {α : Type} (fn : Func env α) : Prop :=
  ∀ c ∈ fn.contract.ensures.toList, c.region.OldScoped fn.isParam

/-- The rules for `base.old`: only an `ensures` clause applies it, and each `old` region sees, from
outside it, only the parameters, the clause's constants and the parameters of the regions that
enclose it. -/
@[expose] def Func.OldWF {env : Env Unit} {α : Type} (fn : Func env α) : Prop :=
  fn.OldPlaced ∧ fn.OldScoped

instance {env : Env Unit} {α : Type} (fn : Func env α) : Decidable fn.OldWF :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Ghosts -/

/-- The ghost that the instruction names, if it is a ghost constant. -/
@[expose] def Instruction.ghost? {env : Env Unit} {α : Type} : Instruction env α → Option Name
  | .const _ _ (.ghost g) => some g
  | _ => none

/-- The function that the instruction refers to, if it is a function reference. -/
@[expose] def Instruction.func? {env : Env Unit} {α : Type} : Instruction env α → Option Name
  | .const _ _ (.func f) => some f
  | _ => none

/-- Only the contract names ghosts: no instruction of the body, at any depth, is a ghost
constant. -/
@[expose, reducible] def Func.GhostsInContract {env : Env Unit} {α : Type} (fn : Func env α) :
    Prop :=
  ∀ b ∈ Block.withNestedList fn.blocks.toList, ∀ i ∈ b.instrs.toList, i.ghost? = none

/-- A well-formed function.  It depends on the function alone: that the functions and the ghosts
it references exist is its module's rule, `Module.Raw.WF`. -/
structure Func.WF {env : Env Unit} {α : Type} [base ≼ env] (fn : Func env α) : Prop where
  /-- It is extern exactly when it has no blocks. -/
  externIff : fn.extern = fn.blocks.isEmpty
  /-- If it is defined, its entry block takes exactly its parameters, ids and types. -/
  entryParams : fn.extern = false → ∀ b ∈ fn.blocks[0]?, b.params = fn.params
  /-- No label occurs twice, counting every region, and none is `Label.exit`. -/
  labelsDistinct : Label.Distinct (Label.exit :: fn.labels)
  /-- No two values share a name. -/
  valueNamesUnique : fn.names.toList.Nodup
  /-- Every value it defines has a name. -/
  valuesNamed : ValDecl.idBound fn.defs ≤ fn.names.size
  /-- Its blocks are well formed. -/
  body : Func.BodyWF fn
  /-- Every block of every body, region bodies included, is reachable from that body's
  entry. -/
  reachable : fn.Reachable
  /-- Some legal tree of each body puts every use in scope. -/
  scoping : fn.Scopable
  /-- Its contract is well formed. -/
  contract : Func.ContractWF fn
  /-- Its `ensures` clauses are `free` exactly when it is extern, and its `requires` clauses
  never are. -/
  clauseModes : Func.ClauseModesWF fn
  /-- Its contract regions send their failures where `Func.ContractRegionsWF` asks, and have no
  cycles. -/
  contractRegions : Func.ContractRegionsWF fn
  /-- Only its `ensures` clauses apply `base.old`, and each `old` region sees, from outside it,
  only the parameters, the clause's constants and the parameters of the regions that enclose
  it. -/
  old : Func.OldWF fn
  /-- Its body names no ghost, at any depth: only its contract does. -/
  ghosts : Func.GhostsInContract fn

/-- Decide `Func.WF`, its reachability and scoping together, as `Func.checkDom` decides them
(`StrataDyn/DomDecide.lean`). -/
instance {env : Env Unit} {α : Type} [base ≼ env] (fn : Func env α) : Decidable fn.WF :=
  have := Name.decNodup fn.names
  decidable_of_iff (fn.extern = fn.blocks.isEmpty ∧
      (fn.extern = false → ∀ b ∈ fn.blocks[0]?, b.params = fn.params) ∧
      Label.Distinct (Label.exit :: fn.labels) ∧ fn.names.toList.Nodup ∧
      ValDecl.idBound fn.defs ≤ fn.names.size ∧ Func.BodyWF fn ∧ (fn.Reachable ∧ fn.Scopable) ∧
      Func.ContractWF fn ∧ Func.ClauseModesWF fn ∧ Func.ContractRegionsWF fn ∧ Func.OldWF fn ∧
      Func.GhostsInContract fn)
    ⟨fun ⟨a, b, c, d, e, f, ⟨g, h⟩, i, j, k, l, m⟩ => ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩,
      fun ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ => ⟨a, b, c, d, e, f, ⟨g, h⟩, i, j, k, l, m⟩⟩

/-- `fn` annotated with `info`, still well formed: well-formedness does not mention
annotations. -/
def Func.setInfo {env : Env Unit} {α : Type} [base ≼ env] (fn : {fn : Func env α // fn.WF})
    (info : α) : {fn : Func env α // fn.WF} :=
  ⟨{ fn.val with info }, by
    obtain ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩ := fn.property
    exact ⟨a, b, c, d, e, f, g, h, i, j, k, l, m⟩⟩

/-- Every value a well-formed function defines has a name. -/
theorem Func.WF.mem_names {env : Env Unit} {α : Type} [base ≼ env] {fn : Func env α}
    (h : fn.WF) {d : ValDecl env} (hd : d ∈ fn.defs) : d.id.id < fn.names.size :=
  (ValDecl.idBound_le_iff _ _).mp h.valuesNamed d hd

/-- A well-formed function is dominance-correct: every use is defined at a point that every
path from its body's entry to the use passes through. -/
theorem Func.WF.domCorrect {env : Env Unit} {α : Type} [base ≼ env] {fn : Func env α}
    (h : fn.WF) : fn.DomCorrect :=
  h.scoping.domCorrect

/-! ## Scopability is dominance-correctness

For a function whose blocks are all reachable, and whose labels are distinct as `Func.WF` asks,
some tree per body scopes it exactly when it is dominance-correct
(`Func.Reachable.scopable_iff`).  `Func.scopable_iff_domCorrect`
(`StrataDyn/DomComplete.lean`) proves it for distinct labels per body, which the distinct
labels of the whole function give. -/

/-- Folding `ofDistinct?`'s step from a map of the labels `seen` gives distinct labels. -/
private theorem nodup_of_foldlM : ∀ (ls seen : List Label) (m : LabelMap Unit),
    (∀ l, (m.find? l).isSome = true ↔ l ∈ seen) → seen.Nodup →
    (ls.foldlM (fun (m : LabelMap Unit) l =>
      if (m.find? l).isSome then none else some (m.insert l ())) m).isSome = true →
        (seen ++ ls).Nodup
  | [], seen, _, _, hn, _ => by simpa using hn
  | l :: ls, seen, m, hm, hn, h => by
    rw [List.foldlM_cons] at h
    by_cases hl : (m.find? l).isSome = true
    · rw [ite_eq_left hl] at h
      simp at h
    · rw [ite_eq_right hl] at h
      have hl₁ : l ∉ seen := fun h₁ => hl ((hm l).mpr h₁)
      have hm₁ : ∀ l₁, ((m.insert l ()).find? l₁).isSome = true ↔ l₁ ∈ seen ++ [l] := by
        intro l₁
        rw [LabelMap.find?_insert]
        by_cases h₂ : l₁ = l
        · simp [h₂]
        · simp [h₂, hm l₁]
      have hn₁ : (seen ++ [l]).Nodup :=
        List.nodup_append.mpr ⟨hn, List.pairwise_singleton _ l, fun a ha b hb hab => by
          rw [List.mem_singleton] at hb
          exact hl₁ (hb ▸ hab ▸ ha)⟩
      simpa using nodup_of_foldlM ls (seen ++ [l]) _ hm₁ hn₁ (by simpa using h)

/-- Labels that `Label.Distinct` accepts are distinct. -/
theorem Label.Distinct.nodup {ls : List Label} (h : Label.Distinct ls) : ls.Nodup := by
  simpa using nodup_of_foldlM ls [] ∅ (fun l => by simp [LabelMap.find?_empty]) List.nodup_nil h

section nested

variable {env : Env Unit} {α : Type}

/-- A region's blocks, with what is nested in them, are part of `blocksList` of a list holding
it. -/
private theorem infix_blocksList {r : Region env α} :
    ∀ {rs : List (Region env α)}, r ∈ rs →
      Block.withNestedList r.blocks.toList <:+: Region.blocksList rs
  | ⟨⟨blocks⟩⟩ :: rs, h => by
    rw [Region.blocksList]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.prefix_append _ _ |>.isInfix
    · exact (infix_blocksList h).trans (List.suffix_append _ _).isInfix

/-- A region's blocks, with what is nested in them, are part of its instruction's nested blocks. -/
private theorem infix_instr {r : Region env α} {i : Instruction env α} (h : r ∈ i.regions) :
    Block.withNestedList r.blocks.toList <:+: i.nestedBlocks := by
  cases i with
  | const => simp [Instruction.regions] at h
  | apply _ _ _ _ _ _ regions =>
    obtain ⟨regions⟩ := regions
    exact infix_blocksList (Array.mem_def.mp h)

/-- A region's blocks, with what is nested in them, are part of its terminator's nested blocks. -/
private theorem infix_term {r : Region env α} {t : Terminator env α} (h : r ∈ t.regions) :
    Block.withNestedList r.blocks.toList <:+: t.nestedBlocks := by
  obtain ⟨_, _, _, _, _, ⟨regions⟩⟩ := t
  exact infix_blocksList (Array.mem_def.mp h)

/-- An instruction's nested blocks are part of `nestedBlocksList` of a list holding it. -/
private theorem infix_nestedBlocksList {i : Instruction env α} :
    ∀ {is : List (Instruction env α)} {k : Nat}, is[k]? = some i →
      i.nestedBlocks <:+: Instruction.nestedBlocksList is
  | i₁ :: is, 0, h => by
    cases h
    exact (List.prefix_append _ _).isInfix
  | i₁ :: is, k + 1, h => by
    rw [Instruction.nestedBlocksList]
    exact (infix_nestedBlocksList (is := is) (k := k) h).trans (List.suffix_append _ _).isInfix

/-- A block of the list, then what is nested in it, is part of `withNestedList`. -/
private theorem infix_withNested {b : Block env α} :
    ∀ {bs : List (Block env α)}, b ∈ bs →
      b :: (Instruction.nestedBlocksList b.instrs.toList ++ b.term.nestedBlocks) <:+:
        Block.withNestedList bs
  | c :: bs, h => by
    obtain ⟨l, ps, ⟨instrs⟩, t, i⟩ := c
    rw [Block.withNestedList]
    rcases List.mem_cons.mp h with rfl | h
    · have := (List.prefix_append (⟨l, ps, ⟨instrs⟩, t, i⟩ ::
        (Instruction.nestedBlocksList instrs ++ t.nestedBlocks)) (Block.withNestedList bs)).isInfix
      rw [List.cons_append] at this
      exact this
    · exact (infix_withNested h).trans (List.infix_cons (List.suffix_append _ _).isInfix)

/-- A body's labels are a sublist of the labels of its blocks with what is nested in them. -/
private theorem sublist_labels :
    ∀ (bs : List (Block env α)),
      (bs.map (·.label)).Sublist ((Block.withNestedList bs).map (·.label))
  | [] => List.Sublist.slnil
  | ⟨l, ps, ⟨instrs⟩, t, i⟩ :: bs => by
    rw [Block.withNestedList, List.map_cons, List.map_cons]
    exact (sublist_labels bs).trans (List.sublist_append_right _ _ |>.map _) |>.cons_cons _

/-- A region's blocks, with what is nested in them, are a shorter part of its owner's. -/
private theorem regionAt_infix {bs : List (Block env α)} {y : Point} {r : Region env α}
    (h : Body.RegionAt bs y r) :
    (Block.withNestedList r.blocks.toList).length < (Block.withNestedList bs).length ∧
      (Block.withNestedList r.blocks.toList) <:+: Block.withNestedList bs := by
  obtain ⟨b, hb, hr⟩ : ∃ b ∈ bs, Block.withNestedList r.blocks.toList <:+:
      Instruction.nestedBlocksList b.instrs.toList ++ b.term.nestedBlocks := by
    cases h with
    | @instr b i k _ hb hk hr =>
      exact ⟨b, hb, (infix_instr hr).trans ((infix_nestedBlocksList
        (by rwa [Array.getElem?_toList])).trans (List.prefix_append _ _).isInfix)⟩
    | @term b _ hb hr =>
      exact ⟨b, hb, (infix_term hr).trans (List.suffix_append _ _).isInfix⟩
  have hw := infix_withNested hb
  refine ⟨Nat.lt_of_lt_of_le ?_ hw.length_le, hr.trans ((List.suffix_cons _ _).isInfix.trans hw)⟩
  rw [List.length_cons]
  exact Nat.lt_succ_of_le hr.length_le

/-- A body whose blocks, with what is nested in them, have distinct labels has distinct labels at
every depth. -/
private theorem distinct_of_nodup : ∀ (n : Nat) (bs : List (Block env α)),
    (Block.withNestedList bs).length < n → ((Block.withNestedList bs).map (·.label)).Nodup →
      Body.Distinct bs
  | 0, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | n + 1, bs, hl, hn => .mk (hn.sublist (sublist_labels bs)) fun _ r hr =>
    have ⟨hlt, hi⟩ := regionAt_infix hr
    distinct_of_nodup n _ (by omega) (hn.sublist (hi.sublist.map _))

end nested

/-- Under reachability, and the distinct labels `Func.WF` asks for, some tree per body scopes the
function exactly when it is dominance-correct. -/
theorem Func.Reachable.scopable_iff {env : Env Unit} {α : Type} {fn : Func env α}
    (hr : fn.Reachable) (hd : Label.Distinct (Label.exit :: fn.labels)) :
    fn.Scopable ↔ fn.DomCorrect :=
  Func.scopable_iff_domCorrect hr (distinct_of_nodup _ _ (Nat.lt_succ_self _)
    (by
      have h := (List.nodup_cons.mp hd.nodup).2
      simp only [Func.labels, Func.allBlocks, List.map_append] at h
      exact h.sublist (List.sublist_append_left _ _)))

/-- A function reference: the function it names, and the type of the value it defines. -/
structure FuncUse (env : Env Unit) where
  target : Name
  type : TypeExpr env

/-- Whether a reference fits its target's code type `ct`: it has that type. -/
@[expose] def FuncUse.Fits {env : Env Unit} (u : FuncUse env) (ct : TypeExpr env) : Prop :=
  u.type = ct

instance {env : Env Unit} (u : FuncUse env) (ct : TypeExpr env) : Decidable (u.Fits ct) :=
  inferInstanceAs (Decidable (_ = _))

/-- A ghost reference: the ghost it names, and the type of the value it defines. -/
structure GhostUse (env : Env Unit) where
  target : Name
  type : TypeExpr env

/-- The function references and the ghost references of the constants of the blocks `bs`, each in
order, collected in one pass. -/
@[expose] def Block.refs {env : Env Unit} {α : Type} (bs : List (Block env α)) :
    Array (FuncUse env) × Array (GhostUse env) :=
  bs.foldl (init := (#[], #[])) fun refs b => b.instrs.foldl (init := refs) fun refs i =>
    match i with
    | .const _ d (.func n) => (refs.1.push ⟨n, d.type⟩, refs.2)
    | .const _ d (.ghost n) => (refs.1, refs.2.push ⟨n, d.type⟩)
    | _ => refs

/-- The function references of `fn`'s constants, regions and contract included. -/
@[expose] def Func.funcRefs {env : Env Unit} {α : Type} (fn : Func env α) :
    Array (FuncUse env) :=
  (Block.refs fn.allBlocks).1

/-- The ghost references of `fn`'s constants, regions and contract included. -/
@[expose] def Func.ghostRefs {env : Env Unit} {α : Type} (fn : Func env α) :
    Array (GhostUse env) :=
  (Block.refs fn.allBlocks).2

/-! ## Ghosts

A ghost's regions are contract regions, checked as a function's are, but entered where nothing
is visible: an initializer takes no arguments, and an invariant the ghost's contents only.  The
values of a ghost's regions are numbered on their own, from `0`, as `Ghost.defs` lists them. -/

section Ghost

variable {env : Env Unit} {α : Type}

/-- Every value the ghost's regions define, in the order the printed form writes them: the
initializer's, then the invariant's. -/
@[expose] def Ghost.defs (g : Ghost env α) : List (ValDecl env) := Region.defsList g.regions

/-- The ids are `0, 1, …` in the order `Ghost.defs` lists the definitions, and each value has one
name: what reading a printed ghost gives. -/
@[expose] def Ghost.Canonical (g : Ghost env α) : Prop :=
  g.defs.map (·.id.id) = List.range g.defs.length ∧ g.names.size = g.defs.length

instance (g : Ghost env α) : Decidable g.Canonical :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The type of every value the ghost's regions define, or `none` if some id is defined
twice. -/
@[expose] def Ghost.ctx? (g : Ghost env α) : Option (Ctx env) :=
  g.defs.foldlM (init := (∅ : Ctx env)) Ctx.define?

/-- The label of every block of the ghost's regions, at any depth. -/
@[expose] def Ghost.labels (g : Ghost env α) : List Label :=
  (Region.blocksList g.regions).map (·.label)

/-- What an initializer must be: no arguments, and the ghost's type as its result. -/
@[expose] def Ghost.initType (g : Ghost env α) : RegionType env := (#[], g.type)

/-- What an invariant must be: the ghost's contents as its argument, and a `base.Bool`
result. -/
@[expose] def Ghost.invariantType [base ≼ env] (g : Ghost env α) : RegionType env :=
  (#[g.type], Base.Bool)

/-- A region of a ghost is well formed at `sig`, in the ghost's context `ctx`; it is shaped and
dominance-correct as a body entered where nothing is visible (`Region.domOK_iff`), so it uses only
its own values; and it applies no operation declared `writes`, at any depth. -/
@[expose, reducible] def Ghost.RegionWF [base ≼ env] (ctx : Ctx env) (sig : RegionType env)
    (r : Region env α) : Prop :=
  Region.WF ctx sig r ∧ r.domOK (fun _ => false) = true ∧ Region.NoWrites [r]

/-- The rule for a ghost's regions, in the context of all their values, which is computed once:
the initializer is well formed at `Ghost.initType`, and the invariant at `Ghost.invariantType`,
as `Ghost.RegionWF` asks. -/
@[expose, reducible] def Ghost.RegionsWF [base ≼ env] (g : Ghost env α) : Prop :=
  OptHolds g.ctx? fun ctx => (∀ r ∈ g.init.toList, Ghost.RegionWF ctx g.initType r) ∧
    ∀ r ∈ g.invariant.toList, Ghost.RegionWF ctx g.invariantType r

/-- How a ghost's regions handle failures and transfer: a failure successor of their own blocks
goes to a block of the region that ends in `unreachable`, the regions nested in them pass their
failures on, every block of them ends in control flow, and none of them has a cycle. -/
@[expose] def Ghost.ContractRegionsWF (g : Ghost env α) : Prop :=
  (∀ r ∈ g.regions, r.FailsWith none) ∧ Region.Propagates g.regions ∧
    Region.EndsInControl g.regions ∧ Region.Acyclic g.regions

instance (g : Ghost env α) : Decidable g.ContractRegionsWF :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- The invariant names no ghost, at any depth: it receives the ghost's contents as its argument
(G8). -/
@[expose, reducible] def Ghost.InvariantNamesNoGhost (g : Ghost env α) : Prop :=
  ∀ b ∈ Region.blocksList g.invariant.toList, ∀ i ∈ b.instrs.toList, i.ghost? = none

/-- No region of the ghost refers to a function, at any depth (G9). -/
@[expose, reducible] def Ghost.NoFuncRefs (g : Ghost env α) : Prop :=
  ∀ b ∈ Region.blocksList g.regions, ∀ i ∈ b.instrs.toList, i.func? = none

/-- A well-formed ghost.  It depends on the ghost alone: that the ghosts and the functions it
references exist is its module's rule, `Module.Raw.WF`. -/
structure Ghost.WF [base ≼ env] (g : Ghost env α) : Prop where
  /-- No label occurs twice, counting every region, and none is `Label.exit`. -/
  labelsDistinct : Label.Distinct (Label.exit :: g.labels)
  /-- No two values share a name. -/
  valueNamesUnique : g.names.toList.Nodup
  /-- Every value its regions define has a name. -/
  valuesNamed : ValDecl.idBound g.defs ≤ g.names.size
  /-- Its initializer and its invariant take and return what they must, see only their own
  values, and apply no operation declared `writes`. -/
  regions : g.RegionsWF
  /-- Its regions send their failures where `Ghost.ContractRegionsWF` asks, and have no
  cycles. -/
  contractRegions : g.ContractRegionsWF
  /-- Its regions do not apply `base.old`, at any depth. -/
  old : Region.NoOld g.regions
  /-- Its invariant names no ghost, at any depth (G8). -/
  invariantNamesNoGhost : g.InvariantNamesNoGhost
  /-- Its regions refer to no function, at any depth (G9). -/
  noFuncRefs : g.NoFuncRefs

instance [base ≼ env] (g : Ghost env α) : Decidable g.WF :=
  have := Name.decNodup g.names
  decidable_of_iff (Label.Distinct (Label.exit :: g.labels) ∧ g.names.toList.Nodup ∧
      ValDecl.idBound g.defs ≤ g.names.size ∧ g.RegionsWF ∧ g.ContractRegionsWF ∧
      Region.NoOld g.regions ∧ g.InvariantNamesNoGhost ∧ g.NoFuncRefs)
    ⟨fun ⟨a, b, c, d, e, f, h, i⟩ => ⟨a, b, c, d, e, f, h, i⟩,
      fun ⟨a, b, c, d, e, f, h, i⟩ => ⟨a, b, c, d, e, f, h, i⟩⟩

/-- The ghost references of the constants of the ghost's initializer. -/
@[expose] def Ghost.initRefs (g : Ghost env α) : Array (GhostUse env) :=
  (Block.refs (Region.blocksList g.init.toList)).2

/-- The ghost references of the constants of the ghost's regions: its initializer's, then its
invariant's. -/
@[expose] def Ghost.ghostRefs (g : Ghost env α) : Array (GhostUse env) :=
  g.initRefs ++ (Block.refs (Region.blocksList g.invariant.toList)).2

end Ghost

/-! ## Modules -/

/-- The names of a module's functions, in order. -/
@[expose] def Module.Raw.funcNames {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : Array Name :=
  m.funcs.mapK (·.name)

/-- Each function's name with its code type, in order. -/
@[expose] def Module.Raw.funcSigs {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : Array (Name × TypeExpr env) :=
  m.funcs.mapK fun f => (f.name, f.codeType)

/-- Each function's code type, by name, which function references are checked against: empty
if two functions share a name. -/
@[expose] def Module.Raw.codeTypes {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : NameMap (TypeExpr env) :=
  (NameMap.ofArray? m.funcSigs).getD ∅

/-- The names of a module's ghosts, in order. -/
@[expose] def Module.Raw.ghostNames {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : Array Name :=
  m.ghosts.mapK (·.name)

/-- Each ghost's name with its position and its type, in order. -/
@[expose] def Module.Raw.ghostSigs {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : Array (Name × Nat × TypeExpr env) :=
  (m.ghosts.toList.zipIdx.map fun (g, i) => (g.name, i, g.type)).toArray

/-- Each ghost's position and type, by name, which ghost references are checked against: empty if
two ghosts share a name. -/
@[expose] def Module.Raw.ghostTable {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : NameMap (Nat × TypeExpr env) :=
  (NameMap.ofArray? m.ghostSigs).getD ∅

/-- Whether a ghost reference names a ghost of `tbl`, the positions and types of a module's
ghosts by name, at the type of its cell: a `base.Ref` of the ghost's type. -/
@[expose] def GhostUse.Fits {env : Env Unit} [base ≼ env] (tbl : NameMap (Nat × TypeExpr env))
    (u : GhostUse env) : Prop :=
  OptHolds (tbl.find? u.target) fun p => u.type = Base.Ref p.2

instance {env : Env Unit} [base ≼ env] (tbl : NameMap (Nat × TypeExpr env)) (u : GhostUse env) :
    Decidable (u.Fits tbl) :=
  inferInstanceAs (Decidable (OptHolds _ _))

/-- Whether a ghost reference of the initializer of the ghost at position `i` names a ghost of
`tbl` declared before it, or a name that `tbl` does not hold, which `GhostUse.Fits` rejects. -/
@[expose] def GhostUse.Before {env : Env Unit} (tbl : NameMap (Nat × TypeExpr env)) (i : Nat)
    (u : GhostUse env) : Prop :=
  (tbl.find? u.target).all (·.1 < i) = true

instance {env : Env Unit} (tbl : NameMap (Nat × TypeExpr env)) (i : Nat) (u : GhostUse env) :
    Decidable (u.Before tbl i) :=
  inferInstanceAs (Decidable (_ = true))

/-- Every ghost reference of the module, of a function or of a ghost, names a ghost of `tbl`, at
the type of its cell. -/
@[expose] def Module.Raw.GhostRefsIn {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) (tbl : NameMap (Nat × TypeExpr env)) : Prop :=
  (∀ f ∈ m.funcs, ∀ u ∈ f.ghostRefs, u.Fits tbl) ∧ ∀ g ∈ m.ghosts, ∀ u ∈ g.ghostRefs, u.Fits tbl

-- Over lists: deciding a quantifier over an array's members takes time quadratic in its size.
instance {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α)
    (tbl : NameMap (Nat × TypeExpr env)) : Decidable (m.GhostRefsIn tbl) :=
  decidable_of_iff ((∀ f ∈ m.funcs.toList, ∀ u ∈ f.ghostRefs.toList, u.Fits tbl) ∧
      ∀ g ∈ m.ghosts.toList, ∀ u ∈ g.ghostRefs.toList, u.Fits tbl)
    (by simp [Module.Raw.GhostRefsIn])

/-- Every ghost reference of the module names a ghost of the module, at the type of its cell
(G2). -/
@[expose, reducible] def Module.Raw.GhostRefsWF {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : Prop :=
  m.GhostRefsIn m.ghostTable

/-- Every ghost reference of each initializer names a ghost of `tbl` declared before the
initializer's own ghost, or a name that `tbl` does not hold. -/
@[expose] def Module.Raw.GhostOrderIn {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) (tbl : NameMap (Nat × TypeExpr env)) : Prop :=
  ∀ p ∈ m.ghosts.toList.zipIdx, ∀ u ∈ p.1.initRefs.toList, u.Before tbl p.2

instance {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α)
    (tbl : NameMap (Nat × TypeExpr env)) : Decidable (m.GhostOrderIn tbl) :=
  inferInstanceAs (Decidable (∀ p ∈ m.ghosts.toList.zipIdx, _))

/-- Every ghost reference of each initializer names a ghost declared before the initializer's own
ghost (G5).  A reference to a name that the module does not hold breaks `GhostRefsWF` instead. -/
@[expose, reducible] def Module.Raw.GhostOrderWF {env : Env Unit} [base ≼ env] {α : Type}
    (m : Module.Raw env α) : Prop :=
  m.GhostOrderIn m.ghostTable

/-- A well-formed module. -/
structure Module.Raw.WF {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α) :
    Prop where
  /-- No two functions share a name. -/
  funcNamesUnique : m.funcNames.toList.Nodup
  /-- Every function is well formed. -/
  funcs : ∀ f ∈ m.funcs, f.WF
  /-- Every function reference names a function of the module, and fits its code type. -/
  refs : ∀ f ∈ m.funcs, ∀ u ∈ f.funcRefs, OptHolds (m.codeTypes.find? u.target) u.Fits
  /-- No two ghosts share a name, and no ghost has the name of a function (G1). -/
  ghostNamesUnique : (m.ghostNames ++ m.funcNames).toList.Nodup
  /-- Every ghost is well formed. -/
  ghosts : ∀ g ∈ m.ghosts, g.WF
  /-- Every ghost reference names a ghost of the module, at the type of its cell (G2). -/
  ghostRefs : m.GhostRefsWF
  /-- An initializer names only the ghosts declared before its own (G5). -/
  ghostOrder : m.GhostOrderWF

/-- The rules of `Module.Raw.WF` about the module as a whole, rather than about one function or one
ghost, with `cts` the functions' code types by name and `tbl` the ghosts' positions and types by
name, as `Module.Raw.codeTypes` and `Module.Raw.ghostTable` give them. -/
@[expose] def Module.Raw.OwnWFIn {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α)
    (cts : NameMap (TypeExpr env)) (tbl : NameMap (Nat × TypeExpr env)) : Prop :=
  m.funcNames.toList.Nodup ∧
    (∀ f ∈ m.funcs, ∀ u ∈ f.funcRefs, OptHolds (cts.find? u.target) u.Fits) ∧
    (m.ghostNames ++ m.funcNames).toList.Nodup ∧ m.GhostRefsIn tbl ∧ m.GhostOrderIn tbl

/-- Whether every function reference of `fn` names a function of `cts` at a type that fits, and
every ghost reference of `fn` a ghost of `tbl` at the type of its cell, from one pass over its
blocks. -/
@[expose] def Func.refsFitB {env : Env Unit} [base ≼ env] {α : Type}
    (cts : NameMap (TypeExpr env)) (tbl : NameMap (Nat × TypeExpr env)) (fn : Func env α) : Bool :=
  let refs := Block.refs fn.allBlocks
  refs.1.toList.all (fun u => decide (OptHolds (cts.find? u.target) u.Fits)) &&
    refs.2.toList.all fun u => decide (u.Fits tbl)

/-- `Func.refsFitB` decides that the function references and the ghost references of `fn` fit. -/
private theorem Func.refsFitB_iff {env : Env Unit} [base ≼ env] {α : Type}
    {cts : NameMap (TypeExpr env)} {tbl : NameMap (Nat × TypeExpr env)} {fn : Func env α} :
    fn.refsFitB cts tbl = true ↔ (∀ u ∈ fn.funcRefs, OptHolds (cts.find? u.target) u.Fits) ∧
      ∀ u ∈ fn.ghostRefs, u.Fits tbl := by
  simp only [Func.refsFitB, Func.funcRefs, Func.ghostRefs, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_eq, Array.mem_toList_iff]

/-- Deciding `Module.Raw.OwnWFIn` in linear time.  One set of names shows that the ghosts' and the
functions' names are distinct, which gives that the functions' names are, and one pass over each
function's blocks collects both kinds of its references.  It decides over lists: Lean decides a
quantifier over an array's members in time quadratic in its size. -/
instance {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α)
    (cts : NameMap (TypeExpr env)) (tbl : NameMap (Nat × TypeExpr env)) :
    Decidable (m.OwnWFIn cts tbl) :=
  have := Name.decNodup (m.ghostNames ++ m.funcNames)
  decidable_of_iff ((m.ghostNames ++ m.funcNames).toList.Nodup ∧
      m.funcs.toList.all (·.refsFitB cts tbl) = true ∧
      (∀ g ∈ m.ghosts.toList, ∀ u ∈ g.ghostRefs.toList, u.Fits tbl) ∧ m.GhostOrderIn tbl) (by
    simp only [Module.Raw.OwnWFIn, Module.Raw.GhostRefsIn, List.all_eq_true, Func.refsFitB_iff,
      Array.mem_toList_iff]
    constructor
    · rintro ⟨hn, hf, hgg, ho⟩
      refine ⟨?_, fun f hm => (hf f hm).1, hn, ⟨fun f hm => (hf f hm).2, hgg⟩, ho⟩
      rw [Array.toList_append] at hn
      exact hn.sublist (List.sublist_append_right _ _)
    · rintro ⟨-, hr, hn, ⟨hgf, hgg⟩, ho⟩
      exact ⟨hn, fun f hm => ⟨hr f hm, hgf f hm⟩, hgg, ho⟩)

/-- A module whose own rules hold, and whose functions and ghosts are each well formed, is well
formed. -/
theorem Module.Raw.WF.of_own {env : Env Unit} [base ≼ env] {α : Type} {m : Module.Raw env α}
    (h : m.OwnWFIn m.codeTypes m.ghostTable) (hf : ∀ f ∈ m.funcs, f.WF)
    (hg : ∀ g ∈ m.ghosts, g.WF) : m.WF :=
  let ⟨a, b, c, d, e⟩ := h
  ⟨a, hf, b, c, hg, d, e⟩

/-- A well-formed module's own rules hold. -/
private theorem Module.Raw.WF.own {env : Env Unit} [base ≼ env] {α : Type} {m : Module.Raw env α}
    (h : m.WF) : m.OwnWFIn m.codeTypes m.ghostTable :=
  ⟨h.funcNamesUnique, h.refs, h.ghostNamesUnique, h.ghostRefs, h.ghostOrder⟩

-- Over lists: deciding a quantifier over an array's members takes time quadratic in its size.
instance {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α) : Decidable m.WF :=
  let cts := m.codeTypes
  let tbl := m.ghostTable
  decidable_of_iff (m.OwnWFIn cts tbl ∧ (∀ f ∈ m.funcs.toList, f.WF) ∧
      ∀ g ∈ m.ghosts.toList, g.WF)
    ⟨fun ⟨h, hf, hg⟩ => .of_own h (fun f hf' => hf f (by simpa using hf'))
        (fun g hg' => hg g (by simpa using hg')),
      fun h => ⟨by exact Module.Raw.WF.own h, fun f hf => h.funcs f (by simpa using hf),
        fun g hg => h.ghosts g (by simpa using hg)⟩⟩

/-- A module with its well-formedness proof. -/
structure Module (env : Env Unit) [base ≼ env] (α : Type) where
  raw : Module.Raw env α
  wf : raw.WF

/-- The names `check` gives for an ill-formed `m`: all its functions' if two functions share a
name, else all its ghosts' if two ghosts share a name or a ghost has the name of a function,
otherwise those of the functions that `badFunc` flags or that have a reference that names no
function or ghost of `m`, or at a type that does not fit, then those of the ghosts that
`badGhost` flags, that have a ghost reference that names no ghost of `m` or at a type that does
not fit, or whose initializer names a ghost declared after it. -/
private def Module.Raw.faulty {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α)
    (badFunc : Func env α → Bool) (badGhost : Ghost env α → Bool) : Array Name :=
  have := Name.decNodup (m.ghostNames ++ m.funcNames)
  match NameMap.ofArray? m.funcSigs with
  | none => m.funcNames
  | some cts =>
    if !decide (m.ghostNames ++ m.funcNames).toList.Nodup then m.ghostNames
    else
      let tbl := m.ghostTable
      let badRef (u : FuncUse env) := !decide (OptHolds (cts.find? u.target) u.Fits)
      let badGhostRef (u : GhostUse env) := !decide (u.Fits tbl)
      (m.funcs.filter fun f =>
          badFunc f || f.funcRefs.any badRef || f.ghostRefs.any badGhostRef).map (·.name) ++
        (m.ghosts.zipIdx.filter fun (g, i) =>
          badGhost g || g.ghostRefs.any badGhostRef ||
            g.initRefs.any fun u => !decide (u.Before tbl i)).map (·.1.name)

/-- `m` with its well-formedness proof, or the names of its functions and ghosts that are not
well formed: those that fail `Func.WF` or `Ghost.WF`, have a reference that names no function or
ghost of `m` or does not fit its target's type, or are ghosts whose initializer names a ghost
declared after it; all its functions if `m` names a function twice, and all its ghosts if it
names a ghost twice or a ghost like a function. -/
def Module.Raw.check {env : Env Unit} [base ≼ env] {α : Type} (m : Module.Raw env α) :
    Except (Array Name) (Module env α) :=
  if h : m.WF then .ok ⟨m, h⟩ else .error (m.faulty (fun f => !decide f.WF) (fun g => !decide g.WF))

/-- The module `name` of the well-formed functions `fs` and ghosts `ghosts`, or the names
`Module.Raw.check` gives.  Only the module's own rules are decided (`Module.Raw.OwnWFIn`): distinct
names, references that name its functions and ghosts at types that fit, and initializers that name
only the ghosts declared before their own. -/
def Module.ofChecked {env : Env Unit} [base ≼ env] {α : Type} (name : Name)
    (fs : Array {f : Func env α // f.WF}) (info : α)
    (ghosts : Array {g : Ghost env α // g.WF} := #[]) : Except (Array Name) (Module env α) :=
  let m : Module.Raw env α := { name, ghosts := ghosts.map (·.val), funcs := fs.map (·.val), info }
  let cts := m.codeTypes
  let tbl := m.ghostTable
  if h : m.OwnWFIn cts tbl then
    have hfs : ∀ f ∈ m.funcs, f.WF := fun f hf => by
      obtain ⟨g, -, rfl⟩ := Array.mem_map.mp hf
      exact g.property
    have hgs : ∀ g ∈ m.ghosts, g.WF := fun g hg => by
      obtain ⟨g', -, rfl⟩ := Array.mem_map.mp hg
      exact g'.property
    .ok ⟨m, .of_own h hfs hgs⟩
  else .error (m.faulty (fun _ => false) (fun _ => false))

end

/-- A well-formed module names no function twice. -/
public theorem Module.Raw.WF.nodup {env : Env Unit} [base ≼ env] {α : Type}
    {m : Module.Raw env α} (h : m.WF) : (m.funcs.toList.map (·.name)).Nodup := by
  simpa [Module.Raw.funcNames, Array.mapK_eq_map_fun] using h.funcNamesUnique

/-- The map a well-formed module checks function references against gives each function's
code type, and nothing else. -/
public theorem Module.Raw.WF.find?_codeTypes {env : Env Unit} [base ≼ env] {α : Type}
    {m : Module.Raw env α} (h : m.WF) (n : Name) (t : TypeExpr env) :
    m.codeTypes.find? n = some t ↔ ∃ f ∈ m.funcs, f.name = n ∧ f.codeType = t := by
  have hnd : (m.funcSigs.toList.map Prod.fst).Nodup := by
    simpa [Module.Raw.funcSigs, Module.Raw.funcNames, Array.mapK_eq_map_fun,
      Function.comp_def] using h.funcNamesUnique
  obtain ⟨cts, hcts⟩ := Option.isSome_iff_exists.mp (NameMap.ofArray?_isSome_iff.mpr hnd)
  rw [Module.Raw.codeTypes, hcts, Option.getD_some, NameMap.find?_ofArray? hcts,
    Module.Raw.funcSigs, Array.mapK_eq_map_fun, Array.mem_map]
  simp only [Prod.mk.injEq]

/-- In a well-formed module, every function reference names one of its functions, and fits
that function's code type. -/
public theorem Module.Raw.WF.ref_fits {env : Env Unit} [base ≼ env] {α : Type}
    {m : Module.Raw env α} (h : m.WF) {f : Func env α} (hf : f ∈ m.funcs) {u : FuncUse env}
    (hu : u ∈ f.funcRefs) : ∃ g ∈ m.funcs, g.name = u.target ∧ u.Fits g.codeType := by
  obtain ⟨t, ht, hfit⟩ := h.refs f hf u hu
  obtain ⟨g, hg, hn, rfl⟩ := (h.find?_codeTypes u.target t).mp ht
  exact ⟨g, hg, hn, hfit⟩

end Strata.Dyn
