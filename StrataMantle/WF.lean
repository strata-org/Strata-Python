/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR
public import StrataMantle.Util.NameMap
public import StrataMantle.Util.LabelMap
public import StrataMantle.DomProps
public import StrataMantle.DomDecide
public import StrataMantle.Util.Array
-- The instances evaluate the environment representation at code-generation time.
import StrataMantle.Env.WF
import all StrataMantle.Util.LabelMapProps

set_option autoImplicit false

/-!
# Well-formedness of the IR

One predicate per level, each stated as an equation between what a site supplies and
what the thing it names demands:

* an `Instruction`'s operands have the types its signature demands at the type
  arguments it supplies, and its result is what that signature returns, a constructor's
  as any other operation's.  An operation is not terminal, and supplies exactly the
  successors and regions its signature declares: each successor is a non-entry block of
  its own region, or the region's exit, and receives exactly the parameters it declares;
  each region is well formed at the signature's region types;
* a `Terminator` is checked as an instruction's operation is, but must be terminal and
  defines no result;
* a `Block`'s instructions and terminator are well formed;
* a `Region`'s entry block takes the declared parameters, and every block is well formed
  against the region's own blocks and its exit, `Label.exit`, which takes the region's
  result;
* a `Func` has an entry block, uses no label twice nor `Label.exit` at all, defines no
  value twice and names every value it defines, no two alike, counting every region, and
  every block is well formed in the context those definitions give, its exit taking the
  function's return type; every block of every body is reachable from the body's entry, and
  some legal tree of each body puts every use in scope;
* a `Module.Raw` names no function twice, its functions are all well formed, and every
  function reference names one of them, at that function's code type or at the untyped
  `base.Code`.

A function's rules depend on the function alone, so a function can be checked before its
module is assembled.

A `Module` is a `Module.Raw` with its proof.  `Module.Raw.check` gives one by running the
checker, and `Module.ofChecked` gives one from checked functions, deciding only the module's
own rules.

`Decidable` instances decide every predicate, so `decide` is the checker.

An operand has the type its definition gives it, wherever in the function that is.  Where a
value may be used is the separate rule `Func.Scopable` (`StrataMantle/Dom.lean`): for each body
some legal dominator tree puts every use in scope, defined above it in that tree or in scope
where the enclosing region's owner runs.  The IR stores no tree; the checker computes one
(`StrataMantle/DomDecide.lean`).  So the rules reject a use before its definition, a use of a
value outside the region that defines it, and a handler's use of the result of the operation
that failed.  Every block must also be reachable from its body's entry (`Func.Reachable`).

The rules do not check:

* **Effects.** `Ref` makes instruction order observable, and these rules say nothing about
  reordering instructions.

Nothing here mentions the annotation type `α`.
-/

namespace Strata.Mantle

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

* `NatTrie` and `LabelMap` (`StrataMantle.Util.LabelMap`): maps from `Nat` and from labels;
* `Label.Distinct`: no label occurs twice, decided through a `LabelMap`;
* `NameMap` and `NameSet` (`StrataMantle.Util.NameMap`): a map and a set of names, as a 2-3
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

/-- The parameter types a transfer to `k` implies for its target: what it supplies,
then what it leaves for the site. -/
@[expose] def BlockValue.implies? {env : Env Unit} (ctx : Ctx env) (k : BlockValue)
    (expects : Array (TypeExpr env)) : Option (Array (TypeExpr env)) :=
  (ctx.typesOf? k.args).map (· ++ expects)

/-- A transfer is well formed when its target is a block of `bs` and declares exactly
the parameters the transfer implies. -/
@[expose, reducible] def BlockValue.WF {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env)
    (k : BlockValue) (expects : Array (TypeExpr env)) : Prop :=
  Agrees (bs.find? k.target) (k.implies? ctx expects)

/-- Each transfer of `ks` is well formed at the corresponding entry of `expects`: one per
entry, in order, as an operation's successors against their declared values. -/
@[expose, reducible] def BlockValue.AllWF {env : Env Unit} (ctx : Ctx env)
    (bs : BlockSigs env) (ks : Array BlockValue)
    (expects : Array (Array (TypeExpr env))) : Prop :=
  ks.size = expects.size ∧ ∀ p ∈ ks.zip expects, BlockValue.WF ctx bs p.1 p.2

instance {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env) (ks : Array BlockValue)
    (expects : Array (Array (TypeExpr env))) :
    Decidable (BlockValue.AllWF ctx bs ks expects) :=
  inferInstanceAs (Decidable (ks.size = expects.size ∧
    ∀ p ∈ ks.zip expects, BlockValue.WF ctx bs p.1 p.2))

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
    (args : Array ValId) (succs : Array BlockValue) : Prop :=
  Agrees (ctx.typesOf? args) (isig.operandTypes? typeArgs args.size) ∧
    BlockValue.AllWF ctx bs succs (isig.succTypes typeArgs)

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

/-- A constant's rule, at the type `t` of the value it defines: a literal has the type the
base gives it.  A function reference may have any type here: which types its target allows is
the module's rule, `Module.Raw.WF`. -/
@[expose] def Const.WF {env : Env Unit} [base ⊑ env] (t : TypeExpr env) : Const → Prop
  | .func _ => True
  | c => t = c.typeOf

instance {env : Env Unit} [base ⊑ env] (t : TypeExpr env) : (c : Const) → Decidable (c.WF t)
  | .func _ => inferInstanceAs (Decidable True)
  | .unit | .bool _ | .int _ | .float _ | .str _ => inferInstanceAs (Decidable (t = _))

mutual

/-- An instruction's rule, in the context `ctx`, with `bs` the blocks its successors may name.

* A constant satisfies `Const.WF` at the type of the value it defines.  Whether a function
  reference names a function of the module, and at which type, is `Module.Raw.WF`'s rule.
* An application has a return type, which its result has at the type arguments, satisfies
  `InsnSig.callWF`, and supplies one region per declared region, each well formed at the
  declared types.  A constructor is applied as any operation is: its signature is the one
  `Env.addData` derived from its datatype. -/
@[expose] def Instruction.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) : Instruction env α → Prop
  | .const _ d c => c.WF d.type
  | @Instruction.apply _ _ _ d isig _ typeArgs args succs ⟨regions⟩ =>
    isig.returnType.map (·.instantiate typeArgs) = some d.type ∧
      isig.callWF ctx bs typeArgs args succs ∧
      Region.WFList ctx (isig.regionTypes typeArgs) regions

/-- `Instruction.WF` of each. -/
@[expose] def Instruction.WFList {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) :
    List (Instruction env α) → Prop
  | [] => True
  | i :: is => Instruction.WF ctx bs i ∧ Instruction.WFList ctx bs is

/-- A terminator's rule: a terminal operation, one with no return type, satisfying
`InsnSig.callWF`, that supplies its regions as `Instruction.apply` does.  Any successor may be
taken and any region run. -/
@[expose] def Terminator.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) : Terminator env α → Prop
  | @Terminator.apply _ _ _ isig _ typeArgs args succs ⟨regions⟩ =>
    isig.returnType = none ∧ isig.callWF ctx bs typeArgs args succs ∧
      Region.WFList ctx (isig.regionTypes typeArgs) regions

/-- A block is well formed when its instructions and its terminator are, against the
blocks `bs` of its region.  `Func.ctx?` checks its parameters. -/
@[expose] def Block.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) : Block env α → Prop
  | ⟨_, _, ⟨instrs⟩, term, _⟩ =>
    Instruction.WFList ctx bs instrs ∧ Terminator.WF ctx bs term

/-- `Block.WF` of each. -/
@[expose] def Block.WFList {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) : List (Block env α) → Prop
  | [] => True
  | b :: l => Block.WF ctx bs b ∧ Block.WFList ctx bs l

/-- A region is well formed at `sig` when its entry block takes `sig`'s parameters and
every block is well formed against the region's own blocks and its exit, taking `sig`'s
result.  So control leaves the region only through its exit, with a value of the declared
type. -/
@[expose] def Region.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (sig : RegionType env) : Region env α → Prop
  | ⟨⟨blocks⟩⟩ =>
    Region.entryWF sig.1 blocks ∧ Block.WFList ctx (BlockSigs.of blocks sig.2) blocks

/-- One region per signature, each well formed at it: the same number, in the same order. -/
@[expose] def Region.WFList {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) :
    List (RegionType env) → List (Region env α) → Prop
  | [], [] => True
  | s :: ss, r :: rs => Region.WF ctx s r ∧ Region.WFList ctx ss rs
  | _, _ => False

end

section Decide

variable {env : Env Unit} {α : Type} [base ⊑ env] (ctx : Ctx env)

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

/-- Every block of the function: its own and those of every region, at any depth. -/
@[expose] def Func.allBlocks {env : Env Unit} {α : Type} (fn : Func env α) :
    List (Block env α) :=
  Block.withNestedList fn.blocks.toList

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

/-- Every value the function defines, in the order the printed form writes the definitions:
each block's parameters (the entry block's are the function's own), then each instruction's
result followed by what its regions define, then what the terminator's regions define. -/
@[expose] def Func.defs {env : Env Unit} {α : Type} (fn : Func env α) : List (ValDecl env) :=
  Block.defsList fn.blocks.toList

/-- The ids are `0, 1, …` in the order `Func.defs` lists the definitions, and each value has
one name: what reading a printed function gives. -/
@[expose] def Func.Canonical {env : Env Unit} {α : Type} (fn : Func env α) : Prop :=
  fn.defs.map (·.id.id) = List.range fn.defs.length ∧ fn.names.size = fn.defs.length

instance {env : Env Unit} {α : Type} (fn : Func env α) : Decidable fn.Canonical :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The function's typing context, or `none` if some id is defined twice. -/
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

/-- The rule for a function's blocks: no value is defined twice, regions included, and every
top-level block is well formed, in the context those definitions give, against the top-level
blocks and the exit.  No transfer names an entry block, the function's or a region's:
`BlockSigs.of` leaves entries out. -/
@[expose, reducible] def Func.BodyWF {env : Env Unit} {α : Type} [base ⊑ env]
    (fn : Func env α) : Prop :=
  OptHolds fn.ctx? fun ctx => ∀ b ∈ fn.blocks, Block.WF ctx fn.blockSigs b

/-- A well-formed function.  It depends on the function alone: that the functions it
references exist is its module's rule, `Module.Raw.WF`. -/
structure Func.WF {env : Env Unit} {α : Type} [base ⊑ env] (fn : Func env α) : Prop where
  /-- It has an entry block. -/
  entry : 0 < fn.blocks.size
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

/-- Decide `Func.WF`, its last two fields together, as `Func.checkDom` decides them
(`StrataMantle/DomDecide.lean`). -/
instance {env : Env Unit} {α : Type} [base ⊑ env] (fn : Func env α) : Decidable fn.WF :=
  have := Name.decNodup fn.names
  decidable_of_iff (0 < fn.blocks.size ∧ Label.Distinct (Label.exit :: fn.labels) ∧
      fn.names.toList.Nodup ∧ ValDecl.idBound fn.defs ≤ fn.names.size ∧ Func.BodyWF fn ∧
      (fn.Reachable ∧ fn.Scopable))
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
      fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

/-- Every value a well-formed function defines has a name. -/
theorem Func.WF.mem_names {env : Env Unit} {α : Type} [base ⊑ env] {fn : Func env α}
    (h : fn.WF) {d : ValDecl env} (hd : d ∈ fn.defs) : d.id.id < fn.names.size :=
  (ValDecl.idBound_le_iff _ _).mp h.valuesNamed d hd

/-- A well-formed function is dominance-correct: every use is defined at a point that every
path from its body's entry to the use passes through. -/
theorem Func.WF.domCorrect {env : Env Unit} {α : Type} [base ⊑ env] {fn : Func env α}
    (h : fn.WF) : fn.DomCorrect :=
  h.scoping.domCorrect

/-! ## Scopability is dominance-correctness

For a function whose blocks are all reachable, and whose labels are distinct as `Func.WF` asks,
some tree per body scopes it exactly when it is dominance-correct
(`Func.Reachable.scopable_iff`).  `Func.scopable_iff_domCorrect`
(`StrataMantle/DomComplete.lean`) proves it for distinct labels per body, which the distinct
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
    · rw [if_pos hl] at h
      simp at h
    · rw [if_neg hl] at h
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
    (List.nodup_cons.mp hd.nodup).2)

/-- A function reference: the function it names, and the type of the value it defines. -/
structure FuncUse (env : Env Unit) where
  target : Name
  type : TypeExpr env

/-- Whether a reference fits its target's code type `ct`: it has that type, or the untyped
`base.Code`. -/
-- `base.Code` is accepted until Python's lowering emits typed references.
@[expose] def FuncUse.Fits {env : Env Unit} [base ⊑ env] (u : FuncUse env)
    (ct : TypeExpr env) : Prop :=
  u.type = ct ∨ u.type = Base.Code.ty

instance {env : Env Unit} [base ⊑ env] (u : FuncUse env) (ct : TypeExpr env) :
    Decidable (u.Fits ct) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The function references of `fn`'s constants, regions included. -/
@[expose] def Func.funcRefs {env : Env Unit} {α : Type} (fn : Func env α) :
    Array (FuncUse env) :=
  fn.allBlocks.foldl (init := #[]) fun refs b => b.instrs.foldl (init := refs) fun refs i =>
    match i with
    | .const _ d (.func n) => refs.push ⟨n, d.type⟩
    | _ => refs

/-- The names of a module's functions, in order. -/
@[expose] def Module.Raw.funcNames {env : Env Unit} [base ⊑ env] {α : Type}
    (m : Module.Raw env α) : Array Name :=
  m.funcs.mapK (·.name)

/-- Each function's name with its code type, in order. -/
@[expose] def Module.Raw.funcSigs {env : Env Unit} [base ⊑ env] {α : Type}
    (m : Module.Raw env α) : Array (Name × TypeExpr env) :=
  m.funcs.mapK fun f => (f.name, f.codeType)

/-- Each function's code type, by name, which function references are checked against: empty
if two functions share a name. -/
@[expose] def Module.Raw.codeTypes {env : Env Unit} [base ⊑ env] {α : Type}
    (m : Module.Raw env α) : NameMap (TypeExpr env) :=
  (NameMap.ofArray? m.funcSigs).getD ∅

/-- A well-formed module. -/
structure Module.Raw.WF {env : Env Unit} [base ⊑ env] {α : Type} (m : Module.Raw env α) :
    Prop where
  /-- No two functions share a name. -/
  funcNamesUnique : m.funcNames.toList.Nodup
  /-- Every function is well formed. -/
  funcs : ∀ f ∈ m.funcs, f.WF
  /-- Every function reference names a function of the module, and fits its code type. -/
  refs : ∀ f ∈ m.funcs, ∀ u ∈ f.funcRefs, OptHolds (m.codeTypes.find? u.target) u.Fits

instance {env : Env Unit} [base ⊑ env] {α : Type} (m : Module.Raw env α) : Decidable m.WF :=
  have := Name.decNodup m.funcNames
  let cts := m.codeTypes
  decidable_of_iff (m.funcNames.toList.Nodup ∧ (∀ f ∈ m.funcs, f.WF) ∧
      ∀ f ∈ m.funcs, ∀ u ∈ f.funcRefs, OptHolds (cts.find? u.target) u.Fits)
    ⟨fun ⟨a, b, c⟩ => ⟨a, b, c⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- A module with its well-formedness proof. -/
structure Module (env : Env Unit) [base ⊑ env] (α : Type) where
  raw : Module.Raw env α
  wf : raw.WF

/-- The names `check` gives for an ill-formed `m`: all of them if two coincide, otherwise
those of the functions `bad` flags or that reference a function `m` does not define, or one
at a type that does not fit its code type. -/
private def Module.Raw.faulty {env : Env Unit} [base ⊑ env] {α : Type} (m : Module.Raw env α)
    (bad : Func env α → Bool) : Array Name :=
  match NameMap.ofArray? m.funcSigs with
  | none => m.funcNames
  | some cts =>
    (m.funcs.filter fun f =>
      bad f || f.funcRefs.any fun u => !decide (OptHolds (cts.find? u.target) u.Fits)).map
      (·.name)

/-- `m` with its well-formedness proof, or the names of its functions that are not well
formed: those that fail `Func.WF` or have a reference that names no function of `m` or does
not fit its target's code type, or all of them if `m` names a function twice. -/
def Module.Raw.check {env : Env Unit} [base ⊑ env] {α : Type} (m : Module.Raw env α) :
    Except (Array Name) (Module env α) :=
  if h : m.WF then .ok ⟨m, h⟩ else .error (m.faulty fun f => !decide f.WF)

/-- The module `name` of the well-formed functions `fs`, or the names `Module.Raw.check`
gives.  Only the module's own rules are decided: distinct names, and references that name its
functions at types that fit. -/
def Module.ofChecked {env : Env Unit} [base ⊑ env] {α : Type} (name : Name)
    (fs : Array {f : Func env α // f.WF}) (info : α) : Except (Array Name) (Module env α) :=
  let m : Module.Raw env α := { name, funcs := fs.map (·.val), info }
  have := Name.decNodup m.funcNames
  let cts := m.codeTypes
  if h : m.funcNames.toList.Nodup ∧
      ∀ f ∈ m.funcs, ∀ u ∈ f.funcRefs, OptHolds (cts.find? u.target) u.Fits then
    have hfs : ∀ f ∈ m.funcs, f.WF := fun f hf => by
      obtain ⟨g, -, rfl⟩ := Array.mem_map.mp hf
      exact g.property
    .ok ⟨m, ⟨h.1, hfs, h.2⟩⟩
  else .error (m.faulty fun _ => false)

end

/-- A well-formed module names no function twice. -/
public theorem Module.Raw.WF.nodup {env : Env Unit} [base ⊑ env] {α : Type}
    {m : Module.Raw env α} (h : m.WF) : (m.funcs.toList.map (·.name)).Nodup := by
  simpa [Module.Raw.funcNames, Array.mapK_eq_map_fun] using h.funcNamesUnique

/-- The map a well-formed module checks function references against gives each function's
code type, and nothing else. -/
public theorem Module.Raw.WF.find?_codeTypes {env : Env Unit} [base ⊑ env] {α : Type}
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
public theorem Module.Raw.WF.ref_fits {env : Env Unit} [base ⊑ env] {α : Type}
    {m : Module.Raw env α} (h : m.WF) {f : Func env α} (hf : f ∈ m.funcs) {u : FuncUse env}
    (hu : u ∈ f.funcRefs) : ∃ g ∈ m.funcs, g.name = u.target ∧ u.Fits g.codeType := by
  obtain ⟨t, ht, hfit⟩ := h.refs f hf u hu
  obtain ⟨g, hg, hn, rfl⟩ := (h.find?_codeTypes u.target t).mp ht
  exact ⟨g, hg, hn, hfit⟩

end Strata.Mantle
