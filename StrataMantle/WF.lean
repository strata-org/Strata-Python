/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.IR
-- The instances evaluate the environment representation at code-generation time.
import StrataMantle.Env.WF

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
* a `Func` has an entry block, uses no label twice nor `Label.exit` at all and defines no
  value twice, counting every region, and every block is well formed in the context those
  definitions give, its exit taking the function's return type;
* a `Module` names no function twice, and its functions are all well formed.

`Decidable` instances decide every predicate, so `decide` is the checker.  The combinators
`OptHolds` and `Agrees` keep the rules decidable, and the checker's maps are tries, so
`decide +kernel` runs it in the kernel.

The rules do not check:

* **Scoping.** An operand is typed by its definition anywhere in the function, so a use
  before its definition, a use of a value outside the region that defines it, and a
  handler's use of the result of the operation that failed are all accepted.
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

The checker's maps are tries, so `decide +kernel` evaluates it:

* `NatTrie`: a map from `Nat`, on the key's binary digits;
* `LabelMap`: a map from labels, on each label's counter;
* `Label.Distinct`: no label occurs twice, decided through a `LabelMap`. -/

/-- A map from `Nat`: a trie on the key's bijective binary digits.  Key `0` is at the root,
and `2k+1` and `2k+2` are key `k` of the left and right subtrees. -/
inductive NatTrie (β : Type) where
  | leaf
  | node (v : Option β) (l r : NatTrie β)

namespace NatTrie

variable {β : Type}

/-- The value at `k`, if any. -/
@[expose] def find? : NatTrie β → Nat → Option β
  | .leaf, _ => none
  | .node v _ _, 0 => v
  | .node _ l r, n + 1 => if n % 2 = 0 then l.find? (n / 2) else r.find? (n / 2)

/-- Map `k` to `x` at most `fuel` levels down. -/
@[expose] def insertAt (x : β) : (fuel : Nat) → NatTrie β → Nat → NatTrie β
  | 0, t, _ => t
  | _ + 1, .leaf, 0 => .node (some x) .leaf .leaf
  | _ + 1, .node _ l r, 0 => .node (some x) l r
  | f + 1, .leaf, n + 1 =>
    if n % 2 = 0 then .node none (insertAt x f .leaf (n / 2)) .leaf
    else .node none .leaf (insertAt x f .leaf (n / 2))
  | f + 1, .node v l r, n + 1 =>
    if n % 2 = 0 then .node v (insertAt x f l (n / 2)) r else .node v l (insertAt x f r (n / 2))

/-- `t` with `k` mapped to `x`.  Key `k` is at most `k` levels down. -/
@[expose] def insert (t : NatTrie β) (k : Nat) (x : β) : NatTrie β := insertAt x (k + 1) t k

end NatTrie

/-- The key of a label in a `LabelMap`: its counter, or `0` if it has none. -/
@[expose] def Label.key : Label → Nat
  | ⟨.num _ i⟩ => i
  | _ => 0

/-- A map from labels: per key, the labels with that key and their values, latest first. -/
structure LabelMap (β : Type) where
  trie : NatTrie (List (Label × β)) := .leaf

namespace LabelMap

variable {β : Type}

instance : EmptyCollection (LabelMap β) := ⟨⟨.leaf⟩⟩

/-- The labels with `l`'s key, and their values. -/
@[expose] def bucket (m : LabelMap β) (l : Label) : List (Label × β) :=
  (m.trie.find? l.key).getD []

/-- The value at `l`, if any. -/
@[expose] def find? (m : LabelMap β) (l : Label) : Option β :=
  ((m.bucket l).find? fun p => decide (p.1 = l)).map (·.2)

/-- `m` with `l` mapped to `x`. -/
@[expose] def insert (m : LabelMap β) (l : Label) (x : β) : LabelMap β :=
  ⟨m.trie.insert l.key ((l, x) :: m.bucket l)⟩

/-- The labels `ls`, as a set, or `none` if one occurs twice. -/
@[expose] def ofDistinct? (ls : List Label) : Option (LabelMap Unit) :=
  ls.foldlM (init := ∅) fun m l => if (m.find? l).isSome then none else some (m.insert l ())

end LabelMap

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
  types : NatTrie (TypeExpr env 0)

namespace Ctx

/-- No value defined yet. -/
@[expose] def empty {env : Env Unit} : Ctx env := ⟨.leaf⟩

instance {env : Env Unit} : EmptyCollection (Ctx env) := ⟨empty⟩

/-- Record a definition, or fail if the id already has one. -/
@[expose] def define? {env : Env Unit} (ctx : Ctx env) (d : ValDecl env) : Option (Ctx env) :=
  if (ctx.types.find? d.id.id).isSome then none else some ⟨ctx.types.insert d.id.id d.type⟩

/-- The type of a value, if it is defined. -/
@[expose] def typeOf? {env : Env Unit} (ctx : Ctx env) (v : ValId) : Option (TypeExpr env 0) :=
  ctx.types.find? v.id

/-- The types of an operand list, if every operand is defined. -/
@[expose] def typesOf? {env : Env Unit} (ctx : Ctx env) (vs : Array ValId) :
    Option (Array (TypeExpr env 0)) :=
  vs.mapM ctx.typeOf?

end Ctx

/-! ## Transfers

A transfer names a block and pre-binds a prefix of its arguments; what the block
still expects is what the operation taking the transfer supplies: its successor's declared
values. -/

/-- The parameter types of the blocks a transfer may name: those of one region, or of the
function's top level, other than its entry, and the exit. -/
abbrev BlockSigs (env : Env Unit) := LabelMap (Array (TypeExpr env 0))

/-- The transfer targets of a body: `Label.exit`, taking the body's result `result`, and
each of `blocks` but the head, which is the entry. -/
@[expose] def BlockSigs.of {env : Env Unit} {α : Type} (blocks : List (Block env α))
    (result : TypeExpr env 0) : BlockSigs env :=
  (blocks.drop 1).foldl (init := (∅ : BlockSigs env).insert Label.exit #[result])
    fun m b => m.insert b.label (b.params.map (·.type))

/-- The parameter types a transfer to `k` implies for its target: what it supplies,
then what it leaves for the site. -/
@[expose] def BlockValue.implies? {env : Env Unit} (ctx : Ctx env) (k : BlockValue)
    (expects : Array (TypeExpr env 0)) : Option (Array (TypeExpr env 0)) :=
  (ctx.typesOf? k.args).map (· ++ expects)

/-- A transfer is well formed when its target is a block of `bs` and declares exactly
the parameters the transfer implies. -/
@[expose, reducible] def BlockValue.WF {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env)
    (k : BlockValue) (expects : Array (TypeExpr env 0)) : Prop :=
  Agrees (bs.find? k.target) (k.implies? ctx expects)

/-- Each transfer of `ks` is well formed at the corresponding entry of `expects`: one per
entry, in order, as an operation's successors against their declared values. -/
@[expose, reducible] def BlockValue.AllWF {env : Env Unit} (ctx : Ctx env)
    (bs : BlockSigs env) (ks : Array BlockValue)
    (expects : Array (Array (TypeExpr env 0))) : Prop :=
  ks.size = expects.size ∧ ∀ p ∈ ks.zip expects, BlockValue.WF ctx bs p.1 p.2

instance {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env) (ks : Array BlockValue)
    (expects : Array (Array (TypeExpr env 0))) :
    Decidable (BlockValue.AllWF ctx bs ks expects) :=
  inferInstanceAs (Decidable (ks.size = expects.size ∧
    ∀ p ∈ ks.zip expects, BlockValue.WF ctx bs p.1 p.2))

/-! ## Operations -/

/-- What an operation's successors receive at its type arguments: per successor, in order. -/
@[expose] def InsnSig.succTypes {env : Env Unit} (isig : InsnSig env)
    (typeArgs : Vector (TypeExpr env 0) isig.typeArgc) : Array (Array (TypeExpr env 0)) :=
  isig.succs.map fun p => p.type.map (·.instantiate typeArgs)

/-- An operation's operands and successors, wherever it sits: its operands have the types
its signature demands at `typeArgs`, and it names one block of `bs` per declared successor,
each receiving that successor's declared values after what the site pre-binds. -/
@[expose, reducible] def InsnSig.callWF {env : Env Unit} (ctx : Ctx env) (bs : BlockSigs env)
    (isig : InsnSig env) (typeArgs : Vector (TypeExpr env 0) isig.typeArgc)
    (args : Array ValId) (succs : Array BlockValue) : Prop :=
  Agrees (ctx.typesOf? args) (isig.operandTypes? typeArgs args.size) ∧
    BlockValue.AllWF ctx bs succs (isig.succTypes typeArgs)

/-- What a region must be: its entry block's parameter types, and the type its exit takes. -/
abbrev RegionType (env : Env Unit) := Array (TypeExpr env 0) × TypeExpr env 0

/-- What each region of an operation must be, at its type arguments. -/
@[expose] def InsnSig.regionTypes {env : Env Unit} (isig : InsnSig env)
    (typeArgs : Vector (TypeExpr env 0) isig.typeArgc) : List (RegionType env) :=
  isig.regions.toList.map fun p =>
    (p.type.params.map (·.type.instantiate typeArgs), p.type.returnType.instantiate typeArgs)

/-- A region's entry block exists and takes exactly `params`. -/
@[expose, reducible] def Region.entryWF {env : Env Unit} {α : Type}
    (params : Array (TypeExpr env 0)) (blocks : List (Block env α)) : Prop :=
  blocks.head?.map (fun b => b.params.map (·.type)) = some params

/-! ## Instructions, terminators, blocks and regions -/

/-- A constant's rule, with `funcs` the module's functions: a function reference names one of
them. -/
@[expose, reducible] def Const.WF (funcs : Array Name) : Const → Prop
  | .func target => target ∈ funcs
  | _ => True

instance (funcs : Array Name) (c : Const) : Decidable (c.WF funcs) :=
  match c with
  | .func target => inferInstanceAs (Decidable (target ∈ funcs))
  | .unit | .bool _ | .int _ | .float _ | .str _ => inferInstanceAs (Decidable True)

mutual

/-- An instruction's rule, in the context `ctx`, with `bs` the blocks its successors may name
and `funcs` the module's functions.

* A constant defines a value of the type the base gives it.  A function-reference constant
  names a function of the module.
* An application has a return type, which its result has at the type arguments, satisfies
  `InsnSig.callWF`, and supplies one region per declared region, each well formed at the
  declared types.  A constructor is applied as any operation is: its signature is the one
  `Env.addData` derived from its datatype. -/
@[expose] def Instruction.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) (funcs : Array Name) : Instruction env α → Prop
  | .const _ d c => d.type = c.typeOf ∧ c.WF funcs
  | @Instruction.apply _ _ _ d isig _ typeArgs args succs ⟨regions⟩ =>
    isig.returnType.map (·.instantiate typeArgs) = some d.type ∧
      isig.callWF ctx bs typeArgs args succs ∧
      Region.WFList ctx funcs (isig.regionTypes typeArgs) regions

/-- `Instruction.WF` of each. -/
@[expose] def Instruction.WFList {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) (funcs : Array Name) :
    List (Instruction env α) → Prop
  | [] => True
  | i :: is => Instruction.WF ctx bs funcs i ∧ Instruction.WFList ctx bs funcs is

/-- A terminator's rule: a terminal operation, one with no return type, satisfying
`InsnSig.callWF`, that supplies its regions as `Instruction.apply` does.  Any successor may be
taken and any region run. -/
@[expose] def Terminator.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) (funcs : Array Name) : Terminator env α → Prop
  | @Terminator.apply _ _ _ isig _ typeArgs args succs ⟨regions⟩ =>
    isig.returnType = none ∧ isig.callWF ctx bs typeArgs args succs ∧
      Region.WFList ctx funcs (isig.regionTypes typeArgs) regions

/-- A block is well formed when its instructions and its terminator are, against the
blocks `bs` of its region.  `Func.ctx?` checks its parameters. -/
@[expose] def Block.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) (funcs : Array Name) : Block env α → Prop
  | ⟨_, _, ⟨instrs⟩, term, _⟩ =>
    Instruction.WFList ctx bs funcs instrs ∧ Terminator.WF ctx bs funcs term

/-- `Block.WF` of each. -/
@[expose] def Block.WFList {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (bs : BlockSigs env) (funcs : Array Name) : List (Block env α) → Prop
  | [] => True
  | b :: l => Block.WF ctx bs funcs b ∧ Block.WFList ctx bs funcs l

/-- A region is well formed at `sig` when its entry block takes `sig`'s parameters and
every block is well formed against the region's own blocks and its exit, taking `sig`'s
result.  So control leaves the region only through its exit, with a value of the declared
type. -/
@[expose] def Region.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (funcs : Array Name) (sig : RegionType env) : Region env α → Prop
  | ⟨⟨blocks⟩⟩ =>
    Region.entryWF sig.1 blocks ∧ Block.WFList ctx (BlockSigs.of blocks sig.2) funcs blocks

/-- One region per signature, each well formed at it: the same number, in the same order. -/
@[expose] def Region.WFList {env : Env Unit} {α : Type} [base ⊑ env]
    (ctx : Ctx env) (funcs : Array Name) :
    List (RegionType env) → List (Region env α) → Prop
  | [], [] => True
  | s :: ss, r :: rs => Region.WF ctx funcs s r ∧ Region.WFList ctx funcs ss rs
  | _, _ => False

end

section Decide

variable {env : Env Unit} {α : Type} [base ⊑ env] (ctx : Ctx env) (funcs : Array Name)

mutual

/-- Deciding `Instruction.WF`. -/
def Instruction.decWF (bs : BlockSigs env) :
    (i : Instruction env α) → Decidable (Instruction.WF ctx bs funcs i)
  | .const _ d c => inferInstanceAs (Decidable (d.type = c.typeOf ∧ c.WF funcs))
  | @Instruction.apply _ _ _ d isig _ typeArgs args succs ⟨regions⟩ =>
    have := Region.decWFList (isig.regionTypes typeArgs) regions
    inferInstanceAs (Decidable
      (isig.returnType.map (·.instantiate typeArgs) = some d.type ∧
        isig.callWF ctx bs typeArgs args succs ∧
        Region.WFList ctx funcs (isig.regionTypes typeArgs) regions))

/-- Deciding `Instruction.WFList`. -/
def Instruction.decWFList (bs : BlockSigs env) :
    (is : List (Instruction env α)) → Decidable (Instruction.WFList ctx bs funcs is)
  | [] => inferInstanceAs (Decidable True)
  | i :: is =>
    have := Instruction.decWF bs i
    have := Instruction.decWFList bs is
    inferInstanceAs
      (Decidable (Instruction.WF ctx bs funcs i ∧ Instruction.WFList ctx bs funcs is))

/-- Deciding `Terminator.WF`. -/
def Terminator.decWF (bs : BlockSigs env) :
    (t : Terminator env α) → Decidable (Terminator.WF ctx bs funcs t)
  | @Terminator.apply _ _ _ isig _ typeArgs args succs ⟨regions⟩ =>
    have := Region.decWFList (isig.regionTypes typeArgs) regions
    inferInstanceAs (Decidable
      (isig.returnType = none ∧ isig.callWF ctx bs typeArgs args succs ∧
        Region.WFList ctx funcs (isig.regionTypes typeArgs) regions))

/-- Deciding `Block.WF`. -/
def Block.decWF (bs : BlockSigs env) :
    (b : Block env α) → Decidable (Block.WF ctx bs funcs b)
  | ⟨_, _, ⟨instrs⟩, term, _⟩ =>
    have := Instruction.decWFList bs instrs
    have := Terminator.decWF bs term
    inferInstanceAs (Decidable (Instruction.WFList ctx bs funcs instrs ∧
      Terminator.WF ctx bs funcs term))

/-- Deciding `Block.WFList`. -/
def Block.decWFList (bs : BlockSigs env) :
    (l : List (Block env α)) → Decidable (Block.WFList ctx bs funcs l)
  | [] => inferInstanceAs (Decidable True)
  | b :: l =>
    have := Block.decWF bs b
    have := Block.decWFList bs l
    inferInstanceAs (Decidable (Block.WF ctx bs funcs b ∧ Block.WFList ctx bs funcs l))

/-- Deciding `Region.WF`. -/
def Region.decWF (sig : RegionType env) :
    (r : Region env α) → Decidable (Region.WF ctx funcs sig r)
  | ⟨⟨blocks⟩⟩ =>
    have := Block.decWFList (BlockSigs.of blocks sig.2) blocks
    inferInstanceAs (Decidable (Region.entryWF sig.1 blocks ∧
      Block.WFList ctx (BlockSigs.of blocks sig.2) funcs blocks))

/-- Deciding `Region.WFList`. -/
def Region.decWFList :
    (sigs : List (RegionType env)) → (rs : List (Region env α)) →
      Decidable (Region.WFList ctx funcs sigs rs)
  | [], [] => inferInstanceAs (Decidable True)
  | s :: ss, r :: rs =>
    have := Region.decWF s r
    have := Region.decWFList ss rs
    inferInstanceAs (Decidable (Region.WF ctx funcs s r ∧ Region.WFList ctx funcs ss rs))
  | [], _ :: _ => inferInstanceAs (Decidable False)
  | _ :: _, [] => inferInstanceAs (Decidable False)

end

instance (bs : BlockSigs env) (i : Instruction env α) :
    Decidable (Instruction.WF ctx bs funcs i) := Instruction.decWF ctx funcs bs i

instance (bs : BlockSigs env) (t : Terminator env α) :
    Decidable (Terminator.WF ctx bs funcs t) := Terminator.decWF ctx funcs bs t

instance (bs : BlockSigs env) (b : Block env α) :
    Decidable (Block.WF ctx bs funcs b) := Block.decWF ctx funcs bs b

instance (sig : RegionType env) (r : Region env α) :
    Decidable (Region.WF ctx funcs sig r) := Region.decWF ctx funcs sig r

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

/-- Every value the function defines, in order: each block's parameters (the entry block's
are the function's own) and each instruction's result, regions included. -/
@[expose] def Func.defs {env : Env Unit} {α : Type} (fn : Func env α) : Array (ValDecl env) :=
  (fn.allBlocks.flatMap fun b =>
    b.params.toList ++ b.instrs.toList.map Instruction.result).toArray

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

/-- A function is well formed when it has an entry block, uses no label twice, nor
`Label.exit`, and defines no value twice, regions included, and every top-level block is well
formed in the context those definitions give, against the top-level blocks and the exit.

No transfer names an entry block, the function's or a region's: `BlockSigs.of` leaves
entries out. -/
@[expose, reducible] def Func.WF {env : Env Unit} {α : Type} [base ⊑ env]
    (funcs : Array Name) (fn : Func env α) : Prop :=
  0 < fn.blocks.size ∧ Label.Distinct (Label.exit :: fn.labels) ∧
    OptHolds fn.ctx? fun ctx =>
      ∀ b ∈ fn.blocks, Block.WF ctx fn.blockSigs funcs b

/-- A module is well formed when it names no function twice and every function in it is
well formed. -/
@[expose, reducible] def Module.WF {env : Env Unit} [base ⊑ env] {α : Type}
    (m : Module env α) : Prop :=
  (m.funcs.toList.map (·.name)).Nodup ∧ ∀ f ∈ m.funcs, Func.WF (m.funcs.map (·.name)) f

end

end Strata.Mantle
