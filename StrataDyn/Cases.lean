/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Cases.Shape
public import StrataDyn.Traverse
public import StrataDyn.Util.Suffixes
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Lowering datatype cases to plain control

`cases` replaces each datatype case by tests of the constructors and reads of the fields, then
jumps to the original arm with the arm's own arguments first and the fields after them. It
also moves the arguments of branch arms onto jumps in new blocks, and does both inside
clauses, frames and ghosts. An arm that passes nothing is branched to directly.

The caller names the accessors (`CaseOps`). The pass checks their signatures: pure, the
datatype's type parameters in order, the scrutinee as the one operand, and `base.Bool` or the
field's type as the result. That a tester is true exactly on its constructor, and that a
selector returns the field of a value of its own constructor, is the caller's obligation.
Nothing is asked of a selector on any other constructor.

The pass rewrites the branches and cases it recognises and leaves any other terminator. It
then decides the output shape (`Cased`) and well-formedness of what it built, so the result
carries both proofs. The input shape (`CasesInput`) is the hypothesis under which a failure of
either decision is a defect of the pass; the code does not use it. That the decisions succeed
on every admissible input is not proved. Behaviour is proved equal under every oracle for
validated linked modules that a certificate of the lowering relates, with the accessors' laws
as its hypotheses (`StrataDyn/CasesSound/`); that the linked output of this pass satisfies the
certificate is not proved, so its tests remain the evidence for the pass itself.

New values take the ids after those in use, so a result is not canonical in general
(`Func.Canonical`), as after ref-to-reg. The cost grows with the blocks, the constructor arms
and their fields; lookups are hash maps.
-/

namespace Strata.Dyn

public section

/-- The operations of a datatype's constructors. Missing operations reject cases that need
them. Names refer to instructions in the module's own environment. -/
structure CaseOps where
  tester : Name → Option Name
  selector : Name → String → Option Name

namespace Cases

/-- Why an accessor that a case needs is refused. -/
inductive Reason where
  | noTester (ctor : Name)
  | noSelector (ctor : Name) (field : String)
  | notInstruction (name : Name)
  /-- The accessor does not take the datatype's type parameters. -/
  | typeArgs (name : Name)
  /-- The accessor is not a pure operation from the scrutinee alone to the expected type. -/
  | accessorType (name : Name)
  deriving DecidableEq, Repr

/-- Why `cases` returns no module. -/
inductive Error where
  /-- The first refused accessor, in the module's printed order: the function or ghost and
  the block whose case needs it. -/
  | accessor (owner : Name) (block : Label) (reason : Reason)
  /-- The functions and ghosts of the lowered module that are not well formed. -/
  | illFormed (names : Array Name)
  /-- The lowered module is not in the output shape: some terminator was left as it was. -/
  | internal
  deriving DecidableEq

variable {env : Env Unit} [base ≼ env] {α : Type}

private structure Context (env : Env Unit) where
  ops : CaseOps
  groups : Std.HashMap Name (Env.Group env)

private def context (env : Env Unit) (ops : CaseOps) : Context env :=
  ⟨ops, env.entries.foldl (init := {}) fun gs e => match e with
    | .data g => gs.insert g.first.decl.name g
    | _ => gs⟩

private structure Names where
  values : ValueNames
  labels : Suffixes

/-- Lowering one block fails with a `Reason`; a traversal adds the label of the block. -/
private abbrev M (env : Env Unit) (ε : Type) := ReaderT (Context env) (StateT Names (Except ε))

private def freshVal (stem : String) : M env Reason ValId :=
  modifyGet fun s =>
    let (v, values) := s.values.fresh (.str .base stem)
    (v, { s with values })

private def freshLabel : M env Reason Label :=
  modifyGet fun s =>
    let (n, labels) := s.labels.fresh (.str .base "cases")
    (⟨n⟩, { s with labels })

/-- One constructor's arm of a case: its fields with their types at the case's type
arguments, and the edge the case takes. -/
private structure Arm (env : Env Unit) where
  ctor : Name
  fields : Array (String × TypeExpr env)
  target : Target.Raw

/-- A datatype's case, as its terminator applies it. -/
private structure Case (env : Env Unit) where
  scrut : ValId
  scrutTy : TypeExpr env
  typeArgs : Array (TypeArg env)
  /-- In the order of the datatype's constructors. -/
  arms : List (Arm env)

/-- The case that a terminator is: an application of the case instruction of a datatype in
the index, to one scrutinee and one edge per constructor. The field types are those the
instruction's signature gives its successors. -/
private def caseOf? (cx : Context env) : Terminator env α → Option (Case env)
  | .apply _ (isig := isig) r ts #[scrut] ks #[] => do
    let addr ← r.caseAddr?
    let d ← cx.groups[addr.head]? >>= (·.members[addr.dataIdx]?)
    let #[scrutTy] ← isig.operandTypes? ts 1 | none
    let payloads := isig.succTypes ts
    guard (d.ctors.size == ks.size && payloads.size == ks.size)
    return ⟨scrut, scrutTy, ts.args, (d.ctors.zip (payloads.zip ks)).toList.map fun (c, tys, k) =>
      ⟨c.name, (c.args.map (·.name)).zip tys, k⟩⟩
  | _ => none

/-- Apply the accessor `name` to the scrutinee, after checking its signature. -/
private def accessor (c : Case env) (name : Name) (resultTy : TypeExpr env) (stem : String)
    (info : α) : M env Reason (Instruction env α × ValId) := do
  let some (.insn (isig := isig) r) := env.get? name
    | throw (.notInstruction name)
  let .ok targs := TypeArgs.check? isig.scope c.typeArgs
    | throw (.typeArgs name)
  unless isig.effect == .pure && isig.variadic.isNone && isig.regions.isEmpty &&
      isig.succs.isEmpty && isig.operandTypes? targs 1 == some #[c.scrutTy] &&
      isig.returnType.map (·.instantiate targs) == some resultTy do
    throw (.accessorType name)
  let v ← freshVal stem
  return (.apply info ⟨v, resultTy⟩ r targs #[c.scrut] #[] #[], v)

/-- How a block ends: its last instructions and its terminator. -/
private structure Tail (env : Env Unit) (α : Type) where
  instrs : Array (Instruction env α)
  term : PlainTerm

/-- An edge to `tail`. A tail that only jumps and passes nothing is reached at its own
target; any other gets a new block, annotated `info`. -/
private def edge (info : α) : Tail env α → M env Reason (Target.Raw × List (Block env α))
  | ⟨#[], .jump ⟨label, #[]⟩⟩ => return (⟨label, #[]⟩, [])
  | tail => do
    let label ← freshLabel
    return (⟨label, #[]⟩, [⟨label, #[], tail.instrs, tail.term.term info, info⟩])

/-- Select the fields and jump, with the edge's own arguments first. -/
private def arm (c : Case env) (info : α) (a : Arm env) : M env Reason (Tail env α) := do
  let selected ← a.fields.mapM fun (f, ty) => do
    let some name := (← read).ops.selector a.ctor f
      | throw (.noSelector a.ctor f)
    accessor c name ty f info
  return ⟨selected.map (·.1), .jump ⟨a.target.label, a.target.args ++ selected.map (·.2)⟩⟩

/-- Test the constructors in order: the tail that dispatches on `arms`, and the blocks it
needs. The last arm is taken when every test before it failed, and no arm at all cannot be
reached. -/
private def dispatch (c : Case env) (info : α) :
    List (Arm env) → M env Reason (Tail env α × List (Block env α))
  | [] => return (⟨#[], .unreachable⟩, [])
  | [a] => return (← arm c info a, [])
  | a :: rest => do
    let some name := (← read).ops.tester a.ctor
      | throw (.noTester a.ctor)
    let (test, cond) ← accessor c name Base.Bool "case" info
    let (t, tb) ← edge info (← arm c info a)
    let (others, ob) ← dispatch c info rest
    let (f, fb) ← edge info others
    return (⟨#[test], .branch cond t f⟩, tb ++ fb ++ ob)

/-- Lower one terminator. Its nested regions have already been traversed. A terminator that
is neither a branch nor a case stays; the output shape decides whether it may. -/
private def block (b : Block env α) : M env Reason (List (Block env α)) := do
  let info := b.term.info
  match b.term.plain? with
  | some (.branch cond t f) =>
    let (t, tb) ← edge info ⟨#[], .jump t⟩
    let (f, fb) ← edge info ⟨#[], .jump f⟩
    return { b with term := .branch info cond t f } :: tb ++ fb
  | some _ => return [b]
  | none =>
    let some c := caseOf? (← read) b.term
      | return [b]
    let (tail, blocks) ← dispatch c info c.arms
    return { b with instrs := b.instrs ++ tail.instrs, term := tail.term.term info } :: blocks

/-- Lower `b`, naming it in a rejection. -/
private def located (b : Block env α) : M env (Label × Reason) (List (Block env α)) :=
  fun cx s => (block b cx s).mapError (b.label, ·)

/-- Run a traversal of the blocks `blocks` of a function or ghost whose values are named
`names`: its result, and the names with those of the new values. -/
private def run {β : Type} (cx : Context env) (names : Array Name) (blocks : List (Block env α))
    (action : M env (Label × Reason) β) : Except (Label × Reason) (β × Array Name) := do
  let (result, s) ← (action.run cx).run ⟨.of names, .of (blocks.toArray.map (·.label.name))⟩
  return (result, s.values.names)

private def func (cx : Context env) (fn : Func env α) :
    Except (Label × Reason) (Func env α) := do
  let ((blocks, contract), names) ← run cx fn.names fn.allBlocks do
    let blocks ← Block.traverseBlocksList located fn.blocks.toList
    let contract ← fn.contract.traverseRegions (·.traverseBlocks located)
    return (blocks.toArray, contract)
  return { fn with blocks, contract, names }

private def ghost (cx : Context env) (g : Ghost env α) :
    Except (Label × Reason) (Ghost env α) := do
  let (g', names) ← run cx g.names (Region.blocksList g.regions)
    (g.traverseRegions (·.traverseBlocks located))
  return { g' with names }

/-- Rewrite every ghost and function. The first refused accessor stops the pass. -/
private def lower (ops : CaseOps) (m : Module.Raw env α) : Except Error (Module.Raw env α) := do
  let cx := context env ops
  let refused (owner : Name) : Label × Reason → Error := fun (block, reason) =>
    .accessor owner block reason
  let ghosts ← m.ghosts.mapM fun g => (ghost cx g).mapError (refused g.name)
  let funcs ← m.funcs.mapM fun fn => (func cx fn).mapError (refused fn.name)
  return { m with funcs, ghosts }

/-- Decide the output shape of a rewritten module, then its well-formedness. -/
private def certify (m : Module.Raw env α) :
    Except Error { m' : Module env α // Cased m'.raw } :=
  if hs : Cased m then
    match hc : m.check with
    | .ok m' => .ok ⟨m', Module.Raw.raw_of_check hc ▸ hs⟩
    | .error names => .error (.illFormed names)
  else .error .internal

end Cases

/-- Lower cases and branch arguments throughout a well-formed module in Cases' input shape.
The result is well formed and in the output shape: both are decided on it. -/
def cases {env : Env Unit} [base ≼ env] {α : Type} (ops : CaseOps)
    (m : Module env α) (_ : CasesInput m.raw) :
    Except Cases.Error { m' : Module env α // Cased m'.raw } :=
  Cases.lower ops m.raw >>= Cases.certify

end

end Strata.Dyn
