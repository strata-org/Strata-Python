/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec
meta import StrataDyn.Exec.Rules
meta import Lean.Elab.Command

set_option autoImplicit false

/-!
# Compiler data that meta code wrote directly

Meta code in a rule's module can write the compiler's data without the attributes that check it.
The check catches two such writes: a `@[csimp]` entry whose lemma doesn't state that its two
functions are equal, and an `_unsafe_rec` that Lean didn't make from a recursive definition.  It
can't catch every write (docs/Dyn.md says which it trusts).  These are deliberate test inputs, in
a module of their own, so that they reach no other rule.
-/

namespace Strata.Dyn.ExecTest.ForgedEntry

open Lean Meta Elab Command Strata.Dyn.Exec

/-- What the check finds on `d`, as a message. -/
meta def checkDecl (d : Lean.Name) : MetaM Unit := do
  match ← notAsProved d m!"{.ofConstName d}" with
  | some m => logInfo m
  | none => logInfo "no finding"

@[expose] public section

/-- The identity, in the logic. -/
def idH (x : Nat) : Nat := x
/-- The code that a forged `@[csimp]` entry runs instead. -/
def plusSeven (x : Nat) : Nat := x + 7

end

-- An entry from `idH` to `plusSeven`, whose lemma, `Nat.add_comm`, is true but states another fact.
run_cmd modifyEnv (Lean.Compiler.CSimp.ext.addEntry ·
  { fromDeclName := ``idH, toDeclName := ``plusSeven, thmName := ``Nat.add_comm })

/-- A rule over `idH`. -/
@[expose] public def viaIdH (x : Nat) : Nat := idH x

/-- info: viaIdH reaches idH (viaIdH → idH), whose @[csimp] entry swaps in plusSeven by Nat.add_comm, which doesn't state that the two are equal -/
#guard_msgs in
#eval checkDecl ``viaIdH

/-- The identity, in the logic. -/
@[expose] public def loopF (x : Nat) : Nat := x

-- `loopF._unsafe_rec`, a `partial` definition that never returns, made by meta code.  Lean
-- compiles a definition from its `_unsafe_rec` when one exists, so the check must not take a
-- hand-made one for Lean's (here `loopF` was compiled first, so its run doesn't change).
run_cmd liftTermElabM do
  let n : Lean.Name := .str `Strata.Dyn.ExecTest.ForgedEntry.loopF "_unsafe_rec"
  let nat := Lean.mkConst ``Nat
  let ty ← mkArrow nat nat
  let body := Lean.mkLambda `x .default nat (Lean.mkApp (Lean.mkConst n) (Lean.mkNatSucc (.bvar 0)))
  let dv := Lean.mkDefinitionValEx n [] ty body .opaque .partial [n]
  addDecl (.mutualDefnDecl [dv])
  compileDecls #[n]

/-- A rule over `loopF`. -/
@[expose] public def viaLoopF (x : Nat) : Nat := loopF x

/-- info: viaLoopF reaches loopF (viaLoopF → loopF), which runs loopF._unsafe_rec instead of its definition (a hand-written _unsafe_rec); a run would not run the definition that proofs see -/
#guard_msgs in
#eval checkDecl ``viaLoopF

end Strata.Dyn.ExecTest.ForgedEntry
