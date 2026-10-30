/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDyn.DDM
public import StrataDyn.DDMRead
import StrataDyn.Env.WF
import StrataDyn.DSL
import StrataDynTest.WFParts
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataDyn.Build
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.WF
meta import StrataDyn.Env.WF
meta import StrataDynTest.WFParts

set_option autoImplicit false

/-!
# Effects

Every instruction declaration has an effect, an upper bound on what the operation may do:
`pure`, `reads`, `calls` or `writes`.  The tests:

* the effect each DSL keyword declares, and `writes` without one;
* the base's effects, and those of a datatype's constructors and case instruction;
* refinement, which compares effects;
* the rule that a contract region, at any depth, applies no operation declared `writes`, in the
  builder and in the reader.
-/

namespace Strata.Dyn.EffectTest

open Strata.Dyn.WFParts (broken failing)

/-- One instruction per effect, instructions without an effect keyword, and a datatype. -/
public environment Eff extends Base where
  namespace eff
  open base
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- The contents of `cell`. -/
  reads insn peek (cell : Ref Int) : Int
  /-- Whether `x` passes a test, which runs code the IR does not show. -/
  calls insn test (x : Int) : Bool
  /-- Stores `x` in `cell`. -/
  writes insn poke (cell : Ref Int) (x : Int) : Unit
  /-- An instruction without an effect keyword. -/
  insn touch (x : Int) : Bool
  /-- Runs `body`. -/
  pure insn wrap [a] (&body : a) : a
  /-- A terminal instruction with an effect keyword. -/
  pure terminal insn stop
  /-- A terminal instruction without one. -/
  terminal insn halt
  /-- Two integers. -/
  data Pair where
    | pair (fst snd : Int)
  end eff

private abbrev E := Eff.env

/-! ## Declared effects -/

/-- The effect `env` declares the instruction `n` with. -/
private def effectOf (env : Env Unit) (n : Name) : Option Effect :=
  match env.get? n with
  | some (.insn (isig := σ) _) => some σ.effect
  | _ => none

-- Each keyword declares its effect, and an instruction without one is `writes`.
#guard (Eff.ge.sig (e := E)).effect == .pure
#guard (Eff.peek.sig (e := E)).effect == .reads
#guard (Eff.test.sig (e := E)).effect == .calls
#guard (Eff.poke.sig (e := E)).effect == .writes
#guard (Eff.touch.sig (e := E)).effect == .writes

-- The keyword comes before `terminal`.
#guard (Eff.stop.sig (e := E)).effect == .pure
#guard (Eff.halt.sig (e := E)).effect == .writes

-- The environment declares the instructions with the effects of their signatures.
#guard ["ge", "peek", "test", "poke", "touch", "stop", "halt"].map
    (fun s => effectOf E (.str (.str .base "eff") s)) ==
  [some .pure, some .reads, some .calls, some .writes, some .writes, some .pure, some .writes]

-- A datatype's constructors and its case instruction are `pure`.
#guard (Eff.Pair.pair.sig (e := E)).effect == .pure
#guard (Eff.Pair.case.sig (e := E)).effect == .pure
#guard [bn "unit", .str (bn "Unit") "case", bn "ok", bn "error", .str (bn "Except") "case"].map
    (effectOf base) ==
  [some .pure, some .pure, some .pure, some .pure, some .pure]

-- The base's instructions.
#guard ["refNew", "refGet", "refSet", "old", "cellLoc", "callCode", "jump", "branch",
    "unreachable"].map (fun s => effectOf base (bn s)) ==
  [some .pure, some .reads, some .writes, some .reads, some .pure, some .writes, some .pure,
    some .pure, some .pure]

-- The effects are ordered from the least an operation may do to the most.
example : Effect.pure < .reads ∧ Effect.reads < .calls ∧ Effect.calls < .writes := by decide

-- `writes` bounds every effect.
example : ∀ e : Effect, e ≤ .writes := by intro e; cases e <;> decide

/-! ## Refinement compares effects

`opEnv e` extends the base by one instruction, `op`, declared with the effect `e`.  Two such
environments refine each other only if their effects are equal. -/

-- The environments are only reasoned about.
noncomputable section

private def opN : Name := .str .base "op"

/-- `op (x : base.Int) : base.Int`, with the effect `e`. -/
private def opSig (e : Effect) : InsnSig base :=
  { ann := (), argTypes := #[⟨"x", Base.Int⟩], returnType := some Base.Int, effect := e }

-- An `abbrev`, so that `rcases` sees a signature carried into it as one of its own.
private abbrev opEnv (e : Effect) : Env Unit := base.addInsn opN (opSig e) (by simp [opN])

/-- Every instruction `opEnv e` declares as `op` has the effect `e`: the base declares no
`op`. -/
private theorem effect_op {e : Effect} {σ : InsnSig (opEnv e)} {k : InsnKind}
    (h : (opEnv e).DeclaresInsn opN σ k) : σ.effect = e := by
  rcases Env.declaresInsn_addInsn h with ⟨-, rfl, -⟩ | ⟨_, h₀, -⟩
  · rfl
  · exact absurd h₀.mem (by simp [opN])

/-- `opEnv e₂` refines `opEnv e₁` only if `e₁ = e₂`. -/
private theorem eq_of_le {e₁ e₂ : Effect} (h : opEnv e₁ ≤ opEnv e₂) : e₁ = e₂ := by
  obtain ⟨_, _, hσ, -, r⟩ := h.insn (Env.declaresInsn_addInsn_self _ _ _ _)
  exact r.eq.effect_eq.trans (effect_op hσ)

example : ¬ opEnv .pure ≤ opEnv .reads := fun h => absurd (eq_of_le h) (by decide)
example : ¬ opEnv .reads ≤ opEnv .pure := fun h => absurd (eq_of_le h) (by decide)
example : opEnv .calls ≤ opEnv .calls := Env.Le.refl _

end

/-! ## No operation declared `writes` in a contract region

`@m.f(c)`, over the cell `c`, returns `0`; the tests vary its contract.  A clause may apply a
`reads` and a `calls` operation, and a `pure` terminal one such as `unreachable`.  It may not
apply a `writes` operation, nor one without an effect keyword, as an instruction or as a
terminator, in the clause or in a region nested in it.  (A terminal operation that is not
control flow, such as `eff.stop`, breaks another rule, `Region.EndsInControl`, which
`StrataDynTest/ContractRegionTest.lean` tests.) -/

open Strata.Dyn.Build (freshVal startFreshBlock emitConst emitApply finishBlock terminate build
  FailedFunc region)

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

private def intT : TypeExpr E := Base.Int
private def boolT : TypeExpr E := Base.Bool

private def nm (s : String) : Name := .str .base s

/-- `@m.f(c : base.Ref(base.Int)) -> base.Int`, returning `0`, with the contract `contract c`. -/
private def withContract (contract : ValId → BuildM E Unit Unit) : Built :=
  build (.str (nm "m") "f") intT () do
    let c ← freshVal (nm "c") (Base.Ref intT)
    let _ ← startFreshBlock #[c] "entry"
    finishBlock (.ret () (← emitConst (nm "z") (.int 0)))
    contract c.id

/-- `test(peek(c))`: a `reads` and a `calls` operation. -/
private def peekTest (c : ValId) : BuildM E Unit Unit := do
  let v ← emitApply (nm "v") intT Eff.peek.ref #[c]
  finishBlock (.ret () (← emitApply (nm "ok") boolT Eff.test.ref #[v]))

/-- `poke(c, 0)`, then `true`: a `writes` operation. -/
private def pokeTrue (c : ValId) : BuildM E Unit Unit := do
  let z ← emitConst (nm "z") (.int 0)
  let _ ← emitApply (nm "u") Base.Unit Eff.poke.ref #[c, z]
  finishBlock (.ret () (← emitConst (nm "t") (.bool true)))

/-- `wrap { body }`, returned. -/
private def wrapped (body : BuildM E Unit Unit) : BuildM E Unit Unit := do
  let inner := region #[] (base := "body") body
  finishBlock (.ret () (← emitApply (nm "w") boolT Eff.wrap.ref #[] (regions := #[inner])))

/-- Print the built function `b` as a module, or why it was not built. -/
private def printBuilt (b : Built) : IO Unit := do
  match b with
  | .error e => IO.println s!"not built: {e}"
  | .ok f =>
    match Module.ofChecked (nm "m") #[f] () with
    | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
    | .ok m => IO.println m

-- A `requires` and an `ensures` clause may apply a `reads` and a `calls` operation.
/-- info: module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    requires {
      pre.0():
        %v.0 : base.Int = eff.peek(%c.0)
        %ok.0 : base.Bool = eff.test(%v.0)
        ret(%ok.0)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      ret(0)
  }
} -/
#guard_msgs in
#eval printBuilt (withContract fun c => Build.requires (peekTest c))

/-- info: module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        %v.0 : base.Int = eff.peek(%c.0)
        %ok.0 : base.Bool = eff.test(%v.0)
        ret(%ok.0)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      ret(0)
  }
} -/
#guard_msgs in
#eval printBuilt (withContract fun c => Build.ensures (nm "r") intT fun _ => peekTest c)

-- A clause may end in `unreachable`, a `pure` terminal operation.
/-- info: module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    requires {
      pre.0():
        unreachable
    }
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      ret(0)
  }
} -/
#guard_msgs in
#eval printBuilt (withContract fun _ => Build.requires (Build.unreachable))

-- The body may apply a `writes` operation.
/-- info: module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%c.0 : base.Ref(base.Int)):
      %u.0 : base.Unit = eff.poke(%c.0, 0)
      ret(0)
  }
} -/
#guard_msgs in
#eval printBuilt (build (.str (nm "m") "f") intT () do
  let c ← freshVal (nm "c") (Base.Ref intT)
  let _ ← startFreshBlock #[c] "entry"
  let z ← emitConst (nm "z") (.int 0)
  let _ ← emitApply (nm "u") Base.Unit Eff.poke.ref #[c.id, z]
  finishBlock (.ret () z))

#guard failing (withContract fun c => Build.ensures (nm "r") intT fun _ => pokeTrue c) ==
  ["contract"]

#guard failing (withContract fun c => Build.requires (wrapped (pokeTrue c))) == ["contract"]

#guard failing (withContract fun c => Build.ensures (nm "r") intT fun _ => wrapped (pokeTrue c)) ==
  ["contract"]

#guard failing (withContract fun _ => Build.requires do
  let ok ← emitApply (nm "ok") boolT Eff.touch.ref #[← emitConst (nm "z") (.int 0)]
  finishBlock (.ret () ok)) == ["contract"]

-- `eff.halt` is not control flow either, so it also breaks `Region.EndsInControl`.
#guard failing (withContract fun _ => Build.requires (terminate Eff.halt.ref)) ==
  ["contract", "terminators"]

#guard failing (withContract fun _ => Build.requires (wrapped (terminate Eff.halt.ref))) ==
  ["contract", "terminators"]

/-- Read `text` in `Eff.env`, and print the diagnostics, or the module if it prints otherwise. -/
private def readBack (text : String) : IO Unit := do
  match ← Module.read Eff.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

/-- `@m.f(c : base.Ref(base.Int)) -> base.Int` with the contract `clauses`, returning `0`. -/
private def withClauses (clauses : String) : String := s!"module m \{
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
{clauses}
  \{
    entry.0(%c.0 : base.Ref(base.Int)):
      ret(0)
  }
}
"

-- A `reads` and a `calls` operation, and `unreachable`, a `pure` terminal one, read back as
-- printed.
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %v.0 : base.Int = eff.peek(%c.0)
        %ok.0 : base.Bool = eff.test(%v.0)
        ret(%ok.0)
    }
    requires {
      pre.1():
        unreachable
    }
    ensures {
      post.0(%r.0 : base.Int):
        %v.1 : base.Int = eff.peek(%c.0)
        %ok.1 : base.Bool = eff.test(%v.1)
        ret(%ok.1)
    }")

/-- info: t.dyn:5:8: a contract region of @m.f may not change state, but eff.poke is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %u.0 : base.Unit = eff.poke(%c.0, 0)
        ret(true)
    }")

/-- info: t.dyn:7:12: a contract region of @m.f may not change state, but eff.poke is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %w.0 : base.Bool = eff.wrap[base.Bool] {
          body.0():
            %u.0 : base.Unit = eff.poke(%c.0, 0)
            ret(true)
        }
        ret(%w.0)
    }")

/-- info: t.dyn:5:8: a contract region of @m.f may not change state, but eff.touch is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = eff.touch(0)
        ret(%ok.0)
    }")

/-- info: t.dyn:5:8: a contract region of @m.f may not change state, but eff.halt is declared writes -/
#guard_msgs in
#eval readBack (withClauses "    requires {
      pre.0():
        eff.halt
    }")

-- The body may apply them.
#guard_msgs in
#eval readBack "module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int {
    entry.0(%c.0 : base.Ref(base.Int)):
      %u.0 : base.Unit = eff.poke(%c.0, 0)
      %ok.0 : base.Bool = eff.touch(0)
      branch(%ok.0) ^done.0() ^stop.0()
    done.0():
      ret(0)
    stop.0():
      eff.halt
  }
}
"

end Strata.Dyn.EffectTest
