/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.DSLTest
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Blocks for control-flow tests

Short names for writing bodies by hand in `Demo.env`, for tests about control flow: the loop
tests, the canonical-form tests and the every-body tests.  Their functions need not be well
formed: these tests are about the shape of the control-flow graph.
-/

namespace Strata.Dyn.Blocks

open Strata.Dyn.DSLTest

public section

abbrev E := Demo.env

def valT : TypeExpr E := Demo.Value

def lbl (s : String) : Label := ⟨.str .base s⟩

def lbls (ss : List String) : List Label := ss.map lbl

/-- Block `s` after `k` instructions. -/
def pt (s : String) (k : Nat) : Point := ⟨lbl s, k⟩

/-- `%r = add %0 %0 ^h()`: an instruction whose failure goes to `h`. -/
def add (r : Nat) (h : String) : Instruction E Unit :=
  .apply () ⟨⟨r⟩, valT⟩ Demo.add.ref ⟨#[], rfl⟩ #[⟨0⟩, ⟨0⟩] #[⟨lbl h, #[]⟩] #[]

/-- `%r = add %0 %0 ^exit()`: an instruction whose failure leaves the body. -/
def addExit (r : Nat) : Instruction E Unit :=
  .apply () ⟨⟨r⟩, valT⟩ Demo.add.ref ⟨#[], rfl⟩ #[⟨0⟩, ⟨0⟩] #[⟨Label.exit, #[]⟩] #[]

/-- `%r = if %0 { thn } { els }`: an instruction with two regions. -/
def ifI (r : Nat) (thn els : Region E Unit) : Instruction E Unit :=
  .apply () ⟨⟨r⟩, valT⟩ Demo.«if».ref ⟨#[.ty valT], rfl⟩ #[⟨0⟩] #[] #[thn, els]

/-- Block `s` with instructions `is` and terminator `t`. -/
def blk (s : String) (is : Array (Instruction E Unit)) (t : Terminator E Unit) : Block E Unit :=
  { label := lbl s, params := #[], instrs := is, term := t, info := () }

/-- `jump ^s()`. -/
def jump (s : String) : Terminator E Unit := .jump () ⟨lbl s, #[]⟩

/-- `branch %0 ^t() ^f()`. -/
def branch (t f : String) : Terminator E Unit := .branch () ⟨0⟩ ⟨lbl t, #[]⟩ ⟨lbl f, #[]⟩

/-- `ret %0`. -/
def ret : Terminator E Unit := .ret () ⟨0⟩

/-- `loop %0 { body } ^s()`: a terminator that runs a region, then goes to `s`. -/
def loopT (body : Region E Unit) (s : String) : Terminator E Unit :=
  .apply () Demo.loop.ref ⟨#[.ty valT], rfl⟩ #[⟨0⟩] #[⟨lbl s, #[]⟩] #[body]

/-- The function `f` whose blocks are `bs`. -/
def fn (bs : List (Block E Unit)) : Func E Unit :=
  { name := .str .base "f", params := #[], retType := valT, blocks := bs.toArray, names := #[],
    info := () }

end

end Strata.Dyn.Blocks
