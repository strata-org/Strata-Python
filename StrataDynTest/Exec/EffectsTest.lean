/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Effects
public import StrataDyn.Exec.EffectsProps
-- `#guard` runs the readings as compiled code.
meta import StrataDyn.Exec.Effects

set_option autoImplicit false

/-!
# The effects of rules

Trees over a small language whose every tag holds a `Nat` and whose world is a `Nat`, checked
against each effect level: which levels each tree stays within, and which it doesn't; and two
readings of a `pure` tree from worlds of one parity, which end alike, while a tree that is not
`pure` reads them apart.
-/

namespace Strata.Dyn.Exec.EffectsTest

open Strata.Dyn.Exec Strata.Dyn.Exec.Effects

/-- Every tag's values are `Nat`s. -/
abbrev I : Ty → Type := fun _ => Nat

/-- A tag. -/
def t : Ty := .app 2 []

/-- A rule's tree in this language, with no regions or successors. -/
abbrev T := Tree I Run Nat [] [] Unit Nat

/-- The world's parity is immutable, and the world may only grow. -/
def sp : WorldSpec Nat Unit where
  immEq _ w₁ w₂ := w₁ % 2 = w₂ % 2
  same _ w w' := w ≤ w'
  same_refl _ w := Nat.le_refl w
  same_trans _ _ _ _ := Nat.le_trans

/-- No cell made by this activation yet. -/
def none' : Cells := fun _ => False

/-- No post-condition. -/
def anyPost : Cells → Nat → Prop := fun _ _ => True

/-- A tree that makes a cell holding `5`, then reads it. -/
def newGet : T := .vis (.new t 5) fun r => .vis (.get t r.loc) fun v => .ret v

/-- A tree that reads the cell at location `7`. -/
def get7 : T := .vis (.get t 7) fun v => .ret v

/-- A tree that writes `9` into the cell at location `0`. -/
def set0 : T := .vis (.set t 0 9) fun _ => .ret 0

/-- A tree that calls a function of no arguments. -/
def call0 : T := .vis (.call ([], t) 0 0 ()) fun v => .ret v

/-- A tree that reads the world's parity. -/
def parity : T := .update fun w => (w, .ret (w % 2))

/-- A tree that reads the whole world. -/
def whole : T := .update fun w => (w, .ret w)

/-- A tree that grows the world by one. -/
def grow : T := .update fun w => (w + 1, .ret 0)

/-- A tree that resets the world to `0`. -/
def reset : T := .update fun _ => (0, .ret 0)

-- Reading a cell it made is `pure`.
example : Within sp () .pure anyPost none' newGet := fun _ => ⟨fun _ => .inr rfl, fun _ => trivial⟩

-- Reading an older cell is not `pure`, but it is `reads`.
example : ¬ Within sp () .pure anyPost none' get7 := fun h => h.1 rfl
example : Within sp () .reads anyPost none' get7 := ⟨(fun h => nomatch h), fun _ => trivial⟩

-- Writing an older cell is `writes`, not `calls`.
example : ¬ Within sp () .calls anyPost none' set0 := fun h => by
  rcases h.1 with h | h <;> cases h
example : Within sp () .writes anyPost none' set0 := ⟨.inl rfl, fun _ => trivial⟩

-- Updating an older cell in place is `writes`, not `calls`; updating a cell it made is `pure`.
/-- A tree that adds one to the cell at location `0`. -/
def mod0 : T := .vis (.modify t 0 (· + 1)) fun _ => .ret 0
example : ¬ Within sp () .calls anyPost none' mod0 := fun h => by
  rcases h.1 with h | h <;> cases h
example : Within sp () .writes anyPost none' mod0 := ⟨.inl rfl, fun _ => trivial⟩
example : Within sp () .pure anyPost none'
    (.vis (.new t 5) fun r => .vis (.modify t r.loc (· + 1)) fun _ => .ret 0 : T) :=
  fun _ => ⟨.inr (.inr rfl), fun _ => trivial⟩

-- A call is `calls`, not `reads`.
example : ¬ Within sp () .reads anyPost none' call0 := fun h => by
  rcases h.1 with h | h <;> cases h
example : Within sp () .calls anyPost none' call0 := ⟨.inl rfl, fun _ => trivial⟩

-- An update whose continuation reads only what `immEq` keeps is `pure`; reading more is not.
/-- `parity` is `pure`. -/
theorem parity_pure : Within sp () .pure anyPost none' parity :=
  ⟨fun _ w => .inr (Nat.le_refl w), fun _ w₁ w₂ (h : w₁ % 2 = w₂ % 2) => ⟨h, by simp only [h]⟩,
    fun _ => trivial⟩
example : ¬ Within sp () .pure anyPost none' whole := fun h => by
  have := (h.2.1 rfl 0 2 rfl).2
  cases this

-- An update that `same` allows is fine at every level; one that it doesn't is `writes` only.
example : Within sp () .pure anyPost none' grow :=
  ⟨fun _ w => .inr (Nat.le_succ w), fun _ w₁ w₂ (h : w₁ % 2 = w₂ % 2) => ⟨by
    show (w₁ + 1) % 2 = (w₂ + 1) % 2
    omega, rfl⟩, fun _ => trivial⟩
example : ¬ Within sp () .calls anyPost none' reset := fun h => by
  rcases h.1 (by decide) 1 with h' | h'
  · cases h'.2
  · cases h'
example : Within sp () .writes anyPost none' reset :=
  ⟨fun h => absurd rfl h, (fun h => nomatch h), fun _ => trivial⟩

/-- A tree that grows the world by a number that depends on more than its parity. -/
def leak : T := .update fun w => (2 * w + w / 2 % 2, .ret 0)

-- `same` allows the update, but a `pure` tree may not carry what `immEq` doesn't keep into the
-- world: `0` and `2` have one parity, and the update gives `0` and `5`.
example : ¬ Within sp () .pure anyPost none' leak := fun h => by
  have := (h.2.1 rfl 0 2 rfl).1
  cases this

-- A read of the whole world is fine at `reads`: its update gives the world back, and
-- `same` is reflexive.
example : Within sp () .reads anyPost none' whole :=
  ⟨fun _ w => .inr (Nat.le_refl w), (fun h => nomatch h), fun _ => trivial⟩

-- `lift`: the `reads` tree is also `writes`.
example : Within sp () .writes anyPost none' get7 :=
  Within.lift (e := .reads) (by decide) get7 ⟨(fun h => nomatch h), fun _ => trivial⟩

/-- A tree that returns the oracle's number. -/
def pick : T := .choose fun i => .ret i

-- An oracle choice is not `pure`, but it is `reads`.
example : ¬ Within sp () .pure anyPost none' pick := fun h => h.1 rfl
example : Within sp () .reads anyPost none' pick := ⟨(fun h => nomatch h), fun _ => trivial⟩

/-- A tree that makes a cell holding `5` and returns its ref. -/
def mk : Tree I Run Nat [] [] Unit (Ref Run Nat) := .vis (.new t 5) .ret

/-- A tree that writes `9` into the cell of the ref `r`. -/
def wr (r : Ref Run Nat) : T := .vis (.set t r.loc 9) fun _ => .ret 0

/-- The ref's cell is one the activation made. -/
def madeRef : Cells → Ref Run Nat → Prop := fun N r => N r.loc

-- `bind`: making a cell, then writing it, is `pure`, since the post-condition of the first part
-- says that the ref's cell is new.
example : Within sp () .pure anyPost none' (mk.bind wr) :=
  Within.bind (sp := sp) (s := ()) (e := .pure) (mid := madeRef) (post := anyPost) (f := wr)
    (fun _ _ h => ⟨.inr h, fun _ => trivial⟩) mk
    (fun _ => .inr rfl)

/-! ## What `pure` means for a reading -/

/-- The result of reading `t` from the world `w`, if it ended with one. -/
def resultFrom (env : Reading.Env I Nat []) (t : T) (w : Nat) : Option Nat :=
  match (Reading.read env (fun _ => 0) t 0 ⟨#[], #[]⟩ w).out with
  | .done r => some r
  | .stop _ => none

/-- An environment that answers every call with `0`, from any heap and world, and keeps the
world. -/
def zeroEnv : Reading.Env I Nat [] where
  answer q h w := match q with
    | .call _ _ _ _ => .ok (0, h, w)
    | _ => .error (.gap "no region")
  bind _ _ _ _ _ := none

/-- `zeroEnv` can't tell worlds apart. -/
theorem zeroEnv_imm : EnvImm sp () zeroEnv := by
  intro q h w₁ w₂ hw
  cases q with
  | call => exact ⟨rfl, rfl, hw⟩
  | region slot _ => exact slot.elim0
  | _ => rfl

-- Two readings of the pure `parity` from `0` and `2`, worlds of one parity, end alike.
example : (Reading.read zeroEnv (fun _ => 0) parity 0 ⟨#[], #[]⟩ 0).out =
    (Reading.read zeroEnv (fun _ => 0) parity 0 ⟨#[], #[]⟩ 2).out :=
  (pure_reads_alike zeroEnv_imm _ parity none' 0 ⟨#[], #[]⟩ 0 2 parity_pure rfl).1
#guard resultFrom zeroEnv parity 0 == resultFrom zeroEnv parity 2
-- `whole`, which is not pure, reads them apart.
#guard resultFrom zeroEnv whole 0 == some 0
#guard resultFrom zeroEnv whole 2 == some 2

-- Its readings from `0` and `2` end in worlds of different parity.
#guard (Reading.read zeroEnv (fun _ => 0) leak 0 ⟨#[], #[]⟩ 0).world % 2 !=
  (Reading.read zeroEnv (fun _ => 0) leak 0 ⟨#[], #[]⟩ 2).world % 2

/-- A tree whose operation has one region, which it runs and whose answer it returns. -/
abbrev TR := Tree I Run Nat [([], t)] [] Unit Nat

/-- Run the region, and return its answer. -/
def runIt : TR := .vis (.region ⟨0, by decide⟩ .nil) fun o => .ret o

/-- An environment whose region answers the world's parity. -/
def parityEnv : Reading.Env I Nat [([], t)] where
  answer q h w := match q with
    | .region _ _ => .ok (w % 2, h, w)
    | _ => .error (.gap "no call")
  bind _ _ _ _ _ := none

/-- An environment whose region answers the whole world. -/
def wholeEnv : Reading.Env I Nat [([], t)] where
  answer q h w := match q with
    | .region _ _ => .ok (w, h, w)
    | _ => .error (.gap "no call")
  bind _ _ _ _ _ := none

/-- `parityEnv` can't tell worlds of one parity apart. -/
theorem parityEnv_imm : EnvImm sp () parityEnv := by
  intro q h w₁ w₂ hw
  cases q with
  | region => exact ⟨hw, rfl, hw⟩
  | _ => rfl

/-- Running a region is `pure`: its run is not counted. -/
theorem runIt_pure : Within sp () .pure anyPost none' runIt := fun _ => trivial

-- With `parityEnv`, the theorem's region case gives equal outcomes from `0` and `2`.
example : (Reading.read parityEnv (fun _ => 0) runIt 0 ⟨#[], #[]⟩ 0).out =
    (Reading.read parityEnv (fun _ => 0) runIt 0 ⟨#[], #[]⟩ 2).out :=
  (pure_reads_alike parityEnv_imm _ runIt none' 0 ⟨#[], #[]⟩ 0 2 runIt_pure rfl).1
-- `wholeEnv` tells them apart, so the theorem doesn't apply, and the readings differ.
#guard (match (Reading.read wholeEnv (fun _ => 0) runIt 0 ⟨#[], #[]⟩ 0).out with
  | .done r => r | _ => 9) == 0
#guard (match (Reading.read wholeEnv (fun _ => 0) runIt 0 ⟨#[], #[]⟩ 2).out with
  | .done r => r | _ => 9) == 2

/-! ## What a reading answers -/

/-- The result of reading `t` from the empty heap and the world `0`, if it ended with one. -/
def resultOf (t : T) : Option Nat := resultFrom zeroEnv t 0

-- A cell that the tree made reads back its value.
#guard resultOf newGet == some 5
-- A write is seen by a later read.
#guard resultOf (.vis (.new t 5) fun r => .vis (.set t r.loc 9) fun _ =>
  .vis (.get t r.loc) fun v => .ret v) == some 9
-- A read of a cell the heap doesn't have stops with `badCell`.
#guard (match (Reading.read zeroEnv (fun _ => 0) get7 0 ⟨#[], #[]⟩ 0).out with
  | .stop (.fault (.badCell 7)) => true | _ => false)
-- An update in place is seen by a later read.
#guard resultOf (.vis (.new t 5) fun r => .vis (.modify t r.loc (· + 1)) fun _ =>
  .vis (.get t r.loc) fun v => .ret v) == some 6

/-- A tree that binds the value `4` into code `3` with no captures cell, and returns the new
captures index. -/
def bind3 : T := .vis (.bind t 4 ([], t) 3 0) fun g => .ret g.captured

-- A bind request is allowed at every level, `pure` included: it binds values into a closure and
-- changes no state.
example : Within sp () .pure anyPost none' bind3 := fun _ => trivial

-- A bind pushes one captures entry and answers its index, one past the old size.
#guard (Reading.read zeroEnv (fun _ => 0) bind3 0 ⟨#[], #[[⟨t, 1⟩]]⟩ 0).heap.caps.size == 2
#guard (match (Reading.read zeroEnv (fun _ => 0) bind3 0 ⟨#[], #[[⟨t, 1⟩]]⟩ 0).out with
  | .done r => r | _ => 0) == 2

/-- A tree that binds the value `4` into code `3` whose captures cell is `1`. -/
def bindOnto1 : T := .vis (.bind t 4 ([], t) 3 1) fun g => .ret g.captured

-- A bind onto a captures cell copies the cell's entries and appends the new value, in a new cell.
#guard ((Reading.read zeroEnv (fun _ => 0) bindOnto1 0 ⟨#[], #[[⟨t, 1⟩]]⟩ 0).heap.caps[1]?.map
  (·.map fun d => (d.2 : Nat))) == some [1, 4]

/-! ## Levels and operand quantifiers -/

-- Above `reads`, a level is not `pure`.
example : Level.writes ≠ .pure := Level.ne_pure_up (e := .reads) (by decide) (by decide)
-- `AtLeast` finds the order of two levels.
example : Level.reads.le .writes := Level.AtLeast.le
example : ¬ Level.writes.le .calls := by decide

/-- The function of two `Nat` operands that adds them. -/
def add2 : Fn I Nat [t, t] := fun a b => a + b

-- `FnAll` quantifies over every operand list.
example : FnAll (· ≥ 0) [t, t] add2 := fun _ _ => Nat.zero_le _
example : ¬ FnAll (· = 0) [t, t] add2 := fun h => Nat.one_ne_zero (h 1 0)
-- A function made from a payload has `P` of every operand list when `k` has it of every payload.
example : FnAll (· < 10) [t, t]
    (Fn.ofPayload (I := I) [t, t] fun (p : Nat × Nat) => (p.1 + p.2) % 10) :=
  FnAll_ofPayload _ _ _ fun _ => Nat.mod_lt _ (by decide : 0 < 10)
-- `VarAll` quantifies over every variadic array, if there is one.
example : VarAll (I := I) (· = 1) none (1 : Nat) := rfl
example : VarAll (I := I) (X := Nat) (· ≤ 0) (some t) (fun xs => xs.size - xs.size) :=
  fun _ => by simp

-- The call bracket: with worlds from `10` up inside a bracket, `reset`, which `same` forbids
-- below `writes`, is within `calls` once guarded.
/-- `sp`, with the worlds from `10` up inside a call bracket. -/
def spB : WorldSpec Nat Unit := { sp with inCall := fun w => decide (10 ≤ w) }

example : ¬ Within spB () .calls anyPost none' reset := fun h => by
  rcases h.1 (by decide) 1 with h' | h'
  · cases h'.2
  · cases h'
example : Within spB () .calls anyPost none' (callBracket spB.inCall "g" reset) :=
  Within.callBracket "g" reset ⟨fun h => absurd rfl h, (fun h => nomatch h),
    fun _ => trivial⟩

-- Inside the bracket the guarded update runs; outside it stops with the gap, the world as it was.
#guard (Reading.read zeroEnv (fun _ => 0) (callBracket spB.inCall "g" reset) 0 ⟨#[], #[]⟩ 12).world
  == 0
#guard (Reading.read zeroEnv (fun _ => 0) (callBracket spB.inCall "g" reset) 0 ⟨#[], #[]⟩ 3).world
  == 3
#guard (match (Reading.read zeroEnv (fun _ => 0) (callBracket spB.inCall "g" reset) 0 ⟨#[], #[]⟩
    3).out with
  | .stop (.fault (.gap m)) => m == "g" | _ => false)

-- An update into the bracket runs too, from a world outside it: setting the world to `12` from `3`
-- (as a language restores its marker after a call that lowered it).
/-- An update that sets the world to `12`. -/
def enter : T := .update fun _ => (12, .ret 0)

#guard (Reading.read zeroEnv (fun _ => 0) (callBracket spB.inCall "g" enter) 0 ⟨#[], #[]⟩ 3).world
  == 12

-- A write to a cell inside the bracket stops with the gap, and so do an update of a cell in place,
-- a jump and a region.
#guard (match (Reading.read zeroEnv (fun _ => 0) (callBracket spB.inCall "g" set0) 0 ⟨#[], #[]⟩
    12).out with
  | .stop (.fault (.gap m)) => m == "g" | _ => false)
#guard (match (Reading.read zeroEnv (fun _ => 0) (callBracket spB.inCall "g" mod0) 0 ⟨#[], #[]⟩
    12).out with
  | .stop (.fault (.gap m)) => m == "g" | _ => false)
#guard (match (Reading.read zeroEnv (fun _ => 0) (callBracket spB.inCall "g" (.stop (.jump (.again ())) : T))
    0 ⟨#[], #[]⟩ 12).out with
  | .stop (.fault (.gap m)) => m == "g" | _ => false)
#guard (match callBracket spB.inCall "g" runIt with
  | .stop (.fault (.gap m)) => m == "g" | _ => false)

-- The other requests pass through the bracket unchanged: a call, a new cell and a read of it, a
-- bind, a choice, and a fault other than the bracket's gap.
section
/-- An environment that answers each call with `0`. -/
def callEnv : Reading.Env I Nat [] where
  answer q h w := match q with
    | .call _ _ _ _ => .ok (0, h, w)
    | _ => .error (.gap "no region")
  bind _ _ _ _ _ := none

/-- The result of the bracketed tree `x` from the world `w`, if it returns. -/
def bracketOut (x : T) (w : Nat) : Option Nat :=
  match (Reading.read callEnv (fun _ => 7) (callBracket spB.inCall "g" x) 0 ⟨#[], #[]⟩ w).out with
  | .done r => some r
  | .stop _ => none

#guard bracketOut (.vis (.call ([], t) 0 0 ()) fun v => .ret (v + 1)) 12 == some 1
#guard bracketOut (.vis (.new t 5) fun r => .vis (.get t r.loc) fun v => .ret v) 12 == some 5
#guard bracketOut (.choose fun i => .ret i) 12 == some 7
#guard bracketOut (.vis (.bind t 4 ([], t) 3 0) fun g => .ret g.captured) 12 == some 1
#guard (match (Reading.read callEnv (fun _ => 0) (callBracket spB.inCall "g" (.stop (.fault (.failure "f")) : T))
    0 ⟨#[], #[]⟩ 12).out with
  | .stop (.fault (.failure m)) => m == "f" | _ => false)
end

end Strata.Dyn.Exec.EffectsTest
