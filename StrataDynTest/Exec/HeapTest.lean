/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Programs
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
import StrataDyn.DSL
-- `#guard` runs the engine and the programs as compiled code.
meta import StrataDynTest.Exec.Programs
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# The heap

Cells anywhere a value may be, rules that make and return them, a world that keeps them, and
the checks.

* the running example: a ref in an `Except`'s payload, read back;
* a ref in a generated datatype, and a closure in one;
* rules that make a cell, return a ref, read and write a machine cell, and hand a ref to a
  region;
* generic rules at type arguments: cells of `Bool` and `Except Int Int`, a cell one rule made
  read by a generic one, and refs of a type parameter in generated datatypes, copied, swapped and
  boxed through a type constructor's tag;
* a world part that keeps refs, in an environment whose world takes the token;
* a module's top level, then functions run, one after another, each from the snapshot of the
  heap and the world where the one before it ended;
* `runPreparedFrom`: a function run from where another run ended, which finds the cells the
  first one kept, makes new cells after them, takes arguments, draws after the first run's
  choices, and doesn't continue a run that faulted or ran out of fuel;
* the checks, on a ref given at the machine's token, which no rule and no start argument can
  make: on the bound and on the tag, through the machine and through a rule, each beside its
  valid twin.
-/

namespace Strata.Dyn.ExecTest.HeapTest

open Strata.Dyn.ExecTest.Programs
open Strata.Dyn.Exec

section
variable {σ : Type} [Store σ]

/-- The `Int` or the `Except Int Int` a run returned, as a string, or its fault. -/
def showRes (r : Result (ExSem.model.interp σ)) : String :=
  match ExSem.model.read? r Int, ExSem.model.read? r (Except Int Int), r with
  | some v, _, _ => s!"{v}"
  | _, some (.ok v), _ => s!"ok {v}"
  | _, some (.error e), _ => s!"raised {e}"
  | none, none, .ok _ => "?"
  | none, none, .fault f => s!"fault {repr f}"

end

/-- Run `f` of the module of `fs` on `args`. -/
def run (fs : List (Func E Unit)) (f : String) (args : Array Int) : String :=
  match mod fs with
  | .ok m =>
    let o := runModule ExSem.model m (nm f) (args.map (ExSem.model.arg ·)) 10000
    showRes o.result
  | .error e => s!"fault {repr e}"

/-! ## Cells anywhere -/

-- The running example's result type is Lean's `Except`, at a payload that depends on the token.
example {σ : Type} [Store σ] :
    ExSem.model.interp σ (ExSem.T.base.Except ExSem.T.base.Int
      (ExSem.T.base.Ref ExSem.T.base.Int)) = Except Int (Ref σ Int) := rfl

-- The running example: `mkRef` returns its cell in an `ok`, and `useRef` reads it back.
#guard run [mkRef, useRef] "useRef" #[5] = "ok 5"
#guard run [mkRef, useRef] "useRef" #[0] = "raised 1"

-- A cell a rule made, in a generated datatype, taken out by its case and read by the machine.
#guard run [slotRead] "slotRead" #[6] = "6"

-- A machine cell, read and written by rules.
#guard run [bump] "bump" #[41] = "42"

-- A region run on a cell its rule made, which reads and writes it: `x + 2x`.
#guard run [regionCell] "regionCell" #[4] = "12"

-- A closure in a generated datatype, taken out by its case and called.
#guard run [incI, cloCall] "cloCall" #[9] = "10"

-- Two updates of one cell, each one request.
#guard run [cellAdds] "cellAdds" #[4] = "7"

-- Pushes onto a sequence in a cell, each one request: `0, 1, 2, 3` packed.
#guard run [pushes] "pushes" #[4] = "10203"
#guard run [pushes] "pushes" #[0] = "0"

-- A chain of two links, each a cell holding the next, made and followed.
#guard run [links] "links" #[] = "1"

-- A thunk whose closure returns a thunk, stored in a cell and called through twice.
#guard run [self, thunks] "thunks" #[9] = "9"

/-! ## Generic rules

A generic rule takes a type argument's tag only if it reaches a cell at it. -/

-- `ex.newAt` and `ex.getAt` at `Bool` and at `Except Int Int`.
#guard run [genericCells] "genericCells" #[3] = "3"

-- A cell `ex.cellNew` made at `Int`, read by `ex.getAt` at `Int`.
#guard run [genericInt] "genericInt" #[8] = "8"

-- `ex.dup` copies a box's cell, so a write to the original leaves the copy.
#guard run [boxes] "boxes" #[4] = "4"

-- `ex.swap` moves refs and takes no tag.
#guard run [swapped] "swapped" #[4] = "0"

-- `ex.boxCell` makes a cell holding a `Box`, whose tag comes from `Box`'s type constructor.
#guard run [boxed] "boxed" #[4] = "4"

/-! ## A world that keeps cells

`Hp`'s world takes the token, and its `Globals` part keeps a cell, which `hp.globalCell` makes on
first use and returns ever after. -/

/-- An environment whose world keeps cells. -/
public environment Hp extends Base where
  namespace hp
  open base
  /-- The one global cell, made on first use. -/
  insn globalCell : Ref Int
  /-- `a + b`. -/
  insn add (a b : Int) : Int
  /-- `a * b`. -/
  insn mul (a b : Int) : Int
  /-- A number the oracle chooses. -/
  insn pick : Int
  end hp

#dyn_types Hp

/-- The global cell, once made: a part of the world that holds a ref. -/
public structure Globals (σ : Type) [Store σ] where
  cell : Option (Ref σ Int) := none

/-- `Hp`'s world, at each token. -/
public structure HpWorld (σ : Type) [Store σ] where
  globals : Globals σ := {}

public instance {σ : Type} [Store σ] : Inhabited (HpWorld σ) := ⟨{}⟩

#dyn_world HpWorld

/-- The global cell: the one the world keeps, or a new one, which it then keeps.  It takes its
capabilities one by one, without a language's class. -/
@[dyn_sem Hp.globalCell, expose]
public def globalCell {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type}
    [HasPart ε.W (Globals σ)] [HasHeap σ ε] [TagOf σ Int] : Sem ε E (Ref σ Int) := do
  if let some c := (← getThe (Globals σ)).cell then return c
  let c ← newRef 0
  modifyThe (Globals σ) fun _ => { cell := some c }
  return c

@[dyn_sem Hp.add, expose] public def add (a b : Int) : Int := a + b

@[dyn_sem Hp.mul, expose] public def mul (a b : Int) : Int := a * b

@[dyn_sem Hp.pick, expose] public def pick {ε : Eff} {E : Type} : Sem ε E Int :=
  return Int.ofNat (← chooseNat)

public section
#dyn_sem_table HpSem for Hp (world := HpWorld)
end

section
abbrev H := Hp.env
def hd (n : Nat) (t : TypeExpr H) : ValDecl H := ⟨⟨n⟩, t⟩

/-- A function named `n` that returns `r`, with the blocks `bs`; its parameters are its entry
block's. -/
def mkF (n : Name) (r : TypeExpr H) (bs : Array (Block H Unit)) : Func H Unit :=
  { name := n, params := (bs[0]?.map (·.params)).getD #[], retType := r, blocks := bs,
    names := #[], info := () }

/-- `twice()`: write `5` to the global cell, then read the global cell, the same one. -/
def twice : Func H Unit :=
  let f : Func H Unit :=
    { name := nm "twice", params := #[], retType := Base.Int, names := #[], info := (),
      blocks := #[
        ⟨⟨nm "entry"⟩, #[], #[
          .apply () (hd 0 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
          .const () (hd 1 Base.Int) (.int 5),
          .apply () (hd 2 Base.Unit) Base.refSet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨0⟩, ⟨1⟩] #[] #[],
          .apply () (hd 3 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
          .apply () (hd 4 Base.Int) Base.refGet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨3⟩] #[] #[]],
          .ret () ⟨4⟩, ()⟩] }
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- The run of `twice`: its result, and whether the world keeps a cell. -/
def runTwice : Option (Option Int × Bool) :=
  match Module.Raw.check { name := nm "hp", funcs := #[twice], info := () } with
  | .ok m =>
    let o := runModule HpSem.model m (nm "twice") #[] 100
    some (o.read? Int, o.snapshot.world.globals.cell.isSome)
  | .error _ => none
end

#guard runTwice = some (some 5, true)

/-! ## From one run to the next

A module's top level runs first, and a function of the module then runs from the snapshot of the
heap and the world where it ended, so it finds the cell that the top level made and kept. -/

section

/-- `main()`, the top level: write `7` to the global cell, and return `0`. -/
def main : Func H Unit :=
  let f : Func H Unit :=
    { name := nm "main", params := #[], retType := Base.Int, names := #[], info := (),
      blocks := #[
        ⟨⟨nm "entry"⟩, #[], #[
          .apply () (hd 0 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
          .const () (hd 1 Base.Int) (.int 7),
          .apply () (hd 2 Base.Unit) Base.refSet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨0⟩, ⟨1⟩] #[] #[],
          .const () (hd 3 Base.Int) (.int 0)],
          .ret () ⟨3⟩, ()⟩] }
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- `fetch()`: the global cell's value. -/
def fetch : Func H Unit :=
  let f : Func H Unit :=
    { name := nm "fetch", params := #[], retType := Base.Int, names := #[], info := (),
      blocks := #[
        ⟨⟨nm "entry"⟩, #[], #[
          .apply () (hd 0 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
          .apply () (hd 1 Base.Int) Base.refGet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨0⟩] #[] #[]],
          .ret () ⟨1⟩, ()⟩] }
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- Run the functions named `fs` of the module of `main`, `twice` and `fetch` one after the
other, each from the snapshot where the one before it ended, the first from the initial
snapshot: each run's result and the number of cells its heap ends with. -/
def chain (fs : List String) : Option (List (Option Int × Nat)) :=
  match Module.Raw.check { name := nm "hp", funcs := #[main, twice, fetch], info := () } with
  | .error _ => none
  | .ok m => match prepare HpSem.model m (nm "main") with
    | .error _ => none
    | .ok ⟨lm, hw, _⟩ =>
      let step (acc : Option (Snapshot HpSem.model.at × List (Option Int × Nat))) (f : String) :=
        acc.bind fun (snap, out) => (lm.funcIndex (nm f)).bind fun j =>
          match startCore hw j [] snap with
          | .error _ => none
          | .ok ⟨_, c, h⟩ =>
            let o : Outcome HpSem.model :=
              (runFused hw (fun _ => 0) 100 ⟨c, .exec, 0, ()⟩ h).outcome 100
            some (o.snapshot, out ++ [(o.read? Int, o.snapshot.heap.cells.size)])
      (fs.foldl step (some (.initial, []))).map (·.2)

end

-- After `main`, `fetch` reads the `7` in the cell `main` made, and makes no cell.
#guard chain ["main", "fetch"] = some [(some 0, 1), (some 7, 1)]

-- On its own, `fetch` makes a new cell, holding `0`.
#guard chain ["fetch"] = some [(some 0, 1)]

-- Each run starts from the snapshot the one before it ended with: `twice` overwrites `main`'s
-- `7` with `5` in the same cell, and `fetch` then reads the `5`.
#guard chain ["main", "twice", "fetch"] = some [(some 0, 1), (some 5, 1), (some 5, 1)]

/-! ## `runPreparedFrom` -/

section

/-- `mix()`: make a new cell holding `42`, then read the global cell. -/
def mix : Func H Unit :=
  let f : Func H Unit := mkF (nm "mix") Base.Int #[
    ⟨⟨nm "entry"⟩, #[], #[
      .const () (hd 0 Base.Int) (.int 42),
      .apply () (hd 1 (Base.Ref Base.Int)) Base.refNew.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨0⟩] #[] #[],
      .apply () (hd 2 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
      .apply () (hd 3 Base.Int) Base.refGet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨2⟩] #[] #[]],
      .ret () ⟨3⟩, ()⟩]
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- `addTo(x)`: the global cell's value plus `x`. -/
def addTo : Func H Unit :=
  let f : Func H Unit := mkF (nm "addTo") Base.Int #[
    ⟨⟨nm "entry"⟩, #[hd 0 Base.Int], #[
      .apply () (hd 1 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
      .apply () (hd 2 Base.Int) Base.refGet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨1⟩] #[] #[],
      .apply () (hd 3 Base.Int) Hp.add.ref ⟨#[], rfl⟩ #[⟨2⟩, ⟨0⟩] #[] #[]],
      .ret () ⟨3⟩, ()⟩]
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- `pickTwo()`: `10 * a + b`, for the oracle's next two numbers `a` and `b`. -/
def pickTwo : Func H Unit :=
  let f : Func H Unit := mkF (nm "pickTwo") Base.Int #[
    ⟨⟨nm "entry"⟩, #[], #[
      .apply () (hd 0 Base.Int) Hp.pick.ref ⟨#[], rfl⟩ #[] #[] #[],
      .apply () (hd 1 Base.Int) Hp.pick.ref ⟨#[], rfl⟩ #[] #[] #[],
      .const () (hd 2 Base.Int) (.int 10),
      .apply () (hd 3 Base.Int) Hp.mul.ref ⟨#[], rfl⟩ #[⟨2⟩, ⟨0⟩] #[] #[],
      .apply () (hd 4 Base.Int) Hp.add.ref ⟨#[], rfl⟩ #[⟨3⟩, ⟨1⟩] #[] #[]],
      .ret () ⟨4⟩, ()⟩]
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- Run `first` for `fuel` steps, then `g` on `args` from where it ended, both with the oracle
`tape`: both runs' outcomes, the second as `runPreparedFrom` gives it. -/
def runThen (first g : String) (args : Array HpSem.model.Arg)
    (fuel : Nat := 100) (tape : List Nat := []) :
    Option (Outcome HpSem.model × Except (Outcome HpSem.model) (Outcome HpSem.model)) :=
  match Module.Raw.check
      { name := nm "hp", funcs := #[main, fetch, mix, addTo, pickTwo], info := () } with
  | .error _ => none
  | .ok m => match prepare HpSem.model m (nm first) with
    | .error _ => none
    | .ok ⟨lm, hw, i⟩ => (lm.funcIndex (nm g)).map fun j =>
      let o₁ := runPrepared hw i #[] fuel (tapeOracle tape)
      (o₁, runPreparedFrom hw j o₁ args 100 (tapeOracle tape))

/-- The second run's result as an integer, and the cells its heap ends with. -/
def second (first g : String) (args : Array HpSem.model.Arg) :
    Option (Option Int × Nat) :=
  (runThen first g args).bind fun (_, o) => o.toOption.map fun o =>
    (o.read? Int, o.snapshot.heap.cells.size)

end

-- After `main`, `fetch` reads the `7` in the cell that `main` made, and makes no cell.
#guard second "main" "fetch" #[] = some (some 7, 1)

-- The second run's new cell comes after the kept one, so `mix` reads `7`, not its own `42`.
#guard second "main" "mix" #[] = some (some 7, 2)

-- The second run takes arguments.
#guard second "main" "addTo" #[HpSem.model.arg (3 : Int)] = some (some 10, 1)

-- The second run draws the oracle's next answers, after the two the first one drew, and the
-- result's `drawn` counts the choices of both runs.
#guard (runThen "pickTwo" "pickTwo" #[] (tape := [3, 8, 5, 6])).map (fun (o₁, o) =>
  (o₁.read? Int, o.toOption.map fun o => (o.read? Int, o.drawn))) = some (some 38, some (some 56, 4))

-- The result's steps are only the second run's: `main` takes 5 steps, and `fetch` after it 3.
#guard (runThen "main" "fetch" #[]).map (fun (o₁, o) =>
  (o₁.steps, o.toOption.map fun (x : Outcome HpSem.model) => x.steps)) = some (5, some 3)

/-- The first run and the second's error, as their steps and whether each ran out of fuel. -/
def errorOf (r : Outcome HpSem.model × Except (Outcome HpSem.model) (Outcome HpSem.model)) :
    Option ((Nat × Bool) × (Nat × Bool)) :=
  let outOfFuel (o : Outcome HpSem.model) := match o.result with
    | .fault .outOfFuel => true
    | _ => false
  match r.2 with
  | .error o => some ((r.1.steps, outOfFuel r.1), (o.steps, outOfFuel o))
  | .ok _ => none

-- After a `main` that ran out of fuel after its 1 step, nothing runs: the error is that run.
#guard (runThen "main" "fetch" #[] (fuel := 1)).bind errorOf = some ((1, true), (1, true))

-- After a first run that faulted otherwise, here `addTo` without its argument, nothing runs.
#guard (runThen "addTo" "fetch" #[]).bind errorOf = some ((0, false), (0, false))

-- A second run that can't start, here on an argument `fetch` doesn't take, keeps the heap.
#guard second "main" "fetch" #[HpSem.model.arg (3 : Int)] = some (none, 1)

/-! ## The checks

A ref given at the machine's token can name any location.  Each function makes one cell, at
location `0`, then uses the ref it is given: at `0` it finds its own cell, or, if it made a
`Bool`, one of another tag; at `7`, nothing.  Through the machine's instructions and through a
rule alike, the check faults with `Fault.badCell`. -/

/-- Run `f` of the module of `fs` on a ref to location `l`, given at the machine's token. -/
def runOnCell (fs : List (Func E Unit)) (f : String) (l : Nat) : String :=
  match mod fs with
  | .error e => s!"fault {repr e}"
  | .ok m => match prepare ExSem.model m (nm f) with
    | .error e => s!"fault {repr e}"
    | .ok ⟨_, hw, i⟩ =>
      let M := ExSem.model.at
      showRes (runPrepared hw i #[⟨Ty.ref ExSem.T.base.Int, M.cellAt ExSem.T.base.Int l⟩] 100
        (fun _ => 0)).result

-- The machine's read: a valid cell, one of another code, and one past the heap.
#guard runOnCell [readInt] "readInt" 0 = "5"
#guard runOnCell [readAfterBool] "readAfterBool" 0 =
  "fault Strata.Dyn.Exec.Fault.badCell 0"
#guard runOnCell [readInt] "readInt" 7 = "fault Strata.Dyn.Exec.Fault.badCell 7"

-- The machine's write, alike.
#guard runOnCell [setInt] "setInt" 0 = "7"
#guard runOnCell [setAfterBool] "setAfterBool" 0 =
  "fault Strata.Dyn.Exec.Fault.badCell 0"
#guard runOnCell [setInt] "setInt" 7 = "fault Strata.Dyn.Exec.Fault.badCell 7"

-- A rule's read, alike.
#guard runOnCell [ruleRead] "ruleRead" 0 = "5"
#guard runOnCell [ruleReadAfterBool] "ruleReadAfterBool" 0 =
  "fault Strata.Dyn.Exec.Fault.badCell 0"
#guard runOnCell [ruleRead] "ruleRead" 7 = "fault Strata.Dyn.Exec.Fault.badCell 7"

/-! ## No forged refs

No term generic in the token is a raw ref or a raw closure, so none is a ref or a closure at any
type, and a start argument holds neither. -/

example (α : Type) (f : (σ : Type) → [Store σ] → Ref σ α) : False := no_forge fun σ _ => (f σ).raw

example (as : List Type) (r : Type) (f : (σ : Type) → [Store σ] → FnRef σ as r) : False :=
  no_forge_fn fun σ _ => (f σ).raw

/-! ## Steps

What each heap program costs. -/

/-- A run, as a line: its outcome and its fused steps. -/
def line (fs : List (Func E Unit)) (f : String) (args : Array Int) : String :=
  match mod fs with
  | .ok m =>
    let a := runModule ExSem.model m (nm f) (args.map (ExSem.model.arg ·)) 10000
    s!"{f} {args}: {showRes a.result} after {a.steps} fused steps"
  | .error e => s!"{f}: fault {repr e}"

/--
info: useRef #[5]: ok 5 after 12 fused steps
slotRead #[6]: 6 after 5 fused steps
bump #[41]: 42 after 7 fused steps
regionCell #[4]: 12 after 7 fused steps
cloCall #[9]: 10 after 8 fused steps
-/
#guard_msgs in
#eval IO.println ("\n".intercalate [line [mkRef, useRef] "useRef" #[5],
  line [slotRead] "slotRead" #[6], line [bump] "bump" #[41], line [regionCell] "regionCell" #[4],
  line [incI, cloCall] "cloCall" #[9]])

end Strata.Dyn.ExecTest.HeapTest
