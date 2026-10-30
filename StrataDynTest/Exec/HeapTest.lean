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
the checks.  Each run is on both engines.

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

/-- Run `f` of the module of `fs` on `args`, on `engine`. -/
def run (fs : List (Func E Unit)) (f : String) (args : Array Int) (engine : Engine := .fused) :
    String :=
  match mod fs with
  | .ok m =>
    let o := runModule ExSem.model m (nm f) (args.map (ExSem.model.arg ·)) 10000 (engine := engine)
    showRes o.result
  | .error e => s!"fault {repr e}"

/-- Both engines' outcomes, if they agree. -/
def both (fs : List (Func E Unit)) (f : String) (args : Array Int) : Option String :=
  let a := run fs f args
  if a == run fs f args (engine := .frames) then some a else none

/-! ## Cells anywhere -/

-- The running example's result type is Lean's `Except`, at a payload that depends on the token.
example {σ : Type} [Store σ] :
    ExSem.model.interp σ (ExSem.T.base.Except ExSem.T.base.Int
      (ExSem.T.base.Ref ExSem.T.base.Int)) = Except Int (Ref σ Int) := rfl

-- The running example: `mkRef` returns its cell in an `ok`, and `useRef` reads it back.
#guard both [mkRef, useRef] "useRef" #[5] = some "ok 5"
#guard both [mkRef, useRef] "useRef" #[0] = some "raised 1"

-- A cell a rule made, in a generated datatype, taken out by its case and read by the machine.
#guard both [slotRead] "slotRead" #[6] = some "6"

-- A machine cell, read and written by rules.
#guard both [bump] "bump" #[41] = some "42"

-- A region run on a cell its rule made, which reads and writes it: `x + 2x`.
#guard both [regionCell] "regionCell" #[4] = some "12"

-- A closure in a generated datatype, taken out by its case and called.
#guard both [incI, cloCall] "cloCall" #[9] = some "10"

-- Two updates of one cell, each one request.
#guard both [cellAdds] "cellAdds" #[4] = some "7"

-- Pushes onto a sequence in a cell, each one request: `0, 1, 2, 3` packed.
#guard both [pushes] "pushes" #[4] = some "10203"
#guard both [pushes] "pushes" #[0] = some "0"

-- A chain of two links, each a cell holding the next, made and followed.
#guard both [links] "links" #[] = some "1"

-- A thunk whose closure returns a thunk, stored in a cell and called through twice.
#guard both [self, thunks] "thunks" #[9] = some "9"

-- A rule that retypes a ref: the machine's check at the access catches it, beside a read
-- through the cell's own ref.
#guard both [retyped] "retyped" #[5] = some "fault Strata.Dyn.Exec.Fault.badCell 0"
#guard both [retypedTwin] "retypedTwin" #[5] = some "5"

/-! ## Generic rules

A generic rule takes a type argument's tag only if it reaches a cell at it. -/

-- `ex.newAt` and `ex.getAt` at `Bool` and at `Except Int Int`.
#guard both [genericCells] "genericCells" #[3] = some "3"

-- A cell `ex.cellNew` made at `Int`, read by `ex.getAt` at `Int`.
#guard both [genericInt] "genericInt" #[8] = some "8"

-- `ex.dup` copies a box's cell, so a write to the original leaves the copy.
#guard both [boxes] "boxes" #[4] = some "4"

-- `ex.swap` moves refs and takes no tag.
#guard both [swapped] "swapped" #[4] = some "0"

-- `ex.boxCell` makes a cell holding a `Box`, whose tag comes from `Box`'s type constructor.
#guard both [boxed] "boxed" #[4] = some "4"

/-! ## A world that keeps cells

`Hp`'s world takes the token, and its `Globals` part keeps a cell, which `hp.globalCell` makes on
first use and returns ever after. -/

/-- An environment whose world keeps cells. -/
public environment Hp extends Base where
  namespace hp
  open base
  /-- The one global cell, made on first use. -/
  insn globalCell : Ref Int
  end hp

#dyn_types Hp

/-- The global cell, once made: a part of the world that holds a ref. -/
public structure Globals (σ : Type) [Store σ] where
  cell : Option (Ref σ Int) := none

/-- `Hp`'s world, at each token. -/
public structure HpWorld (σ : Type) [Store σ] where
  globals : Globals σ := {}

public instance {σ : Type} [Store σ] : Inhabited (HpWorld σ) := ⟨{}⟩

public instance {σ : Type} [Store σ] : HasPart (HpWorld σ) (Globals σ) :=
  ⟨(·.globals), fun _ g => { globals := g }⟩

/-- The global cell: the one the world keeps, or a new one, which it then keeps.  It takes its
capabilities one by one, without a language's class. -/
@[dyn_sem Hp.globalCell, expose]
public def globalCell {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type}
    [HasPart ε.W (Globals σ)] [HasHeap σ ε] [TagOf σ Int] : Sem ε E (Ref σ Int) := do
  if let some c := (← getThe (Globals σ)).cell then return c
  let c ← newRef 0
  modifyThe (Globals σ) fun _ => { cell := some c }
  return c

public section
#dyn_sem_table HpSem for Hp (world := HpWorld)
end

section
abbrev H := Hp.env
def hd (n : Nat) (t : TypeExpr H) : ValDecl H := ⟨⟨n⟩, t⟩

/-- `twice()`: write `5` to the global cell, then read the global cell, the same one. -/
def twice : Func H Unit :=
  let f : Func H Unit := ⟨nm "twice", Base.Int, #[
    ⟨⟨nm "entry"⟩, #[], #[
      .apply () (hd 0 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
      .const () (hd 1 Base.Int) (.int 5),
      .apply () (hd 2 Base.Unit) Base.refSet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨0⟩, ⟨1⟩] #[] #[],
      .apply () (hd 3 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
      .apply () (hd 4 Base.Int) Base.refGet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨3⟩] #[] #[]],
      .ret () ⟨4⟩, ()⟩], #[], ()⟩
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- The run of `twice`: its result, and whether the world keeps a cell. -/
def runTwice (engine : Engine) : Option (Option Int × Bool) :=
  match Module.Raw.check ⟨nm "hp", #[twice], ()⟩ with
  | .ok m =>
    let o := runModule HpSem.model m (nm "twice") #[] 100 (engine := engine)
    some (o.read? Int, o.snapshot.world.globals.cell.isSome)
  | .error _ => none
end

#guard runTwice .fused = some (some 5, true)
#guard runTwice .frames = some (some 5, true)

/-! ## From one run to the next

A module's top level runs first, and a function of the module then runs from the snapshot of the
heap and the world where it ended, so it finds the cell that the top level made and kept. -/

section

/-- `main()`, the top level: write `7` to the global cell, and return `0`. -/
def main : Func H Unit :=
  let f : Func H Unit := ⟨nm "main", Base.Int, #[
    ⟨⟨nm "entry"⟩, #[], #[
      .apply () (hd 0 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
      .const () (hd 1 Base.Int) (.int 7),
      .apply () (hd 2 Base.Unit) Base.refSet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨0⟩, ⟨1⟩] #[] #[],
      .const () (hd 3 Base.Int) (.int 0)],
      .ret () ⟨3⟩, ()⟩], #[], ()⟩
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- `fetch()`: the global cell's value. -/
def fetch : Func H Unit :=
  let f : Func H Unit := ⟨nm "fetch", Base.Int, #[
    ⟨⟨nm "entry"⟩, #[], #[
      .apply () (hd 0 (Base.Ref Base.Int)) Hp.globalCell.ref ⟨#[], rfl⟩ #[] #[] #[],
      .apply () (hd 1 Base.Int) Base.refGet.ref ⟨#[.ty Base.Int], rfl⟩ #[⟨0⟩] #[] #[]],
      .ret () ⟨1⟩, ()⟩], #[], ()⟩
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- Run the functions named `fs` of the module of `main`, `twice` and `fetch` one after the
other, each from the snapshot where the one before it ended, the first from the initial
snapshot: each run's result and the number of cells its heap ends with. -/
def chain (fs : List String) (engine : Engine) : Option (List (Option Int × Nat)) :=
  match Module.Raw.check ⟨nm "hp", #[main, twice, fetch], ()⟩ with
  | .error _ => none
  | .ok m => match prepare HpSem.model m (nm "main") with
    | .error _ => none
    | .ok ⟨lm, hw, _⟩ =>
      let step (acc : Option (Snapshot HpSem.model.at × List (Option Int × Nat))) (f : String) :=
        acc.bind fun (snap, out) => (lm.funcIndex (nm f)).bind fun j =>
          match startCore hw j [] snap with
          | .error _ => none
          | .ok ⟨_, c, h⟩ =>
            let s : State HpSem.model.at := ⟨c, .exec, 0, ()⟩
            let o : Outcome HpSem.model := (match engine with
              | .fused => runFused hw (fun _ => 0) 100 s h
              | .frames => runFrames hw (fun _ => 0) 100 s h).outcome 100
            some (o.snapshot, out ++ [(o.read? Int, o.snapshot.heap.cells.size)])
      (fs.foldl step (some (.initial, []))).map (·.2)

end

-- After `main`, `fetch` reads the `7` in the cell `main` made, and makes no cell.
#guard chain ["main", "fetch"] .fused = some [(some 0, 1), (some 7, 1)]
#guard chain ["main", "fetch"] .frames = some [(some 0, 1), (some 7, 1)]

-- On its own, `fetch` makes a new cell, holding `0`.
#guard chain ["fetch"] .fused = some [(some 0, 1)]
#guard chain ["fetch"] .frames = some [(some 0, 1)]

-- Each run starts from the snapshot the one before it ended with: `twice` overwrites `main`'s
-- `7` with `5` in the same cell, and `fetch` then reads the `5`.
#guard chain ["main", "twice", "fetch"] .fused = some [(some 0, 1), (some 5, 1), (some 5, 1)]
#guard chain ["main", "twice", "fetch"] .frames = some [(some 0, 1), (some 5, 1), (some 5, 1)]

/-! ## The checks

A ref given at the machine's token can name any location.  Each function makes one cell, at
location `0`, then uses the ref it is given: at `0` it finds its own cell, or, if it made a
`Bool`, one of another tag; at `7`, nothing.  Through the machine's instructions and through a
rule alike, the check faults with `Fault.badCell`. -/

/-- Run `f` of the module of `fs` on a ref to location `l`, given at the machine's token. -/
def runOnCell (fs : List (Func E Unit)) (f : String) (l : Nat) (engine : Engine := .fused) :
    String :=
  match mod fs with
  | .error e => s!"fault {repr e}"
  | .ok m => match prepare ExSem.model m (nm f) with
    | .error e => s!"fault {repr e}"
    | .ok ⟨_, hw, i⟩ =>
      let M := ExSem.model.at
      showRes (runPrepared hw i #[⟨Ty.ref ExSem.T.base.Int, M.cellAt ExSem.T.base.Int l⟩] 100
        (fun _ => 0) engine).result

/-- Both engines' outcomes on a cell at `l`, if they agree. -/
def bothOnCell (fs : List (Func E Unit)) (f : String) (l : Nat) : Option String :=
  let a := runOnCell fs f l
  if a == runOnCell fs f l (engine := .frames) then some a else none

-- The machine's read: a valid cell, one of another code, and one past the heap.
#guard bothOnCell [readInt] "readInt" 0 = some "5"
#guard bothOnCell [readAfterBool] "readAfterBool" 0 =
  some "fault Strata.Dyn.Exec.Fault.badCell 0"
#guard bothOnCell [readInt] "readInt" 7 = some "fault Strata.Dyn.Exec.Fault.badCell 7"

-- The machine's write, alike.
#guard bothOnCell [setInt] "setInt" 0 = some "7"
#guard bothOnCell [setAfterBool] "setAfterBool" 0 =
  some "fault Strata.Dyn.Exec.Fault.badCell 0"
#guard bothOnCell [setInt] "setInt" 7 = some "fault Strata.Dyn.Exec.Fault.badCell 7"

-- A rule's read, alike.
#guard bothOnCell [ruleRead] "ruleRead" 0 = some "5"
#guard bothOnCell [ruleReadAfterBool] "ruleReadAfterBool" 0 =
  some "fault Strata.Dyn.Exec.Fault.badCell 0"
#guard bothOnCell [ruleRead] "ruleRead" 7 = some "fault Strata.Dyn.Exec.Fault.badCell 7"

/-! ## No forged refs

No term generic in the token is a raw ref or a raw closure, so none is a ref or a closure at any
type, and a start argument holds neither. -/

example (α : Type) (f : (σ : Type) → [Store σ] → Ref σ α) : False := no_forge fun σ _ => (f σ).raw

example (as : List Type) (r : Type) (f : (σ : Type) → [Store σ] → FnRef σ as r) : False :=
  no_forge_fn fun σ _ => (f σ).raw

/-! ## Steps

What each heap program costs on each engine. -/

/-- A run, as a line: its outcome and its steps on each engine. -/
def line (fs : List (Func E Unit)) (f : String) (args : Array Int) : String :=
  match mod fs with
  | .ok m =>
    let a := runModule ExSem.model m (nm f) (args.map (ExSem.model.arg ·)) 10000
    let b := runModule ExSem.model m (nm f) (args.map (ExSem.model.arg ·)) 10000 (engine := .frames)
    s!"{f} {args}: {showRes a.result} after {a.steps} fused, {b.steps} by step"
  | .error e => s!"{f}: fault {repr e}"

/--
info: useRef #[5]: ok 5 after 12 fused, 18 by step
slotRead #[6]: 6 after 5 fused, 9 by step
bump #[41]: 42 after 7 fused, 11 by step
regionCell #[4]: 12 after 7 fused, 15 by step
cloCall #[9]: 10 after 8 fused, 13 by step
-/
#guard_msgs in
#eval IO.println ("\n".intercalate [line [mkRef, useRef] "useRef" #[5],
  line [slotRead] "slotRead" #[6], line [bump] "bump" #[41], line [regionCell] "regionCell" #[4],
  line [incI, cloCall] "cloCall" #[9]])

end Strata.Dyn.ExecTest.HeapTest
