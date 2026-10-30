/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Programs
public import StrataDynTest.Examples.While.Programs
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
import StrataDyn.DSL
-- `#guard` runs the engine and the programs as compiled code.
meta import StrataDynTest.Exec.Programs
meta import StrataDynTest.Examples.While.Programs
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# A parent's rules in a child's table

A rule is written at Lean types, and takes its table's decoding as `Decode σ`, so a child's table
runs its parent's rules unchanged, those that call and those that reach cells included: the
child's wrapper builds the parent's tags from the child's own decoding.

* `ExKid` extends `Ex` with a datatype and a calling rule of its own, whose language class
  extends `Ex.Lang`.  Its table runs `Ex`'s programs, calls of closures and partial application
  included, as `Ex`'s table does, on both engines.
* `WhileKid` extends `While` with one instruction.  Its table runs While's programs, cells
  included, as `While`'s does.
-/

namespace Strata.Dyn.ExecTest.InheritTest

open Strata.Dyn.Exec

/-- A child of `Ex`. -/
public environment ExKid extends Ex where
  namespace exKid
  open base
  /-- A point. -/
  data Pt where
    | pt (x y : Int)
  /-- Call `f` on `p`. -/
  insn callPt (f : Fn [Pt] Int) (p : Pt) : Int
  end exKid

#dyn_types ExKid

namespace ExKidRules

@[expose] public section

/-- `ExKid`'s capabilities: `Ex`'s, and the tag of points. -/
@[dyn_lang] class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff)
    extends ExRules.Lang σ ε where
  tagPt : TagOf σ ExKid.Pt.Val

variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [Lang σ ε]

@[dyn_sem ExKid.callPt]
def callPt (f : FnRef σ [ExKid.Pt.Val] Int) (p : ExKid.Pt.Val) : Sem ε E Int := callFn f p

end

end ExKidRules

public section

/-- info: ExKidSem: no rule for ex.nope -/
#guard_msgs in
#dyn_sem_table ExKidSem for ExKid (world := ExRules.World)

end

-- The child's tags of the parent's types are the parent's: its own types' heads come after.
example : ExKidSem.T.base.Int = ExSem.T.base.Int := rfl
example : ExKidSem.T.ex.Box ExKidSem.T.base.Int = ExSem.T.ex.Box ExSem.T.base.Int := rfl

section
open Strata.Dyn.ExecTest.Programs

/-- What a run of `f` of the module of `fs` on `args` returned, in a table: an `Int`, an
`Except Int Int` or a fault, as a string, with its steps. -/
def runIn (M : Model) [∀ (σ : Type) [Store σ], @TagOf σ _ (M.decode σ) Int]
    [@TagOf Run _ (M.decode Run) (Except Int Int)]
    (fs : List (Func Programs.E Unit)) (f : String) (args : Array Int) (engine : Engine) :
    String :=
  match mod fs with
  | .error e => s!"fault {repr e}"
  | .ok m =>
    let o := runModule M m (nm f) (args.map (M.arg ·)) 10000 (engine := engine)
    let r := match o.read? Int, o.read? (Except Int Int), o.result with
      | some v, _, _ => s!"{v}"
      | _, some (.ok v), _ => s!"ok {v}"
      | _, some (.error e), _ => s!"error {e}"
      | none, none, .ok _ => "?"
      | none, none, .fault f => s!"fault {repr f}"
    s!"{r} after {o.steps}"

/-- A run in `Ex`'s table. -/
def runEx (fs : List (Func Programs.E Unit)) (f : String) (args : Array Int) (engine : Engine) :
    String :=
  runIn ExSem.model fs f args engine

/-- The same run in `ExKid`'s table. -/
def runKid (fs : List (Func Programs.E Unit)) (f : String) (args : Array Int) (engine : Engine) :
    String :=
  runIn ExKidSem.model fs f args engine

/-- The child's table runs `f` as the parent's does, on both engines, with the same result. -/
def same (fs : List (Func Programs.E Unit)) (f : String) (args : Array Int) : Option String :=
  let a := runKid fs f args .fused
  if a == runEx fs f args .fused && runKid fs f args .frames == runEx fs f args .frames then
    some a
  else none

-- `ex.call` (raising) and `ex.callInt`, each a rule's checked call, in the child's table.
#guard same [inc, fib] "fib" #[10] = some "ok 55 after 1589"
#guard same [incI, typed] "typed" #[5] = some "6 after 6"
-- A partial application, called by a rule and by `base.callCode`.
#guard same [addRef, closure] "closure" #[5] = some "19 after 21"
-- Cells, and generic rules at type arguments, through a type constructor's tag.
#guard same [bump] "bump" #[41] = some "42 after 7"
#guard same [genericCells] "genericCells" #[3] = some "3 after 8"
#guard same [boxes] "boxes" #[4] = some "4 after 8"
#guard same [boxed] "boxed" #[4] = some "4 after 5"

end

/-! ## While's rules in a child's table -/

/-- A child of `While`. -/
public environment WhileKid extends While where
  namespace whileKid
  open base
  /-- `x + 1`. -/
  insn succ (x : Int) : Int
  end whileKid

#dyn_types WhileKid

/-- `x + 1`. -/
@[dyn_sem WhileKid.succ] public def succ (x : Int) : Int := x + 1

public section
#dyn_sem_table WhileKidSem for WhileKid (world := WhileRules.World)
end

section
open Strata.Dyn.While Strata.Dyn.While.Programs

/-- The `Int`, or the `ok` of the `Except Int Int`, a While program's function `f` returns on
`args`, in `M`, on `engine`, with its steps. -/
def runWhile (M : Model) [∀ (σ : Type) [Store σ], @TagOf σ _ (M.decode σ) Int]
    [@TagOf Run _ (M.decode Run) (Except Int Int)]
    (p : Ast.Program) (f : String) (args : Array Int) (engine : Engine) :
    Option (Option Int × Nat) :=
  match lower p with
  | .error _ => none
  | .ok m =>
    let o := runModule M m (nm f) (args.map (M.arg ·)) 100000 (engine := engine)
    some ((o.read? Int).orElse fun _ => (o.read? (Except Int Int)).bind (·.toOption), o.steps)

/-- `f` in While's table and in the child's, on both engines. -/
def whileSame (p : Ast.Program) (f : String) (args : Array Int) : Option (Option Int × Nat) :=
  let parent (e : Engine) := runWhile WhileSem.model p f args e
  let kid (e : Engine) := runWhile WhileKidSem.model p f args e
  if kid .fused == parent .fused && kid .frames == parent .frames then kid .fused else none

#guard (whileSame fib "fib" #[10]).map (·.1) = some (some 55)
#guard (whileSame cells "counter" #[5]).map (·.1) = some (some 5)
#guard (whileSame rcounter "rcounter" #[5]).map (·.1) = some (some 5)

end

end Strata.Dyn.ExecTest.InheritTest
