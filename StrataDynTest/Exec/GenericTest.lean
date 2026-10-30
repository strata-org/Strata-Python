/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
public import StrataDyn.Exec
public import StrataDyn.Exec.Base
public import StrataDyn.Exec.Run
import StrataDyn.Env.WF
import StrataDyn.DSL
meta import StrataDyn.Exec.Run
meta import StrataDyn.Env.WF
meta import StrataDyn.Base
meta import StrataDyn.Exec
meta import StrataDyn.Exec.Base

set_option autoImplicit false

/-!
# A rule written once over a record of primitives

`twiceBump` is written once, over the record of primitives `Prims`, generic in the monad and the
value type.  Its machine instance is `GM σ`, in the shape of the Python semantics' `PyM`: a
computation generic in the requests and the exits under a language's class, which takes two
continuations, one for a result and one for an error, with a proof whose statement names a ref's
location and the machine's heap capability.  The table's check skips propositions, which never
run, so it accepts `gn.twice`, the rule that runs the computation with `pure` and a jump along
its error target.  It runs on both paths: `bump` uses a machine cell, `note`
updates a part of the world with `modifyThe`, and `check` fails on a negative number.  The same
protocol also runs at a second instance, a plain state monad, which shows that the record serves
monads other than the machine's.
-/

namespace Strata.Dyn.ExecTest.Generic

open Strata.Dyn Strata.Dyn.Exec

/-- One instruction, given by a generic protocol. -/
public environment Gn extends Base where
  namespace gn
  open base
  insn twice (x : Int) (^neg (e : Int)) : Int
  end gn

#dyn_types Gn

/-- The values that `note` wrote. -/
public structure Notes where
  items : Array Int := #[]

/-- `Gn`'s world. -/
public structure GnWorld where
  notes : Notes := {}
  steps : Nat := 0

public instance : Inhabited GnWorld := ⟨{}⟩

#dyn_world GnWorld

/-- The primitives, in the monad `m`, over the values `V`.  No primitive takes or gives a
cell.  `m` lands in `Type 1`, as a monad of computations generic in the requests does. -/
public class Prims (m : Type → Type 1) (V : Type) where
  /-- `x + 1`. -/
  bump : V → m V
  /-- Write `x` down. -/
  note : V → m Unit
  /-- Fail with `x` if it is negative. -/
  check : V → m Unit

/-- `x + 2`, by two bumps, writing down the value between them, after checking `x`: the
protocol, written once. -/
@[expose] public def twiceBump {m : Type → Type 1} {V : Type} [Monad m] [Prims m V] (x : V) :
    m V := do
  Prims.check x
  let y ← Prims.bump x
  Prims.note y
  Prims.bump y

/-- `Gn`'s capabilities. -/
@[dyn_lang] public class Lang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  notes : HasPart ε.W Notes
  heap : HasHeap σ ε
  tagInt : TagOf σ Int

section
variable {σ : Type} [Store σ] [Decode σ]

/-- What a computation is, before its proof: from two continuations, one for a result and one for
an error, a tree, as the Python semantics' `PyFn` is. -/
public abbrev GFn (σ : Type) [Store σ] [Decode σ] (α : Type) : Type 1 :=
  ∀ {ε : Eff} {E : Type} [Lang σ ε] {β : Type}, (α → Sem ε E β) → (Int → Sem ε E β) → Sem ε E β

/-- A statement about a computation, at the machine's boundary: it names a ref's location and
the machine's heap capability, as a locality statement does.  (It holds of every computation.) -/
@[expose] public def Good {α : Type} (_f : GFn σ α) : Prop :=
  ∀ (I : Ty → Type) (r : Ref σ Int) (t : @TagOf σ _ ⟨I⟩ Int), r.loc = r.loc ∧
    (@HasHeap.mreq σ _ I Unit []).getReq t r = (@HasHeap.mreq σ _ I Unit []).getReq t r

/-- Every computation satisfies `Good`: for every ref, its location equals itself, and so does the
heap capability's read request of it, both by reflexivity. -/
public theorem good {α : Type} (f : GFn σ α) : Good f :=
  fun _ _ _ => ⟨rfl, rfl⟩

/-- The machine's monad: a computation with the proof that it is `Good`. -/
public abbrev GM (σ : Type) [Store σ] [Decode σ] (α : Type) : Type 1 := { f : GFn σ α // Good f }

public instance : Monad (GM σ) where
  pure a := ⟨fun {_ _ _ _} ok _ => ok a, good _⟩
  bind x k := ⟨fun {_ _ _ _} ok err => x.1 (fun a => (k a).1 ok err) err, good _⟩

/-- The machine's primitives: `bump` puts `x` in a new cell, adds one to it, and reads it, and
`note` appends to the world's notes in place. -/
public instance : Prims (GM σ) Int where
  bump x := ⟨fun {_ _ _ _} ok _ => do
    let r : Ref σ Int ← newRef x
    let v ← readRef r
    writeRef r (v + 1)
    ok (← readRef r), good _⟩
  note x := ⟨fun {_ _ _ _} ok _ => do modifyThe Notes fun n => ⟨n.items.push x⟩; ok (), good _⟩
  check x := ⟨fun {_ _ _ _} ok err => if x < 0 then err x else ok (), good _⟩

/-- `gn.twice` runs the protocol at the machine's primitives, with `pure` for a result and a
jump along `neg` for an error. -/
@[dyn_sem Gn.twice, expose]
public def twice {ε : Eff} {E : Type} [Lang σ ε] (x : Int) (neg : Target E [Int]) :
    Sem ε E Int :=
  (twiceBump (m := GM σ) x).1 pure (jump neg)
end

public section
#guard_msgs in
#dyn_sem_table GnSem for Gn (world := GnWorld)
end

section
abbrev H := Gn.env
def hd (n : Nat) (t : TypeExpr H) : ValDecl H := ⟨⟨n⟩, t⟩
def nm (s : String) : Name := .str .base s

/-- `main(x)`: `gn.twice x`, or `e` if it fails with `e`. -/
def main : Func H Unit :=
  let f : Func H Unit := {
    name := nm "main"
    params := #[hd 0 Base.Int]
    retType := Base.Int
    blocks := #[
      ⟨⟨nm "entry"⟩, #[hd 0 Base.Int], #[
        .apply () (hd 1 Base.Int) Gn.twice.ref ⟨#[], rfl⟩ #[⟨0⟩] #[⟨⟨nm "neg"⟩, #[]⟩] #[]],
        .ret () ⟨1⟩, ()⟩,
      ⟨⟨nm "neg"⟩, #[hd 2 Base.Int], #[], .ret () ⟨2⟩, ()⟩]
    names := #[]
    info := () }
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- `main x`'s result and the notes. -/
def runMain (x : Int) : Option (Option Int × Array Int) :=
  match Module.Raw.check { name := nm "gn", funcs := #[main], info := () } with
  | .ok m =>
    let o := runModule GnSem.model m (nm "main") #[GnSem.model.arg x] 100
    some (o.read? Int, o.snapshot.world.notes.items)
  | .error _ => none
end

-- The result path: `5 + 2`, with `6` written down.
#guard runMain 5 = some (some 7, #[6])

-- The error path: `check` fails with `-3`, before anything is written down.
#guard runMain (-3) = some (some (-3), #[])

/-! ## A second instance, in a plain state monad -/

/-- A state monad over the notes, in `Type 1`. -/
structure Plain (α : Type) : Type 1 where
  run : Array Int → α × Array Int

instance : Monad Plain where
  pure a := ⟨fun s => (a, s)⟩
  bind x k := ⟨fun s => let (a, s₁) := x.run s; (k a).run s₁⟩

/-- The second instance's primitives: `bump` adds one, `note` appends to the state, and `check`
accepts every number. -/
instance : Prims Plain Int where
  bump x := ⟨fun s => (x + 1, s)⟩
  note x := ⟨fun s => ((), s.push x)⟩
  check _ := ⟨fun s => ((), s)⟩

#guard (twiceBump (m := Plain) (5 : Int)).run #[] = (7, #[6])

end Strata.Dyn.ExecTest.Generic
