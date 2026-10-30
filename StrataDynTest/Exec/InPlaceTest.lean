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
# World updates in place

`modifyThe` and `modifyGetThe` go through the part instance's `modifyGet`, which `#dyn_world`
defines in place: the part has one reference when `f` runs, so an array in it grows without a
copy.  That holds for a rule that Lean specializes to the table's world, and also for a rule
that keeps its computation in a record and gets the part's instance only when it runs, through
a language's class or not, as the Python semantics' rules will.  A hand-written instance without
its own `modifyGet` reads the part while the world still holds it, so a rule that isn't
specialized to the world copies the part.
Each update below runs `dbgTraceIfShared`, which prints `shared RC copied` when the array that
`logged` grows is shared.  `logged` skips the check for an empty array, so the first update of
each run never prints.
-/

namespace Strata.Dyn.ExecTest.InPlace

open Strata.Dyn Strata.Dyn.Exec

/-- Two ways to log a number. -/
public environment Ip extends Base where
  namespace ip
  open base
  insn logThe (x : Int) : Unit
  insn logGet (x : Int) : Int
  insn recThe (x : Int) : Unit
  insn recGet (x : Int) : Int
  insn langThe (x : Int) : Unit
  end ip

#dyn_types Ip

/-- What the run logged. -/
public structure Log where
  items : Array Int := #[]

/-- A parent environment's world, which `Ip`'s world holds. -/
public structure Inner where
  log : Log := {}
  count : Int := 0

/-- `Ip`'s world.  The log is a part of a part, which `#dyn_world`'s `modifyGet` also updates in
place. -/
public structure IpWorld where
  inner : Inner := {}
  steps : Nat := 0

public instance : Inhabited Inner := ⟨{}⟩
public instance : Inhabited IpWorld := ⟨{}⟩

#dyn_world Inner

#dyn_world IpWorld

/-- `l` with `x` appended, reporting a copy of a non-empty array. -/
@[expose] public def logged (l : Log) (x : Int) : Log :=
  ⟨(if l.items.isEmpty then l.items else dbgTraceIfShared "copied" l.items).push x⟩

/-- Log `x`, specialized to the table's world. -/
@[dyn_sem Ip.logThe, expose]
public def logThe {ε : Eff} {E : Type} [HasPart ε.W Log] (x : Int) : Sem ε E Unit :=
  modifyThe Log (logged · x)

/-- Log `x`, and give the log's size before it. -/
@[dyn_sem Ip.logGet, expose]
public def logGet {ε : Eff} {E : Type} [HasPart ε.W Log] (x : Int) : Sem ε E Int :=
  modifyGetThe Log fun l => ((l.items.size : Int), logged l x)

/-- Computations kept in a record, which get their part's instance only when they run. -/
public structure Prim where
  logThe : ∀ {ε : Eff} {E : Type} [HasPart ε.W Log], Int → Sem ε E Unit
  logGet : ∀ {ε : Eff} {E : Type} [HasPart ε.W Log], Int → Sem ε E Int

/-- The record's computations.  Lean doesn't inline it into the rules, so the rules can't be
specialized to the world. -/
@[noinline, expose] public def prim : Prim :=
  ⟨fun x => modifyThe Log (logged · x), fun x => modifyGetThe Log fun l => ((l.items.size : Int), logged l x)⟩

/-- Log `x` with `prim.logThe`. -/
@[dyn_sem Ip.recThe, expose]
public def recThe {ε : Eff} {E : Type} [HasPart ε.W Log] (x : Int) : Sem ε E Unit :=
  prim.logThe x

/-- Log `x` with `prim.logGet`. -/
@[dyn_sem Ip.recGet, expose]
public def recGet {ε : Eff} {E : Type} [HasPart ε.W Log] (x : Int) : Sem ε E Int :=
  prim.logGet x

/-- A language whose class holds the log part, as the Python semantics' class will hold its
parts. -/
@[dyn_lang] public class IpLang (ε : Eff) where
  log : HasPart ε.W Log

/-- A computation kept in a record, over the language's class. -/
public structure LangPrim where
  logThe : ∀ {ε : Eff} {E : Type} [IpLang ε], Int → Sem ε E Unit

/-- The record's computation. -/
@[noinline, expose] public def langPrim : LangPrim := ⟨fun x => modifyThe Log (logged · x)⟩

/-- Log `x` with `langPrim.logThe`, through the language's class. -/
@[dyn_sem Ip.langThe, expose]
public def langThe {ε : Eff} {E : Type} [IpLang ε] (x : Int) : Sem ε E Unit :=
  langPrim.logThe x

public section
#guard_msgs in
#dyn_sem_table IpSem for Ip (world := IpWorld)
end

section
abbrev H := Ip.env
def hd (n : Nat) (t : TypeExpr H) : ValDecl H := ⟨⟨n⟩, t⟩

/-- A function named `n` that returns `r`, with the blocks `bs`; its parameters are its entry
block's. -/
def mkF (n : Name) (r : TypeExpr H) (bs : Array (Block H Unit)) : Func H Unit :=
  { name := n, params := (bs[0]?.map (·.params)).getD #[], retType := r, blocks := bs,
    names := #[], info := () }
def nm (s : String) : Name := .str .base s

/-- The instructions that log. -/
inductive How where
  | logThe | logGet | recThe | recGet | langThe

/-- Log value `arg` into `res` with the instruction `o`. -/
def logIt (o : How) (res arg : Nat) : Instruction H Unit :=
  match o with
  | .logThe => .apply () (hd res Base.Unit) Ip.logThe.ref ⟨#[], rfl⟩ #[⟨arg⟩] #[] #[]
  | .logGet => .apply () (hd res Base.Int) Ip.logGet.ref ⟨#[], rfl⟩ #[⟨arg⟩] #[] #[]
  | .recThe => .apply () (hd res Base.Unit) Ip.recThe.ref ⟨#[], rfl⟩ #[⟨arg⟩] #[] #[]
  | .recGet => .apply () (hd res Base.Int) Ip.recGet.ref ⟨#[], rfl⟩ #[⟨arg⟩] #[] #[]
  | .langThe => .apply () (hd res Base.Unit) Ip.langThe.ref ⟨#[], rfl⟩ #[⟨arg⟩] #[] #[]

/-- A function that logs `1`, `2`, `3` and `4`, and returns `0`. -/
def logFour (o : How) : Func H Unit :=
  let f : Func H Unit := mkF (nm "four") Base.Int #[
    ⟨⟨nm "entry"⟩, #[], #[
      .const () (hd 0 Base.Int) (.int 1), logIt o 1 0,
      .const () (hd 2 Base.Int) (.int 2), logIt o 3 2,
      .const () (hd 4 Base.Int) (.int 3), logIt o 5 4,
      .const () (hd 6 Base.Int) (.int 4), logIt o 7 6,
      .const () (hd 8 Base.Int) (.int 0)],
      .ret () ⟨8⟩, ()⟩]
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- A function that logs `1`, `2`, `3` and `4` with the instruction `o`, which gives the log's
size before each update, and returns the last size. -/
def sizeFour (o : How) : Func H Unit :=
  let f : Func H Unit := mkF (nm "four") Base.Int #[
    ⟨⟨nm "entry"⟩, #[], #[
      .const () (hd 0 Base.Int) (.int 1), logIt o 1 0,
      .const () (hd 2 Base.Int) (.int 2), logIt o 3 2,
      .const () (hd 4 Base.Int) (.int 3), logIt o 5 4,
      .const () (hd 6 Base.Int) (.int 4), logIt o 7 6],
      .ret () ⟨7⟩, ()⟩]
  { f with names := (Array.range (ValDecl.idBound f.defs)).map (.num (.str .base "v")) }

/-- What `sizeFour o` returns -/
def lastSize (o : How) : Option (Option Int) :=
  match Module.Raw.check { name := nm "ip", funcs := #[sizeFour o], info := () } with
  | .ok m => some ((runModule IpSem.model m (nm "four") #[] 1000).read? Int)
  | .error _ => none

/-- What `logFour o` logs -/
def logs (o : How) : Option (Array Int) :=
  match Module.Raw.check { name := nm "ip", funcs := #[logFour o], info := () } with
  | .ok m =>
    some (runModule IpSem.model m (nm "four") #[] 1000).snapshot.world.inner.log.items
  | .error _ => none
end

-- Specialized to the world, `modifyThe` and `modifyGetThe` update in place.
/-- info: (some #[1, 2, 3, 4]) -/
#guard_msgs in
#eval IO.println (logs .logThe)

/-- info: (some #[1, 2, 3, 4]) -/
#guard_msgs in
#eval IO.println (logs .logGet)

-- `modifyGetThe` gives `f`'s result: the size before the fourth update is 3.
#guard lastSize .logGet = some (some 3)

-- From a record, they update in place too, and so they do through a language's class.
/-- info: (some #[1, 2, 3, 4]) -/
#guard_msgs in
#eval IO.println (logs .recThe)

/-- info: (some #[1, 2, 3, 4]) -/
#guard_msgs in
#eval IO.println (logs .recGet)

/-- info: (some #[1, 2, 3, 4]) -/
#guard_msgs in
#eval IO.println (logs .langThe)

#guard lastSize .recGet = some (some 3)

/-- A world whose log part is written by hand, without its own `modifyGet`. -/
public structure BareWorld where
  log : Log := {}
  steps : Nat := 0

public instance : Inhabited BareWorld := ⟨{}⟩

public instance : HasPart BareWorld Log :=
  { get := (·.log), set := fun w l => { w with log := l } }

public section
#guard_msgs in
#dyn_sem_table IpBareSem for Ip (world := BareWorld)
end

/-- What `logFour o` logs, over `BareWorld`. -/
def bareLogs (o : How) : Option (Array Int) :=
  match Module.Raw.check { name := nm "ip", funcs := #[logFour o], info := () } with
  | .ok m =>
    some (runModule IpBareSem.model m (nm "four") #[] 1000).snapshot.world.log.items
  | .error _ => none

-- In a run too, the default `modifyGet` copies the part in a rule from a record.
/--
info: shared RC copied
shared RC copied
shared RC copied
(some #[1, 2, 3, 4])
-/
#guard_msgs in
#eval IO.println (bareLogs .recThe)

/-! A caller that Lean does not specialize reaches the part through the instance, at run time.
`#dyn_world`'s `modifyGet` updates the part in place, for a field and for a field of a field,
but the default `modifyGet` of a hand-written instance copies it. -/

/-- A world with a hand-written part.  It has two fields: Lean stores a structure with one
field as that field, so there the default `modifyGet` would be in place too. -/
structure Bare where
  log : Log := {}
  steps : Nat := 0

instance : HasPart Bare Log := { get := (·.log), set := fun w l => { w with log := l } }

/-- Log `1` to `4` through `h`, unspecialized. -/
@[noinline, nospecialize] def logThrough {W : Type} (h : HasPart W Log) (w : W) : W := Id.run do
  let mut w := w
  for i in [1:5] do w := (h.modifyGet (fun l => ((), logged l i)) w).2
  return w

/-- info: #[1, 2, 3, 4] -/
#guard_msgs in
#eval IO.println (logThrough inferInstance ({} : IpWorld)).inner.log.items

/-- info: #[1, 2, 3, 4] -/
#guard_msgs in
#eval IO.println (logThrough inferInstance ({} : Inner)).log.items

/--
info: shared RC copied
shared RC copied
shared RC copied
#[1, 2, 3, 4]
-/
#guard_msgs in
#eval IO.println (logThrough inferInstance ({} : Bare)).log.items

end Strata.Dyn.ExecTest.InPlace
