/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
public import StrataDyn.Exec.Base
public import StrataDyn.Exec.World
public import StrataDyn.Examples.While.Env
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# Worlds

`#dyn_world W` gives each field of the structure `W` its part instance, the part's laws, and,
for each ordered pair of parts, the theorem that writing the first leaves the second as it is.  A
table doesn't require the laws: a world whose parts have none still makes a table.
-/

namespace Strata.Dyn.ExecTest.WorldTest

open Strata.Dyn.Exec

/-- A count. -/
structure Count where
  n : Nat := 0
  deriving Inhabited, Repr, DecidableEq

/-- A log. -/
structure Log where
  items : Array String := #[]
  deriving Inhabited, Repr, DecidableEq

/-- A world with two parts. -/
structure Plain where
  count : Count := {}
  log : Log := {}
  deriving Inhabited, Repr, DecidableEq

#guard_msgs in
#dyn_world Plain

example : LawfulHasPart Plain Count := inferInstance
example : LawfulHasPart Plain Log := inferInstance
example : HasPart.Indep Plain Count Log := Plain.indep_count_log
example : HasPart.Indep Plain Log Count := Plain.indep_log_count

-- Reading after writing gives what was written, and the other part stays as it was.
#guard (HasPart.get (HasPart.set ({ log := ⟨#["a"]⟩ } : Plain) (⟨3⟩ : Count)) : Count) == ⟨3⟩
#guard (HasPart.get (HasPart.set ({ log := ⟨#["a"]⟩ } : Plain) (⟨3⟩ : Count)) : Log) == ⟨#["a"]⟩

/-- A part that holds refs, at each token. -/
structure Globals (σ : Type) [Store σ] where
  cells : Array (Ref σ Int) := #[]

/-- A world that holds refs, at each token. -/
structure Held (σ : Type) [Store σ] where
  globals : Globals σ := {}
  count : Count := {}

#guard_msgs in
#dyn_world Held

example {σ : Type} [Store σ] : LawfulHasPart (Held σ) (Globals σ) := inferInstance
example {σ : Type} [Store σ] : HasPart.Indep (Held σ) (Globals σ) Count := Held.indep_globals_count

/-- A child's world, holding its parent's as a field. -/
structure Child where
  parent : Plain := {}
  flag : Bool := false
  deriving Inhabited

#guard_msgs in
#dyn_world Child

-- The parent's parts are the child's too, through the field.
example : LawfulHasPart Child Count := inferInstance
example : LawfulHasPart Child Log := inferInstance
example : HasPart.Indep Child Count Bool := Child.indep_parent_count_flag
#guard (HasPart.get (HasPart.set ({} : Child) (⟨5⟩ : Count)) : Count) == ⟨5⟩
#guard ((HasPart.set ({} : Child) (⟨5⟩ : Count)).parent.log) == {}

/-- A world that extends a structure that is not a world: that structure is one part. -/
structure ExtCount extends Count where
  log : Log := {}

#guard_msgs in
#dyn_world ExtCount

example : LawfulHasPart ExtCount Count := inferInstance
example : HasPart.Indep ExtCount Count Log := ExtCount.indep_toCount_log
#guard (HasPart.get (HasPart.set ({} : ExtCount) (⟨4⟩ : Count)) : Count) == ⟨4⟩

/-- A world that extends a world: the parent's parts are its parts. -/
structure ExtPlain extends Plain where
  flag : Bool := false

#guard_msgs in
#dyn_world ExtPlain

example : LawfulHasPart ExtPlain Count := inferInstance
example : LawfulHasPart ExtPlain Log := inferInstance
#guard (HasPart.get (HasPart.set ({} : ExtPlain) (⟨6⟩ : Count)) : Count) == ⟨6⟩

/-- A child of a world that takes the token. -/
structure HeldChild (σ : Type) [Store σ] where
  parent : Held σ := {}
  flag : Bool := false

#guard_msgs in
#dyn_world HeldChild

example {σ : Type} [Store σ] : LawfulHasPart (HeldChild σ) (Globals σ) := inferInstance
example {σ : Type} [Store σ] : LawfulHasPart (HeldChild σ) Count := inferInstance

/-- A child of a world from another module, While's. -/
structure WhileChild where
  parent : WhileRules.World := {}
  count : Count := {}

#guard_msgs in
#dyn_world WhileChild

example : LawfulHasPart WhileChild WhileRules.Output := inferInstance
example : HasPart.Indep WhileChild WhileRules.Ticks Count := WhileChild.indep_parent_ticks_count

/-- Two fields of one type: a rule could not tell them apart. -/
structure Twice where
  a : Count := {}
  b : Count := {}

/-- error: #dyn_world Twice: the fields a and b both have type Count, but a rule names a part by its type -/
#guard_msgs in
#dyn_world Twice

/-- error: #dyn_world Nat: Nat is not a structure -/
#guard_msgs in
#dyn_world Nat

/-! A table takes a world whose parts have laws, and one whose parts have none. -/

/-- An instruction that reads a part. -/
environment Wt extends Base where
  namespace wt
  open base
  insn count : Int
  end wt

#dyn_types Wt

/-- The count. -/
@[dyn_sem Wt.count] def count {ε : Eff} {E : Type} [HasPart ε.W Count] : Sem ε E Int := do
  return ((← getThe Count).n : Int)

#guard_msgs in
#dyn_sem_table PlainSem for Wt (world := Plain)

-- The parent's rules run on the child's world.
#guard_msgs in
#dyn_sem_table ChildSem for Wt (world := Child)

/-- A world whose part has no laws. -/
structure Lawless where
  count : Count := {}
  deriving Inhabited

/-- A part instance written by hand, without its laws. -/
instance : HasPart Lawless Count := ⟨(·.count), fun _ c => { count := c }⟩

#guard_msgs in
#dyn_sem_table LawlessSem for Wt (world := Lawless)

/-! A language's class names its parts too, with or without their laws. -/

/-- A language whose class names the count part. -/
@[dyn_lang] class CountLang (ε : Eff) where
  count : HasPart ε.W Count

/-- An instruction for it. -/
environment Wb extends Base where
  namespace wb
  open base
  insn count : Int
  end wb

#dyn_types Wb

section
variable {ε : Eff} {E : Type} [CountLang ε]
/-- The count, through the language's class. -/
@[dyn_sem Wb.count] def countB : Sem ε E Int := do
  return ((← getThe Count).n : Int)
end

#guard_msgs in
#dyn_sem_table PlainBSem for Wb (world := Plain)

#guard_msgs in
#dyn_sem_table LawlessBSem for Wb (world := Lawless)

/-- A world with a universe parameter. -/
structure Lifted.{u} where
  count : Count := {}
  extra : PUnit.{u+1} := ⟨⟩

/-- error: #dyn_world Lifted: Lifted takes a universe parameter -/
#guard_msgs in
#dyn_world Lifted

/-- A world with an implicit parameter. -/
structure Hidden {α : Type} where
  count : Count := {}
  x : Option α := none

/-- error: #dyn_world Hidden: its parameter α is implicit -/
#guard_msgs in
#dyn_world Hidden

/-- A world with a field whose type depends on another field. -/
structure Dependent where
  n : Nat := 0
  v : Fin (n + 1) := 0

/-- error: #dyn_world Dependent: the type of field v depends on another field -/
#guard_msgs in
#dyn_world Dependent

/-- Parts whose names, joined by `_`, give one theorem name twice: `indep_a_b_c`. -/
structure Clash where
  a_b : Count := {}
  c : Log := {}
  a : Nat := 0
  b_c : Bool := false

/-- error: #dyn_world Clash: parts a_b and c and parts a and b_c would both declare Strata.Dyn.ExecTest.WorldTest.Clash.indep_a_b_c; rename a field -/
#guard_msgs in
#dyn_world Clash

/-- A field whose name holds a space still names its declarations. -/
structure Spaced where
  «my count» : Count := {}
  log : Log := {}

#guard_msgs in
#dyn_world Spaced

example : HasPart.Indep Spaced Count Log := Spaced.«indep_my count_log»

end Strata.Dyn.ExecTest.WorldTest

/-! The declarations go into the world's namespace, whatever namespace the command runs in. -/

namespace Strata.Dyn.ExecTest.WorldTest.Foo
/-- A world in namespace `Foo`. -/
structure Wld where
  count : Count := {}
  log : Log := {}
end Strata.Dyn.ExecTest.WorldTest.Foo

namespace Strata.Dyn.ExecTest.WorldTest.Bar
open Strata.Dyn.Exec
open Strata.Dyn.ExecTest.WorldTest.Foo in
#dyn_world Wld
end Strata.Dyn.ExecTest.WorldTest.Bar

example : Strata.Dyn.Exec.HasPart.Indep Strata.Dyn.ExecTest.WorldTest.Foo.Wld
    Strata.Dyn.ExecTest.WorldTest.Count Strata.Dyn.ExecTest.WorldTest.Log :=
  Strata.Dyn.ExecTest.WorldTest.Foo.Wld.indep_count_log
