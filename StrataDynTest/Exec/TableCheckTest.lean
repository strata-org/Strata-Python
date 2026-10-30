/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Base
public import StrataDyn.Exec
public import StrataDyn.Exec.Base
public import StrataDynTest.Exec.RuleHelpers
public import StrataDynTest.Exec.ReqHelpers
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# The table's check, in another module than the helpers

`#dyn_check_rule` judges a rule in its own module's view.  The Python semantics' tables are in
other modules than their helpers, so these tables check rules whose helpers are in
`RuleHelpers`, as a table there would.  Each failing table names its rule.
-/

namespace Strata.Dyn.ExecTest.TableCheck

open Strata.Dyn.Exec

/-- One instruction, with a rule that reaches another module's unexposed helper. -/
environment TcHidden extends Base where
  namespace tcHidden
  open base
  insn f (x : Int) : Int
  end tcHidden

#dyn_types TcHidden

@[dyn_sem TcHidden.f] def hidden (x : Int) : Int := Helpers.hiddenLie x

/-- error: the table HiddenSem: rule hidden for tcHidden.f reaches Helpers.hiddenLie (HiddenSem.ops → HiddenSem.impl.tcHidden.f → HiddenSem.rule.tcHidden.f → hidden → Helpers.hiddenLie), whose definition its module does not expose, so the check cannot see it: mark it @[expose], or, for a derived instance, derive it in an @[expose] section or write it by hand -/
#guard_msgs in
#dyn_sem_table HiddenSem for TcHidden

/-- One instruction, with a rule whose proof is `sorry`. -/
environment TcSorry extends Base where
  namespace tcSorry
  open base
  insn f (x : Int) : Int
  end tcSorry

#dyn_types TcSorry

set_option warn.sorry false in
@[dyn_sem TcSorry.f] def sorried (x : Int) : Int :=
  #[x][0]'(by sorry)

/-- error: the table SorrySem: rule sorried for tcSorry.f reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_sem_table SorrySem for TcSorry

/-- One instruction, with a rule over another module's exposed helper. -/
environment TcShown extends Base where
  namespace tcShown
  open base
  insn f (x : Int) : Int
  end tcShown

#dyn_types TcShown

@[dyn_sem TcShown.f] def shown (x : Int) : Int := Helpers.shownDouble x

#guard_msgs in
#dyn_sem_table ShownSem for TcShown

/-- One instruction, with a rule over another module's helper that was compiled with a local
swap to a function with an unused parameter. -/
environment TcRd extends Base where
  namespace tcRd
  open base
  insn f (x : Int) : Int
  end tcRd

#dyn_types TcRd

@[dyn_sem TcRd.f] def viaRd (x : Int) : Int := Helpers.swappedRd x

/-- error: the table RdSem: rule viaRd for tcRd.f reaches Helpers.myRd (RdSem.ops → RdSem.impl.tcRd.f → RdSem.rule.tcRd.f → viaRd → Helpers.swappedRd → Helpers.pRd → Helpers.myRd), which carries @[implemented_by Helpers.lieRd]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_sem_table RdSem for TcRd

/-- One instruction, with a rule over another module's helper that was compiled with a swap whose
lemma is private there.  The rule inlines the helper, so its own compiled code calls `lieRevB`,
which its definition doesn't reach. -/
environment TcB extends Base where
  namespace tcB
  open base
  insn f (xs : Sequence Int) : Sequence Int
  end tcB

#dyn_types TcB

@[dyn_sem TcB.f] def viaB (xs : Array Int) : Array Int := Helpers.swappedB xs

/-- error: the table BSem: rule viaB for tcB.f reaches viaB (BSem.ops → BSem.impl.tcB.f → BSem.rule.tcB.f → viaB), whose compiled code calls Strata.Dyn.ExecTest.Helpers.lieRevB, which its definition does not reach: it was compiled with a swap that the check cannot see, such as a local @[csimp] lemma -/
#guard_msgs in
#dyn_sem_table BSem for TcB

/-- The same with a private swap to a function with an unused parameter: the rule's compiled code
calls `lieQ._redArg`, which is `lieQ`'s code. -/
environment TcQ extends Base where
  namespace tcQ
  open base
  insn f (x : Int) : Int
  end tcQ

#dyn_types TcQ

@[dyn_sem TcQ.f] def viaQ (x : Int) : Int := Helpers.swappedQ x

/-- error: the table QSem: rule viaQ for tcQ.f reaches viaQ (QSem.ops → QSem.impl.tcQ.f → QSem.rule.tcQ.f → viaQ), whose compiled code calls Strata.Dyn.ExecTest.Helpers.lieQ, which its definition does not reach: it was compiled with a swap that the check cannot see, such as a local @[csimp] lemma -/
#guard_msgs in
#dyn_sem_table QSem for TcQ

/-- `swappedB`, behind a helper with an unused parameter that is too large to inline: the
compiler puts its body into `bigB._redArg`, whose code calls `lieRevB`. -/
def bigB (xs : Array Int) (_n : Nat) : Array Int := Id.run do
  let mut a := xs
  for i in [0:10] do
    a := (Helpers.swappedB a).push (Int.ofNat i) ++ (if a.size > 5 then a else #[1, 2])
  return Helpers.swappedB a

/-- One instruction, with a rule over `bigB`. -/
environment TcBig extends Base where
  namespace tcBig
  open base
  insn f (xs : Sequence Int) : Sequence Int
  end tcBig

#dyn_types TcBig

@[dyn_sem TcBig.f] def viaBig (xs : Array Int) : Array Int := bigB xs 0

/-- error: the table BigSem: rule viaBig for tcBig.f reaches bigB (BigSem.ops → BigSem.impl.tcBig.f → BigSem.rule.tcBig.f → viaBig → bigB), whose compiled code calls Strata.Dyn.ExecTest.Helpers.lieRevB, which its definition does not reach: it was compiled with a swap that the check cannot see, such as a local @[csimp] lemma -/
#guard_msgs in
#dyn_sem_table BigSem for TcBig

/-- `bigB`, and `lieRevB` called openly: a caller that reaches `lieRevB` itself doesn't explain
the call in `bigB`'s body. -/
def openB (xs : Array Int) : Array Int := bigB xs 1 ++ Helpers.lieRevB xs

/-- One instruction, with a rule over `openB` and `bigB`. -/
environment TcOpen extends Base where
  namespace tcOpen
  open base
  insn f (xs : Sequence Int) : Sequence Int
  end tcOpen

#dyn_types TcOpen

@[dyn_sem TcOpen.f] def viaOpen (xs : Array Int) : Array Int := openB xs ++ bigB xs 0

/-- error: the table OpenSem: rule viaOpen for tcOpen.f reaches bigB (OpenSem.ops → OpenSem.impl.tcOpen.f → OpenSem.rule.tcOpen.f → viaOpen → bigB), whose compiled code calls Strata.Dyn.ExecTest.Helpers.lieRevB, which its definition does not reach: it was compiled with a swap that the check cannot see, such as a local @[csimp] lemma -/
#guard_msgs in
#dyn_sem_table OpenSem for TcOpen

/-- A loop rule that reads a world part whose getter runs other code: the walk reaches the part's
instance through the loop's wrapper, and the error names the rule. -/
environment TcLoop extends Base where
  namespace tcLoop
  open base
  insn lp (x : Int) : Int
  end tcLoop

#dyn_types TcLoop

/-- Printed output, as a part of the world. -/
structure Out where
  items : Array Int := #[]

/-- A world holding the output. -/
structure OutWorld where
  out : Out := {}

instance : Inhabited OutWorld := ⟨{}⟩

/-- The code that runs for `outGet`. -/
def outGetImpl (_w : OutWorld) : Out := { items := #[999] }
/-- The output, compiled as `outGetImpl`. -/
@[implemented_by outGetImpl] def outGet (w : OutWorld) : Out := w.out

instance : HasPart OutWorld Out := { get := outGet, set := fun w o => { w with out := o } }

/-- Count `x` down, then give the output's size. -/
@[dyn_sem TcLoop.lp]
def lp {ε : Eff} {E : Type} [HasPart ε.W Out] (x : Int) (st : Option Int) (again : Again E Int) :
    Sem ε E Int := do
  let n := st.getD x
  if n > 0 then jump again (n - 1) else return (← getThe Out).items.size

/-- error: the table LoopSem: rule lp for tcLoop.lp reaches outGet (LoopSem.ops → LoopSem.impl.tcLoop.lp → LoopSem.again.tcLoop.lp → instHasPartOutWorldOut → outGet), which carries @[implemented_by outGetImpl]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_sem_table LoopSem for TcLoop (world := OutWorld)

/-- Two instructions, the second with a rule whose proof is `sorry`: the error names that rule. -/
environment TcTwo extends Base where
  namespace tcTwo
  open base
  insn good (x : Int) : Int
  insn bad (x : Int) : Int
  end tcTwo

#dyn_types TcTwo

@[dyn_sem TcTwo.good] def goodRule (x : Int) : Int := x + 1

set_option warn.sorry false in
@[dyn_sem TcTwo.bad] def badRule (x : Int) : Int := #[x][0]'(by sorry)

/-- error: the table TwoSem: rule badRule for tcTwo.bad reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_sem_table TwoSem for TcTwo

/-! `#dyn_check_rule` names an instruction that has a rule. -/

/-- error: `Base.Int` is a type, not an instruction -/
#guard_msgs in
#dyn_check_rule Base.Int

/-- An instruction without a rule. -/
environment TcNone extends Base where
  namespace tcNone
  open base
  insn f (x : Int) : Int
  end tcNone

/-- error: tcNone.f has no rule -/
#guard_msgs in
#dyn_check_rule TcNone.f

/-! ## Machine requests

A machine request holds locations, so a rule may neither take one apart nor build one: only the
handles that a table passes to a rule do.  A part's instance is chosen at the table, so these are
tables. -/

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type}

/-- An instruction whose rule reads a location through a part that takes a request apart, in
another module. -/
environment TcPeek extends Base where
  namespace tcPeek
  open base
  insn f (x : Int) : Int
  end tcPeek

#dyn_types TcPeek

/-- The location of a cell it made, through a part. -/
@[dyn_sem TcPeek.f] def peek [HasHeap σ ε] [t : TagOf σ Int] [HasPart ε.W (ε.I → Nat)] (x : Int) :
    Sem ε E Int := do
  let c ← newRef (σ := σ) x
  let loc ← getThe (ε.I → Nat)
  return (loc (HasHeap.getReq t c) : Int)

-- The rule alone passes: its part's instance is chosen at the table.
#guard_msgs in
#dyn_check_rule TcPeek.f

/-- error: the table PeekSem: rule peek for tcPeek.f reaches MReq.get (PeekSem.ops → PeekSem.impl.tcPeek.f → PeekSem.rule.tcPeek.f → ReqHelpers.locOfReq → ReqHelpers.locOfReq.match_1 → MReq.get), which builds or takes apart a machine request: a request holds locations, so only the handles that a table passes to a rule may build one, and only the machine reads it -/
#guard_msgs in
#dyn_sem_table PeekSem for TcPeek

/-- An instruction whose rule reads a location through a part of this module. -/
environment TcPeekHere extends Base where
  namespace tcPeekHere
  open base
  insn f (x : Int) : Int
  end tcPeekHere

#dyn_types TcPeekHere

/-- The location that a read request names, as a part defined in this module. -/
instance locHere {W : Type} {I : Ty → Type} {rs : List (List Ty × Ty)} :
    HasPart W (MReq I rs → Option Nat) where
  get _ := fun
    | .get _ l => some l
    | _ => none
  set w _ := w

/-- The location of a cell it made, through a part of this module. -/
@[dyn_sem TcPeekHere.f] def peekHere [HasHeap σ ε] [t : TagOf σ Int] [HasPart ε.W (ε.I → Option Nat)]
    (x : Int) : Sem ε E Int := do
  let c ← newRef (σ := σ) x
  let loc ← getThe (ε.I → Option Nat)
  return ((loc (HasHeap.getReq t c)).getD 0 : Int)

/-- error: the table PeekHereSem: rule peekHere for tcPeekHere.f reaches MReq.get (PeekHereSem.ops → PeekHereSem.impl.tcPeekHere.f → PeekHereSem.rule.tcPeekHere.f → locHere → locHere.match_1 → MReq.get), which builds or takes apart a machine request: a request holds locations, so only the handles that a table passes to a rule may build one, and only the machine reads it -/
#guard_msgs in
#dyn_sem_table PeekHereSem for TcPeekHere

/-- An instruction whose rule asks for a cell that nobody passed, through a part that builds a
request without taking one apart. -/
environment TcForge extends Base where
  namespace tcForge
  open base
  insn f (n : Int) : Int
  end tcForge

#dyn_types TcForge

/-- Reads cell `n`, which nobody passed to it. -/
@[dyn_sem TcForge.f] def forge [t : TagOf σ Int] [HasPart ε.W (Ty → Nat → ε.I)] (n : Int) :
    Sem ε E Int := do
  let mk ← getThe (Ty → Nat → ε.I)
  .vis (mk t.tag n.toNat) fun _ => .ret 0

/-- error: the table ForgeSem: rule forge for tcForge.f reaches MReq.get (ForgeSem.ops → ForgeSem.impl.tcForge.f → ForgeSem.rule.tcForge.f → ReqHelpers.readCell → MReq.get), which builds or takes apart a machine request: a request holds locations, so only the handles that a table passes to a rule may build one, and only the machine reads it -/
#guard_msgs in
#dyn_sem_table ForgeSem for TcForge

/-- A language whose class holds a part that takes a request apart. -/
@[dyn_lang] class PeekLang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  heap : HasHeap σ ε
  tagInt : TagOf σ Int
  loc : HasPart ε.W (ε.I → Nat)

/-- An instruction whose rule reads a location through its language's class. -/
environment TcPeekLang extends Base where
  namespace tcPeekLang
  open base
  insn f (x : Int) : Int
  end tcPeekLang

#dyn_types TcPeekLang

/-- The location of a cell it made, through its language's class. -/
@[dyn_sem TcPeekLang.f] def peekLang [PeekLang σ ε] (x : Int) : Sem ε E Int := do
  let c ← newRef (σ := σ) x
  let loc ← getThe (ε.I → Nat)
  return (loc (HasHeap.getReq (inferInstanceAs (TagOf σ Int)) c) : Int)

/-- error: the table PeekLangSem: rule peekLang for tcPeekLang.f reaches MReq.get (PeekLangSem.ops → PeekLangSem.impl.tcPeekLang.f → PeekLangSem.rule.tcPeekLang.f → ReqHelpers.locOfReq → ReqHelpers.locOfReq.match_1 → MReq.get), which builds or takes apart a machine request: a request holds locations, so only the handles that a table passes to a rule may build one, and only the machine reads it -/
#guard_msgs in
#dyn_sem_table PeekLangSem for TcPeekLang

/-- The twin of `TcPeek`: a part that holds a plain value passes. -/
environment TcPlainPart extends Base where
  namespace tcPlainPart
  open base
  insn f (x : Int) : Int
  end tcPlainPart

#dyn_types TcPlainPart

/-- A counter, as a world's only part. -/
structure Count where
  n : Int := 0
  deriving Inhabited

/-- The counter, as a part. -/
instance : HasPart Count Int := { get := (·.n), set := fun w n => { w with n } }

/-- Adds `x` to the counter, and returns the new count. -/
@[dyn_sem TcPlainPart.f] def bump [HasPart ε.W Int] (x : Int) : Sem ε E Int := do
  modifyThe Int (· + x)
  getThe Int

#guard_msgs in
#dyn_sem_table PlainPartSem for TcPlainPart (world := Count)

/-- An instruction whose rule tells whether a request writes a cell, through `MReq.writesCell`,
which the check trusts. -/
environment TcWrites extends Base where
  namespace tcWrites
  open base
  insn f (x : Int) : Bool
  end tcWrites

#dyn_types TcWrites

/-- Whether a request writes a cell, as a part: one bit, which depends only on the constructor. -/
instance writesPart {W : Type} {I : Ty → Type} {rs : List (List Ty × Ty)} :
    HasPart W (MReq I rs → Bool) where
  get _ := MReq.writesCell
  set w _ := w

/-- Whether a write of `x` to a cell it made writes a cell. -/
@[dyn_sem TcWrites.f] def writes [HasHeap σ ε] [t : TagOf σ Int] [HasPart ε.W (ε.I → Bool)]
    (x : Int) : Sem ε E Bool := do
  let c ← newRef (σ := σ) x
  let wc ← getThe (ε.I → Bool)
  return wc (HasHeap.setReq t c x)

#guard_msgs in
#dyn_sem_table WritesSem for TcWrites

end

/-- One instruction, whose rule uses String functions that run loops of Lean's library over the
string they receive.  This module sees those loops only as axioms; the recheck sees them, and
accepts them, since `endingPartials` lists them (`DynRecheckTest`). -/
environment TcStr extends Base where
  namespace tcStr
  open base
  insn f (x : Int) : Int
  end tcStr

#dyn_types TcStr

/-- `x` read back from its digits, plus its number of characters, plus one if it is a natural
number. -/
@[dyn_sem TcStr.f] def strRule (x : Int) : Int :=
  let s := toString x
  s.toInt?.getD 0 + s.foldl (fun n _ => n + 1) 0 + (s.toNat?.getD 0 : Int) * 0 +
    if s.isNat then 1 else 0

#guard strRule 42 = 45
#guard strRule (-7) = -5

#guard_msgs in
#dyn_sem_table StrSem for TcStr

/-- `Int` under another name, equal to it only once unfolded. -/
def MyInt : Type := Int

/-- Two types whose Lean types are equal once unfolded: they would get two tags, so a rule could
read a cell of one at the other's tag. -/
environment TcAlias extends Base where
  namespace tcAlias
  open base
  type Num
  type Mine
  insn f (x : Num) : Mine
  end tcAlias

attribute [dyn_type TcAlias.Num] Int
attribute [dyn_type TcAlias.Mine] MyInt

#dyn_types TcAlias

@[dyn_sem TcAlias.f] def aliasRule (x : Int) : MyInt := x

/-- error: the type rules Int for base.Int and MyInt for tcAlias.Mine are both the type Int, so one Lean type would get two tags: give them one type rule, or distinct Lean types -/
#guard_msgs in
#dyn_sem_table AliasSem for TcAlias

/-- `Array` under another name. -/
def MySeq : Type → Type := Array

/-- A parametric type equal to `base.Sequence`'s `Array` once unfolded. -/
environment TcSeqAlias extends Base where
  namespace tcSeqAlias
  open base
  type Mine (+a)
  insn f (x : Int) : Int
  end tcSeqAlias

attribute [dyn_type TcSeqAlias.Mine] MySeq

#dyn_types TcSeqAlias

@[dyn_sem TcSeqAlias.f] def seqAliasRule (x : Int) : Int := x

/-- error: the type rules Array for base.Sequence and MySeq for tcSeqAlias.Mine are both the type Array, so one Lean type would get two tags: give them one type rule, or distinct Lean types -/
#guard_msgs in
#dyn_sem_table SeqAliasSem for TcSeqAlias

/-- `Fault` as a Dyn type: a rule given one could stop with it. -/
environment TcFault extends Base where
  namespace tcFault
  open base
  type F
  insn f (x : F) : Int
  end tcFault

attribute [dyn_type TcFault.F] Fault

#dyn_types TcFault

@[dyn_sem TcFault.f] def reraise {ε : Eff} {E : Type} (f : Fault) : Sem ε E Int := .stop (.fault f)

/-- error: the type rule Fault for tcFault.F is the type Fault, whose values may hold a Fault: a rule given one could stop with a fault that only the machine reports -/
#guard_msgs in
#dyn_sem_table FaultSem for TcFault

/-- A structure that holds a `Fault` in a field. -/
structure FaultBox where
  fault : Option Fault

/-- `FaultBox` as a Dyn type. -/
environment TcFaultBox extends Base where
  namespace tcFaultBox
  open base
  type B
  insn f (x : B) : Int
  end tcFaultBox

attribute [dyn_type TcFaultBox.B] FaultBox

#dyn_types TcFaultBox

@[dyn_sem TcFaultBox.f] def reraiseBox {ε : Eff} {E : Type} (b : FaultBox) : Sem ε E Int :=
  match b.fault with
  | some f => .stop (.fault f)
  | none => semanticGap "none"

/-- error: the type rule FaultBox for tcFaultBox.B is the type FaultBox, whose values may hold a Fault: a rule given one could stop with a fault that only the machine reports -/
#guard_msgs in
#dyn_sem_table FaultBoxSem for TcFaultBox

/-- `Fault` under another name. -/
def FaultAlias : Type := Fault
/-- `Fault` under another name, reducible. -/
abbrev FaultAbbrev := Fault
/-- A list of faults under another name. -/
def FaultList : Type := List Fault
/-- A type that holds a type. -/
class HasT where
  T : Type
/-- `HasT`'s type is `Fault`. -/
instance faultT : HasT := ⟨Fault⟩

/-- Structures whose fields hold a `Fault` behind a definition. -/
structure AliasBox where
  fault : FaultAlias
structure AbbrevBox where
  fault : FaultAbbrev
structure ListBox where
  faults : FaultList
structure InstBox where
  fault : @HasT.T faultT

/-- `AliasBox` as a Dyn type. -/
environment TcHiddenAlias extends Base where
  namespace tcHiddenAlias
  open base
  type B
  insn f (b : B) : Int
  end tcHiddenAlias

attribute [dyn_type TcHiddenAlias.B] AliasBox

#dyn_types TcHiddenAlias

@[dyn_sem TcHiddenAlias.f] def reraiseAlias {ε : Eff} {E : Type} (b : AliasBox) : Sem ε E Int :=
  .stop (.fault b.fault)

/-- error: the type rule AliasBox for tcHiddenAlias.B is the type AliasBox, whose values may hold a Fault: a rule given one could stop with a fault that only the machine reports -/
#guard_msgs in
#dyn_sem_table HiddenAliasSem for TcHiddenAlias

/-- `AbbrevBox` as a Dyn type. -/
environment TcHiddenAbbrev extends Base where
  namespace tcHiddenAbbrev
  open base
  type B
  insn f (b : B) : Int
  end tcHiddenAbbrev

attribute [dyn_type TcHiddenAbbrev.B] AbbrevBox

#dyn_types TcHiddenAbbrev

@[dyn_sem TcHiddenAbbrev.f] def reraiseAbbrev {ε : Eff} {E : Type} (b : AbbrevBox) : Sem ε E Int :=
  .stop (.fault b.fault)

/-- error: the type rule AbbrevBox for tcHiddenAbbrev.B is the type AbbrevBox, whose values may hold a Fault: a rule given one could stop with a fault that only the machine reports -/
#guard_msgs in
#dyn_sem_table HiddenAbbrevSem for TcHiddenAbbrev

/-- `ListBox` as a Dyn type. -/
environment TcHiddenList extends Base where
  namespace tcHiddenList
  open base
  type B
  insn f (b : B) : Int
  end tcHiddenList

attribute [dyn_type TcHiddenList.B] ListBox

#dyn_types TcHiddenList

@[dyn_sem TcHiddenList.f] def reraiseList {ε : Eff} {E : Type} (b : ListBox) : Sem ε E Int :=
  match b.faults with
  | f :: _ => .stop (.fault f)
  | [] => semanticGap "none"

/-- error: the type rule ListBox for tcHiddenList.B is the type ListBox, whose values may hold a Fault: a rule given one could stop with a fault that only the machine reports -/
#guard_msgs in
#dyn_sem_table HiddenListSem for TcHiddenList

/-- `InstBox` as a Dyn type. -/
environment TcHiddenInst extends Base where
  namespace tcHiddenInst
  open base
  type B
  insn f (b : B) : Int
  end tcHiddenInst

attribute [dyn_type TcHiddenInst.B] InstBox

#dyn_types TcHiddenInst

@[dyn_sem TcHiddenInst.f] def reraiseInst {ε : Eff} {E : Type} (b : InstBox) : Sem ε E Int :=
  .stop (.fault b.fault)

/-- error: the type rule InstBox for tcHiddenInst.B is the type InstBox, whose values may hold a Fault: a rule given one could stop with a fault that only the machine reports -/
#guard_msgs in
#dyn_sem_table HiddenInstSem for TcHiddenInst

/-- `Array Int` as a type of its own name. -/
def IntSeq : Type := Array Int

/-- A type equal to `base.Sequence Int` once unfolded: equal to `Array` at one parameter. -/
environment TcAppAlias extends Base where
  namespace tcAppAlias
  open base
  type Mine
  insn f (x : Int) : Int
  end tcAppAlias

attribute [dyn_type TcAppAlias.Mine] IntSeq

#dyn_types TcAppAlias

@[dyn_sem TcAppAlias.f] def appAliasRule (x : Int) : Int := x

/-- error: the type rule IntSeq for tcAppAlias.Mine isn't, once unfolded, an inductive, structure or opaque type with no index, a constructor and no axiom but propext, Classical.choice and Quot.sound, applied to exactly its parameters: it could give a Lean type that another tag has, by definition or by proof, so a rule could read a cell at the wrong tag; make it a structure -/
#guard_msgs in
#dyn_sem_table AppAliasSem for TcAppAlias

/-- A ref of `Int` as a type of its own name, which takes the token. -/
def IntRef (σ : Type) [Store σ] : Type := Ref σ Int

/-- A type equal to the engine's `Ref Int` once unfolded. -/
environment TcRefAlias extends Base where
  namespace tcRefAlias
  open base
  type Mine
  insn f (x : Int) : Int
  end tcRefAlias

attribute [dyn_type TcRefAlias.Mine] IntRef

#dyn_types TcRefAlias

@[dyn_sem TcRefAlias.f] def refAliasRule (x : Int) : Int := x

/-- error: the type rule IntRef for tcRefAlias.Mine isn't, once unfolded, an inductive, structure or opaque type with no index, a constructor and no axiom but propext, Classical.choice and Quot.sound, applied to exactly its parameters: it could give a Lean type that another tag has, by definition or by proof, so a rule could read a cell at the wrong tag; make it a structure -/
#guard_msgs in
#dyn_sem_table RefAliasSem for TcRefAlias

/-- `Nat` at every parameter. -/
def Phantom (_α : Type) : Type := Nat

/-- A type whose Lean type ignores its parameter: `phantom int` and `phantom bool` would be one
Lean type with two tags. -/
environment TcPhantom extends Base where
  namespace tcPhantom
  open base
  type Ph (+a)
  insn f (x : Int) : Int
  end tcPhantom

attribute [dyn_type TcPhantom.Ph] Phantom

#dyn_types TcPhantom

@[dyn_sem TcPhantom.f] def phantomRule (x : Int) : Int := x

/-- error: the type rule Phantom for tcPhantom.Ph isn't, once unfolded, an inductive, structure or opaque type with no index, a constructor and no axiom but propext, Classical.choice and Quot.sound, applied to exactly its parameters: it could give a Lean type that another tag has, by definition or by proof, so a rule could read a cell at the wrong tag; make it a structure -/
#guard_msgs in
#dyn_sem_table PhantomSem for TcPhantom

/-- The even numbers, as a subtype: a proof could equate it with another subtype of `Nat`. -/
def Even : Type := {n : Nat // n % 2 = 0}

/-- A type that unfolds to a `Subtype` with a fixed predicate, not to a type of its own. -/
environment TcSubtype extends Base where
  namespace tcSubtype
  open base
  type Ev
  insn f (x : Int) : Int
  end tcSubtype

attribute [dyn_type TcSubtype.Ev] Even

#dyn_types TcSubtype

@[dyn_sem TcSubtype.f] def subtypeRule (x : Int) : Int := x

/-- error: the type rule Even for tcSubtype.Ev isn't, once unfolded, an inductive, structure or opaque type with no index, a constructor and no axiom but propext, Classical.choice and Quot.sound, applied to exactly its parameters: it could give a Lean type that another tag has, by definition or by proof, so a rule could read a cell at the wrong tag; make it a structure -/
#guard_msgs in
#dyn_sem_table SubtypeSem for TcSubtype

/-- A type with no constructor. -/
inductive NoValue : Type

/-- A type with no value, which no cell can hold. -/
environment TcEmpty extends Base where
  namespace tcEmpty
  open base
  type Nothing
  insn f (x : Int) : Int
  end tcEmpty

attribute [dyn_type TcEmpty.Nothing] NoValue

#dyn_types TcEmpty

@[dyn_sem TcEmpty.f] def emptyRule (x : Int) : Int := x

/-- error: the type rule NoValue for tcEmpty.Nothing isn't, once unfolded, an inductive, structure or opaque type with no index, a constructor and no axiom but propext, Classical.choice and Quot.sound, applied to exactly its parameters: it could give a Lean type that another tag has, by definition or by proof, so a rule could read a cell at the wrong tag; make it a structure -/
#guard_msgs in
#dyn_sem_table EmptySem for TcEmpty

/-- `Fin 3`: a type with a term argument, which a theorem could rewrite. -/
def Fin3 : Type := Fin 3

/-- A type that unfolds to a type former applied to a term. -/
environment TcTermArg extends Base where
  namespace tcTermArg
  open base
  type Three
  insn f (x : Int) : Int
  end tcTermArg

attribute [dyn_type TcTermArg.Three] Fin3

#dyn_types TcTermArg

@[dyn_sem TcTermArg.f] def termArgRule (x : Int) : Int := x

/-- error: the type rule Fin3 for tcTermArg.Three isn't, once unfolded, an inductive, structure or opaque type with no index, a constructor and no axiom but propext, Classical.choice and Quot.sound, applied to exactly its parameters: it could give a Lean type that another tag has, by definition or by proof, so a rule could read a cell at the wrong tag; make it a structure -/
#guard_msgs in
#dyn_sem_table TermArgSem for TcTermArg

/-- `Int`, irreducible. -/
@[irreducible] def HiddenInt : Type := Int

/-- A type equal to `Int` only by unfolding an irreducible definition. -/
environment TcIrred extends Base where
  namespace tcIrred
  open base
  type Hid
  insn f (x : Int) : Int
  end tcIrred

attribute [dyn_type TcIrred.Hid] HiddenInt

#dyn_types TcIrred

@[dyn_sem TcIrred.f] def irredRule (x : Int) : Int := x

/-- error: the type rules Int for base.Int and HiddenInt for tcIrred.Hid are both the type Int, so one Lean type would get two tags: give them one type rule, or distinct Lean types -/
#guard_msgs in
#dyn_sem_table IrredSem for TcIrred

/-- A type whose declaration reaches Lean's standard axioms only, through a proof field: it is a
type of its own. -/
structure Checked where
  val : String
  ok : val.length = val.length := by simp

/-- A type rule for `Checked`, accepted. -/
environment TcStdAx extends Base where
  namespace tcStdAx
  open base
  type Ch
  insn f (x : Int) : Int
  end tcStdAx

attribute [dyn_type TcStdAx.Ch] Checked

#dyn_types TcStdAx

@[dyn_sem TcStdAx.f] def stdAxRule (x : Int) : Int := x

#guard_msgs in
#dyn_sem_table StdAxSem for TcStdAx

/-- A type with no definition that proofs see: a type of its own. -/
opaque Opq : Type

/-- An opaque type of ours as a type rule: the tag check accepts it, but the table's code reaches
it, and the check of what a table runs rejects our own opaque constants. -/
environment TcOpaque extends Base where
  namespace tcOpaque
  open base
  type Op
  insn f (x : Int) : Int
  end tcOpaque

attribute [dyn_type TcOpaque.Op] Opq

#dyn_types TcOpaque

@[dyn_sem TcOpaque.f] def opaqueRule (x : Int) : Int := x

/-- error: the table OpaqueSem, through OpaqueSem.ops, reaches Opq (OpaqueSem.ops → OpaqueSem.interp → OpaqueSem.H → Opq), which is opaque: its definition is hidden from proofs -/
#guard_msgs in
#dyn_sem_table OpaqueSem for TcOpaque

/-- `Opq` under another name, for a second Dyn type. -/
def Opq2 : Type := Opq

/-- One opaque type for two Dyn types: one Lean type would get two tags. -/
environment TcOpaqueTwice extends Base where
  namespace tcOpaqueTwice
  open base
  type Op
  type Op2
  insn f (x : Int) : Int
  end tcOpaqueTwice

attribute [dyn_type TcOpaqueTwice.Op] Opq
attribute [dyn_type TcOpaqueTwice.Op2] Opq2

#dyn_types TcOpaqueTwice

@[dyn_sem TcOpaqueTwice.f] def opaqueTwiceRule (x : Int) : Int := x

/-- error: the type rules Opq for tcOpaqueTwice.Op and Opq2 for tcOpaqueTwice.Op2 are both the type Opq, so one Lean type would get two tags: give them one type rule, or distinct Lean types -/
#guard_msgs in
#dyn_sem_table OpaqueTwiceSem for TcOpaqueTwice

/-- An axiom that a type's declaration reaches; a deliberate test input. -/
axiom someNat : Nat

/-- A structure whose field's type reaches `someNat`. -/
structure Axed where
  v : Fin (someNat + 1)

/-- A type rule whose declaration reaches an axiom other than Lean's three. -/
environment TcAxed extends Base where
  namespace tcAxed
  open base
  type Ax
  insn f (x : Int) : Int
  end tcAxed

attribute [dyn_type TcAxed.Ax] Axed

#dyn_types TcAxed

@[dyn_sem TcAxed.f] def axedRule (x : Int) : Int := x

/-- error: the type rule Axed for tcAxed.Ax isn't, once unfolded, an inductive, structure or opaque type with no index, a constructor and no axiom but propext, Classical.choice and Quot.sound, applied to exactly its parameters: it could give a Lean type that another tag has, by definition or by proof, so a rule could read a cell at the wrong tag; make it a structure -/
#guard_msgs in
#dyn_sem_table AxedSem for TcAxed

/-! `MReq.writesCell` depends on a request's constructor alone, so it can't tell a location. -/

section
variable {I : Ty → Type} {rs : List (List Ty × Ty)}
example (s : Fin rs.length) (a : Args I (rs.get s).1) : (MReq.region s a).writesCell = false := rfl
example (sig : List Ty × Ty) (i c : Nat) (a : Payload (sig.1.map I)) :
    (MReq.call (I := I) (rs := rs) sig i c a).writesCell = false := rfl
example (t : Ty) (v : I t) : (MReq.new (rs := rs) t v).writesCell = false := rfl
example (t : Ty) (l : Nat) : (MReq.get (I := I) (rs := rs) t l).writesCell = false := rfl
example (t : Ty) (l : Nat) (v : I t) : (MReq.set (rs := rs) t l v).writesCell = true := rfl
example (t : Ty) (l : Nat) (f : I t → I t) : (MReq.modify (rs := rs) t l f).writesCell = true := rfl
example (t : Ty) (v : I t) (sig : List Ty × Ty) (i c : Nat) :
    (MReq.bind (rs := rs) t v sig i c).writesCell = false := rfl
end

end Strata.Dyn.ExecTest.TableCheck
