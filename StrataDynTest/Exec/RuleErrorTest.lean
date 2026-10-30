/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.Demo
public import StrataDyn.Base
public import StrataDyn.Exec.Base
import StrataDyn.Env.WF
import StrataDyn.DSL

set_option autoImplicit false

/-!
# Registration errors

Each check `@[dyn_type]` and `@[dyn_sem]` make, with the error it reports, and the one
warning.  `Err` extends `Demo`, whose types have rules, with types and instructions that have
none.
-/

namespace Strata.Dyn.ExecTest.Errors

-- `Exec.Target` and `Exec.Region` are written in full: in this namespace, `Target` and `Region`
-- are the typed builder's and the IR's.
open Strata.Dyn.Exec

/-- Declarations without rules. -/
environment Err extends Demo where
  namespace err
  open demo
  type Str
  type Pair (+a) (+b)
  data Opt (+a) where
    | nothing
    | just (val : a)
  data Two where
    | one (x : Int)
    | two (x y : Int)
  data Color where
    | red
    | green
  mutual
    data Even where
      | zero
      | succE (pred : Odd)
    data Odd where
      | succO (pred : Even)
  end
  insn inc (x : Int) : Int
  insn isZero (x : Int) : Bool
  insn len (s : Str) : Int
  insn split (x : Int) (^neg) (^big (q r : Int)) : Int
  insn first [a] (xs : Seq a) (^empty) : a
  insn count (*xs : Int) : Int
  insn stop (x : Int) : Int
  insn veiled (x : Int) : Int
  terminal insn halt (x : Int) (^done)
  type Count
  insn twice (&body (i : Int) : Int) : Int
  insn drain (x : Int) (*xs : Int) (^neg) : Int
  end err

/-! ## Keys -/

/-- error: unknown Dyn type or instruction `Err.nope` -/
#guard_msgs in
@[dyn_sem Err.nope] def nope (a : Int) : Int := a

/-- error: `Err.Str` is a type, not an instruction -/
#guard_msgs in
@[dyn_sem Err.Str] def str (a : Int) : Int := a

/-- error: `Err.inc` is an instruction, not a type -/
#guard_msgs in
attribute [dyn_type Err.inc] Int

/-- error: demo.add already has the rule Rules.add -/
#guard_msgs in
@[dyn_sem Demo.add] def add2 (a b : Int) : Int := a + b

/-- error: demo.Int already has the type rule Int -/
#guard_msgs in
attribute [dyn_type Demo.Int] Nat

/-! ## `@[dyn_type]` -/

/--
error: the type rule for err.Pair must be a Type →
  Type → Type, or one at every token, (σ : Type) → [inst : Store σ] → Type → Type → Type, but Option : Type u → Type u
-/
#guard_msgs in
attribute [dyn_type Err.Pair] Option

/--
error: the type rule for err.Str must be a Type, or one at every token, (σ : Type) →
  [inst : Store σ] → Type, but List : Type u → Type u
-/
#guard_msgs in
attribute [dyn_type Err.Str] List

/-! A datatype may take a hand-written rule, as the base's `Unit` and `Except` do, if its
constructors match. -/

/-- A type that is not an inductive. -/
def NotInd (_ : Type) : Type := Nat → Nat

/-- error: NotInd does not unfold to an inductive type -/
#guard_msgs in
attribute [dyn_type Err.Opt] NotInd

/-- An inductive with its parameter under another type. -/
def ListOpt (α : Type) : Type := Option (List α)

/-- error: ListOpt must unfold to an inductive whose parameters are err.Opt's (a), in order, with no indices -/
#guard_msgs in
attribute [dyn_type Err.Opt] ListOpt

/-- A constructor named differently. -/
inductive TwoWrongNames where
  | one (x : Int)
  | three (x y : Int)

/-- error: TwoWrongNames has no constructor named two, for err.two -/
#guard_msgs in
attribute [dyn_type Err.Two] TwoWrongNames

/-- One constructor too many. -/
inductive ThreeColors where
  | red
  | green
  | blue

/-- error: err.Color has 2 constructors, but ThreeColors has 3 -/
#guard_msgs in
attribute [dyn_type Err.Color] ThreeColors

/-- A constructor with a field too few. -/
inductive TwoShort where
  | one (x : Int)
  | two (x : Int)

/-- error: TwoShort.two takes 1 field, but err.two declares 2 -/
#guard_msgs in
attribute [dyn_type Err.Two] TwoShort

/-- A constructor with a field of the wrong type. -/
inductive TwoNat where
  | one (x : Nat)
  | two (x y : Int)

/-- error: field x of err.one: TwoNat.one has Nat, but ⟦demo.Int⟧ is Int -/
#guard_msgs in
attribute [dyn_type Err.Two] TwoNat

/-- `Option`, under its own name. -/
inductive Opt (α : Type) where
  | nothing
  | just (val : α)

#guard_msgs in
attribute [dyn_type Err.Opt] Opt

-- A primitive type takes one.
attribute [dyn_type Err.Pair] Prod

-- `#dyn_types` keeps `err.Opt`'s rule, and generates `Two` and `Color`, and `Even` and
-- `Odd` as one mutual group, from `demo.Int`'s rule.
#guard_msgs in
#dyn_types Err

example : Err.Two.Val := .two 1 2
example : Opt Int := .just 1
example : Err.Even.Val := .succE (.succO .zero)

/-- A datatype over a type without a rule. -/
environment Err2 extends Err where
  namespace err2
  open err
  data Named where
    | named (s : Str)
  end err2

/--
error: no type rule for err.Str: register one with @[dyn_type], or run #dyn_types for its environment, before this datatype's
-/
#guard_msgs in
#dyn_types Err2

/-- The same datatype, over a type with a rule. -/
environment Err3 extends Err where
  namespace err3
  type Word
  data Named where
    | named (s : Word)
  end err3

attribute [dyn_type Err3.Word] String

#guard_msgs in
#dyn_types Err3

example : Err3.Named.Val := .named "x"

/-- A datatype that holds a cell. -/
environment Err4 extends Base where
  namespace err4
  open base
  data Box where
    | box (c : Ref Int)
  end err4

/-- A hand-written `err4.Box`. -/
inductive Box where
  | box (c : Int)

/--
error: field c of err4.box may hold a ref or a closure, which a hand-written rule cannot interpret; leave err4.Box to #dyn_types
-/
#guard_msgs in
attribute [dyn_type Err4.Box] Box

-- Its generated Lean type takes the token.
#guard_msgs in
#dyn_types Err4

example {σ : Type} [Store σ] (c : Ref σ Int) : Err4.Box.Val σ := .box c

/-- Calls through code pointers. -/
environment ErrCall extends Base where
  namespace errCall
  open base
  insn callAt (f : Fn [Int] Int) (x : Int) : Int
  insn callBy (f : Fn [Int] Int) (x : Int) : Int
  insn tagAt (x : Int) : Int
  /-- `code` with its first arguments bound to `cells`. -/
  insn spread [(cs : list)] (code : Fn [*cs, Int] Int) (*cells : cs) : Fn [Int] Int
  /-- A closure whose arguments are a list variable's, which no rule may return. -/
  insn spreadOut [(cs : list)] (code : Fn [*cs, Int] Int) : Fn [*cs] Int
  /-- A list variable inside an operand's datatype, which no rule may take. -/
  insn spreadIn [(cs : list)] (x : Sequence (Fn [*cs] Int)) : Int
  end errCall

#dyn_types ErrCall

/-- A child, whose table runs its parent's rules, those that call included. -/
environment ErrCallKid extends ErrCall where
  namespace errCallKid
  data Mark where
    | mark
  end errCallKid

#dyn_types ErrCallKid

/-! ## `@[dyn_sem]` -/

variable {ε : Eff} {E : Type}

/-- error: demo.box is a constructor of demo.Box, derived, and takes no rule -/
#guard_msgs in
@[dyn_sem Demo.Box.box] def box (a : Int) : Int := a

/-- error: demo.Box.case is the case instruction of demo.Box, derived, and takes no rule -/
#guard_msgs in
@[dyn_sem Demo.Box.case] def boxCase (a : Int) : Int := a


/-- error: no type rule for err.Str; register one with @[dyn_type Err.Str] -/
#guard_msgs in
@[dyn_sem Err.len] def len (_s : String) : Int := 0

/-- error: operand x of err.inc: expected Int, but incNat takes Nat -/
#guard_msgs in
@[dyn_sem Err.inc] def incNat (x : Nat) : Int := x

/-- error: err.inc takes 1 operand, but inc2 takes 2 -/
#guard_msgs in
@[dyn_sem Err.inc] def inc2 (x _y : Int) : Int := x

/-- error: the result of incNat' is Nat, but err.inc needs Int or Sem ε E Int -/
#guard_msgs in
@[dyn_sem Err.inc] def incNat' (_x : Int) : Nat := 0

/-- error: the result of incSem is Sem ε E Bool, but err.inc needs Sem ε E Int -/
#guard_msgs in
@[dyn_sem Err.inc] def incSem (_x : Int) : Sem ε E Bool := pure true

/-- error: incFixed must be generic in its requests and exits: incFixed {ε : Eff} {E : Type} … : Sem ε E … -/
#guard_msgs in
@[dyn_sem Err.inc] def incFixed (x : Int) : Sem ε Nat Int := pure x

/-- error: err.split has 2 successors (^neg, ^big), but split1 takes 1 target -/
#guard_msgs in
@[dyn_sem Err.split] def split1 (x : Int) (_neg : Exec.Target E []) : Sem ε E Int := pure x

/-- error: err.split has 2 successors (^neg, ^big), but split3 takes 3 targets -/
#guard_msgs in
@[dyn_sem Err.split]
def split3 (x : Int) (_a _b _c : Exec.Target E []) : Sem ε E Int := pure x

/-- error: target big of err.split: expected Target [Int, Int], got Target [Int] -/
#guard_msgs in
@[dyn_sem Err.split]
def splitBig (x : Int) (_neg : Exec.Target E []) (_big : Exec.Target E [Int]) : Sem ε E Int :=
  pure x

/-- error: target neg of err.split: expected Target [], got Target [Bool] -/
#guard_msgs in
@[dyn_sem Err.split]
def splitNeg (x : Int) (_neg : Exec.Target E [Bool]) (_big : Exec.Target E [Int, Int]) :
    Sem ε E Int := pure x

/-- error: the result of splitPure is Int, but err.split needs Sem ε E Int -/
#guard_msgs in
@[dyn_sem Err.split] def splitPure (x : Int) : Int := x

/-- error: err.first has 1 type parameter (a), but firstMono binds 0 type variables -/
#guard_msgs in
@[dyn_sem Err.first]
def firstMono (xs : Array Int) (empty : Exec.Target E []) : Sem ε E Int :=
  match xs[0]? with
  | some x => pure x
  | none => jump empty ()

/-- error: operand xs of err.first: expected Array α, but firstList takes List α -/
#guard_msgs in
@[dyn_sem Err.first]
def firstList {α : Type} (xs : List α) (empty : Exec.Target E []) : Sem ε E α :=
  match xs with
  | x :: _ => pure x
  | [] => jump empty ()

/-- error: err.isZero has 0 type parameters, but isZeroPoly binds 1 type variable -/
#guard_msgs in
@[dyn_sem Err.isZero] def isZeroPoly {α : Type} (_x : Int) (_y : Option α) : Bool := true

/-- error: variadic xs of err.count: expected Array Int, but countList takes List Int -/
#guard_msgs in
@[dyn_sem Err.count] def countList (xs : List Int) : Int := xs.length

/-- error: the result of haltInt is Sem ε E Int, but err.halt needs Sem ε E Empty -/
#guard_msgs in
@[dyn_sem Err.halt] def haltInt (_x : Int) (done : Exec.Target E []) : Sem ε E Int := jump done ()

/-- error: the result of haltNat is Nat, but err.halt needs Sem ε E Empty -/
#guard_msgs in
@[dyn_sem Err.halt] def haltNat (_x : Int) : Nat := 0

/-! ### Regions, the world and callees -/

/-- error: region body of err.twice: expected Region [Int] Int, got Region [] Int -/
#guard_msgs in
@[dyn_sem Err.twice] def twiceNoArg (body : Exec.Region ε [] Int) : Sem ε E Int := runRegion body ()

/--
error: twiceInh may require only parts of the world, HasPart ε.W P, the machine's cells, HasHeap σ ε, its calls, HasCall σ ε, and tags, TagOf σ α, SigOf σ as r, TagCon σ F, TagCon₂ σ F and TagsOf σ cs, but requires Inhabited
  ε.W
-/
#guard_msgs in
@[dyn_sem Err.twice]
def twiceInh [Inhabited ε.W] (body : Exec.Region ε [Int] Int) : Sem ε E Int := runRegion body 0

@[dyn_sem Err.twice] def twice (body : Exec.Region ε [Int] Int) : Sem ε E Int := do
  let x ← runRegion body 0
  runRegion body x

/--
error: stopExtra takes Nat after its targets, but only its state and its Again may follow them
-/
#guard_msgs in
@[dyn_sem Err.stop] def stopExtra (x : Int) (_n : Nat) : Sem ε E Int := pure x

/-! ### The state and `Again`

A rule that loops takes its state, `Option σ`, and then its operation's `Again E σ`, after its
targets, at a Lean type `σ` of its own. -/

/-- error: the Again of err.drain: expected Again (Int × Array Int), got Again Int -/
#guard_msgs in
@[dyn_sem Err.drain]
def drainMismatch (x : Int) (_xs : Array Int) (_neg : Exec.Target E [])
    (_st : Option (Int × Array Int)) (_again : Again E Int) : Sem ε E Int := pure x

/--
error: drainNoState takes Again (Int × Array Int) without its state: a rule that loops takes (st : Option σ) before its Again
-/
#guard_msgs in
@[dyn_sem Err.drain]
def drainNoState (x : Int) (_xs : Array Int) (_neg : Exec.Target E [])
    (_again : Again E (Int × Array Int)) : Sem ε E Int := pure x

/-- error: drainNoAgain takes its state, Option (Int × Array Int), but no Again after it -/
#guard_msgs in
@[dyn_sem Err.drain]
def drainNoAgain (x : Int) (_xs : Array Int) (_neg : Exec.Target E [])
    (_st : Option (Int × Array Int)) :
    Sem ε E Int := pure x

/--
error: drainSwapped takes its Again before its state: a rule that loops takes (st : Option σ), then its Again
-/
#guard_msgs in
@[dyn_sem Err.drain]
def drainSwapped (x : Int) (_xs : Array Int) (_neg : Exec.Target E [])
    (_again : Again E (Int × Array Int)) (_st : Option (Int × Array Int)) : Sem ε E Int := pure x

/-- error: err.drain has 1 successor (^neg), but drainEarly takes 0 targets -/
#guard_msgs in
@[dyn_sem Err.drain]
def drainEarly (x : Int) (_xs : Array Int) (_st : Option (Int × Array Int))
    (_again : Again E (Int × Array Int)) (_neg : Exec.Target E []) : Sem ε E Int := pure x

/-- error: drainExtra takes Nat after its Again, but nothing may follow it -/
#guard_msgs in
@[dyn_sem Err.drain]
def drainExtra (x : Int) (_xs : Array Int) (_neg : Exec.Target E [])
    (_st : Option (Int × Array Int)) (_again : Again E (Int × Array Int)) (_n : Nat) :
    Sem ε E Int := pure x

/--
error: the state E of drainExits mentions E, but may mention only its token and type variables
-/
#guard_msgs in
@[dyn_sem Err.drain]
def drainExits (x : Int) (_xs : Array Int) (_neg : Exec.Target E []) (_st : Option E)
    (_again : Again E E) : Sem ε E Int := pure x

/-- `x` plus the elements of `xs`, one per run of the rule, or `^neg` at a negative total: its
state is the total so far and the elements left. -/
@[dyn_sem Err.drain]
def drain (x : Int) (xs : Array Int) (neg : Exec.Target E []) (st : Option (Int × Array Int))
    (again : Again E (Int × Array Int)) : Sem ε E Int :=
  let (x, xs) := st.getD (x, xs)
  if x < 0 then jump neg ()
  else match xs.back? with
    | some y => jump again (x + y, xs.pop)
    | none => pure x

/-! ### Calls -/

section
variable {σ : Type} [Store σ] [Decode σ]

-- A pure rule may take a closure, and pass it on; it cannot call it.
#guard_msgs in
@[dyn_sem ErrCall.callAt] def callAtPure (_f : FnRef σ [Int] Int) (x : Int) : Int := x

-- A rule's tags are at Lean types of Dyn types.
/--
error: List Int is the Lean type of no Dyn type: register its type with @[dyn_type]
-/
#guard_msgs in
@[dyn_sem ErrCall.tagAt]
def tagAtList [TagOf σ (List Int)] (x : Int) : Sem ε E Int := pure x

#guard_msgs in
@[dyn_sem ErrCall.tagAt]
def tagAt [TagOf σ (Except Int Int)] (x : Int) : Sem ε E Int := pure x

end

/-! ### A language's capabilities, as one class -/

/-- error: NotLang is not a class -/
#guard_msgs in
@[dyn_lang] structure NotLang where
  n : Nat

/--
error: field n of NatLang is not a capability: parts of the world, HasPart ε.W P, the machine's cells, HasHeap σ ε, its calls, HasCall σ ε, and tags, TagOf σ α, SigOf σ as r, TagCon σ F, TagCon₂ σ F and TagsOf σ cs
-/
#guard_msgs in
@[dyn_lang] class NatLang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  n : Nat

/-- A plain class, not a language's. -/
class Plain (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  call : HasCall σ ε

/-- error: Kid extends Plain, which is not a language's class: declare it with @[dyn_lang] -/
#guard_msgs in
@[dyn_lang] class Kid (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) extends Plain σ ε where
  heap : HasHeap σ ε

-- The language's class of `ErrCall`, and a child's that extends it.
#guard_msgs in
@[dyn_lang] class CallLang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  call : HasCall σ ε
  tagInt : TagOf σ Int

#guard_msgs in
@[dyn_lang] class CellLang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff)
    extends CallLang σ ε where
  heap : HasHeap σ ε

section
variable {σ : Type} [Store σ] [Decode σ]

-- A plain class is not a capability; the language's is.
/--
error: callByPlain may require only parts of the world, HasPart ε.W P, the machine's cells, HasHeap σ ε, its calls, HasCall σ ε, and tags, TagOf σ α, SigOf σ as r, TagCon σ F, TagCon₂ σ F and TagsOf σ cs, but requires Plain
  σ ε
-/
#guard_msgs in
@[dyn_sem ErrCall.callBy]
def callByPlain [Plain σ ε] (_f : FnRef σ [Int] Int) (x : Int) : Sem ε E Int :=
  pure x

-- A rule over a list-kinded type variable binds it as a `List Type`, and takes its elements'
-- tags as `TagsOf`; the spread is a payload.
/--
error: type parameter cs of errCall.spread is a list, so spreadType's cs must be a List Type
-/
#guard_msgs in
@[dyn_sem ErrCall.spread]
def spreadType [CallLang σ ε] {cs : Type} (_code : FnRef σ [cs, Int] Int) (_cells : cs) :
    Sem ε E (FnRef σ [Int] Int) :=
  semanticGap "spreadType"

/--
error: spreadTags takes TagsOf σ [Int], but TagsOf takes a list-kinded type variable
-/
#guard_msgs in
@[dyn_sem ErrCall.spread]
def spreadTags [CallLang σ ε] {cs : List Type} [TagsOf σ [Int]]
    (_code : FnRef σ (cs ++ [Int]) Int) (_cells : Payload cs) : Sem ε E (FnRef σ [Int] Int) :=
  semanticGap "spreadTags"

#guard_msgs in
@[dyn_sem ErrCall.spread]
def spread [CallLang σ ε] {cs : List Type} [TagsOf σ cs] (code : FnRef σ (cs ++ [Int]) Int)
    (cells : Payload cs) : Sem ε E (FnRef σ [Int] Int) :=
  bindAll cs code cells

-- A list variable may not reach a rule's result, nor an operand's datatype.
/--
error: the result of errCall.spreadOut: a list type variable may occur only in the arguments of a closure operand, as a splice, and as the spread
-/
#guard_msgs in
@[dyn_sem ErrCall.spreadOut]
def spreadOut [CallLang σ ε] {cs : List Type} (_code : FnRef σ (cs ++ [Int]) Int) :
    Sem ε E (FnRef σ cs Int) :=
  semanticGap "spreadOut"

/--
error: operand x of errCall.spreadIn: a list type variable may occur only in the arguments of a closure operand, as a splice, and as the spread
-/
#guard_msgs in
@[dyn_sem ErrCall.spreadIn]
def spreadIn {cs : List Type} (_x : Array (FnRef σ cs Int)) : Int := 0

-- A class's fields, its parent's included, are its rules' instances.
#guard_msgs in
@[dyn_sem ErrCall.callBy]
def callByLang [CellLang σ ε] (f : FnRef σ [Int] Int) (x : Int) : Sem ε E Int := do
  let c : Ref σ Int ← newRef x
  callFn f (← readRef c)

end

-- `ErrCall`'s table runs its calling rules, and so does its child's: a rule takes its table's
-- decoding.
/-- info: ErrCallSem: no rule for errCall.spreadOut, errCall.spreadIn -/
#guard_msgs in
#dyn_sem_table ErrCallSem for ErrCall

/-- info: ErrCallKidSem: no rule for errCall.spreadOut, errCall.spreadIn -/
#guard_msgs in
#dyn_sem_table ErrCallKidSem for ErrCallKid

/-! ### Keys -/

#guard_msgs in
@[dyn_sem Err.veiled] def veiled (x : Int) : Sem ε E Int := pure x

-- An instruction's key is its own name, which its emitter shares, not its reference.
/-- error: unknown Dyn type or instruction `Err.veiled.ref` -/
#guard_msgs in
@[dyn_sem Err.veiled.ref] def veiledRef (x : Int) : Sem ε E Int := pure x

/-! ### The machine's and the engine's -/

/-- error: base.refNew is implemented by the machine, and takes no rule -/
#guard_msgs in
@[dyn_sem Base.refNew] def refNew {α : Type} (x : α) : α := x

/-- error: the engine interprets base.Ref as Ref, and it takes no type rule -/
#guard_msgs in
attribute [dyn_type Base.Ref] Option

/-- error: the engine interprets base.Fn as FnRef, and it takes no type rule -/
#guard_msgs in
attribute [dyn_type Base.Fn] Prod

-- A correct rule after the failed ones: the failures registered nothing.
@[dyn_sem Err.inc] def inc (x : Int) : Int := x + 1

/-! ## Mutual groups -/

/-- A mutual group, generated as one `mutual` block, whose table builds. -/
environment Mut where
  namespace mu
  type Int
  mutual
    data A where
      | a (b : B)
      | stop
    data B where
      | b (x : Int) (a : A)
  end
  end mu

attribute [dyn_type Mut.Int] Int

#guard_msgs in
#dyn_types Mut

#guard_msgs in
#dyn_sem_table MutSem for Mut

example : Mut.A.Val := .a (.b 1 .stop)

/-- A rule whose tag names a Lean type of no type of the table it runs in. -/
environment ErrTag extends Base where
  namespace errTag
  open base
  insn tagged (x : Int) : Int
  end errTag

#dyn_types ErrTag

@[dyn_sem ErrTag.tagged]
def tagged {σ : Type} [Store σ] [Decode σ] [TagOf σ Mut.A.Val] (x : Int) : Sem ε E Int := pure x

/--
error: a capability names Mut.A.Val, the Lean type of no type of this table
-/
#guard_msgs in
#dyn_sem_table ErrTagSem for ErrTag


/-! ## Refs

A rule that takes or makes refs is generic in the token, and names refs at Lean types.  Each
rejection is beside its accepted twin. -/

/-- Instructions on refs. -/
environment CellErr extends Base where
  namespace cellErr
  open base
  insn mk (v : Int) : Ref Int
  insn loc (c : Ref Int) : Int
  insn twoTokens (c : Ref Int) : Int
  end cellErr

#dyn_types CellErr

section
variable {ε : Eff} {E : Type}

/--
error: the result of mkBool is Sem ε E (Ref σ Bool), but cellErr.mk needs Sem ε E (Ref σ Int)
-/
#guard_msgs in
@[dyn_sem CellErr.mk]
def mkBool {σ : Type} [Store σ] [Decode σ] [HasHeap σ ε] [TagOf σ Bool] (_v : Int) :
    Sem ε E (Ref σ Bool) := newRef true

#guard_msgs in
@[dyn_sem CellErr.mk]
def mk {σ : Type} [Store σ] [Decode σ] [HasHeap σ ε] [TagOf σ Int] (v : Int) :
    Sem ε E (Ref σ Int) := newRef v

/--
error: base.Ref needs the run token: a rule that takes or makes one must be generic in it, {σ : Type} [Store σ]
-/
#guard_msgs in
@[dyn_sem CellErr.loc] def locAtRun (c : Ref Run Int) : Int := c.loc

#guard_msgs in
@[dyn_sem CellErr.loc] def loc {σ : Type} [Store σ] (c : Ref σ Int) : Int := c.loc

/-- error: locTwo is generic in 2 tokens, but a run has one -/
#guard_msgs in
@[dyn_sem CellErr.twoTokens]
def locTwo {σ τ : Type} [Store σ] [Store τ] (c : Ref σ Int) (_ : Option (Ref τ Int)) :
    Int := c.loc

#guard_msgs in
@[dyn_sem CellErr.twoTokens]
def locOne {σ : Type} [Store σ] (c : Ref σ Int) : Int := c.loc

end

/-- A datatype holding a closure, and one holding a ref of its parameter. -/
environment GoodBox extends Base where
  namespace goodBox
  open base
  data Clo where
    | clo (f : Fn [Int] Int)
  data Box (+a) where
    | box (c : Ref a)
  end goodBox

#guard_msgs in
#dyn_types GoodBox

example (σ : Type) [Store σ] (f : FnRef σ [Int] Int) : GoodBox.Clo.Val σ := .clo f
example (σ : Type) [Store σ] (c : Ref σ Bool) : GoodBox.Box.Val σ Bool := .box c

end Strata.Dyn.ExecTest.Errors
