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
import StrataDynTest.Exec.RuleHelpers
import StrataDynTest.Exec.ReqHelpers

set_option autoImplicit false

/-!
# Registration errors

Each check `@[dyn_type]` and `@[dyn_sem]` make, and each check that a rule runs as it is written
(`#dyn_check_rule`, and `#dyn_sem_table` for the ones only a table can make), with the error it
reports.  `Err` extends `Demo`, whose types have rules, with types and instructions that have
none.

Many rules here are inputs that the check must reject: they use `sorry`, `native_decide`, the
false axiom `bad : False` or false swap lemmas, and each test checks the rejection.  So `bad` is
in scope for any module that imports this one; no other module does.
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
  insn fast (x : Int) : Int
  insn quick (x : Int) : Int
  insn sly (x : Int) : Int
  insn veiled (x : Int) : Int
  insn spinning (x : Int) : Int
  insn greet (x : Int) : Int
  insn setAt (xs : Seq Int) (i v : Int) : Seq Int
  insn getAt (xs : Seq Int) (i : Int) : Int
  insn sorried (xs : Seq Int) (i : Int) : Int
  insn native (x : Int) : Int
  insn axed (x : Int) : Int
  insn helped (x : Int) : Int
  insn shown (x : Int) : Int
  insn externed (x : Int) : Int
  insn swapped (xs : Seq Int) : Seq Int
  insn swappedOk (xs : Seq Int) : Seq Int
  insn swappedThere (xs : Seq Int) : Seq Int
  insn privSwap (x : Int) : Int
  insn csimpSorry (x : Int) : Int
  insn viaSpec (x : Int) : Int
  insn swElse (x : Int) : Int
  insn swSelf (x : Int) : Int
  insn swElsewhere (x : Int) : Int
  insn swDef (x : Int) : Int
  insn swUnsafe (x : Int) : Int
  insn swGlobalUnsafe (x : Int) : Int
  insn swChain (x : Int) : Int
  insn viaRec (x : Int) : Int
  insn viaRd (x : Int) : Int
  insn viaInit (x : Int) : Int
  insn whileLoop (x : Int) : Int
  insn fixLoop (x : Int) : Int
  insn extLoop (x : Int) : Int
  insn rangeLoop (x : Int) : Int
  insn stdRangeLoop (x : Int) : Int
  insn nestedEq (x : Int) : Bool
  insn nestedOrd (x : Int) : Bool
  insn stLoop (x : Int) : Int
  insn stVoid (x : Int) : Int
  insn estLoop (x : Int) : Int
  insn strSpin (x : Int) : Int
  insn trick (x : Int) : Int
  insn unsafely (x : Int) : Int
  insn shadeEq (x : Int) : Bool
  insn toneEq (x : Int) : Bool
  insn libSwap (xs : Seq Int) : Seq Int
  insn irDirect (xs : Seq Int) : Seq Int
  insn irSpec (xs : Seq Int) : Seq Int
  insn irClosed (x : Int) : Seq Int
  insn irFold (xs : Seq Int) (n : Int) : Seq Int
  insn irClosure (xs : Seq Int) (n : Int) : Seq Int
  insn irLoop (xs : Seq Int) : Seq Int
  insn mutual1 (x : Int) : Bool
  insn mutual2 (x : Int) : Bool
  insn hiddenRec (x : Int) : Int
  insn mutualSwap (xs : Seq Int) : Seq Int
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

#guard_msgs in
#dyn_check_rule ErrCall.callAt

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

#guard_msgs in
#dyn_check_rule ErrCall.tagAt

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

#guard_msgs in
#dyn_check_rule ErrCall.spread

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

#guard_msgs in
#dyn_check_rule ErrCall.callBy

end

-- `ErrCall`'s table runs its calling rules, and so does its child's: a rule takes its table's
-- decoding.
/-- info: ErrCallSem: no rule for errCall.spreadOut, errCall.spreadIn -/
#guard_msgs in
#dyn_sem_table ErrCallSem for ErrCall

/-- info: ErrCallKidSem: no rule for errCall.spreadOut, errCall.spreadIn -/
#guard_msgs in
#dyn_sem_table ErrCallKidSem for ErrCallKid

/-! ### What a rule may use

A rule may use Lean's library and our own definitions, as long as they run as they are
proved (below).  A `partial` helper doesn't: proofs see its loop as an opaque constant. -/

/-- A helper that may not terminate. -/
partial def spin (x : Int) : Int := if x > 0 then spin x else x

#guard_msgs in
@[dyn_sem Err.spinning] def spinning (x : Int) : Sem ε E Int := pure (spin x)

/-- error: rule spinning for err.spinning reaches spin (spinning → spin), which is partial: proofs see an opaque constant, while a run executes a loop that may never end; use structural or well-founded recursion, or a loop through `again`, which the machine runs step by step -/
#guard_msgs in
#dyn_check_rule Err.spinning

/-- A helper in `IO`. -/
def hello : IO Unit := pure ()

#guard_msgs in
@[dyn_sem Err.greet] def greet (x : Int) : Sem ε E Int := (fun _ => pure x) hello

#guard_msgs in
#dyn_check_rule Err.greet

-- `Array.set`, whose proof argument has a tactic default, and `l[i]?` draw no warning.
#guard_msgs in
@[dyn_sem Err.setAt] def setAt (xs : Array Int) (i v : Int) : Array Int :=
  if h : i.toNat < xs.size then xs.set i.toNat v h else xs

#guard_msgs in
#dyn_check_rule Err.setAt

#guard_msgs in
@[dyn_sem Err.getAt] def getAt (xs : Array Int) (i : Int) : Int := xs.toList[i.toNat]?.getD 0

#guard_msgs in
#dyn_check_rule Err.getAt

/-! ### Code that runs as it is proved

A rule's meaning is its definition, so the code that runs must be that definition.  So a rule may
reach no `sorry`, no axiom of ours, no unexposed definition of ours, and none of our own
`implemented_by`, `extern` or `opaque` definitions.  A `@[csimp]` lemma is proved, so a swap to
code that passes the same check is accepted. -/

/-- A helper whose compiled code is other code: proofs read `x`, and a run executes `spin`. -/
@[implemented_by spin] def slow (x : Int) : Int := x

/-- A helper that reaches `slow`. -/
def viaSlow (x : Int) : Int := slow x + 0

@[dyn_sem Err.fast] def fast (x : Int) : Sem ε E Int := pure (viaSlow x)

/--
error: rule fast for err.fast reaches slow (fast → viaSlow → slow), which carries @[implemented_by spin]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead
-/
#guard_msgs in
#dyn_check_rule Err.fast

/-- A helper with compiled code of its own, by a `@[csimp]` theorem; both must be public and
exposed. -/
@[expose] public def plain (x : Int) : Int := x

/-- The code that runs in place of `plain`. -/
@[expose] public def plainImpl (x : Int) : Int := id x

/-- `plain`'s compiled code, `plainImpl`, is `plain`. -/
@[csimp] public theorem plain_eq_plainImpl : @plain = @plainImpl := rfl

#guard_msgs in
@[dyn_sem Err.quick] def quick (x : Int) : Sem ε E Int := pure (plain x)

#guard_msgs in
#dyn_check_rule Err.quick

/-- A `@[csimp]` replacement that carries `implemented_by` itself. -/
@[expose, implemented_by spin] public def sneakyImpl (x : Int) : Int := x

/-- A helper whose `@[csimp]` replacement is `sneakyImpl`. -/
@[expose] public def sneaky (x : Int) : Int := x

/-- `sneaky`'s compiled code is `sneakyImpl`. -/
@[csimp] public theorem sneaky_eq_sneakyImpl : @sneaky = @sneakyImpl := rfl

@[dyn_sem Err.sly] def sly (x : Int) : Sem ε E Int := pure (sneaky x)

/--
error: rule sly for err.sly reaches sneakyImpl (sly → sneaky → sneakyImpl), which carries @[implemented_by spin]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead
-/
#guard_msgs in
#dyn_check_rule Err.sly

/-- An opaque helper. -/
opaque hidden : Int → Int

-- An opaque helper is rejected: its definition is hidden from proofs.  Lean's own `@[extern]`
-- and `implemented_by` definitions, such as `Int.add` and `Array.push`, are accepted.
@[dyn_sem Err.veiled] def veiled (x : Int) : Sem ε E Int := pure (hidden x + #[x].size)

/-- error: rule veiled for err.veiled reaches hidden (veiled → hidden), which is opaque: its definition is hidden from proofs -/
#guard_msgs in
#dyn_check_rule Err.veiled

-- An instruction's key is its own name, which its emitter shares, not its reference.
/-- error: unknown Dyn type or instruction `Err.veiled.ref` -/
#guard_msgs in
@[dyn_sem Err.veiled.ref] def veiledRef (x : Int) : Sem ε E Int := pure x

set_option warn.sorry false in
@[dyn_sem Err.sorried] def sorried (xs : Array Int) (i : Int) : Int :=
  if i.toNat < xs.size then xs[i.toNat]'sorry else 0

/-- error: rule sorried for err.sorried reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule Err.sorried

@[dyn_sem Err.native] def native (x : Int) : Int :=
  have : (2 : Nat) + 2 = 4 := by native_decide
  x

/-- error: rule native for err.native reaches the axiom native._native.native_decide.ax_1; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule Err.native

/-- An axiom of ours, a false one: it proves anything, a forged ref's validity included. -/
axiom bad : False

@[dyn_sem Err.axed] def axed (x : Int) : Int := if (bad.elim : Bool) then x else x

/-- error: rule axed for err.axed reaches the axiom bad; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule Err.axed

@[dyn_sem Err.helped] def helped (x : Int) : Int := Helpers.hiddenLie x

/-- error: rule helped for err.helped reaches Helpers.hiddenLie (helped → Helpers.hiddenLie), whose definition its module does not expose, so the check cannot see it: mark it @[expose], or, for a derived instance, derive it in an @[expose] section or write it by hand -/
#guard_msgs in
#dyn_check_rule Err.helped

#guard_msgs in
@[dyn_sem Err.shown] def shown (x : Int) : Int := Helpers.shownDouble x

#guard_msgs in
#dyn_check_rule Err.shown

/-- A helper implemented in C. -/
@[extern "lean_int_neg"] def negC (x : Int) : Int := -x

@[dyn_sem Err.externed] def externed (x : Int) : Int := negC x

/-- error: rule externed for err.externed reaches negC (externed → negC), which carries @[extern]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.externed

/-- The compiled code of `myRev`: it drops everything. -/
@[expose] public def lieRev (_xs : Array Int) : Array Int := #[]
/-- `xs` reversed in the logic, and run as `lieRev`. -/
@[implemented_by lieRev, expose] public def myRev (xs : Array Int) : Array Int := xs.reverse
/-- The reversal of our own, `rev`, swapped for `myRev` when compiled. -/
@[expose] public def rev (xs : Array Int) : Array Int := xs.reverse
/-- `rev` is `myRev`, so the compiler swaps `rev` for `myRev`. -/
@[csimp] public theorem rev_eq_myRev : @rev = @myRev := by funext xs; rfl

@[dyn_sem Err.swapped] def swapped (xs : Array Int) : Array Int := rev xs

/-- error: rule swapped for err.swapped reaches myRev (swapped → rev → myRev), which carries @[implemented_by lieRev]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.swapped

/-- A slow reversal, and a fast one proved equal and swapped in. -/
@[expose] public def revSlow (xs : Array Int) : Array Int := xs.toList.reverse.toArray
@[expose] public def revFast (xs : Array Int) : Array Int := xs.reverse
/-- `revSlow` is `revFast`, so the compiler swaps in the fast version. -/
@[csimp] public theorem revSlow_eq_revFast : @revSlow = @revFast := by
  funext xs; apply Array.ext'; simp [revSlow, revFast]

#guard_msgs in
@[dyn_sem Err.swappedOk] def swappedOk (xs : Array Int) : Array Int := revSlow xs

#guard_msgs in
#dyn_check_rule Err.swappedOk

/-! A swap that a `local` `@[csimp]` lemma made in another module: `swappedHere` was compiled
there with `revH` swapped for `myRevH`, which runs `lieRevH`.  The lemma is public, so the check
follows it from `revH` to `myRevH`, and rejects `myRevH`'s `@[implemented_by]`. -/
@[dyn_sem Err.swappedThere] def swappedThere (xs : Array Int) : Array Int :=
  Helpers.swappedHere xs

/-- error: rule swappedThere for err.swappedThere reaches Helpers.myRevH (swappedThere → Helpers.swappedHere → Helpers.revH → Helpers.myRevH), which carries @[implemented_by Helpers.lieRevH]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.swappedThere

-- A swap whose lemma is private in another module: this module can't see the lemma, and the
-- helper reaches the swap's target itself, so the check passes here.
@[dyn_sem Err.privSwap] def privSwap (x : Int) : Int := Helpers.privSwapped x

#guard_msgs in
#dyn_check_rule Err.privSwap

/-- `x`. -/
@[expose] public def f1 (x : Int) : Int := x
/-- `x + 1`. -/
@[expose] public def g1 (x : Int) : Int := x + 1
set_option warn.sorry false in
/-- A false swap of `f1` for `g1`, by `sorry`. -/
@[csimp] public theorem f1_eq_g1 : @f1 = @g1 := sorry

@[dyn_sem Err.csimpSorry] def csimpSorry (x : Int) : Int := f1 x

/-- error: rule csimpSorry for err.csimpSorry reaches f1 (csimpSorry → f1), whose @[csimp] lemma f1_eq_g1 reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule Err.csimpSorry

/-- `x`, specified by a choice, with no code of its own. -/
@[expose] public noncomputable def specId (x : Int) : Int := Classical.epsilon (· = x)

/-- `x`, by code. -/
@[expose] public def fastId (x : Int) : Int := x

/-- The specification is the code, so the code is swapped in. -/
@[csimp] public theorem specId_eq_fastId : @specId = @fastId :=
  funext fun x => Classical.epsilon_spec (p := (· = x)) ⟨x, rfl⟩

-- A noncomputable specification that a proved swap gives code runs as that code.
#guard_msgs in
@[dyn_sem Err.viaSpec] def viaSpec (x : Int) : Int := specId x

#guard_msgs in
#dyn_check_rule Err.viaSpec

/-! A `local` swap leaves no trace in the csimp state once its section ends, but its lemma stays.
So every constant `@f = @g` of a definition `f` that a rule reaches counts as a swap, and must be
a theorem with the allowed axioms: then `f` and `g` are equal, and checking `f` suffices.  Here a false lemma swaps `fP` for `gP`, which the rule also reaches
elsewhere, or which the helper reaches itself. -/

/-- The identity. -/
@[expose] public def fP (x : Int) : Int := x
/-- `x + 100`. -/
@[expose] public def gP (x : Int) : Int := x + 100
/-- A false equation, used only as a local swap. -/
axiom fP_eq_gP : @fP = @gP

section
attribute [local csimp] fP_eq_gP
/-- `fP x` in the logic, compiled as `gP x`. -/
@[expose] public def hP (x : Int) : Int := fP x
/-- `fP x + gP 0 - 100` in the logic, which reaches `gP` itself. -/
@[expose] public def hP2 (x : Int) : Int := fP x + gP 0 - 100
end

@[dyn_sem Err.swElse] def swElse (x : Int) : Int := hP x + gP 0 - 100

/-- error: rule swElse for err.swElse reaches fP (swElse → hP → fP), and the lemma fP_eq_gP equates fP with gP, so a local @[csimp] swap may run gP instead; fP_eq_gP reaches the axiom fP_eq_gP, but a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule Err.swElse

@[dyn_sem Err.swSelf] def swSelf (x : Int) : Int := hP2 x

/-- error: rule swSelf for err.swSelf reaches fP (swSelf → hP2 → fP), and the lemma fP_eq_gP equates fP with gP, so a local @[csimp] swap may run gP instead; fP_eq_gP reaches the axiom fP_eq_gP, but a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule Err.swSelf

/-! A swap lemma may be any constant, not only a theorem: a `def` proved by `sorry`, or an
`unsafe def` that proves it by calling itself, with no axiom at all. -/

/-- The identity. -/
@[expose] public def fD (x : Int) : Int := x
/-- `x + 100`. -/
@[expose] public def gD (x : Int) : Int := x + 100
set_option linter.defProp false in
set_option warn.sorry false in
/-- A false equation, as a definition. -/
public def fD_eq_gD : @fD = @gD := sorry
/-- The identity. -/
@[expose] public def fU (x : Int) : Int := x
/-- `x + 100`. -/
@[expose] public def gU (x : Int) : Int := x + 100
set_option linter.defProp false in
/-- A false equation, by unsafe recursion. -/
public unsafe def fU_eq_gU : @fU = @gU := fU_eq_gU

section
attribute [local csimp] fD_eq_gD fU_eq_gU
/-- `fD x + gD 0 - 100`, compiled as `gD x + gD 0 - 100`. -/
@[expose] public def hD (x : Int) : Int := fD x + gD 0 - 100
/-- `fU x + gU 0 - 100`, compiled as `gU x + gU 0 - 100`. -/
@[expose] public def hU (x : Int) : Int := fU x + gU 0 - 100
end

@[dyn_sem Err.swDef] def swDef (x : Int) : Int := hD x

/-- error: rule swDef for err.swDef reaches fD (swDef → hD → fD), and fD_eq_gD equates fD with gD, so a @[csimp] swap may run gD instead, but fD_eq_gD is not a theorem -/
#guard_msgs in
#dyn_check_rule Err.swDef

@[dyn_sem Err.swUnsafe] def swUnsafe (x : Int) : Int := hU x

/-- error: rule swUnsafe for err.swUnsafe reaches fU (swUnsafe → hU → fU), and fU_eq_gU equates fU with gU, so a @[csimp] swap may run gU instead, but fU_eq_gU is not a theorem -/
#guard_msgs in
#dyn_check_rule Err.swUnsafe

/-- The identity. -/
@[expose] public def fG (x : Int) : Int := x
/-- `x + 100`. -/
@[expose] public def gG (x : Int) : Int := x + 100
set_option linter.defProp false in
/-- A false equation, by unsafe recursion, as a global swap. -/
@[csimp] public unsafe def fG_eq_gG : @fG = @gG := fG_eq_gG

@[dyn_sem Err.swGlobalUnsafe] def swGlobalUnsafe (x : Int) : Int := fG x

/-- error: rule swGlobalUnsafe for err.swGlobalUnsafe reaches fG (swGlobalUnsafe → fG), and fG_eq_gG equates fG with gG, so a @[csimp] swap may run gG instead, but fG_eq_gG is not a theorem -/
#guard_msgs in
#dyn_check_rule Err.swGlobalUnsafe

/-! Lean applies swaps one after another, so the lemmas of a swap's target are checked too: here
a proved swap of `fC` for `gC`, then a false one of `gC` for `kC`. -/

/-- The identity. -/
@[expose] public def fC (x : Int) : Int := x
/-- The identity, by another name. -/
@[expose] public def gC (x : Int) : Int := id x
/-- `x + 100`. -/
@[expose] public def kC (x : Int) : Int := x + 100
/-- `fC` is `gC`. -/
public theorem fC_eq_gC : @fC = @gC := rfl
/-- A false equation. -/
axiom gC_eq_kC : @gC = @kC

section
attribute [local csimp] fC_eq_gC gC_eq_kC
/-- `fC x + kC 0 - 100`, compiled as `kC x + kC 0 - 100`. -/
@[expose] public def hC (x : Int) : Int := fC x + kC 0 - 100
end

@[dyn_sem Err.swChain] def swChain (x : Int) : Int := hC x

/-- error: rule swChain for err.swChain reaches fC (swChain → hC → fC), and the lemma gC_eq_kC equates gC with kC, so a local @[csimp] swap may run kC instead; gC_eq_kC reaches the axiom gC_eq_kC, but a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule Err.swChain

/-! A local swap with a proved lemma is right: `hQ` was compiled with a local swap of `fQ` for
`gQ`, and the check follows the lemma from `fQ` to `gQ`, which runs as written, so it accepts
the rule. -/

/-- The identity. -/
@[expose] public def fQ (x : Int) : Int := x
/-- The identity, by another name. -/
@[expose, noinline] public def gQ (x : Int) : Int := id x
/-- `fQ` is `gQ`. -/
public theorem fQ_eq_gQ : @fQ = @gQ := rfl

section
attribute [local csimp] fQ_eq_gQ
/-- `fQ x`, compiled as `gQ x`. -/
@[expose] public def hQ (x : Int) : Int := fQ x
end

@[dyn_sem Err.swElsewhere] def swElsewhere (x : Int) : Int := hQ x + gQ 0

#guard_msgs in
#dyn_check_rule Err.swElsewhere

/-- The code that runs for `myRd1`: `x + 1000`. -/
def lieRd1 (x : Int) (_n : Nat) : Int := x + 1000
/-- `x` in the logic, run as `lieRd1`; its unused parameter gives it a reduced-arity version. -/
@[implemented_by lieRd1] def myRd1 (x : Int) (n : Nat) : Int := x + 0 * n
/-- `x`. -/
def pRd1 (x : Int) (n : Nat) : Int := x + 0 * n
/-- `pRd1` is `myRd1`. -/
theorem pRd1_eq : @pRd1 = @myRd1 := rfl

section
attribute [local csimp] pRd1_eq
/-- `x` in the logic, compiled here as a call of `lieRd1`'s reduced-arity version. -/
def hRd (x : Int) : Int := pRd1 x 0
end

-- The local swap's target is walked, so its `implemented_by` is found, though the compiled
-- code calls only `lieRd1._redArg`.
@[dyn_sem Err.viaRd] def viaRd (x : Int) : Int := hRd x

/-- error: rule viaRd for err.viaRd reaches myRd1 (viaRd → hRd → pRd1 → myRd1), which carries @[implemented_by lieRd1]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.viaRd

/-- The initializer of `initFive`: at run time, its value is `7`. -/
def initSeven : IO Int := pure 7
/-- `5` in the logic; at run time, what `initSeven` computes. -/
@[init initSeven] def initFive : Int := 5

@[dyn_sem Err.viaInit] def viaInit (x : Int) : Int := x + initFive

/-- error: rule viaInit for err.viaInit reaches initFive (viaInit → initFive), which carries @[init initSeven]: a run uses the value that initSeven computes, not the definition proofs read -/
#guard_msgs in
#dyn_check_rule Err.viaInit

/-- A recursive helper over code that runs differently. -/
def viaSlowRec : Nat → Int → Int
  | 0, x => slow x
  | n + 1, x => viaSlowRec n x

@[dyn_sem Err.viaRec] def viaRec (x : Int) : Int := viaSlowRec 1 x

/-- error: rule viaRec for err.viaRec reaches slow (viaRec → viaSlowRec → viaSlowRec._f → slow), which carries @[implemented_by spin]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.viaRec

/-! Lean's library loops too: a `while` loop, a `partial_fixpoint` definition, a fixed point over a
relation that our own code names, and a `for` loop over `0...n`, whose range is a fixed point of
the same kind.  So does an instance that Lean derives as `partial`, for a nested type. -/

/-- `x` counted up while it is positive: forever, for a positive `x`. -/
def countUp (x : Int) : Int := Id.run do
  let mut i := x
  while i > 0 do
    i := i + 1
  return i

@[dyn_sem Err.whileLoop] def whileLoop (x : Int) : Int := countUp x

/-- error: rule whileLoop for err.whileLoop reaches Lean.Loop.forIn (whileLoop → countUp → Lean.instForInLoopUnitOfMonad → Lean.Loop.forIn), a loop of Lean's library that may never end, while proofs see a value; a loop that may not end goes through `again`, which the machine runs step by step -/
#guard_msgs in
#dyn_check_rule Err.whileLoop

/-- A fixed point that never ends. -/
def upForever (x : Int) : Int := upForever (x + 1)
partial_fixpoint

@[dyn_sem Err.fixLoop] def fixLoop (x : Int) : Int := upForever x

/-- error: rule fixLoop for err.fixLoop reaches Lean.Order.fix (fixLoop → upForever → Lean.Order.fix), a loop of Lean's library that may never end, while proofs see a value; a loop that may not end goes through `again`, which the machine runs step by step -/
#guard_msgs in
#dyn_check_rule Err.fixLoop

/-- A fixed point over a relation that isn't well-founded. -/
def upExt (x : Int) : Int :=
  WellFounded.extrinsicFix (C := fun _ => Int) (fun (_ _ : Int) => True)
    (fun a rec => rec (a + 1) trivial) x

@[dyn_sem Err.extLoop] def extLoop (x : Int) : Int := upExt x

/-- error: rule extLoop for err.extLoop reaches WellFounded.extrinsicFix (extLoop → upExt → WellFounded.extrinsicFix), a loop of Lean's library that may never end, while proofs see a value; a loop that may not end goes through `again`, which the machine runs step by step -/
#guard_msgs in
#dyn_check_rule Err.extLoop

/-- The sum of `0`, …, `n - 1`, over the range `0...n`. -/
def sumTo (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in 0...n do
    s := s + i
  return s

@[dyn_sem Err.rangeLoop] def rangeLoop (x : Int) : Int := sumTo x.toNat

/-- error: rule rangeLoop for err.rangeLoop reaches Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId (rangeLoop → sumTo → Std.Rco.instForIn'InferInstanceMembershipOfLawfulUpwardEnumerableOfLawfulUpwardEnumerableLEOfLawfulUpwardEnumerableLTOfMonadOfFiniteIteratorId), a loop of Lean's library that may never end, while proofs see a value; a loop that may not end goes through `again`, which the machine runs step by step -/
#guard_msgs in
#dyn_check_rule Err.rangeLoop

/-- The sum of `0`, …, `n - 1`, over `[0:n]`, a `Std.Range`, whose loop ends by its fuel. -/
def sumToStd (n : Nat) : Nat := Id.run do
  let mut s := 0
  for i in [0:n] do
    s := s + i
  return s

@[dyn_sem Err.stdRangeLoop] def stdRangeLoop (x : Int) : Int := sumToStd x.toNat

#guard_msgs in
#dyn_check_rule Err.stdRangeLoop

/-- A nested type, whose derived instances Lean makes `partial`. -/
inductive Tree where
  | node (kids : List Tree)
  deriving BEq, Ord

@[dyn_sem Err.nestedEq] def nestedEq (x : Int) : Bool := Tree.node [] == Tree.node (List.replicate x.toNat (.node []))

/-- error: rule nestedEq for err.nestedEq reaches instBEqTree.beq (nestedEq → instBEqTree → instBEqTree.beq), which is partial: proofs see an opaque constant, while a run executes a loop that may never end; use structural or well-founded recursion, or a loop through `again`, which the machine runs step by step (Lean derives this instance as partial for a nested, mutual or, for Ord, recursive type: write it by hand) -/
#guard_msgs in
#dyn_check_rule Err.nestedEq

@[dyn_sem Err.nestedOrd] def nestedOrd (x : Int) : Bool :=
  compare (Tree.node []) (Tree.node (List.replicate x.toNat (.node []))) == .lt

/-- error: rule nestedOrd for err.nestedOrd reaches instOrdTree.ord (nestedOrd → instOrdTree → instOrdTree.ord), which is partial: proofs see an opaque constant, while a run executes a loop that may never end; use structural or well-founded recursion, or a loop through `again`, which the machine runs step by step (Lean derives this instance as partial for a nested, mutual or, for Ord, recursive type: write it by hand) -/
#guard_msgs in
#dyn_check_rule Err.nestedOrd

/-- A loop without recursion: an `ST` cell holds a closure that reads the cell and calls what it
holds, forever. -/
def knot (n : Nat) : Nat := runST fun σ => do
  let r : ST.Ref σ (Nat → ST σ Nat) ← ST.mkRef (fun _ => pure 0)
  r.set (fun k => do let f ← r.get; f k)
  let f ← r.get
  f n

@[dyn_sem Err.stLoop] def stLoop (x : Int) : Int := knot x.toNat

/-- error: rule stLoop for err.stLoop reaches runST (stLoop → knot → runST), which runs `ST` code: a cell that holds a closure can make a loop that never ends, while proofs see a value -/
#guard_msgs in
#dyn_check_rule Err.stLoop

/-- The same loop, started as `runST` starts it, by applying it to `Void.mk ()`. -/
def knotVoid (n : Nat) : Nat :=
  let act : ST Unit Nat := do
    let r : ST.Ref Unit (Nat → ST Unit Nat) ← ST.mkRef (fun _ => pure 0)
    r.set (fun k => do let f ← r.get; f k)
    let f ← r.get
    f n
  (act (Void.mk ())).val

@[dyn_sem Err.stVoid] def stVoid (x : Int) : Int := knotVoid x.toNat

/-- error: rule stVoid for err.stVoid reaches Void.mk (stVoid → knotVoid → Void.mk), which runs `ST` code: a cell that holds a closure can make a loop that never ends, while proofs see a value -/
#guard_msgs in
#dyn_check_rule Err.stVoid

/-- The same loop in `EST`, run by `runEST`. -/
def knotE (n : Nat) : Nat :=
  match runEST (ε := String) fun σ => do
    let r : ST.Ref σ (Nat → EST String σ Nat) ← ST.mkRef (fun _ => pure 0)
    r.set (fun k => do let f ← r.get; f k)
    let f ← r.get
    f n with
  | .ok a => a
  | .error _ => 0

@[dyn_sem Err.estLoop] def estLoop (x : Int) : Int := knotE x.toNat

/-- error: rule estLoop for err.estLoop reaches runEST (estLoop → knotE → runEST), which runs `ST` code: a cell that holds a closure can make a loop that never ends, while proofs see a value -/
#guard_msgs in
#dyn_check_rule Err.estLoop

/-- A loop that the rule passes to `String.foldl`, which the check trusts: the rule's own function
is still walked. -/
@[dyn_sem Err.strSpin] def strSpin (x : Int) : Int :=
  (toString x).foldl (fun n _ => spin n) 0

/-- error: rule strSpin for err.strSpin reaches spin (strSpin → spin), which is partial: proofs see an opaque constant, while a run executes a loop that may never end; use structural or well-founded recursion, or a loop through `again`, which the machine runs step by step -/
#guard_msgs in
#dyn_check_rule Err.strSpin

/-- The body that the compiler would run for `trickFn`.  It is `noncomputable` here, since the C
emitter loops on a hand-written `_unsafe_rec` that it compiles. -/
noncomputable def trickFn._unsafe_rec (x : Int) : Int := x + 100
/-- `x` in the logic; the compiler would compile it from `trickFn._unsafe_rec`. -/
def trickFn (x : Int) : Int := x

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'trickFn', which is 'noncomputable'
-/
#guard_msgs in
@[dyn_sem Err.trick] def trick (x : Int) : Int := trickFn x

/-- error: rule trick for err.trick reaches trickFn (trick → trickFn), which runs trickFn._unsafe_rec instead of its definition (a hand-written _unsafe_rec); a run would not run the definition that proofs see -/
#guard_msgs in
#dyn_check_rule Err.trick

-- An `unsafe` rule registers, but no table can run it (`UnsSem` below).
#guard_msgs in
@[dyn_sem Err.unsafely] unsafe def unsafely (x : Int) : Int := x

#guard_msgs in
#dyn_check_rule Err.unsafely

@[dyn_sem Err.shadeEq] def shadeEq (x : Int) : Bool :=
  (if x > 0 then Helpers.Shade.light else .dark) == .light

/-- error: rule shadeEq for err.shadeEq reaches Helpers.instBEqShade.beq (shadeEq → Helpers.instBEqShade → Helpers.instBEqShade.beq), whose definition its module does not expose, so the check cannot see it: mark it @[expose], or, for a derived instance, derive it in an @[expose] section or write it by hand -/
#guard_msgs in
#dyn_check_rule Err.shadeEq

#guard_msgs in
@[dyn_sem Err.toneEq] def toneEq (x : Int) : Bool :=
  (if x > 0 then Helpers.Tone.low else .high) == .low

#guard_msgs in
#dyn_check_rule Err.toneEq

section
/-- A swap of Lean's own `Array.reverse` for code of ours that drops everything. -/
@[expose] public def dropAll.{u} {α : Type u} (_xs : Array α) : Array α := #[]
/-- `xs` reversed in the logic, and run as `dropAll`. -/
@[implemented_by dropAll, expose] public def revOurs.{u} {α : Type u} (xs : Array α) : Array α :=
  xs.reverse
/-- `Array.reverse` is `revOurs`, so the compiler swaps it, here only. -/
public theorem reverse_eq_revOurs.{u} : @Array.reverse.{u} = @revOurs.{u} := by
  funext α xs; rfl
attribute [local csimp] reverse_eq_revOurs

@[dyn_sem Err.libSwap] def libSwap (xs : Array Int) : Array Int := xs.reverse

/-- error: rule libSwap for err.libSwap reaches revOurs (libSwap → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.libSwap
end

/-! Helpers compiled with a `local` swap, in a section that has ended, so the swap is no longer in
the csimp state when the check runs.  The swap lemmas are still constants, so the check follows
them, here to `revOurs`, through the lemma for `Array.reverse` above.  (Only a swap whose lemma
the check can't see shows in compiled code alone: `TableCheckTest`'s `BSem` and `QSem`.) -/

/-- `xs` reversed. -/
@[expose] public def revL (xs : Array Int) : Array Int := xs.reverse
/-- `xs` reversed in the logic, and run as `lieRev`. -/
@[implemented_by lieRev, expose] public def myRevL (xs : Array Int) : Array Int := xs.reverse
/-- `revL` is `myRevL`; only the section below uses it as a swap. -/
public theorem revL_eq_myRevL : @revL = @myRevL := by funext xs; rfl

section
attribute [local csimp] revL_eq_myRevL
/-- `revL xs`, called directly. -/
@[expose] public def h1 (xs : Array Int) : Array Int := revL xs
/-- `revL` inside a lambda that a library function takes: compiled as a specialization. -/
@[expose] public def h2 (xs : Array Int) : Array Int := ((#[xs].map revL)[0]?).getD #[]
/-- `revL` in a closed term. -/
@[expose] public def h3 (x : Int) : Array Int := (revL #[1, 2, 3]).push x
/-- `revL` in a fold. -/
@[expose] public def h4 (xs : Array Int) (n : Nat) : Array Int :=
  (List.range n).foldl (fun acc _ => revL acc) xs
/-- `revL` in a returned closure. -/
@[expose] public def h5 (xs : Array Int) : Nat → Array Int :=
  fun n => if n == 0 then xs else revL xs
/-- `revL` in a loop. -/
@[expose] public def h6 (xs : Array Int) : Array Int := Id.run do
  let mut a := xs
  for _ in [0:2] do
    a := revL a
  return a
end

@[dyn_sem Err.irDirect] def irDirect (xs : Array Int) : Array Int := h1 xs

/-- error: rule irDirect for err.irDirect reaches revOurs (irDirect → h1 → revL → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.irDirect
@[dyn_sem Err.irSpec] def irSpec (xs : Array Int) : Array Int := h2 xs

/-- error: rule irSpec for err.irSpec reaches revOurs (irSpec → h2 → revL → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.irSpec
@[dyn_sem Err.irClosed] def irClosed (x : Int) : Array Int := h3 x

/-- error: rule irClosed for err.irClosed reaches revOurs (irClosed → h3 → revL → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.irClosed
@[dyn_sem Err.irFold] def irFold (xs : Array Int) (n : Int) : Array Int := h4 xs n.toNat

/-- error: rule irFold for err.irFold reaches revOurs (irFold → h4 → revL → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.irFold
@[dyn_sem Err.irClosure] def irClosure (xs : Array Int) (n : Int) : Array Int := h5 xs n.toNat

/-- error: rule irClosure for err.irClosure reaches revOurs (irClosure → h5 → revL → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.irClosure
@[dyn_sem Err.irLoop] def irLoop (xs : Array Int) : Array Int := h6 xs

/-- error: rule irLoop for err.irLoop reaches revOurs (irLoop → h6 → revL → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.irLoop

/-! Mutual recursion compiles each function's code under its own name again, for its
`_unsafe_rec`, and is accepted, structural or well-founded. -/

mutual
/-- Whether `n` is even. -/
def evenP : Nat → Bool
  | 0 => true
  | n + 1 => oddP n
/-- Whether `n` is odd. -/
def oddP : Nat → Bool
  | 0 => false
  | n + 1 => evenP n
end

mutual
/-- Whether `n` is even, by well-founded recursion. -/
def evenW (n : Nat) : Bool := if h : n = 0 then true else oddW (n - 1)
termination_by n
decreasing_by omega
/-- Whether `n` is odd, by well-founded recursion. -/
def oddW (n : Nat) : Bool := if h : n = 0 then false else evenW (n - 1)
termination_by n
decreasing_by omega
end

#guard_msgs in
@[dyn_sem Err.mutual1] def mutual1 (x : Int) : Bool := evenP x.toNat

#guard_msgs in
#dyn_check_rule Err.mutual1
#guard_msgs in
@[dyn_sem Err.mutual2] def mutual2 (x : Int) : Bool := evenW x.toNat

#guard_msgs in
#dyn_check_rule Err.mutual2

section
attribute [local csimp] revL_eq_myRevL
mutual
/-- `xs` after `n` steps; the sibling reverses it at `0`. -/
@[expose] public def evS : Nat → Array Int → Array Int
  | 0, xs => xs
  | n + 1, xs => odS n xs
/-- `xs` reversed after `n` steps, compiled here with the local swap of `revL`. -/
@[expose] public def odS : Nat → Array Int → Array Int
  | 0, xs => revL xs
  | n + 1, xs => evS n xs
end
end

@[dyn_sem Err.mutualSwap] def mutualSwap (xs : Array Int) : Array Int := evS 1 xs

/-- error: rule mutualSwap for err.mutualSwap reaches revOurs (mutualSwap → evS → odS._f → revL → Array.reverse → revOurs), which carries @[implemented_by dropAll]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule Err.mutualSwap

@[dyn_sem Err.hiddenRec] def hiddenRec (x : Int) : Int := Helpers.countDown x.toNat

/-- error: rule hiddenRec for err.hiddenRec reaches Helpers.countDown (hiddenRec → Helpers.countDown), whose definition its module does not expose, so the check cannot see it: mark it @[expose], or, for a derived instance, derive it in an @[expose] section or write it by hand -/
#guard_msgs in
#dyn_check_rule Err.hiddenRec

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
error: #dyn_sem_table: a capability names Mut.A.Val, the Lean type of no type of this table
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
  insn forged (v : Int) : Ref Int
  insn forgedAx (v : Int) : Ref Int
  insn confuse (c : Ref Int) : Int
  insn peek (c : Ref Int) : Int
  insn peekProj (c : Ref Int) : Int
  insn peekMatch (c : Ref Int) : Int
  insn peekRepr (c : Ref Int) : String
  insn same (a b : Ref Int) : Bool
  insn peekFn (f : Fn [Int] Int) : Int
  insn peekHeap (c : Ref Int) : Int
  insn buildHeap (c : Ref Int) : Bool
  insn named (c : Ref Int) : Int
  insn asked (c : Ref Int) : Int
  insn provedIn (c : Ref Int) : Int
  insn decided (c : Ref Int) : Int
  insn veiledSub (x : Int) : Int
  insn eps (c : Ref Int) : Int
  insn classical (c : Ref Int) : Int
  insn forgedEps (c : Ref Int) : Ref Int
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

#guard_msgs in
#dyn_check_rule CellErr.mk

/--
error: base.Ref needs the run token: a rule that takes or makes one must be generic in it, {σ : Type} [Store σ]
-/
#guard_msgs in
@[dyn_sem CellErr.loc] def locAtRun (c : Ref Run Int) : Int := c.loc

#guard_msgs in
@[dyn_sem CellErr.loc] def loc {σ : Type} [Store σ] (_c : Ref σ Int) : Int := 0

#guard_msgs in
#dyn_check_rule CellErr.loc

/-- error: locTwo is generic in 2 tokens, but a run has one -/
#guard_msgs in
@[dyn_sem CellErr.twoTokens]
def locTwo {σ τ : Type} [Store σ] [Store τ] (c : Ref σ Int) (_ : Option (Ref τ Int)) :
    Int := c.loc

#guard_msgs in
@[dyn_sem CellErr.twoTokens]
def locOne {σ : Type} [Store σ] (_c : Ref σ Int) : Int := 0

#guard_msgs in
#dyn_check_rule CellErr.twoTokens

/-! A rule may not see where a ref's cell is: a pass such as ref-to-reg may move cells, and the
rule's result must not change.  Equality of refs shows nothing of where they are. -/

@[dyn_sem CellErr.peek] def peek {σ : Type} [Store σ] (c : Ref σ Int) : Int := c.loc

/-- error: rule peek for cellErr.peek reaches Ref.loc (peek → Ref.loc), which tells where a ref's cell or a closure's function is; only the machine may know it, since a pass may move cells -/
#guard_msgs in
#dyn_check_rule CellErr.peek

@[dyn_sem CellErr.peekProj] def peekProj {σ : Type} [Store σ] (c : Ref σ Int) : Int := c.raw.1

/-- error: rule peekProj for cellErr.peekProj reaches Ref.Raw.loc (peekProj → Ref.Raw.loc), which tells where a ref's cell or a closure's function is; only the machine may know it, since a pass may move cells -/
#guard_msgs in
#dyn_check_rule CellErr.peekProj

@[dyn_sem CellErr.peekMatch] def peekMatch {σ : Type} [Store σ] (c : Ref σ Int) : Int :=
  match c with
  | ⟨l, _⟩ => l

/-- error: rule peekMatch for cellErr.peekMatch reaches Ref.Raw.mk (peekMatch → peekMatch.match_1 → Ref.Raw.mk), which builds or takes apart a raw ref or closure; only the machine may, since a rule could point a ref at any cell, or read where it is -/
#guard_msgs in
#dyn_check_rule CellErr.peekMatch

@[dyn_sem CellErr.peekRepr] def peekRepr {σ : Type} [Store σ] (c : Ref σ Int) : String :=
  reprStr c

/-- error: rule peekRepr for cellErr.peekRepr reaches Ref.loc (peekRepr → instReprRef → Ref.loc), which tells where a ref's cell or a closure's function is; only the machine may know it, since a pass may move cells -/
#guard_msgs in
#dyn_check_rule CellErr.peekRepr

#guard_msgs in
@[dyn_sem CellErr.same] def same {σ : Type} [Store σ] (a b : Ref σ Int) : Bool := a == b

#guard_msgs in
#dyn_check_rule CellErr.same

@[dyn_sem CellErr.peekFn] def peekFn {σ : Type} [Store σ] (f : FnRef σ [Int] Int) : Int :=
  f.idx

/-- error: rule peekFn for cellErr.peekFn reaches FnRef.idx (peekFn → FnRef.idx), which tells where a ref's cell or a closure's function is; only the machine may know it, since a pass may move cells -/
#guard_msgs in
#dyn_check_rule CellErr.peekFn

-- A rule that builds the machine's heap capability itself, at a decoding of its own, and takes a
-- location out of the request it makes.
@[dyn_sem CellErr.peekHeap] def peekHeap {σ : Type} [Store σ] (c : Ref σ Int) : Int :=
  letI : Decode σ := ⟨fun _ => Int⟩
  let t : TagOf σ Int := ⟨.app 7 [], rfl⟩
  let q : MReq (fun _ => Int) [] := (@HasHeap.mreq σ _ (fun _ => Int) Unit []).getReq t c
  match q with
  | .get _ l => l
  | _ => -1

/-- error: rule peekHeap for cellErr.peekHeap reaches MReq.get (peekHeap → peekHeap.match_1 → MReq.get), which builds or takes apart a machine request: a request holds locations, so only the handles that a table passes to a rule may build one, and only the machine reads it -/
#guard_msgs in
#dyn_check_rule CellErr.peekHeap

-- A rule that builds the machine's heap capability itself, and reads nothing out of the request
-- but whether it writes a cell.
@[dyn_sem CellErr.buildHeap] def buildHeap {σ : Type} [Store σ] (c : Ref σ Int) : Bool :=
  letI : Decode σ := ⟨fun _ => Int⟩
  let t : TagOf σ Int := ⟨.app 7 [], rfl⟩
  ((@HasHeap.mreq σ _ (fun _ => Int) Unit []).getReq t c).writesCell

/-- error: rule buildHeap for cellErr.buildHeap reaches HasHeap.mreq (buildHeap → HasHeap.mreq), the machine's own capability, which only the declarations a table command emits may build: its requests name cells, closures or regions that only the machine may choose -/
#guard_msgs in
#dyn_check_rule CellErr.buildHeap

/-! A proposition never runs, so a location or the machine's capability inside one, or inside a
proof, changes no result of a rule with code (a `noncomputable` one is rejected below): a rule
may name them there, inside its own body too.  Deciding such a proposition runs, so it may
not. -/

/-- A predicate on refs that names a location. -/
def Named {σ : Type} [Store σ] (r : Ref σ Int) : Prop := r.loc = r.loc

/-- A predicate on refs that names the machine's heap capability. -/
def Asked {σ : Type} [Store σ] (r : Ref σ Int) : Prop :=
  letI : Decode σ := ⟨fun _ => Int⟩
  ∀ t : TagOf σ Int, (@HasHeap.mreq σ _ (fun _ => Int) Unit []).getReq t r =
    (@HasHeap.mreq σ _ (fun _ => Int) Unit []).getReq t r

#guard_msgs in
@[dyn_sem CellErr.named]
def named {σ : Type} [Store σ] [Decode σ] [HasHeap σ ε] [TagOf σ Int] (c : Ref σ Int) :
    Sem ε E Int :=
  let s : {r : Ref σ Int // Named r} := ⟨c, rfl⟩
  readRef s.1

#guard_msgs in
#dyn_check_rule CellErr.named

#guard_msgs in
@[dyn_sem CellErr.asked]
def asked {σ : Type} [Store σ] [Decode σ] [HasHeap σ ε] [TagOf σ Int] (c : Ref σ Int) :
    Sem ε E Int :=
  let s : {r : Ref σ Int // Asked r} := ⟨c, fun _ => rfl⟩
  readRef s.1

#guard_msgs in
#dyn_check_rule CellErr.asked

-- A proof about the operand's location, inside the rule's body.
#guard_msgs in
@[dyn_sem CellErr.provedIn]
def provedIn {σ : Type} [Store σ] [Decode σ] [HasHeap σ ε] [TagOf σ Int] (c : Ref σ Int) :
    Sem ε E Int :=
  have _h : c.loc = c.loc := rfl
  readRef c

#guard_msgs in
#dyn_check_rule CellErr.provedIn

@[dyn_sem CellErr.decided]
def decided {σ : Type} [Store σ] [Decode σ] [HasHeap σ ε] [TagOf σ Int] (c : Ref σ Int) :
    Sem ε E Int :=
  if c.loc < 3 then pure 0 else readRef c

/-- error: rule decided for cellErr.decided reaches Ref.loc (decided → Ref.loc), which tells where a ref's cell or a closure's function is; only the machine may know it, since a pass may move cells -/
#guard_msgs in
#dyn_check_rule CellErr.decided

/-- A predicate whose body its module hides, as an `opaque` one. -/
opaque Veiled : Int → Prop

-- An unapplied predicate in a type is skipped too, unlike the opaque definitions a rule runs.
#guard_msgs in
@[dyn_sem CellErr.veiledSub]
def veiledSub (x : Int) : Int := ((none : Option (@Subtype Int Veiled)).map (·.1)).getD x

#guard_msgs in
#dyn_check_rule CellErr.veiledSub

/-! A `noncomputable` rule may take a location out of a proposition, with `Classical.epsilon`.
It registers, but no table can run it (`NcSem` below). -/

#guard_msgs in
@[dyn_sem CellErr.eps]
noncomputable def eps {σ : Type} [Store σ] (c : Ref σ Int) : Int :=
  Int.ofNat (Classical.epsilon (fun (n : Nat) => n = c.loc))

#guard_msgs in
#dyn_check_rule CellErr.eps

#guard_msgs in
@[dyn_sem CellErr.classical]
noncomputable def classical {σ : Type} [Store σ] (c : Ref σ Int) : Int :=
  @ite _ (c.loc < 3) (Classical.propDecidable _) 0 1

#guard_msgs in
#dyn_check_rule CellErr.classical

@[dyn_sem CellErr.forgedEps]
noncomputable def forgedEps {σ : Type} [Store σ] (c : Ref σ Int) : Ref σ Int :=
  ⟨⟨Classical.epsilon (fun n => Store.Valid σ n),
    @Classical.epsilon_spec Nat (fun n => Store.Valid σ n) ⟨c.raw.loc, c.raw.valid⟩⟩⟩

/-- error: rule forgedEps for cellErr.forgedEps reaches Ref.Raw.mk (forgedEps → Ref.Raw.mk), which builds or takes apart a raw ref or closure; only the machine may, since a rule could point a ref at any cell, or read where it is -/
#guard_msgs in
#dyn_check_rule CellErr.forgedEps

/-! A rule can't forge a ref: its validity is a proof, which only `sorry`, an axiom of ours, or
`Classical.epsilon` in a noncomputable definition (above) can give, and the check rejects all
three, the first two inside proofs too. -/

set_option warn.sorry false in
@[dyn_sem CellErr.forged]
def forged {σ : Type} [Store σ] (_v : Int) : Ref σ Int := ⟨5, sorry⟩

/-- error: rule forged for cellErr.forged reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule CellErr.forged

@[dyn_sem CellErr.forgedAx]
def forgedAx {σ : Type} [Store σ] (_v : Int) : Ref σ Int := ⟨5, bad.elim⟩

/-- error: rule forgedAx for cellErr.forgedAx reaches the axiom bad; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule CellErr.forgedAx

@[dyn_sem CellErr.confuse]
def confuse {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasHeap σ ε] [t : TagOf σ Int]
    (c : Ref σ Int) : Sem ε E Int := do
  -- A tag of `String` that is `Int`'s, which would make the machine read an `Int` as a `String`.
  let fake : TagOf σ String := ⟨t.tag, bad.elim⟩
  let s ← @readRef σ _ _ ε E _ String fake ⟨c.loc, bad.elim⟩
  return s.length

/-- error: rule confuse for cellErr.confuse reaches the axiom bad; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_check_rule CellErr.confuse

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

/-! ## The initial world

A table checks its initial world as it checks a rule: one could forge a ref. -/

/-- A type whose values hold a ref. -/
environment Smuggle extends Base where
  namespace smuggle
  type Held
  end smuggle

#dyn_types Smuggle

/-- A ref at every token. -/
structure HeldBox (σ : Type) [Store σ] where
  cell : Ref σ Int

attribute [dyn_type Smuggle.Held] HeldBox

/-- A type whose type rule names the machine's token, and an instruction that makes one. -/
environment RunBox extends Base where
  namespace runBox
  type Box
  insn mkBox : Box
  end runBox

#dyn_types RunBox

/-- A ref at the machine's own token, `Run`, where a ref needs no axiom. -/
structure MachineBox where
  cell : Ref Run Int

attribute [dyn_type RunBox.Box] MachineBox

/-- A box with a ref to the run's first cell, made up. -/
@[dyn_sem RunBox.mkBox] def mkBox : MachineBox := ⟨⟨⟨0, trivial⟩⟩⟩

/-- error: rule mkBox for runBox.mkBox reaches Ref.Raw.mk (mkBox → Ref.Raw.mk), which builds or takes apart a raw ref or closure; only the machine may, since a rule could point a ref at any cell, or read where it is -/
#guard_msgs in
#dyn_check_rule RunBox.mkBox

/-- A world without the token, whose default holds a ref to the run's first cell, made up. -/
structure MachineWorld where
  cells : Array (Ref Run Int) := #[]

instance : Inhabited MachineWorld := ⟨{ cells := #[⟨⟨0, trivial⟩⟩] }⟩

/-- error: the initial world of MachineSem, MachineSem.w0, reaches Ref.Raw.mk (MachineSem.w0 → instInhabitedMachineWorld → Ref.Raw.mk), which builds or takes apart a raw ref or closure; only the machine may, since a rule could point a ref at any cell, or read where it is -/
#guard_msgs in
#dyn_sem_table MachineSem for Smuggle (world := MachineWorld)

/-- A world whose initial value holds a forged ref, which would alias the run's first cell. -/
structure ForgedWorld (σ : Type) [Store σ] where
  cells : Array (Ref σ Int) := #[]

set_option warn.sorry false in
instance {σ : Type} [Store σ] : Inhabited (ForgedWorld σ) := ⟨{ cells := #[⟨0, sorry⟩] }⟩

/-- error: the initial world of ForgedSem, ForgedSem.w0, reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_sem_table ForgedSem for Smuggle (world := ForgedWorld)

/-! The table checks the world parts' instances that its wrappers supply: one could forge a ref. -/

/-- An instruction that reads a world part holding refs. -/
environment PartErr extends Base where
  namespace partErr
  open base
  insn firstLoc : Int
  end partErr

#dyn_types PartErr

/-- A part that holds refs. -/
structure Cells (σ : Type) [Store σ] where
  cells : Array (Ref σ Int) := #[]

/-- A world with that part. -/
structure CellsWorld (σ : Type) [Store σ] where
  cells : Cells σ := {}

instance {σ : Type} [Store σ] : Inhabited (CellsWorld σ) := ⟨{}⟩

set_option warn.sorry false in
/-- A part instance that forges a ref on every read. -/
instance {σ : Type} [Store σ] : HasPart (CellsWorld σ) (Cells σ) :=
  ⟨fun _ => ⟨#[⟨0, sorry⟩]⟩, fun _ c => { cells := c }⟩

/-- How many refs the part holds. -/
@[dyn_sem PartErr.firstLoc]
def firstLoc {σ : Type} {ε : Eff} {E : Type} [Store σ] [HasPart ε.W (Cells σ)] :
    Sem ε E Int := do
  return (← getThe (Cells σ)).cells.size

/-- error: the table PartSem: rule firstLoc for partErr.firstLoc reaches the axiom sorryAx; a rule may reach only propext, Classical.choice and Quot.sound -/
#guard_msgs in
#dyn_sem_table PartSem for PartErr (world := CellsWorld)

/-- A number, as a part of the world. -/
structure Num where
  n : Int := 0

/-- A world whose number part is read from a cell's location. -/
structure PeekWorld (σ : Type) [Store σ] where
  cells : Cells σ := {}

instance {σ : Type} [Store σ] : Inhabited (PeekWorld σ) := ⟨{}⟩

/-- The location of `c`, through a heap capability built here. -/
def heapLoc {σ : Type} [Store σ] (c : Ref σ Int) : Int :=
  letI : Decode σ := ⟨fun _ => Int⟩
  let t : TagOf σ Int := ⟨.app 7 [], rfl⟩
  let q : MReq (fun _ => Int) [] := (@HasHeap.mreq σ _ (fun _ => Int) Unit []).getReq t c
  match q with
  | .get _ l => l
  | _ => -1

/-- A part instance that reads the first cell's location. -/
instance {σ : Type} [Store σ] : HasPart (PeekWorld σ) Num :=
  ⟨fun w => ⟨(w.cells.cells[0]?.map heapLoc).getD (-1)⟩, fun w _ => w⟩

/-- An instruction that reads the number part. -/
environment PeekErr extends Base where
  namespace peekErr
  open base
  insn num : Int
  end peekErr

#dyn_types PeekErr

/-- The number part. -/
@[dyn_sem PeekErr.num]
def num {ε : Eff} {E : Type} [HasPart ε.W Num] : Sem ε E Int := do
  return (← getThe Num).n

/-- error: the table PeekSem: rule num for peekErr.num reaches MReq.get (PeekSem.ops → PeekSem.impl.peekErr.num → PeekSem.rule.peekErr.num → instHasPartPeekWorldNum → heapLoc → peekHeap.match_1 → MReq.get), which builds or takes apart a machine request: a request holds locations, so only the handles that a table passes to a rule may build one, and only the machine reads it -/
#guard_msgs in
#dyn_sem_table PeekSem for PeekErr (world := PeekWorld)

/-! A helper named into a table's namespace before the table is not one the table emitted, so
it may not build the heap capability either. -/

/-- A world like `PeekWorld`, for a second table. -/
structure NsWorld (σ : Type) [Store σ] where
  cells : Cells σ := {}

instance {σ : Type} [Store σ] : Inhabited (NsWorld σ) := ⟨{}⟩

/-- Whether a read of `c` writes a cell, through a heap capability built right here, in a
declaration named into `NsSem` before the table: it builds the capability, and takes nothing apart. -/
def NsSem.readWrites {σ : Type} [Store σ] (c : Ref σ Int) : Int :=
  letI : Decode σ := ⟨fun _ => Int⟩
  let t : TagOf σ Int := ⟨.app 7 [], rfl⟩
  if ((@HasHeap.mreq σ _ (fun _ => Int) Unit []).getReq t c).writesCell then 1 else 0

/-- A part instance that tells, through `NsSem.readWrites`, whether a read of the first cell writes
a cell. -/
instance {σ : Type} [Store σ] : HasPart (NsWorld σ) Num :=
  ⟨fun w => ⟨(w.cells.cells[0]?.map NsSem.readWrites).getD (-1)⟩, fun w _ => w⟩

/-- error: the table NsSem: rule num for peekErr.num reaches HasHeap.mreq (NsSem.ops → NsSem.impl.peekErr.num → NsSem.rule.peekErr.num → instHasPartNsWorldNum → NsSem.readWrites → HasHeap.mreq), the machine's own capability, which only the declarations a table command emits may build: its requests name cells, closures or regions that only the machine may choose -/
#guard_msgs in
#dyn_sem_table NsSem for PeekErr (world := NsWorld)

/-! ## Closures, and code that runs other code

A rule can't rebuild a closure: its function index and its captures cell are locations. -/

/-- Instructions on closures, and ones that run other code. -/
environment CloErr extends Base where
  namespace cloErr
  open base
  insn steal (f : Fn [Int] Int) (x : Int) : Int
  insn dropCaps (f : Fn [Int] Int) (x : Int) : Int
  insn opq (x : Int) : Int
  insn print (x : Int) : Unit
  end cloErr

#dyn_types CloErr

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [HasCall σ ε] [TagOf σ Int]

@[dyn_sem CloErr.steal] def steal (f : FnRef σ [Int] Int) (x : Int) : Sem ε E Int :=
  callFn (⟨{ f.raw with captured := f.raw.captured + 1 }⟩ : FnRef σ [Int] Int) x

/-- error: rule steal for cloErr.steal reaches FnRef.Raw.captured (steal → FnRef.Raw.captured), which tells where a ref's cell or a closure's function is; only the machine may know it, since a pass may move cells -/
#guard_msgs in
#dyn_check_rule CloErr.steal

@[dyn_sem CloErr.dropCaps] def dropCaps (f : FnRef σ [Int] Int) (x : Int) : Sem ε E Int :=
  callFn (⟨⟨f.raw.idx, 0, f.raw.valid⟩⟩ : FnRef σ [Int] Int) x

/-- error: rule dropCaps for cloErr.dropCaps reaches FnRef.Raw.idx (dropCaps → FnRef.Raw.idx), which tells where a ref's cell or a closure's function is; only the machine may know it, since a pass may move cells -/
#guard_msgs in
#dyn_check_rule CloErr.dropCaps

end

/-- The code that runs for `wrapped`. -/
def wrapImpl (x : Int) : Int := x + 1000
/-- An opaque whose compiled code is `wrapImpl`. -/
@[implemented_by wrapImpl] opaque wrapped : Int → Int

@[dyn_sem CloErr.opq] def opq (x : Int) : Int := wrapped x

/-- error: rule opq for cloErr.opq reaches wrapped (opq → wrapped), which carries @[implemented_by wrapImpl]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_check_rule CloErr.opq

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

-- `print` registers: the getter is in the world's instance, which only the table gives.
#guard_msgs in
@[dyn_sem CloErr.print]
def print {ε : Eff} {E : Type} [HasPart ε.W Out] (x : Int) : Sem ε E Unit :=
  modifyThe Out fun o => { o with items := o.items.push x }

#guard_msgs in
#dyn_check_rule CloErr.print

/-! The table checks what its rules reach, with the world's instances and the swaps declared since. -/

/-- error: the table CloErrSem: rule print for cloErr.print reaches outGet (CloErrSem.ops → CloErrSem.impl.cloErr.print → CloErrSem.rule.cloErr.print → instHasPartOutWorldOut → outGet), which carries @[implemented_by outGetImpl]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_sem_table CloErrSem for CloErr (world := OutWorld)

/-- A rule whose helper gets a swap after the rule registers. -/
environment LateErr extends Base where
  namespace lateErr
  open base
  insn late (x : Int) : Int
  end lateErr

#dyn_types LateErr

/-- A helper that runs as written when `late` registers. -/
@[expose] public def lateHelper (x : Int) : Int := x
-- `late` registers.
#guard_msgs in
@[dyn_sem LateErr.late] def late (x : Int) : Int := lateHelper x

#guard_msgs in
#dyn_check_rule LateErr.late
/-- The code that runs for `lateSwap`. -/
public def lateImpl (x : Int) : Int := x + 1000
/-- `x`, compiled as `lateImpl`. -/
@[implemented_by lateImpl, expose] public def lateSwap (x : Int) : Int := x
/-- A swap of `lateHelper`, declared after `late` registers. -/
@[csimp] public theorem lateHelper_eq : @lateHelper = @lateSwap := rfl

/-- error: the table LateSem: rule late for lateErr.late reaches lateSwap (LateSem.ops → LateSem.impl.lateErr.late → LateSem.rule.lateErr.late → late → lateHelper → lateSwap), which carries @[implemented_by lateImpl]: a run executes other code than the definition proofs read; give the compiled code with a @[csimp] theorem instead -/
#guard_msgs in
#dyn_sem_table LateSem for LateErr

/-! ## Rules that no table can run -/

/-- An instruction whose rule is `noncomputable`. -/
environment NcErr extends Base where
  namespace ncErr
  open base
  insn eps (c : Ref Int) : Int
  end ncErr

#dyn_types NcErr

attribute [dyn_sem NcErr.eps] eps

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Errors.eps', which is 'noncomputable'
---
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'rule.ncErr.eps', which is 'noncomputable'
---
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'impl.ncErr.eps', which is 'noncomputable'
---
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'ops', which is 'noncomputable'
---
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'table', which is 'noncomputable'
-/
#guard_msgs in
#dyn_sem_table NcSem for NcErr

/-- An instruction whose rule is `unsafe`. -/
environment UnsErr extends Base where
  namespace unsErr
  open base
  insn unsafely (x : Int) : Int
  end unsErr

#dyn_types UnsErr

attribute [dyn_sem UnsErr.unsafely] unsafely

/--
error: the table UnsSem: rule unsafely for unsErr.unsafely reaches the axiom UnsSem.rule.unsErr.unsafely; a rule may reach only propext, Classical.choice and Quot.sound
---
error: (kernel) invalid declaration, it uses unsafe declaration '_private.StrataDynTest.Exec.RuleErrorTest.0.Strata.Dyn.ExecTest.Errors.unsafely'
---
error: Failed to find LCNF signature for _private.StrataDynTest.Exec.RuleErrorTest.0.Strata.Dyn.ExecTest.Errors.UnsSem.rule.unsErr.unsafely
---
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'impl.unsErr.unsafely', which is 'noncomputable'
-/
#guard_msgs in
#dyn_sem_table UnsSem for UnsErr

/-! ### Refs and closures retyped

A rule may not build a ref or a closure from a raw one: it could give it another type than the
machine made it at.  Every way to build one reaches `Ref.mk` or `FnRef.mk`. -/

environment RetypeErr extends Base where
  namespace retypeErr
  open base
  insn mkDirect (c : Ref Int) : Ref Bool
  insn anon (c : Ref Int) : Ref Bool
  insn struct (c : Ref Int) : Ref Bool
  insn coerced (c : Ref Int) : Ref Bool
  insn helper (c : Ref Int) : Ref Bool
  insn fnAnon (f : Fn [Int] Int) : Fn [Bool] Int
  insn fnRebuild (f : Fn [Int] Int) : Fn [Bool] Int
  insn fnInst (f : Fn [Int] Int) : Fn [Bool] Int
  end retypeErr

#dyn_types RetypeErr

section
variable {σ : Type} [Store σ]

@[dyn_sem RetypeErr.mkDirect] def mkDirect (c : Ref σ Int) : Ref σ Bool := Ref.mk c.raw

/-- error: rule mkDirect for retypeErr.mkDirect reaches Ref.mk (mkDirect → Ref.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.mkDirect

@[dyn_sem RetypeErr.anon] def anon (c : Ref σ Int) : Ref σ Bool := ⟨c.raw⟩

/-- error: rule anon for retypeErr.anon reaches Ref.mk (anon → Ref.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.anon

@[dyn_sem RetypeErr.struct] def struct (c : Ref σ Int) : Ref σ Bool := { raw := c.raw }

/-- error: rule struct for retypeErr.struct reaches Ref.mk (struct → Ref.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.struct

/-- A coercion that retypes a ref. -/
instance retypeCoe : Coe (Ref σ Int) (Ref σ Bool) := ⟨fun c => ⟨c.raw⟩⟩

@[dyn_sem RetypeErr.coerced] def coerced (c : Ref σ Int) : Ref σ Bool := c

/-- error: rule coerced for retypeErr.coerced reaches Ref.mk (coerced → Ref.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.coerced

@[dyn_sem RetypeErr.helper] def helper (c : Ref σ Int) : Ref σ Bool := ReqHelpers.retypeRef c

/-- error: rule helper for retypeErr.helper reaches Ref.mk (helper → ReqHelpers.retypeRef → Ref.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.helper

@[dyn_sem RetypeErr.fnAnon] def fnAnon (f : FnRef σ [Int] Int) : FnRef σ [Bool] Int := ⟨f.raw⟩

/-- error: rule fnAnon for retypeErr.fnAnon reaches FnRef.mk (fnAnon → FnRef.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.fnAnon

@[dyn_sem RetypeErr.fnRebuild] def fnRebuild (f : FnRef σ [Int] Int) : FnRef σ [Bool] Int :=
  match f with
  | ⟨r⟩ => ⟨r⟩

/-- error: rule fnRebuild for retypeErr.fnRebuild reaches FnRef.mk (fnRebuild → FnRef.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.fnRebuild

/-- A class whose instance retypes a closure. -/
class Retyper (σ : Type) [Store σ] where
  go : FnRef σ [Int] Int → FnRef σ [Bool] Int

instance : Retyper σ := ⟨fun f => ⟨f.raw⟩⟩

@[dyn_sem RetypeErr.fnInst] def fnInst (f : FnRef σ [Int] Int) : FnRef σ [Bool] Int :=
  Retyper.go f

/-- error: rule fnInst for retypeErr.fnInst reaches FnRef.mk (fnInst → instRetyper → FnRef.mk), which builds a ref or a closure from a raw one: it could give it another type than the machine made it at, so only the declarations that a table command emits may build one -/
#guard_msgs in
#dyn_check_rule RetypeErr.fnInst

end

/-! ### Faults that only the machine reports

A rule may stop with `semanticGap`, `semanticFailure` or `assume`, but not with a fault that only
the machine reports: it would make its own case look like the machine's. -/

environment FaultErr extends Base where
  namespace faultErr
  open base
  insn gap (x : Int) : Int
  insn failure (x : Int) : Int
  insn blocked (x : Int) : Int
  insn badCall (x : Int) : Int
  insn badCell (x : Int) : Int
  insn outOfFuel (x : Int) : Int
  insn missingRules (x : Int) : Int
  insn invalid (x : Int) : Int
  insn noFunction (x : Int) : Int
  insn helperElsewhere (x : Int) : Int
  insn swapped (x : Int) : Int
  end faultErr

#dyn_types FaultErr

section
variable {ε : Eff} {E : Type}

@[dyn_sem FaultErr.gap] def gapRule (_x : Int) : Sem ε E Int := semanticGap "gap"

#guard_msgs in
#dyn_check_rule FaultErr.gap

@[dyn_sem FaultErr.failure] def failureRule (_x : Int) : Sem ε E Int := semanticFailure "failure"

#guard_msgs in
#dyn_check_rule FaultErr.failure

@[dyn_sem FaultErr.blocked] def blockedRule (x : Int) : Sem ε E Int := do
  assume (x > 0) "blocked"
  return x

#guard_msgs in
#dyn_check_rule FaultErr.blocked

@[dyn_sem FaultErr.badCall] def badCallRule (_x : Int) : Sem ε E Int :=
  .stop (.fault (.badCall .base))

/-- error: rule badCallRule for faultErr.badCall reaches Fault.badCall (badCallRule → Fault.badCall), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.badCall

@[dyn_sem FaultErr.badCell] def badCellRule (_x : Int) : Sem ε E Int :=
  .stop (.fault (.badCell 0))

/-- error: rule badCellRule for faultErr.badCell reaches Fault.badCell (badCellRule → Fault.badCell), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.badCell

@[dyn_sem FaultErr.outOfFuel] def outOfFuelRule (_x : Int) : Sem ε E Int :=
  .stop (.fault .outOfFuel)

/-- error: rule outOfFuelRule for faultErr.outOfFuel reaches Fault.outOfFuel (outOfFuelRule → Fault.outOfFuel), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.outOfFuel

@[dyn_sem FaultErr.missingRules] def missingRulesRule (_x : Int) : Sem ε E Int :=
  .stop (.fault (.missingRules #[]))

/-- error: rule missingRulesRule for faultErr.missingRules reaches Fault.missingRules (missingRulesRule → Fault.missingRules), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.missingRules

@[dyn_sem FaultErr.invalid] def invalidRule (_x : Int) : Sem ε E Int :=
  .stop (.fault (.invalid "invalid"))

/-- error: rule invalidRule for faultErr.invalid reaches Fault.invalid (invalidRule → Fault.invalid), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.invalid

/-- A helper that stops with a fault that only the machine reports. -/
def stopNoFunction : Sem ε E Int := .stop (.fault (.noFunction .base))

@[dyn_sem FaultErr.noFunction] def noFunctionRule (_x : Int) : Sem ε E Int := stopNoFunction

/-- error: rule noFunctionRule for faultErr.noFunction reaches Fault.noFunction (noFunctionRule → stopNoFunction → Fault.noFunction), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.noFunction

@[dyn_sem FaultErr.helperElsewhere] def helperElsewhereRule (_x : Int) : Sem ε E Int :=
  Helpers.stopBadCell

/-- error: rule helperElsewhereRule for faultErr.helperElsewhere reaches Fault.badCell (helperElsewhereRule → Helpers.stopBadCell → Fault.badCell), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.helperElsewhere

/-- `semanticGap`, swapped below for `stopUnlessEq`. -/
@[expose] public def stopGap (x : Int) : Sem ε E Int := semanticGap s!"{x}"

/-- `semanticGap` too, but its code names `Fault.badCell` on a branch that never runs. -/
@[expose] public def stopUnlessEq (x : Int) : Sem ε E Int :=
  if x = x then semanticGap s!"{x}" else .stop (.fault (.badCell 0))

/-- `stopGap` is `stopUnlessEq`, so a run of `stopGap` runs `stopUnlessEq`. -/
@[csimp] public theorem stopGap_eq_stopUnlessEq : @stopGap = @stopUnlessEq := by
  funext ε E x
  simp [stopGap, stopUnlessEq]

@[dyn_sem FaultErr.swapped] def swappedRule (x : Int) : Sem ε E Int := stopGap x

/-- error: rule swappedRule for faultErr.swapped reaches Fault.badCell (swappedRule → stopGap → stopUnlessEq → Fault.badCell), a fault that only the machine reports. A case that the rules don't model stops with semanticGap. semanticFailure is only for a case the rule's author holds impossible. -/
#guard_msgs in
#dyn_check_rule FaultErr.swapped

end

end Strata.Dyn.ExecTest.Errors
