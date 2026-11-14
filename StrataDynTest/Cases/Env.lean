/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Cases
public import StrataDyn.Examples.While.Env
import StrataDyn.DSL
import StrataDyn.Env.WF

set_option autoImplicit false

/-!
# Test vocabularies for Cases

`CaseEnv` is While plus datatypes with hand-declared constructor tests and guarded field
selectors, a quantifier over the finite domain {0, 1}, a tester with a wrong rule and a
terminator that is not control. Its datatypes are a three-constructor one, a single-constructor
one and a mutually recursive pair. Every operation has a rule, so its modules run on Dyn's
engine (`CaseSem`).

`StaticEnv` extends it with what is only lowered and never run: accessors whose signatures
Cases refuses, and two datatypes that the engine's type rules do not take. One has no
constructors. The other is a mutually recursive pair of which only the first takes a type
parameter; Lean's mutual inductives share their parameters.

The accessors are declared by hand; nothing generates them yet.
-/

namespace Strata.Dyn.CasesTest

public environment CaseEnv extends While where
  namespace test
  open base
  data Choice (+a) where
    | empty
    | one (value : a)
    | pair (lhs rhs : a)
  data Only (+a) where
    | only (value : a)
  mutual
    data Rose (+a) where
      | rose (label : a) (kids : Forest a)
    data Forest (+a) where
      | grown (first : Rose a) (rest : Forest a)
      | bare
  end
  pure insn isNone [a] (v : Choice a) : Bool
  pure insn isOne [a] (v : Choice a) : Bool
  pure insn getOne [a] (v : Choice a) : a
  pure insn getLeft [a] (v : Choice a) : a
  pure insn getRight [a] (v : Choice a) : a
  pure insn getOnly [a] (v : Only a) : a
  pure insn getLabel [a] (v : Rose a) : a
  pure insn getKids [a] (v : Rose a) : Forest a
  pure insn isGrown [a] (v : Forest a) : Bool
  pure insn getFirst [a] (v : Forest a) : Rose a
  pure insn getRest [a] (v : Forest a) : Forest a
  pure insn isOk [e a] (v : Except e a) : Bool
  pure insn getOk [e a] (v : Except e a) : a
  pure insn getError [e a] (v : Except e a) : e
  pure insn isNil (v : while.IntList) : Bool
  pure insn getHead (v : while.IntList) : Int
  pure insn getTail (v : while.IntList) : while.IntList
  pure insn all (&body (x : Int) : Bool) : Bool
  pure insn same (lhs rhs : Int) : Bool
  pure insn wrongIsNone [a] (v : Choice a) : Bool
  pure terminal insn halt
  end test

#dyn_types CaseEnv

public section

namespace Rules

open Strata.Dyn.Exec
variable {ε : Eff} {E : Type}

@[dyn_sem CaseEnv.isNone] def isNone {a : Type} : CaseEnv.Choice.Val a → Bool
  | .empty => true
  | _ => false

@[dyn_sem CaseEnv.isOne] def isOne {a : Type} : CaseEnv.Choice.Val a → Bool
  | .one _ => true
  | _ => false

@[dyn_sem CaseEnv.getOne] def getOne {a : Type} : CaseEnv.Choice.Val a → Sem ε E a
  | .one v => pure v
  | _ => semanticFailure "expected one"

@[dyn_sem CaseEnv.getLeft] def getLeft {a : Type} : CaseEnv.Choice.Val a → Sem ε E a
  | .pair v _ => pure v
  | _ => semanticFailure "expected pair"

@[dyn_sem CaseEnv.getRight] def getRight {a : Type} : CaseEnv.Choice.Val a → Sem ε E a
  | .pair _ v => pure v
  | _ => semanticFailure "expected pair"

@[dyn_sem CaseEnv.getOnly] def getOnly {a : Type} : CaseEnv.Only.Val a → a
  | .only v => v

@[dyn_sem CaseEnv.getLabel] def getLabel {a : Type} : CaseEnv.Rose.Val a → a
  | .rose label _ => label

@[dyn_sem CaseEnv.getKids] def getKids {a : Type} : CaseEnv.Rose.Val a → CaseEnv.Forest.Val a
  | .rose _ kids => kids

@[dyn_sem CaseEnv.isGrown] def isGrown {a : Type} : CaseEnv.Forest.Val a → Bool
  | .grown .. => true
  | .bare => false

@[dyn_sem CaseEnv.getFirst] def getFirst {a : Type} :
    CaseEnv.Forest.Val a → Sem ε E (CaseEnv.Rose.Val a)
  | .grown first _ => pure first
  | .bare => semanticFailure "expected grown"

@[dyn_sem CaseEnv.getRest] def getRest {a : Type} :
    CaseEnv.Forest.Val a → Sem ε E (CaseEnv.Forest.Val a)
  | .grown _ rest => pure rest
  | .bare => semanticFailure "expected grown"

@[dyn_sem CaseEnv.isOk] def isOk {e a : Type} : Except e a → Bool
  | .ok _ => true
  | .error _ => false

@[dyn_sem CaseEnv.getOk] def getOk {e a : Type} : Except e a → Sem ε E a
  | .ok v => pure v
  | .error _ => semanticFailure "expected ok"

@[dyn_sem CaseEnv.getError] def getError {e a : Type} : Except e a → Sem ε E e
  | .error e => pure e
  | .ok _ => semanticFailure "expected error"

@[dyn_sem CaseEnv.isNil] def isNil : While.IntList.Val → Bool
  | .nil => true
  | .cons .. => false

@[dyn_sem CaseEnv.getHead] def getHead : While.IntList.Val → Sem ε E Int
  | .cons h _ => pure h
  | _ => semanticFailure "expected cons"

@[dyn_sem CaseEnv.getTail] def getTail : While.IntList.Val → Sem ε E While.IntList.Val
  | .cons _ t => pure t
  | _ => semanticFailure "expected cons"

@[dyn_sem CaseEnv.all] def all (body : Exec.Region ε [Int] Bool) : Sem ε E Bool := do
  return (← runRegion body 0) && (← runRegion body 1)

@[dyn_sem CaseEnv.same] def same (lhs rhs : Int) : Bool := lhs == rhs

@[dyn_sem CaseEnv.wrongIsNone] def wrongIsNone {a : Type} (_v : CaseEnv.Choice.Val a) : Bool := true

@[dyn_sem CaseEnv.halt] def halt : Sem ε E Empty := semanticFailure "test.halt"

end Rules

#dyn_coverage CaseEnv (complete)

#dyn_sem_table CaseSem for CaseEnv (world := WhileRules.World)

end

/-- Each refused accessor differs from `test.getOne` or `test.isNone` in the one respect its
name gives. -/
public environment StaticEnv extends CaseEnv where
  namespace refused
  open base test
  pure insn resultType [a] (v : Choice a) : Int
  writes insn effect [a] (v : Choice a) : a
  pure insn successor [a] (v : Choice a) (^err (code : Int)) : a
  pure insn region [a] (v : Choice a) (&body (x : Int) : Bool) : a
  pure insn secondOperand [a] (v w : Choice a) : a
  pure insn variadic [a] (*vs : Choice a) : a
  pure insn noTypeParams (v : Choice Int) : Bool
  pure insn paramOrder [a e] (v : Except e a) : e
  end refused
  namespace still
  open base
  data Never where
  mutual
    data Tagged (+a) where
      | tagged (tag : a) (inner : Untagged)
    data Untagged where
      | stop
      | step (count : Int) (next : Tagged Bool)
  end
  pure insn getTag [a] (v : Tagged a) : a
  pure insn getInner [a] (v : Tagged a) : Untagged
  pure insn isStop (v : Untagged) : Bool
  pure insn getCount (v : Untagged) : Int
  pure insn getNext (v : Untagged) : Tagged Bool
  end still

public section

private def testers : Std.HashMap Name Name := .ofList [
    (CaseEnv.Choice.empty.name, CaseEnv.isNone.name),
    (CaseEnv.Choice.one.name, CaseEnv.isOne.name),
    (CaseEnv.Forest.grown.name, CaseEnv.isGrown.name),
    (Base.Except.ok.name, CaseEnv.isOk.name),
    (While.IntList.nil.name, CaseEnv.isNil.name),
    (StaticEnv.Untagged.stop.name, StaticEnv.isStop.name)]

private def selectors : Std.HashMap (Name × String) Name := .ofList [
    ((CaseEnv.Choice.one.name, "value"), CaseEnv.getOne.name),
    ((CaseEnv.Choice.pair.name, "lhs"), CaseEnv.getLeft.name),
    ((CaseEnv.Choice.pair.name, "rhs"), CaseEnv.getRight.name),
    ((CaseEnv.Only.only.name, "value"), CaseEnv.getOnly.name),
    ((CaseEnv.Rose.rose.name, "label"), CaseEnv.getLabel.name),
    ((CaseEnv.Rose.rose.name, "kids"), CaseEnv.getKids.name),
    ((CaseEnv.Forest.grown.name, "first"), CaseEnv.getFirst.name),
    ((CaseEnv.Forest.grown.name, "rest"), CaseEnv.getRest.name),
    ((Base.Except.ok.name, "value"), CaseEnv.getOk.name),
    ((Base.Except.error.name, "err"), CaseEnv.getError.name),
    ((While.IntList.cons.name, "head"), CaseEnv.getHead.name),
    ((While.IntList.cons.name, "tail"), CaseEnv.getTail.name),
    ((StaticEnv.Tagged.tagged.name, "tag"), StaticEnv.getTag.name),
    ((StaticEnv.Tagged.tagged.name, "inner"), StaticEnv.getInner.name),
    ((StaticEnv.Untagged.step.name, "count"), StaticEnv.getCount.name),
    ((StaticEnv.Untagged.step.name, "next"), StaticEnv.getNext.name)]

/-- Accessors keyed by full constructor identities, not by their last components. -/
def ops : CaseOps where
  tester c := testers[c]?
  selector c f := selectors[(c, f)]?

end

end Strata.Dyn.CasesTest
