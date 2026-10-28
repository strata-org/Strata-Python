/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.WF
public import StrataMantle.Build
public import StrataMantle.Env.Handle
public import StrataMantleTest.DSLTest
import StrataMantle.Env.WF
import StrataMantle.DSL
-- `Env.add?` is private: a test below adds a declaration that the DSL would reject.
import all StrataMantle.Env
-- The matcher, inference and the builder run as compiled code below.
meta import StrataMantle.Build
meta import StrataMantle.Env.WF
meta import StrataMantleTest.DSLTest

set_option autoImplicit false

/-!
# Inferring type arguments from operands

The matcher on raw types, then `InsnSig.inferTypeArgs?`, then the builder, which infers an
application's type arguments from its operands' types and its result type when the result type
alone does not fix them.  Each failure sits beside the same call with what it lacks supplied.
-/

namespace Strata.Mantle.InferTest

open Strata.Mantle.DSLTest

/-! ## Matching -/

section Matching

open TypeExpr.Raw

private def intR : TypeExpr.Raw := .app (bn "Int") #[]
private def boolR : TypeExpr.Raw := .app (bn "Bool") #[]

/-- `base.Fn` of `as` and `r`. -/
private def fnR (as : Array TypeExpr.Raw) (r : TypeExpr.Raw) : TypeExpr.Raw :=
  .app (bn "Fn") #[.list as, r]

/-- What `matchAll` finds for variables of kinds `ks`, from nothing bound. -/
private def solve (ks : Array Kind) (pts : List (TypeExpr.Raw × TypeExpr.Raw)) :
    Except MatchError Subst :=
  matchAll ks pts (.replicate ks.size none)

/-- The substitution found, if any. -/
private def found (r : Except MatchError Subst) : Option Subst := r.toOption

/-- Why matching failed, if it did. -/
private def failure (r : Except MatchError Subst) : Option MatchError :=
  match r with
  | .error e => some e
  | .ok _ => none

-- A list parameter passed whole: `Fn [*as] r` at `Fn [Int, Bool] Int`.
#guard found (solve #[.list, .type] [(fnR #[.var 0] (.var 1), fnR #[intR, boolR] intR)]) ==
  some #[some (.list #[intR, boolR]), some intR]

-- Spliced after a type, taking the run the type leaves, which may be empty.
#guard found (solve #[.type, .list] [(fnR #[.var 0, .var 1] intR, fnR #[intR, boolR, boolR] intR)]) ==
  some #[some intR, some (.list #[boolR, boolR])]
#guard found (solve #[.type, .list] [(fnR #[.var 0, .var 1] intR, fnR #[intR] intR)]) ==
  some #[some intR, some (.list #[])]

-- Spliced before a type.
#guard found (solve #[.list, .type] [(fnR #[.var 0, .var 1] intR, fnR #[intR, boolR] intR)]) ==
  some #[some (.list #[intR]), some boolR]

-- One splice in each literal: a `OneSplice` pattern, which matching always solves or rejects
-- (`matchAll_complete_oneSplice`).  Two splices are not.
#guard oneSplice #[.type, .list] (fnR #[.var 0, .var 1] intR)
#guard oneSplice #[.list, .list] (fnR #[.var 0] (fnR #[.var 1] intR))
#guard !oneSplice #[.list, .list] (fnR #[.var 0, .var 1] intR)

-- Two splices are ambiguous, unless an earlier pair fixes one of them.
#guard failure (solve #[.list, .list] [(fnR #[.var 0, .var 1] intR, fnR #[intR, boolR] intR)]) ==
  some (.ambiguous [0, 1])
#guard found (solve #[.list, .list]
    [(fnR #[.var 0] intR, fnR #[intR] intR),
     (fnR #[.var 0, .var 1] intR, fnR #[intR, boolR] intR)]) ==
  some #[some (.list #[intR]), some (.list #[boolR])]

-- Environment well-formedness does not ask for one splice per literal: `Base.env` accepts
-- `insn two [as : list, bs : list] (f : Fn [*as, *bs] Int) : Int`.  Matching its operand's
-- type against `Fn [] Int` reports an ambiguity, as `matchAll_complete` allows for any pattern.
private def twoDecl : InsnDecl.Raw Unit :=
  { ann := (), name := bn "two", typeParams := #[⟨"as", .list⟩, ⟨"bs", .list⟩]
    argTypes := #[⟨"f", fnR #[.var 0, .var 1] intR⟩], returnType := some intR }
#guard (Base.env.add? (.insn twoDecl)).isSome
#guard failure (solve #[.list, .list] [(fnR #[.var 0, .var 1] intR, fnR #[] intR)]) ==
  some (.ambiguous [0, 1])

-- A variable used twice binds once and must agree.
#guard found (solve #[.type] [(fnR #[.var 0] (.var 0), fnR #[intR] intR)]) ==
  some #[some intR]
#guard failure (solve #[.type] [(fnR #[.var 0] (.var 0), fnR #[intR] boolR)]) ==
  some .mismatch

-- Too few elements for the fixed ones, and another constructor, do not match.
#guard failure (solve #[.type, .type] [(fnR #[.var 0, .var 1] intR, fnR #[intR] intR)]) ==
  some .mismatch
#guard failure (solve #[.type] [(fnR #[.var 0] intR, .app (bn "Ref") #[intR])]) ==
  some .mismatch

end Matching

/-! ## Inference -/

/-- An instruction whose type argument nothing fixes.  (The DSL lets a literal splice one list
parameter, so a signature it declares is never ambiguous; the matcher's tests above cover
two.) -/
private environment Ops extends Fns where
  namespace ops
  open base
  /-- `a` occurs nowhere but in the type arguments. -/
  insn phantom [a] (x : Int) : Int
  end ops

private def intT : TypeExpr Ops.env := Base.Int
private def boolT : TypeExpr Ops.env := Base.Bool
private def fnT (as : Array (TypeExpr Ops.env)) (r : TypeExpr Ops.env) : TypeExpr Ops.env :=
  Base.Fn (TypeList.ofTypes as) r

/-- The arguments `inferTypeArgs?` gives an application of `isig`, if any. -/
private def inferred {isig : InsnSig Ops.env} (_r : InsnRef Ops.env isig)
    (result? : Option (TypeExpr Ops.env)) (ops : Array (TypeExpr Ops.env)) :
    Option (Array (TypeArg Ops.env)) :=
  ((isig.inferTypeArgs? result? ops).map (·.args)).toOption

/-- Why `inferTypeArgs?` gives an application of `isig` no arguments, if it does not. -/
private def notInferred {isig : InsnSig Ops.env} (_r : InsnRef Ops.env isig)
    (result? : Option (TypeExpr Ops.env)) (ops : Array (TypeExpr Ops.env)) : Option String :=
  match isig.inferTypeArgs? result? ops with
  | .ok _ => none
  | .error e => some (e.text "it")

-- `callCode`'s list comes from its function's type, and its spread checks against it.
#guard inferred Base.callCode (some intT) #[fnT #[intT, boolT] intT, intT, boolT] ==
  some #[.list (.ofTypes #[intT, boolT]), .ty intT]
-- With no result type given, the function's type gives `r` too.
#guard inferred Base.callCode none #[fnT #[intT, boolT] intT, intT, boolT] ==
  some #[.list (.ofTypes #[intT, boolT]), .ty intT]
-- An operand of the wrong type, or one too many, fits no arguments.
#guard notInferred Base.callCode (some intT) #[fnT #[intT, boolT] intT, intT, intT] ==
  some "cannot infer the type arguments of it: the types of its operands and result do not fit its signature"
#guard notInferred Base.callCode (some intT) #[fnT #[intT] intT, intT, intT] ==
  some "cannot infer the type arguments of it: the types of its operands and result do not fit its signature"

-- `refSet`'s cell type gives `a`, and `Except.case`'s scrutinee gives `e` and `a`.
#guard inferred Base.refSet (some Base.Unit) #[Base.Ref intT, intT] == some #[.ty intT]
#guard inferred Base.Except.case none #[Base.Except boolT intT] == some #[.ty boolT, .ty intT]

-- What nothing fixes is reported by name.
#guard notInferred Ops.phantom (some intT) #[intT] ==
  some "cannot infer type argument(s) `a` of it: they occur in no operand's type and not in its result type; pass them with `(typeArgs := ta[…])`"

/-! ## The builder

With no `ta[…]`, the builder infers what the result type does not fix when it runs.  What it
cannot infer is a misuse, which names the instruction and says to write the arguments. -/

open Build (freshVal startFreshBlock emitApply terminate finishBlock build goto freshLabel
  startBlock FailedFunc)

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc Ops.env Unit Unit) {fn : Func Ops.env Unit // fn.WF}

/-- The misuses a build fails with, or none. -/
private def misuses (f : Built) : Array String :=
  match f with
  | .ok _ => #[]
  | .error e => e.misuses

/-- `f(%g : Fn [Int, Bool] Int, %x : Int, %y : Bool) : Int`, returning `callCode(%g, ops)`. -/
private def call (ops : Array Nat) : Built :=
  build (.str .base "f") intT () do
    let g ← freshVal (.str .base "g") (fnT #[intT, boolT] intT)
    let x ← freshVal (.str .base "x") intT
    let y ← freshVal (.str .base "y") boolT
    let _ ← startFreshBlock #[g, x, y] "entry"
    let ps := #[g.id, x.id, y.id]
    let r ← emitApply (.str .base "r") intT Base.callCode (#[g.id] ++ ops.filterMap (ps[·]?))
    finishBlock (.ret () r)

#guard (call #[1, 2]).isOk
#guard misuses (call #[1, 1]) ==
  #["cannot infer the type arguments of base.callCode: the types of its operands and result do not fit its signature"]

/-- `f(%x : Int) : Int`, returning `phantom(%x)`, with `ta` its type arguments. -/
private def phantom (ta : TypeArgsOf (Ops.phantom (e := Ops.env)) (some intT)) : Built :=
  build (.str .base "f") intT () do
    let x ← freshVal (.str .base "x") intT
    let _ ← startFreshBlock #[x] "entry"
    let r ← emitApply (.str .base "r") intT Ops.phantom #[x.id] (typeArgs := ta)
    finishBlock (.ret () r)

#guard (phantom ta[Base.Bool]).isOk
#guard misuses (phantom .infer) ==
  #["cannot infer type argument(s) `a` of ops.phantom: they occur in no operand's type and not in its result type; pass them with `(typeArgs := ta[…])`"]

-- With no `ta[…]`, the same call does not compile: `a` occurs in no operand's type of the
-- signature, so the compiler can tell, beside the call with `ta[…]`, which compiles.
/--
error: could not synthesize default value for parameter 'typeArgs' using tactics
---
error: cannot infer type argument(s) `a` of Ops.phantom: they occur in no operand's type and not in its result type; pass them with `(typeArgs := ta[…])`
-/
#guard_msgs in
example (x : ValId) : BuildM Ops.env Unit ValId :=
  emitApply (.str .base "r") intT Ops.phantom #[x]
example (x : ValId) : BuildM Ops.env Unit ValId :=
  emitApply (.str .base "r") intT Ops.phantom #[x] (typeArgs := ta[Base.Bool])

/-- `f(%e : Except Bool Int) : Int`: `Except.case` of `%e`, with no `ta[…]`, its `ok` value
returned and its `error` replaced by `0`. -/
private def caseOf : Built :=
  build (.str .base "f") intT () do
    let e ← freshVal (.str .base "e") (Base.Except boolT intT)
    let _ ← startFreshBlock #[e] "entry"
    let ok ← freshLabel "ok"
    let err ← freshLabel "err"
    terminate Base.Except.case #[e.id] #[goto ok, goto err]
    let v ← freshVal (.str .base "v") intT
    startBlock ok #[v]
    finishBlock (.ret () v.id)
    let b ← freshVal (.str .base "b") boolT
    startBlock err #[b]
    finishBlock (.ret () (← Build.emitConst (.str .base "z") (.int 0)))

#guard caseOf.isOk

end Strata.Mantle.InferTest
