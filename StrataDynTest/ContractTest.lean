/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.WF
public import StrataDyn.Build
public import StrataDyn.DDM
public import StrataDyn.DDMRead
import StrataDyn.Build.Typed
import StrataDyn.Env.WF
import StrataDyn.DSL
import StrataDynTest.WFParts
-- The builder, the checker, the printer and the reader run as compiled code below.
meta import StrataDyn.Build
meta import StrataDyn.Build.Typed
meta import StrataDyn.DDM
meta import StrataDyn.DDMRead
meta import StrataDyn.WF
meta import StrataDyn.Env.WF
meta import StrataDynTest.WFParts

set_option autoImplicit false

/-!
# Contracts

A function with a `requires` and an `ensures` clause is emitted, checked, printed and read
back.  Then the mistakes the contract rules reject, from the builder and from the reader.
-/

namespace Strata.Dyn.ContractTest

open Strata.Dyn.WFParts (broken failing)

/-- Integer addition and comparison over the base. -/
public environment Spec extends Base where
  namespace spec
  open base
  /-- `lhs + rhs`. -/
  pure insn add (lhs rhs : Int) : Int
  /-- `lhs ≥ rhs`. -/
  pure insn ge (lhs rhs : Int) : Bool
  /-- Run `then` if `cond` holds, else `else`. -/
  pure insn «if» [a] (cond : Bool) (&«then» &«else» : a) : a
  /-- Whether `f` is a code pointer: an operation that takes one and reads no state. -/
  pure insn isFn (f : Fn [Int] Bool) : Bool
  end spec

open Strata.Dyn.Build (freshVal emitConst emitFunc emitApply finishBlock build FailedFunc region)
open Strata.Dyn.Build.Raw (startBlock startFreshBlock freshLabel goto)

private abbrev E := Spec.env

/-- What `build` gives: a checked function, or the `FailedFunc`. -/
private abbrev Built := Except (FailedFunc E Unit Unit) {fn : Func E Unit // fn.WF}

private def boolT : TypeExpr E := Base.Bool
private def intT : TypeExpr E := Base.Int

private def nm (s : String) : Name := .str .base s

/-! ## A function with a contract

`inc(x) = x + 1`, which requires `x ≥ 0` and ensures that its result is at least `x`.  The
body is emitted first and the contract after it, so the ids follow `Func.defs`: the function
is canonical. -/

/-- `inc`, with `pre` and `post` its contract, emitted after the body. -/
private def incWith (pre : ValId → ValId → BuildM E Unit Unit)
    (post : ValId → ValId → BuildM E Unit Unit) (resT : TypeExpr E := intT) : Built :=
  build (.str (nm "m") "inc") intT () do
    let x ← freshVal (nm "x") intT
    let _ ← startFreshBlock #[x] "entry"
    let one ← emitConst (nm "one") (.int 1)
    let s ← emitApply (nm "s") intT Spec.add.ref #[x.id, one]
    finishBlock (.ret () s)
    Build.requires (pre x.id s)
    Build.ensures (nm "r") resT (post x.id)

/-- `x ≥ 0`. -/
private def nonNeg (x : ValId) : BuildM E Unit Unit := do
  let zero ← emitConst (nm "zero") (.int 0)
  finishBlock (.ret () (← emitApply (nm "ok") boolT Spec.ge.ref #[x, zero]))

/-- `r ≥ x`. -/
private def atLeast (x r : ValId) : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitApply (nm "ok") boolT Spec.ge.ref #[r, x]))

private def inc : Built := incWith (fun x _ => nonNeg x) atLeast

#guard inc.isOk

#guard inc.toOption.any (decide ·.val.Canonical)

-- `Func.map` keeps the contract's clauses: the mapped function prints the same.
#guard inc.toOption.any fun f => (f.val.map fun _ => ({} : Info)).format .full == f.val.format .full

/-- The printed form of `inc`, folded. -/
private def incText : String := "module contracts {
  func @m.inc(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
    ensures {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = spec.ge(%r.0, %x.0)
        ret(%ok.1)
    }
  {
    entry.0(%x.0 : base.Int):
      %s.0 : base.Int = spec.add(%x.0, 1)
      ret(%s.0)
  }
}
"

/-- info: module contracts {
  func @m.inc(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
    ensures {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = spec.ge(%r.0, %x.0)
        ret(%ok.1)
    }
  {
    entry.0(%x.0 : base.Int):
      %s.0 : base.Int = spec.add(%x.0, 1)
      ret(%s.0)
  }
} -/
#guard_msgs in
#eval do
  match Module.ofChecked (nm "contracts") #[← IO.ofExcept inc] () with
  | .ok m => IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

/-- Read `text` in `Spec.env`, and print the module in full and folded, or the diagnostics. -/
private def roundTrip (text : String) : IO Unit := do
  match ← Module.read Spec.env text "t.dyn" with
  | .error e => IO.println e
  | .ok m =>
    IO.println (m.format .full)
    IO.println (toString m)

-- Reading the printed `inc` gives it back, in both forms.  The folded constants of the
-- contract are read as constants of the contract.
/-- info: module contracts {
  func @m.inc(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %c.1 : base.Int = const 0
        %ok.0 : base.Bool = spec.ge(%x.0, %c.1)
        ret(%ok.0)
    }
    ensures {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = spec.ge(%r.0, %x.0)
        ret(%ok.1)
    }
  {
    entry.0(%x.0 : base.Int):
      %c.0 : base.Int = const 1
      %s.0 : base.Int = spec.add(%x.0, %c.0)
      ret(%s.0)
  }
}

module contracts {
  func @m.inc(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
    ensures {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = spec.ge(%r.0, %x.0)
        ret(%ok.1)
    }
  {
    entry.0(%x.0 : base.Int):
      %s.0 : base.Int = spec.add(%x.0, 1)
      ret(%s.0)
  }
} -/
#guard_msgs in
#eval roundTrip incText

-- What reading gives is canonical: the body's values first, then the contract's.
#guard_msgs in
#eval do
  match ← Module.read Spec.env incText with
  | .error e => IO.println e
  | .ok m => unless m.raw.funcs.all (decide ·.Canonical) do IO.println "not canonical"

-- A clause may hold an operation with regions of its own.
/-- info: module m {
  func @m.f(%c.0 : base.Bool, %x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %v.0 : base.Bool = spec.if[base.Bool](%c.0) {
          then.0():
            %ok.0 : base.Bool = spec.ge(%x.0, 0)
            ret(%ok.0)
        } {
          else.0():
            ret(true)
        }
        ret(%v.0)
    }
  {
    entry.0(%c.0 : base.Bool, %x.0 : base.Int):
      ret(%x.0)
  }
} -/
#guard_msgs in
#eval do
  match ← Module.read Spec.env "module m {
  func @m.f(%c.0 : base.Bool, %x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %v.0 : base.Bool = spec.if[base.Bool](%c.0) {
          then.0():
            %ok.0 : base.Bool = spec.ge(%x.0, 0)
            ret(%ok.0)
        } {
          else.0():
            ret(true)
        }
        ret(%v.0)
    }
  {
    entry.0(%c.0 : base.Bool, %x.0 : base.Int):
      ret(%x.0)
  }
}
" with
  | .error e => IO.println e
  | .ok m => IO.println m

-- A clause may name a function of the module through a `pure` operation, and a function may
-- call one with a contract.
#guard_msgs in
#eval do
  let text := "module m {
  func @m.pos(%x.0 : base.Int) -> base.Bool
    requires {
      pre.0():
        %ok.0 : base.Bool = spec.isFn(@m.pos)
        ret(%ok.0)
    }
  {
    entry.0(%x.0 : base.Int):
      ret(true)
  }
  func @m.apply(%x.0 : base.Int) -> base.Bool {
    entry.0(%x.0 : base.Int):
      %r.0 : base.Bool = base.callCode[[base.Int], base.Bool](@m.pos, %x.0)
      ret(%r.0)
  }
}
"
  match ← Module.read Spec.env text with
  | .error e => IO.println e
  | .ok m => unless toString m == text do IO.println m

-- Several clauses of each kind, and a clause with blocks of its own.
/-- info: module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %a.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%a.0)
    }
    requires {
      pre.1():
        jump ^more.0(%y.0)
      more.0(%v.0 : base.Int):
        %b.0 : base.Bool = spec.ge(%v.0, %x.0)
        ret(%b.0)
    }
    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }
    ensures {
      post.1(%r.1 : base.Int):
        %d.0 : base.Bool = spec.ge(%r.1, %y.0)
        ret(%d.0)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%y.0)
  }
} -/
#guard_msgs in
#eval do
  match ← Module.read Spec.env "module m {
  func @m.f(%x.0 : base.Int, %y.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %a.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%a.0)
    }
    requires {
      pre.1():
        jump ^more.0(%y.0)
      more.0(%v.0 : base.Int):
        %b.0 : base.Bool = spec.ge(%v.0, %x.0)
        ret(%b.0)
    }
    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }
    ensures {
      post.1(%r.1 : base.Int):
        %d.0 : base.Bool = spec.ge(%r.1, %y.0)
        ret(%d.0)
    }
  {
    entry.0(%x.0 : base.Int, %y.0 : base.Int):
      ret(%y.0)
  }
}
" with
  | .error e => IO.println e
  | .ok m => IO.println m

-- The labels of the body and of the contract are numbered together when the function is
-- finished.  Here the body's block `pre`, allocated `bb.0` and labelled by `named`, comes before
-- the clause, so it is `pre.0`, and the clause's entry, allocated `pre.0`, is `pre.1`.
/-- info: module m {
  func @m.f() -> base.Int
    requires {
      pre.1():
        ret(true)
    }
  {
    entry.0():
      jump ^pre.0()
    pre.0():
      ret(0)
  }
} -/
#guard_msgs in
#eval do
  let f ← IO.ofExcept <| build (.str (nm "m") "f") intT () do
    let _ ← startFreshBlock #[] "entry"
    let pre ← Build.named "pre" (Emit.freshLabel [] : BuildM E Unit (BlockRef E []))
    finishBlock (.jump () (goto pre.label))
    startBlock pre.label
    finishBlock (.ret () (← emitConst (nm "zero") (.int 0)))
    Build.requires (do finishBlock (.ret () (← emitConst (nm "t") (.bool true))))
  match Module.ofChecked (nm "m") #[f] () with
  | .ok m => IO.print m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

/-! ## What the builder rejects -/

-- A `requires` clause that returns an integer, not a `base.Bool`.
#guard failing (incWith (fun x _ => finishBlock (.ret () x)) atLeast) == ["contract"]

-- An `ensures` clause that returns an integer.
#guard failing (incWith (fun x _ => nonNeg x) (fun _ r => finishBlock (.ret () r))) == ["contract"]

-- An `ensures` clause whose argument is not of the function's return type.
#guard failing (incWith (fun x _ => nonNeg x)
  (fun _ _ => do finishBlock (.ret () (← emitConst (nm "t") (.bool true)))) (resT := boolT)) == ["contract"]

-- A clause that uses a value of the body: it sees only the parameters and its own values.
#guard failing (incWith (fun _ s => nonNeg s) atLeast) == ["contract"]

-- A clause transfers only among its own blocks, never to a block of the body, here `done`.
#guard failing (build (.str (nm "m") "f") intT () do
  let x ← freshVal (nm "x") intT
  let _ ← startFreshBlock #[x] "entry"
  let done ← freshLabel "done"
  finishBlock (.jump () (goto done))
  startBlock done
  finishBlock (.ret () x.id)
  Build.requires (finishBlock (.jump () (goto done)))) == ["contract"]

-- A clause is scoped as a body of its own: here `v`, defined in `a`, is used in `d`, which the
-- clause's entry reaches through `b`, avoiding `a`.
#guard failing (incWith (fun x _ => do
  let a ← freshLabel "a"
  let b ← freshLabel "b"
  let d ← freshLabel "d"
  let c ← emitApply (nm "c") boolT Spec.ge.ref #[x, ← emitConst (nm "zero") (.int 0)]
  finishBlock (.branch () c (goto a) (goto b))
  startBlock a
  let v ← emitApply (nm "v") boolT Spec.ge.ref #[x, ← emitConst (nm "one") (.int 1)]
  finishBlock (.jump () (goto d))
  startBlock b
  finishBlock (.jump () (goto d))
  startBlock d
  finishBlock (.ret () v)) atLeast) == ["contract"]

-- The body does not see the contract's values.
#guard failing (build (.str (nm "m") "f") intT () do
  let x ← freshVal (nm "x") intT
  Build.requires (nonNeg x.id)
  let _ ← startFreshBlock #[x] "entry"
  -- `%zero.0`, the clause's constant.
  finishBlock (.ret () ⟨1⟩)) == ["scoping"]

-- A clause's value may not share an id with a body value: here `%one.0`'s, 1.
#guard failing (incWith (fun x _ => do
  let _ ← Build.emit ⟨⟨1⟩, boolT⟩ (.const () ⟨⟨1⟩, boolT⟩ (.bool true))
  nonNeg x) atLeast) == ["body", "contract"]

-- A clause's labels count with the body's: the builder refuses a label used twice, and the
-- checker rejects a function whose clause has a block labelled like the body's entry.
#guard match incWith (fun x _ => do
    finishBlock (.jump () (goto ⟨.num (nm "entry") 0⟩))
    startBlock ⟨.num (nm "entry") 0⟩
    nonNeg x) atLeast with
  | .error e => e.misuses == #["block entry.0 opened twice: its label is already used"]
  | .ok _ => false

#guard inc.toOption.any fun f =>
  let relabel (c : Clause E Unit) : Clause E Unit :=
    { c with region := ⟨c.region.blocks.map ({ · with label := ⟨.num (nm "entry") 0⟩ })⟩ }
  let g : Func E Unit := { f.val with contract.requires := f.val.contract.requires.map relabel }
  !decide (Label.Distinct (Label.exit :: g.labels)) && decide g.BodyWF && decide g.ContractWF

-- A clause may name only functions of the module.
#guard match incWith (fun x _ => do
    let _ ← emitFunc (nm "missing") (Base.Fn (TypeList.ofTypes #[]) intT); nonNeg x) atLeast with
  | .ok f => match Module.ofChecked (nm "m") #[f] () with
    | .error bad => bad.map ToDDM.nameText == #["m.inc"]
    | .ok _ => false
  | .error _ => false

-- A clause applies no operation declared `writes`, such as `base.refSet`: it is rejected in a
-- clause, at any depth, and accepted in the body.
/-- `f(c)`, over the cell `c`, whose body is `body c` and whose `requires` clause is `pre c`. -/
private def cellFn (body pre : ValId → BuildM E Unit Unit) : Built :=
  build (.str (nm "m") "f") intT () do
    let c ← freshVal (nm "c") (Base.Ref intT)
    let _ ← startFreshBlock #[c] "entry"
    body c.id
    Build.requires (pre c.id)

/-- `c := 0`, then return `v` from `ret`. -/
private def setZero (c : ValId) (ret : ValId → BuildM E Unit Unit) : BuildM E Unit Unit := do
  let zero ← emitConst (nm "zero") (.int 0)
  let _ ← emitApply (nm "u") Base.Unit Base.refSet.ref (typeArgs := ta[intT]) #[c, zero]
  ret zero

private def retTrue : BuildM E Unit Unit := do
  finishBlock (.ret () (← emitConst (nm "t") (.bool true)))

/-- info: module m.f {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    requires {
      pre.0():
        %t.0 : base.Bool = const true
        ret(%t.0)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      %zero.0 : base.Int = const 0
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %zero.0)
      ret(%zero.0)
  }
} -/
#guard_msgs in
#eval do
  let f ← IO.ofExcept <|
    cellFn (fun c => setZero c fun z => finishBlock (.ret () z)) fun _ => retTrue
  IO.print (f.val.format .full)

#guard failing (cellFn (fun _ => do finishBlock (.ret () (← emitConst (nm "z") (.int 0))))
  fun c => setZero c fun _ => retTrue) == ["contract"]

#guard failing (cellFn (fun _ => do finishBlock (.ret () (← emitConst (nm "z") (.int 0))))
  fun c => do
    let t ← emitConst (nm "t") (.bool true)
    let thn := region #[] (base := "then") (setZero c fun _ => retTrue)
    let els := region #[] (base := "else") retTrue
    finishBlock (.ret () (← emitApply (nm "v") boolT Spec.«if».ref #[t] (regions := #[thn, els])))) ==
  ["contract"]

-- A `requires` clause comes before the `ensures` clauses.
#guard match build (.str (nm "m") "f") intT () (do
    let x ← freshVal (nm "x") intT
    let _ ← startFreshBlock #[x] "entry"
    finishBlock (.ret () x.id)
    Build.ensures (nm "r") intT (atLeast x.id)
    Build.requires (nonNeg x.id)) with
  | .error e => e.misuses == #["a requires clause after an ensures clause"]
  | .ok _ => false

-- A clause that leaves a block open is a misuse.
#guard match incWith (fun _ _ => do let _ ← emitConst (nm "zero") (.int 0)) atLeast with
  | .error e => e.misuses == #["region pre ends with block pre.0 open"]
  | .ok _ => false

/-! ## What the reader rejects -/

/-- Read `text` in `Spec.env` and print the diagnostics, or that it was read. -/
private def readErrors (text : String) : IO Unit := do
  match ← Module.read Spec.env text "t.dyn" with
  | .error e => IO.println e
  | .ok _ => IO.println "read"

/-- `@m.f(x) -> base.Int` with the contract `clauses` and the body `ret(%x.0)`. -/
private def withClauses (clauses : String) : String := s!"module m \{
  func @m.f(%x.0 : base.Int) -> base.Int
{clauses}
  \{
    entry.0(%x.0 : base.Int):
      %s.0 : base.Int = spec.add(%x.0, 1)
      ret(%s.0)
  }
}
"

/-- info: t.dyn:3:13: the region's entry block takes (base.Int), but () is expected -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0(%y.0 : base.Int):
        ret(true)
    }")

/-- info: t.dyn:3:12: the region's entry block takes (), but (base.Int) is expected -/
#guard_msgs in
#eval readErrors (withClauses "    ensures {
      post.0():
        ret(true)
    }")

/-- info: t.dyn:5:12: %x.0 has type base.Int, but ret, operand 1 takes base.Bool -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        ret(%x.0)
    }")

/-- info: t.dyn:5:36: a contract of @m.f uses %s.0, which is neither a parameter of @m.f nor defined in the clause -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%s.0, 0)
        ret(%ok.0)
    }")

/-- info: t.dyn:5:8: a contract region of @m.f may not change state, but base.refSet is declared writes -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%c.0 : base.Ref(base.Int)) -> base.Int
    requires {
      pre.0():
        %u.0 : base.Unit = base.refSet[base.Int](%c.0, 0)
        ret(true)
    }
  {
    entry.0(%c.0 : base.Ref(base.Int)):
      ret(0)
  }
}
"

-- A clause may not call a function: `base.callCode` is declared `writes`.
/-- info: t.dyn:5:8: a contract region of @m.f may not change state, but base.callCode is declared writes -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%x.0 : base.Int) -> base.Bool
    requires {
      pre.0():
        %r.0 : base.Bool = base.callCode[[base.Int], base.Bool](@m.f, %x.0)
        ret(%r.0)
    }
  {
    entry.0(%x.0 : base.Int):
      ret(true)
  }
}
"

-- A value of another clause is not visible either, whichever comes first.
/-- info: t.dyn:9:36: a contract of @m.f uses %r.0, which is neither a parameter of @m.f nor defined in the clause -/
#guard_msgs in
#eval readErrors (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }
    ensures {
      post.1(%r.1 : base.Int):
        %ok.0 : base.Bool = spec.ge(%r.0, %r.1)
        ret(%ok.0)
    }")

/-- info: t.dyn:5:36: %r.1 is not defined in its clause -/
#guard_msgs in
#eval readErrors (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        %ok.0 : base.Bool = spec.ge(%r.1, %r.0)
        ret(%ok.0)
    }
    ensures {
      post.1(%r.1 : base.Int):
        ret(true)
    }")

/-- info: t.dyn:7:4: a requires clause must come before the ensures clauses -/
#guard_msgs in
#eval readErrors (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }
    requires {
      pre.0():
        ret(true)
    }")

-- The body does not see the contract's values either.
/-- info: t.dyn:12:10: the body of @m.f uses %ok.0, a value of its contract -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%x.0 : base.Int) -> base.Bool
    requires {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
  {
    entry.0(%x.0 : base.Int):
      jump ^done.0()
    done.0():
      ret(%ok.0)
  }
}
"

-- A scope error comes before a type error.
/-- info: t.dyn:12:33: the body of @m.f uses %ok.0, a value of its contract -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
  {
    entry.0(%x.0 : base.Int):
      jump ^done.0()
    done.0():
      %s.0 : base.Int = spec.add(%ok.0, 1)
      ret(%s.0)
  }
}
"

-- `requires`, `ensures`, `reads`, `writes`, `extern` and `free` are keywords, so a one-segment
-- name spelled like one of them reads only pipe-delimited, and prints so.
/-- info: t.dyn:1:6: unexpected token 'requires'; expected Dyn.MName
t.dyn:1:6: unexpected token 'ensures'; expected Dyn.MName
t.dyn:1:6: unexpected token 'reads'; expected Dyn.MName
t.dyn:1:6: unexpected token 'writes'; expected Dyn.MName
t.dyn:1:6: unexpected token 'extern'; expected Dyn.MName
t.dyn:1:6: unexpected token 'free'; expected Dyn.MName -/
#guard_msgs in
#eval show IO Unit from do
  for k in ["requires", "ensures", "reads", "writes", "extern", "free"] do
    readErrors s!"module {k} \{\n}\n"

/-- info: module |requires| {
}
module |ensures| {
}
module |reads| {
}
module |writes| {
}
module |extern| {
}
module |free| {
} -/
#guard_msgs in
#eval show IO Unit from do
  for k in ["requires", "ensures", "reads", "writes", "extern", "free"] do
    match ← Module.read Spec.env s!"module |{k}| \{\n}\n" with
    | .error e => IO.println e
    | .ok m => IO.print m

-- A clause's labels count with the body's.
/-- info: t.dyn:4:6: block entry.0 is defined twice -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      entry.0():
        ret(true)
    }")

-- A clause transfers only among its own blocks, never to a block of the body.
/-- info: t.dyn:5:13: no block done.0 to transfer to here -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        jump ^done.0()
    }
  {
    entry.0(%x.0 : base.Int):
      jump ^done.0()
    done.0():
      ret(%x.0)
  }
}
"

/-! ### Scoping in a clause

A clause is scoped as a body of its own, entered where only the parameters are visible: each of
its blocks is reachable from its entry, and each use in it is dominated by its definition.  The
reader names each block and each use that breaks this. -/

-- A use on a path that avoids its definition.
/-- info: t.dyn:2:2: @m.f is not well formed
  in a requires clause, `%v.0` (defined in `a.0`) is used in `d.0`, reachable via `pre.0 → b.0 → d.0` without it -/
#guard_msgs in
#eval readErrors (withClauses "    requires {
      pre.0():
        %c.0 : base.Bool = spec.ge(%x.0, 0)
        branch(%c.0) ^a.0() ^b.0()
      a.0():
        %v.0 : base.Bool = spec.ge(%x.0, 1)
        jump ^d.0()
      b.0():
        jump ^d.0()
      d.0():
        ret(%v.0)
    }")

-- A block that the clause's entry does not reach.  The builder drops such a block, so only the
-- reader meets one.
/-- info: t.dyn:2:2: @m.f is not well formed
  in an ensures clause, block `dead.0` is unreachable from the entry -/
#guard_msgs in
#eval readErrors (withClauses "    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
      dead.0():
        ret(false)
    }")

-- The same in a `free ensures` clause of an extern.
/-- info: t.dyn:2:2: @m.g is not well formed
  in a free ensures clause, block `dead.0` is unreachable from the entry -/
#guard_msgs in
#eval readErrors "module m {
  extern func @m.g(%x.0 : base.Int) -> base.Int
    free ensures {
      post.0(%r.0 : base.Int):
        ret(true)
      dead.0():
        ret(false)
    }
}
"

/-! ## Frames

`bump(c, k)` adds `k` to the cell `c` and returns the new contents.  It reads and writes `c`,
and no other cell.  A `reads` or `writes` clause is a frame: it names cells among the
parameters.  A function without a `reads` clause may read any cell, and one with `reads()`
reads none. -/

private def refIntT : TypeExpr E := Base.Ref intT
private def unitT : TypeExpr E := Base.Unit

/-- `bump`, with the frames `reads` and `writes` of its parameters `c` and `k`, if given. -/
private def bumpWith (reads writes : Option (ValId → ValId → Array ValId)) : Built :=
  build (.str (nm "m") "bump") intT () do
    let c ← freshVal (nm "c") refIntT
    let k ← freshVal (nm "k") intT
    let _ ← startFreshBlock #[c, k] "entry"
    let v ← emitApply (nm "v") intT Base.refGet.ref #[c.id]
    let s ← emitApply (nm "s") intT Spec.add.ref #[v, k.id]
    let _ ← emitApply (nm "u") unitT Base.refSet.ref (typeArgs := ta[intT]) #[c.id, s]
    finishBlock (.ret () s)
    Build.requires (nonNeg k.id)
    if let some r := reads then Build.reads ((r c.id k.id).map .cell)
    if let some w := writes then Build.writes ((w c.id k.id).map .cell)

private def bump : Built := bumpWith (some fun c _ => #[c]) (some fun c _ => #[c])

#guard bump.isOk

#guard bump.toOption.any (decide ·.val.Canonical)

/-- The cell each entry of a frame names, or `none` for a region. -/
private def cellsOf {α : Type} (frame : Option (Array (FrameEntry E α))) :
    Option (Array (Option ValId)) :=
  frame.map (·.map FrameEntry.cell?)

#guard bump.toOption.any fun f =>
  cellsOf f.val.contract.reads == some #[some ⟨0⟩] &&
    cellsOf f.val.contract.writes == some #[some ⟨0⟩]

-- `Func.map` keeps the frames.
#guard bump.toOption.any fun f =>
  let g := f.val.map fun _ => 0
  cellsOf g.contract.reads == some #[some ⟨0⟩] && cellsOf g.contract.writes == some #[some ⟨0⟩]

/-- The printed form of `bump`. -/
private def bumpText : String := "module m {
  func @m.bump(%c.0 : base.Ref(base.Int), %k.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%k.0, 0)
        ret(%ok.0)
    }
    reads(%c.0)
    writes(%c.0)
  {
    entry.0(%c.0 : base.Ref(base.Int), %k.0 : base.Int):
      %v.0 : base.Int = base.refGet[base.Int](%c.0)
      %s.0 : base.Int = spec.add(%v.0, %k.0)
      %u.0 : base.Unit = base.refSet[base.Int](%c.0, %s.0)
      ret(%s.0)
  }
}"

#guard_msgs in
#eval do
  match Module.ofChecked (nm "m") #[← IO.ofExcept bump] () with
  | .ok m => unless toString m == bumpText ++ "\n" do IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

-- It reads back as printed.
#guard_msgs in
#eval do
  match ← Module.read Spec.env bumpText with
  | .error e => IO.println e
  | .ok m => unless toString m == bumpText ++ "\n" do IO.println m

-- An empty frame prints, and reads back as empty, not as absent.  A frame alone is a
-- contract.
/-- info: module m {
  func @m.bump(%c.0 : base.Ref(base.Int), %k.0 : base.Int) -> base.Int
    reads()
  {
    entry.0(%c.0 : base.Ref(base.Int), %k.0 : base.Int):
      ret(%k.0)
  }
}
reads: some #[], writes: none -/
#guard_msgs in
#eval do
  match ← Module.read Spec.env "module m {
  func @m.bump(%c.0 : base.Ref(base.Int), %k.0 : base.Int) -> base.Int
    reads()
  {
    entry.0(%c.0 : base.Ref(base.Int), %k.0 : base.Int):
      ret(%k.0)
  }
}" with
  | .error e => IO.println e
  | .ok m =>
    IO.print m
    for f in m.raw.funcs do
      let ids (fr : Option (Array (FrameEntry Spec.env Info))) : Option (Array (Option Nat)) :=
        Option.map (Array.map (Option.map ValId.id)) (cellsOf fr)
      IO.println s!"reads: {repr (ids f.contract.reads)}, writes: {repr (ids f.contract.writes)}"

-- A frame names cells among the parameters: not an integer parameter, nor a value of the
-- body.
#guard failing (bumpWith (some fun _ k => #[k]) none) == ["contract"]

#guard failing (bumpWith none (some fun _ _ => #[⟨2⟩])) == ["contract"]

/-- `g(a, b, k)`, over the cells `a` and `b`, whose body allocates the cell `d`: `frames a b d`
emits its frames. -/
private def cellsWith (frames : ValId → ValId → ValId → BuildM E Unit Unit) : Built :=
  build (.str (nm "m") "g") intT () do
    let a ← freshVal (nm "a") refIntT
    let b ← freshVal (nm "b") refIntT
    let k ← freshVal (nm "k") intT
    let _ ← startFreshBlock #[a, b, k] "entry"
    let d ← emitApply (nm "d") refIntT Base.refNew.ref #[k.id]
    finishBlock (.ret () k.id)
    frames a.id b.id d

#guard (cellsWith fun a b _ => do Build.reads #[.cell a, .cell b]; Build.writes #[.cell b]).isOk

-- A frame names no cell that the body allocates.
#guard failing (cellsWith fun _ _ d => Build.writes #[.cell d]) == ["contract"]

-- A frame names a cell once.
#guard failing (cellsWith fun a _ _ => Build.reads #[.cell a, .cell a]) == ["contract"]

-- A second frame of a kind is a misuse.
#guard match cellsWith fun a b _ => do Build.writes #[.cell a]; Build.writes #[.cell b] with
  | .error e => e.misuses == #["a second writes clause"]
  | .ok _ => false

#guard match cellsWith fun a b _ => do Build.reads #[.cell a]; Build.reads #[.cell b] with
  | .error e => e.misuses == #["a second reads clause"]
  | .ok _ => false

-- A frame of several cells reads back as printed.
#guard_msgs in
#eval do
  let text := "module m {
  func @m.g(%a.0 : base.Ref(base.Int), %b.0 : base.Ref(base.Int), %k.0 : base.Int) -> base.Int
    reads(%a.0, %b.0)
    writes(%b.0)
  {
    entry.0(%a.0 : base.Ref(base.Int), %b.0 : base.Ref(base.Int), %k.0 : base.Int):
      %d.0 : base.Ref(base.Int) = base.refNew[base.Int](%k.0)
      ret(%k.0)
  }
}
"
  match ← Module.read Spec.env text,
      cellsWith fun a b _ => do Build.reads #[.cell a, .cell b]; Build.writes #[.cell b] with
  | .ok m, .ok g =>
    unless toString m == text do IO.println m
    match Module.ofChecked (nm "m") #[g] () with
    | .ok n => unless toString n == text do IO.println n
    | .error _ => IO.println "not well formed"
  | .error e, _ => IO.println e
  | _, .error e => IO.println e

-- Only the outer type counts: a cell of cells is a cell, a sequence of cells is not.
/-- info: read -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%c.0 : base.Ref(base.Ref(base.Int))) -> base.Unit
    reads(%c.0)
  {
    entry.0(%c.0 : base.Ref(base.Ref(base.Int))):
      ret(unit)
  }
}
"

/-- info: t.dyn:3:10: reads names %c.0, of type base.Sequence(base.Ref(base.Int)), but a frame names only cells, of type base.Ref -/
#guard_msgs in
#eval readErrors "module m {
  func @m.f(%c.0 : base.Sequence(base.Ref(base.Int))) -> base.Unit
    reads(%c.0)
  {
    entry.0(%c.0 : base.Sequence(base.Ref(base.Int))):
      ret(unit)
  }
}
"

/-- `@m.f(c : base.Ref(base.Int), k : base.Int) -> base.Int` with the contract `clauses` and a
body that allocates the cell `%d.0`. -/
private def withFrames (clauses : String) : String := s!"module m \{
  func @m.f(%c.0 : base.Ref(base.Int), %k.0 : base.Int) -> base.Int
{clauses}
  \{
    entry.0(%c.0 : base.Ref(base.Int), %k.0 : base.Int):
      %d.0 : base.Ref(base.Int) = base.refNew[base.Int](%k.0)
      ret(%k.0)
  }
}
"

/-- info: t.dyn:3:10: reads names %k.0, of type base.Int, but a frame names only cells, of type base.Ref -/
#guard_msgs in
#eval readErrors (withFrames "    reads(%k.0)")

/-- info: t.dyn:3:11: writes names %d.0, which is not a parameter of @m.f -/
#guard_msgs in
#eval readErrors (withFrames "    writes(%d.0)")

/-- info: t.dyn:3:10: reads names %e.0, which is not a parameter of @m.f -/
#guard_msgs in
#eval readErrors (withFrames "    reads(%e.0)")

/-- info: t.dyn:3:16: reads names %c.0 twice -/
#guard_msgs in
#eval readErrors (withFrames "    reads(%c.0, %c.0)")

/-- info: t.dyn:4:4: @m.f has two reads clauses -/
#guard_msgs in
#eval readErrors (withFrames "    reads(%c.0)\n    reads()")

/-- info: t.dyn:4:4: @m.f has two writes clauses -/
#guard_msgs in
#eval readErrors (withFrames "    writes(%c.0)\n    writes()")

/-- info: t.dyn:4:4: an ensures clause must come before the reads clause -/
#guard_msgs in
#eval readErrors (withFrames "    reads(%c.0)
    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }")

/-- info: t.dyn:4:4: a reads clause must come before the writes clause -/
#guard_msgs in
#eval readErrors (withFrames "    writes(%c.0)\n    reads(%c.0)")

/-- info: t.dyn:4:4: a requires clause must come before the reads clause -/
#guard_msgs in
#eval readErrors (withFrames "    reads(%c.0)
    requires {
      pre.0():
        ret(true)
    }")

/-! ## Extern functions and clause modes

An extern function has a signature and a contract, and no blocks.  Its parameters are its first
values.  Its `requires` clauses are checked at calls, and its `ensures` clauses are `free`:
assumed after a call, never checked.  A defined function's `ensures` clauses are all checked.
Any clause may carry a message. -/

/-- The extern `@m.f(x : base.Int) -> base.Int`, whose contract `contract x` emits. -/
private def externWith (contract : ValId → BuildM E Unit Unit) : Built :=
  Build.buildExtern (.str (nm "m") "f") #[(nm "x", intT)] intT () fun ps => do
    if let some x := ps[0]? then contract x

/-- `f`, which requires `x ≥ 0` and is assumed to return a result `≥ 0`, each clause with a
message. -/
private def ext : Built := externWith fun x => do
  Build.requires (nonNeg x) (message := "x is non-negative")
  Build.ensures (nm "r") intT nonNeg (free := true) (message := "admitted postcondition of 'f'")

#guard ext.isOk

#guard ext.toOption.any (decide ·.val.Canonical)

-- Its code type is read from its parameters, since it has no entry block.
#guard ext.toOption.any (·.val.codeType == Base.Fn (TypeList.ofTypes #[intT]) intT)

-- `Func.map` keeps each clause's mode and message.
#guard ext.toOption.any fun f => (f.val.map fun _ => ({} : Info)).format .full == f.val.format .full

/-- The printed form of `f`, folded. -/
private def extText : String := "module m {
  extern func @m.f(%x.0 : base.Int) -> base.Int
    requires \"x is non-negative\" {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
    free ensures \"admitted postcondition of 'f'\" {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = spec.ge(%r.0, 0)
        ret(%ok.1)
    }
}
"

#guard_msgs in
#eval do
  match Module.ofChecked (nm "m") #[← IO.ofExcept ext] () with
  | .ok m => unless toString m == extText do IO.println m
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"

-- It reads back unchanged, in both forms.
/-- info: module m {
  extern func @m.f(%x.0 : base.Int) -> base.Int
    requires "x is non-negative" {
      pre.0():
        %c.0 : base.Int = const 0
        %ok.0 : base.Bool = spec.ge(%x.0, %c.0)
        ret(%ok.0)
    }
    free ensures "admitted postcondition of 'f'" {
      post.0(%r.0 : base.Int):
        %c.1 : base.Int = const 0
        %ok.1 : base.Bool = spec.ge(%r.0, %c.1)
        ret(%ok.1)
    }
}

module m {
  extern func @m.f(%x.0 : base.Int) -> base.Int
    requires "x is non-negative" {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
    free ensures "admitted postcondition of 'f'" {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = spec.ge(%r.0, 0)
        ret(%ok.1)
    }
} -/
#guard_msgs in
#eval roundTrip extText

#guard_msgs in
#eval do
  match ← Module.read Spec.env extText with
  | .error e => IO.println e
  | .ok m => unless m.raw.funcs.all (decide ·.Canonical) do IO.println "not canonical"

/-- `@m.g(x : base.Int) -> base.Int`, an extern without a contract. -/
private def bare : Built :=
  Build.buildExtern (.str (nm "m") "g") #[(nm "x", intT)] intT () fun _ => pure ()

-- An extern without a contract is one line, and reads back unchanged.
/-- info: module m {
  extern func @m.g(%x.0 : base.Int) -> base.Int
}
read back unchanged -/
#guard_msgs in
#eval do
  match Module.ofChecked (nm "m") #[← IO.ofExcept bare] () with
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
  | .ok m =>
    IO.print m
    match ← Module.read Spec.env (toString m) with
    | .error e => IO.println e
    | .ok r => IO.println (if toString r == toString m then "read back unchanged" else toString r)

/-- `@m.h(x) = g(x)`, which calls the extern `g` through a reference at `g`'s code type. -/
private def callsBare : Built :=
  build (.str (nm "m") "h") intT () do
    let x ← freshVal (nm "x") intT
    let _ ← startFreshBlock #[x] "entry"
    let g ← emitFunc (.str (nm "m") "g") (Base.Fn (TypeList.ofTypes #[intT]) intT)
    finishBlock (.ret () (← emitApply (nm "r") intT Base.callCode.ref #[g, x.id]))

-- A module whose function references an extern at its code type is well formed, built and read.
#guard_msgs in
#eval do
  let text := "module m {
  extern func @m.g(%x.0 : base.Int) -> base.Int
  func @m.h(%x.0 : base.Int) -> base.Int {
    entry.0(%x.0 : base.Int):
      %code.0 : base.Fn([base.Int], base.Int) = const @m.g
      %r.0 : base.Int = base.callCode[[base.Int], base.Int](%code.0, %x.0)
      ret(%r.0)
  }
}
"
  match Module.ofChecked (nm "m") #[← IO.ofExcept bare, ← IO.ofExcept callsBare] () with
  | .ok m => unless m.format .full == text do IO.println (m.format .full)
  | .error bad => IO.println s!"not well formed: {bad.map ToDDM.nameText}"
  match ← Module.read Spec.env text with
  | .ok m => unless m.format .full == text do IO.println (m.format .full)
  | .error e => IO.println e

-- An extern's frames name cells among its parameters.
#guard_msgs in
#eval do
  let text := "module m {
  extern func @m.set(%c.0 : base.Ref(base.Int), %v.0 : base.Int) -> base.Unit
    reads()
    writes(%c.0)
}
"
  match ← Module.read Spec.env text with
  | .ok m => unless toString m == text do IO.println m
  | .error e => IO.println e

-- The printer leaves out an extern's attributes.
/-- info: module m.g {
  extern func @m.g(%x.0 : base.Int) -> base.Int
} -/
#guard_msgs in
#eval do
  let attrs : Array Attr := #[(nm "k", .const (.int 1))]
  let f ← IO.ofExcept (Build.buildExtern (.str (nm "m") "g") #[(nm "x", intT)] intT
    ({ attrs } : Info) fun _ => pure ())
  IO.print (f.val.format .full)

-- A defined function's clauses may carry messages too.
#guard_msgs in
#eval do
  let text := withClauses "    requires \"x is non-negative\" {
      pre.0():
        %ok.0 : base.Bool = spec.ge(%x.0, 0)
        ret(%ok.0)
    }
    ensures \"the result is at least x\" {
      post.0(%r.0 : base.Int):
        %ok.1 : base.Bool = spec.ge(%r.0, %x.0)
        ret(%ok.1)
    }"
  match ← Module.read Spec.env text with
  | .ok m => unless toString m == text do IO.println m
  | .error e => IO.println e

/-! ### What the rules reject -/

-- A function is extern exactly when it has no blocks.
#guard failing (externWith fun _ => do
  let _ ← startFreshBlock #[] "entry"
  finishBlock (.ret () (← emitConst (nm "z") (.int 0)))) == ["extern"]

#guard failing (build (.str (nm "m") "f") intT () (pure ())) == ["extern"]

-- An extern's contract may not leave a block open.
#guard failing (externWith fun _ => do let _ ← startFreshBlock #[] "entry") == ["misuse"]

/-! A front end in `ExceptT` can throw out of a region nested in a clause and catch the error
outside it, as in `TypedEmitTest`.  The region is then never closed, and the clause's entry
block is lost, so `Build.buildExtern` records a misuse. -/

/-- A `requires` clause, `if true` of two regions that return `true`, whose `then` region, with
`fail`, throws, which is caught by returning `true`. -/
private def guarded (fail : Bool) : ExceptT String (BuildM E Unit) Unit := do
  let t ← (emitConst (nm "t") (.bool true) : BuildM E Unit ValId)
  try
    let (thn, _) ← Build.regionWith #[] (base := "then") do
      if fail then throw "unsupported"
      (retTrue : BuildM E Unit Unit)
    let v ← (emitApply (nm "v") boolT Spec.«if».ref #[t]
      (regions := #[pure thn, region #[] (base := "else") retTrue]) : BuildM E Unit ValId)
    (finishBlock (.ret () v) : BuildM E Unit Unit)
  catch _ => (retTrue : BuildM E Unit Unit)

/-- The module of the extern `f` whose `requires` clause is `guarded fail`, printed, or the
misuses. -/
private def guardedExtern (fail : Bool) : String :=
  match externWith fun _ => Build.requires (do let _ ← (guarded fail).run) with
  | .error e => toString e
  | .ok f => match Module.ofChecked (nm "m") #[f] () with
    | .ok m => toString m
    | .error _ => "the module is not well formed"

/-- info: module m {
  extern func @m.f(%x.0 : base.Int) -> base.Int
    requires {
      pre.0():
        %v.0 : base.Bool = spec.if[base.Bool](true) {
          then.0():
            ret(true)
        } {
          else.0():
            ret(true)
        }
        ret(%v.0)
    }
} -/
#guard_msgs in
#eval IO.print (guardedExtern false)
/-- info: region pre.0 is still open when the function ends: its body did not return -/
#guard_msgs in
#eval IO.print (guardedExtern true)

/-- `id(x) = x`, without a contract. -/
private def idFn : Built :=
  build (.str (nm "m") "id") intT () do
    let x ← freshVal (nm "x") intT
    let _ ← startFreshBlock #[x] "entry"
    finishBlock (.ret () x.id)

-- A defined function's parameters are its entry block's, ids and types.
#guard idFn.toOption.any fun f => broken f.val == []

#guard idFn.toOption.any fun f => broken { f.val with params := #[⟨⟨1⟩, intT⟩] } == ["params"]

#guard idFn.toOption.any fun f => broken { f.val with params := #[⟨⟨0⟩, boolT⟩] } == ["params"]

#guard idFn.toOption.any fun f => broken { f.val with params := #[] } == ["params"]

-- No `requires` clause is free.
#guard inc.toOption.any fun f =>
  broken { f.val with
    contract.requires := f.val.contract.requires.map ({ · with free := true }) } == ["modes"]

-- An extern's `ensures` clauses are free, and a defined function's are checked.
#guard failing (externWith fun x => Build.ensures (nm "r") intT (atLeast x)) == ["modes"]

#guard failing (build (.str (nm "m") "f") intT () do
  let x ← freshVal (nm "x") intT
  let _ ← startFreshBlock #[x] "entry"
  finishBlock (.ret () x.id)
  Build.ensures (nm "r") intT (atLeast x.id) (free := true)) == ["modes"]

/-- info: t.dyn:3:4: @m.f is extern, so its ensures clauses must be free -/
#guard_msgs in
#eval readErrors "module m {
  extern func @m.f(%x.0 : base.Int) -> base.Int
    ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }
}
"

/-- info: t.dyn:3:4: free ensures is allowed only on an extern function, but @m.f has a body -/
#guard_msgs in
#eval readErrors (withClauses "    free ensures {
      post.0(%r.0 : base.Int):
        ret(true)
    }")

-- `free` comes only before `ensures`.
/-- info: t.dyn:3:8: unexpected token 'requires'; expected 'ensures' -/
#guard_msgs in
#eval readErrors (withClauses "    free requires {
      pre.0():
        ret(true)
    }")

end Strata.Dyn.ContractTest
