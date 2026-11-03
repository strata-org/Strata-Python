/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDynTest.Exec.TestEnv
public import StrataDyn.Exec.CertTactic
public import StrataDyn.Exec.CertLink
public import StrataDyn.Examples.While.Cert

set_option autoImplicit false

/-!
# Certificates of the test environment's rules

`dyn_cert` proves the certificate of each of `Ex`'s operations below, from `Ex`'s accounts:
a ref's cell, a closure's captures cell, an array's elements', an `Except`'s value's, and the
refs of the datatypes `Slot`, `Clo`, `Box`, `Two`, `Chain` and `Thunk`.  Among them are rules that
make, read, write and update cells, at `Int`, at a type argument and through `Box`, that run
regions on a cell, that call and bind closures, and that loop with a state.

`ex.retype` gives a ref another contents' type, and is not certified (`retype_not_certified`):
the ref it returns is not valid at `Bool` in a typing where its cell holds an `Int`.  Beside it,
`ex.cellGet`, which returns its cell's contents, is.  `dyn_cert` fails on `ex.retype` and shows
the ref it could not show valid.

`dyn_cert` does not prove the certificate of a rule that builds a closure over a list of cells,
such as `ex.mkClo`, which has the shape of Python's `mkClosure` (its failure is pinned below);
such a rule needs a hand-written certificate, with a lemma for `bindAll` by induction on the list;
this package has none yet.

The axioms of While's certificate and of linking's theorems are pinned.
-/

namespace Strata.Dyn.ExecTest.CertTest

open Strata.Dyn.Exec

@[expose] public section

/-- The account of a closure's captures cell. -/
def caps (c : Nat) : List Loc := if c = 0 then [] else [.caps c]

/-- Where the refs of a value of `Ex`'s tag `t` are. -/
def acct : (t : Ty) → ExSem.interp Run t → List Loc
  | .app 0 [a], x => [.cell x.loc a]
  | .app 1 [.list ts, r], f => caps (ExSem.model.at.fnOf (ts := ts) (r := r) f).captured
  | .app 7 [a], xs => xs.toList.flatMap (acct a)
  | .app 8 [e, a], x => match x with
    | .error v => acct e v
    | .ok v => acct a v
  | .app 10 [], .slot c => [.cell c.loc (.app 4 [])]
  | .app 11 [], .clo f => caps f.captured
  | .app 12 [a], .box c => [.cell c.loc a]
  | .app 13 [a], .two x y => [.cell x.loc a, .cell y.loc a]
  | .app 14 [], .done => []
  | .app 14 [], .link n => [.cell n.loc (.app 14 [])]
  | .app 15 [], .thunk f => caps f.captured
  | _, _ => []
termination_by structural t => t

/-- `Ex`'s accounts. -/
def accounts : Accounts ExSem.model.at where
  acct := acct
  world _ := []
  st _ _ := []
  ref t x := by simp only [acct, RunModel.locOf, cast_eq]
  fn ts r x := by simp only [acct, caps]
  unit := rfl
  bool _ := rfl
  int _ := rfl
  float _ := rfl
  str _ := rfl

example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.Except.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.Unit.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.branch := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.error := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.cellLoc := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.jump := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.old := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.ok := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.unit := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.base.unreachable := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.Box.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.Chain.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.Clo.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.Slot.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.Thunk.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.Two.case := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.add := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.assume := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.bind := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.box := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.boxCell := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.br := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.call := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.callInt := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.cellAdd := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.cellGet := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.cellNew := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.cellPush := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.cellSet := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.clo := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.div := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.done := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.dup := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.fold := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.gap := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.getAt := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.goto := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.halt := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.le := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.link := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.loop := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.lt := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.mapList := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.mapRange := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.mul := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.ne := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.newAt := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.pack := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.pick := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.pickInt := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.pickNat := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.print := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.range := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.rem := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.slot := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.sub := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.swap := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.thunk := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.tick := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.two := by dyn_cert [accounts, acct, caps]
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.withCell := by dyn_cert [accounts, acct, caps]

/-- **`ex.retype` is not certified**: in a typing where location `0` holds an `Int`, a ref to it
at `Int` is valid, and the same ref at `Bool`, which the rule returns, is not. -/
theorem retype_not_certified (k : Nat) :
    ¬ ExSem.model.OpCertified accounts k ExSem.impl.ex.retype := by
  intro h
  let S : Typing := { cell := fun l => if l = 0 then some (.app 4 []) else none }
  have hx := h #v[] S ⟨⟨0, trivial⟩⟩ (by
    show S.AllValid [.cell 0 (.app 4 [])]
    exact Typing.allValid_singleton.mpr rfl)
  have hv : S.Valid 0 (.app 3 []) := Typing.allValid_singleton.mp hx
  exact nomatch (show (some (Ty.app 4 []) : Option Ty) = some (.app 3 []) from hv)

-- `dyn_cert` fails on `ex.retype`, and shows the result that it could not show valid.
/--
error: dyn_cert: 1 goal(s) left proving
  ExSem.model.OpCertified accounts 0 ExSem.impl.ex.retype
each a request, result, exit or world that the recipe could not show valid:
  targs✝ : Vector Ty 0
  S✝ : Typing
  x✝ : ExSem.interp Run (Ty.app 0 [Ty.app 4 []])
  a✝ : S✝.Valid (Ref.loc x✝) (Ty.app 4 [])
  ⊢ S✝.Valid { raw := x✝.raw }.loc (Ty.app 3 [])
-/
#guard_msgs in
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.retype := by
  dyn_cert [accounts, acct, caps]

-- `dyn_cert` fails on `ex.mkClo`: it cannot show valid the closure that `bindAll` makes over the
-- list of cells.  The pin keeps the message down to the hypotheses, because the goal after them
-- prints the proofs that Lean generates for `accounts`, under names such as `accounts._proof_1`
-- that a change to `accounts` or to Lean can renumber.
/--
error: dyn_cert: 1 goal(s) left proving
  ExSem.model.OpCertified accounts 0 ExSem.impl.ex.mkClo
each a request, result, exit or world that the recipe could not show valid:
  targs✝ : Vector Ty 1
  S✝ : Typing
  x✝ : ExSem.interp Run (Ty.app 1 [Ty.list (targs✝[0].elems ++ [Ty.app 4 []]), Ty.app 4 []])
  a✝ : S✝.CapValid (cast ⋯ x✝).captured
-/
#guard_msgs (substring := true) in
example : ExSem.model.OpCertified accounts 0 ExSem.impl.ex.mkClo := by
  dyn_cert [accounts, acct, caps]

end

/-- info: 'Strata.Dyn.WhileCert.certified' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WhileCert.certified

/--
info: 'Strata.Dyn.Exec.link_rulesOK' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms link_rulesOK

/-- info: 'Strata.Dyn.Exec.link_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms link_inv

end Strata.Dyn.ExecTest.CertTest
