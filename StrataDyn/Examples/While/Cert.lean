/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Examples.While.Env
public import StrataDyn.Exec.CertTactic

set_option autoImplicit false

/-!
# While's table is certified

`WhileCert.accounts` gives the refs of While's values: a ref's cell, a closure's captures cell,
an array's elements' refs and an `Except`'s value's refs; While's own datatypes, its world and
its loop's state hold none.  `WhileCert.certified` says every rule of `WhileSem` respects the
heap's typing, so a proof about While's runs may rely on rules reaching only what they are
given.  `#dyn_certs` proves each operation's certificate, as its own theorem.
-/

namespace Strata.Dyn.WhileCert

open Strata.Dyn.Exec

@[expose] public section

/-- Where the refs of a value of While's tag `t` are.  Heads `0` and `1` are a ref's and a
closure's; `7` is `Array` and `8` is `Except`; the other heads hold no refs. -/
def acct : (t : Ty) → WhileSem.interp Run t → List Loc
  | .app 0 [a], x => [.cell x.loc a]
  | .app 1 [.list ts, r], f =>
    if (WhileSem.model.at.fnOf (ts := ts) (r := r) f).captured = 0 then []
    else [.caps (WhileSem.model.at.fnOf (ts := ts) (r := r) f).captured]
  | .app 7 [a], xs => xs.toList.flatMap (acct a)
  | .app 8 [e, a], x => match x with
    | .error v => acct e v
    | .ok v => acct a v
  | _, _ => []
termination_by structural t => t

/-- While's accounts. -/
def accounts : Accounts WhileSem.model.at where
  acct := acct
  world _ := []
  st _ _ := []
  ref t x := by simp only [acct, RunModel.locOf, cast_eq]
  fn ts r x := by simp only [acct]
  unit := rfl
  bool _ := rfl
  int _ := rfl
  float _ := rfl
  str _ := rfl

-- One theorem per operation, `cert.while.add` and so on, each proved by `dyn_cert`, and
-- `cert.ops`, which assembles them.
#dyn_certs WhileSem accounts [accounts, acct]

/-- **While's table is certified**: each of its rules respects every typing of the heap under
which its operands are valid. -/
theorem certified : WhileSem.model.Certified accounts :=
  Model.certified_of_ops cert.ops

end

end Strata.Dyn.WhileCert
