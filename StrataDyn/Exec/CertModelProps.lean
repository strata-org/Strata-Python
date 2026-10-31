/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.CertModel
public import StrataDyn.Exec.Effects

set_option autoImplicit false

/-!
# Properties of accounts

Facts about the validity predicates of `Accounts`, for any model, that a table's certificate uses:
payloads and exits of tags that hold no ref are always valid (`argsOK_nil`, `argsOK_cons`,
`exitOK_nil`, `exitOK_cons`), and a property of every operand list or every variadic array holds
of every valid one (`fnOK_of_fnAll`, `varOK_of_varAll`).

`sat_retyped_cell`: a read, write or update of a cell at another tag than the one it holds is
rejected by the machine's spec (`Accounts.spec`), at any accounts, so a rule that reads, writes or
updates a cell through a retyped ref has no certificate.
-/

namespace Strata.Dyn.Exec.Accounts

open Strata.Dyn.Exec.Effects

@[expose] public section

variable {M : RunModel} (A : Accounts M)

/-- No exit of an operation without successors. -/
theorem exitOK_nil (G : Typing) : ∀ x : Exit M.interp [], A.ExitOK G x :=
  fun x => nomatch x

/-- Every exit is valid when every payload of the first successor and every exit of the others
are. -/
theorem exitOK_cons (G : Typing) {ts : List Ty} {ps : List (List Ty)}
    (ha : ∀ a : Args M.interp ts, A.ArgsOK G a) (he : ∀ e : Exit M.interp ps, A.ExitOK G e) :
    ∀ x : Exit M.interp (ts :: ps), A.ExitOK G x
  | .here a => ha a
  | .there e => he e

/-- The empty payload is valid. -/
theorem argsOK_nil (G : Typing) : ∀ a : Args M.interp [], A.ArgsOK G a
  | .nil => trivial

/-- A payload is valid when its first value holds no ref and the rest is valid. -/
theorem argsOK_cons (G : Typing) {t : Ty} {ts : List Ty} (hx : ∀ x : M.interp t, A.acct t x = [])
    (h : ∀ a : Args M.interp ts, A.ArgsOK G a) : ∀ a : Args M.interp (t :: ts), A.ArgsOK G a
  | .cons x xs => ⟨by show G.AllValid (A.acct t x); rw [hx x]; exact Typing.allValid_nil G, h xs⟩

/-- `FnAll` gives `FnOK`: a property of every operand list holds of every valid one. -/
theorem fnOK_of_fnAll {R : Type} {P P' : R → Prop} (hP : ∀ x, P x → P' x) (G : Typing) :
    ∀ {ts : List Ty} {f : Fn M.interp R ts}, FnAll P ts f → A.FnOK G P' ts f
  | [], _, h => hP _ h
  | _ :: _, _, h => fun x _ => fnOK_of_fnAll hP G (h x)

/-- `VarAll` gives `VarOK`: a property of every variadic array holds of every valid one. -/
theorem varOK_of_varAll {X : Type} {P P' : X → Prop} (hP : ∀ x, P x → P' x) (G : Typing) :
    ∀ {v : Option Ty} {f : VarFn M.interp v X}, VarAll P v f → A.VarOK G P' v f
  | none, _, h => hP _ h
  | some _, _, h => fun xs _ => hP _ (h xs)

variable {rs : List (List Ty × Ty)} {ps : List (List Ty)} {St : Type} (StOK : Typing → St → Prop)
  {R : Type} (Q : Typing → R → Prop)

/-- **A cell request at another tag has no certificate**: when location `l` holds values of the
tag `t₁` in `S`, a tree whose next request reads, writes or updates `l` at a tag `t₂ ≠ t₁` is
rejected by the machine's spec at the accounts `A`, whatever follows the request.  A cell's tag is a
function of its location, and every typing that the run reaches keeps it, so a rule that reads,
writes or updates a cell through a retyped ref (`⟨r.raw⟩`) has no certificate. -/
theorem sat_retyped_cell {S : Typing} {l : Nat} {t₁ t₂ : Ty}
    (hl : S.Valid l t₁) (hne : t₁ ≠ t₂) {q : MReq M.interp rs}
    (hq : q = .get t₂ l ∨ (∃ v, q = .set t₂ l v) ∨ ∃ f, q = .modify t₂ l f)
    (k : q.Out Run → Tree M.interp Run M.W rs ps St R) :
    ¬ (A.spec rs ps StOK).Sat Q S (.vis q k) := by
  intro h
  have hpre : A.PreOK S q := (Spec.sat_vis.mp h).1
  have hv : S.Valid l t₂ := by
    rcases hq with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact hpre
    · exact hpre.1
    · exact hpre.1
  exact hne (Option.some.inj (hl.symm.trans hv))

end

end Strata.Dyn.Exec.Accounts
