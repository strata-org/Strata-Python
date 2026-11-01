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
of every valid one (`fnOK_of_fnAll`, `varOK_of_varAll`, `fnOK_ofPayload`).

`bindAll_sat`: binding valid values into a valid closure, one `bind` request each, makes only
valid requests and gives a valid closure, at the machine's spec of a model's accounts.  It is what
a rule that makes a closure from its operands (a language's closure-making operation) needs for its
certificate.  `ArgsOK.mono` says that valid values stay valid as the typing grows.

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

/-- `FnOK` of a function made from a payload (`Fn.ofPayload`): `P` holds of `k` of every valid
payload. -/
theorem fnOK_ofPayload {R : Type} (P : R → Prop) (G : Typing) :
    ∀ (ts : List Ty) (k : Payload (ts.map M.interp) → R),
      (∀ vs, A.ArgsOK G (Args.ofPayload ts vs) → P (k vs)) → A.FnOK G P ts (Fn.ofPayload ts k)
  | [], _, h => h () trivial
  | [_], _, h => fun x hx => h x ⟨hx, trivial⟩
  | _ :: t' :: ts, k, h => fun x hx =>
    fnOK_ofPayload P G (t' :: ts) (fun p => k (x, p)) fun p hp => h (x, p) ⟨hx, hp⟩

/-- Valid values stay valid in an extension. -/
theorem ArgsOK.mono {S S₁ : Typing} (h : S.Extends S₁) :
    ∀ {ts : List Ty} {a : Args M.interp ts}, A.ArgsOK S a → A.ArgsOK S₁ a
  | _, .nil, _ => trivial
  | _, .cons _ _, hx => ⟨Typing.AllValid.mono h hx.1, ArgsOK.mono h hx.2⟩

/-- A closure's captures cell, after a cast of its parameter and result types, is the
closure's. -/
theorem captured_cast {as as' : List Type} {r r' : Type} (h₁ : as = as') (h₂ : r = r')
    (g : FnRef Run as r) : (cast (congr (congrArg (FnRef Run) h₁) h₂) g).captured = g.captured := by
  subst h₁; subst h₂; rfl

variable {rs : List (List Ty × Ty)} {ps : List (List Ty)} {St : Type} (StOK : Typing → St → Prop)
  {R : Type} (Q : Typing → R → Prop)

/-- **Binding valid values into a valid closure is allowed and gives a valid closure**: at the
machine's spec, `bindAll` of the values `vs`, of the tags `tys`, into `f`, followed by `k`,
satisfies the spec from `S` when `f`'s captures cell and `vs` are valid in `S`, and `k` of every
closure whose captures cell is valid satisfies it from every extension.  By induction on `tys`. -/
theorem bindAll_sat {as : List Type} {r : Type} [s : @SigOf Run _ ⟨M.interp⟩ as r] :
    letI : Decode Run := ⟨M.interp⟩
    ∀ (tys : List Ty) (f : FnRef Run (tys.map M.interp ++ as) r) (vs : Payload (tys.map M.interp))
      (k : FnRef Run as r → Tree M.interp Run M.W rs ps St R) (S : Typing),
      S.CapValid f.captured → A.ArgsOK S (Args.ofPayload tys vs) →
      (∀ S₁, S.Extends S₁ → ∀ g : FnRef Run as r, S₁.CapValid g.captured →
        (A.spec rs ps StOK).Sat Q S₁ (k g)) →
      (A.spec rs ps StOK).Sat Q S
        (@Sem.bind (MEff M.interp Run M.W rs) (Out M.interp ps St) _ _
          (@bindAll Run _ ⟨M.interp⟩ (MEff M.interp Run M.W rs) (Out M.interp ps St)
            HasCall.mreq as r s (tys.map M.interp) ⟨tys, rfl⟩ f vs) k)
  | [], f, (), _, S, hf, _, hk => hk S (Typing.Extends.refl S) f hf
  | [_], _, _, _, S, hf, hv, hk => Spec.sat_vis.mpr ⟨⟨hf, hv.1⟩, fun S₁ he o ho =>
      hk S₁ he _ (by
        show S₁.CapValid (FnRef.captured (cast _ o : FnRef Run _ _))
        rw [captured_cast s.ok.1 s.ok.2]
        exact ho)⟩
  | _ :: t' :: ts, _, (_, xs), k, S, hf, hv, hk => Spec.sat_vis.mpr ⟨⟨hf, hv.1⟩, fun S₁ he o ho =>
      bindAll_sat (t' :: ts) _ xs k S₁ (by
          show S₁.CapValid (FnRef.captured (cast _ o : FnRef Run _ _))
          rw [captured_cast ((List.map_append ..).trans (congrArg _ s.ok.1)) s.ok.2]
          exact ho)
        (ArgsOK.mono A he hv.2) fun S₂ he₂ g hg => hk S₂ (he.trans he₂) g hg⟩

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
