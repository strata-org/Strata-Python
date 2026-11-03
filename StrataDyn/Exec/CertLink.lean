/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.CertModel
public import StrataDyn.Exec.LinkInv

set_option autoImplicit false

/-!
# Linking keeps certificates

`link_rulesOK`: a module linked against a certified model has certified rules
(`LModule.RulesOK`).  It is the link invariant `LinkInv.certified` (`LinkInv.lean`), whose
wrappers are those that are `ImplOK`.

* Uncurrying a wrapper, collecting its variadic operands, keeps `FnOK` (`fnOK_uncurry`), so
  what linking makes of a wrapper that is `ImplOK` is certified (`insnOK_linked`,
  `termOK_linked`).
* Casting a wrapper's state type keeps `ImplOK` at `OpCertified`'s state predicate
  (`implOK_cast`), so a certified model's wrappers, as linking casts them, are `ImplOK`.
* A native instruction is certified (`insnOK_native`): a constant holds no ref by `Accounts`'s
  laws for literals and closures.
-/

namespace Strata.Dyn.Exec

public section

/-! ## Curried functions -/

namespace Accounts

variable {R : RunModel} (A : Accounts R)

/-- `FnOK` of a constant function is its value's. -/
theorem fnOK_const {S : Typing} {X : Type} {P : X → Prop} {x : X} (h : P x) :
    ∀ ts, A.FnOK S P ts (Fn.const x ts)
  | [] => h
  | _ :: ts => fun _ _ => fnOK_const h ts

/-- `FnOK` of `g` after `f` follows from `f`'s, when `g` takes `Q` to `P`. -/
theorem fnOK_map {S : Typing} {X Y : Type} {Q : X → Prop} {P : Y → Prop} {g : X → Y}
    (hg : ∀ x, Q x → P (g x)) : ∀ {ts} {f : Fn R.interp X ts}, A.FnOK S Q ts f →
      A.FnOK S P ts (Fn.map g f)
  | [], _, h => hg _ h
  | _ :: _, _, h => fun x hx => fnOK_map hg (h x hx)

/-- `FnOK` of an uncurried function is its curried one's. -/
theorem fnOK_append {S : Typing} {X : Type} {P : X → Prop} {us : List Ty} :
    ∀ {ts} {f : Fn R.interp (Fn R.interp X us) ts}, A.FnOK S (A.FnOK S P us) ts f →
      A.FnOK S P (ts ++ us) (Fn.append f)
  | [], _, h => h
  | _ :: _, _, h => fun x hx => fnOK_append (h x hx)

/-- `FnOK` of collecting operands after a valid accumulator, for a continuation that takes
every valid array to `P`. -/
theorem fnOK_collect {S : Typing} {X : Type} {P : X → Prop} {v : Ty}
    {k : Array (R.interp v) → X}
    (hk : ∀ xs : Array (R.interp v), (∀ x ∈ xs.toList, A.ValOK S v x) → P (k xs)) :
    ∀ (n : Nat) {acc : Array (R.interp v)}, (∀ x ∈ acc.toList, A.ValOK S v x) →
      A.FnOK S P (List.replicate n v) (Fn.collect v acc n k)
  | 0, _, h => hk _ h
  | n + 1, acc, h => fun x hx => fnOK_collect hk n (acc := acc.push x) (by
      intro y hy
      rw [Array.toList_push, List.mem_append, List.mem_singleton] at hy
      rcases hy with hy | rfl
      · exact h y hy
      · exact hx)

/-- **Uncurrying keeps `FnOK`**: a wrapper that satisfies `P` on every valid operand list and
variadic array, curried in all its operands, satisfies `P` on every valid operand list. -/
theorem fnOK_uncurry {S : Typing} {X : Type} {P : X → Prop} {args : List Ty} :
    ∀ {var : Option Ty} {f : Fn R.interp (VarFn R.interp var X) args} {n : Nat} {ts : List Ty}
      {g : Fn R.interp X ts}, A.FnOK S (A.VarOK S P var) args f →
      uncurry args var f n = some ⟨ts, g⟩ →
      A.FnOK S P ts g
  | none, f, n, ts, g, h, hu => by
    by_cases hn : n = args.length
    · rw [uncurry, ite_eq_left hn] at hu
      cases hu
      exact h
    · rw [uncurry, ite_eq_right hn] at hu
      cases hu
  | some v, f, n, ts, g, h, hu => by
    by_cases hn : args.length ≤ n
    · rw [uncurry, ite_eq_left hn] at hu
      cases hu
      exact A.fnOK_append (A.fnOK_map (fun k hk => A.fnOK_collect hk _ (by simp)) h)
    · rw [uncurry, ite_eq_right hn] at hu
      cases hu

end Accounts

/-- `ImplOK` at a state predicate that holds at every proof of a state type's equation
transports along a cast of the wrapper to the other type. -/
theorem Accounts.implOK_cast {R : RunModel} {A : Accounts R} {s : Shape} {St₁ St₂ : Type}
    (h : St₁ = St₂) {StOK : Typing → St₂ → Prop} {impl : Impl Run R.interp R.W s St₁}
    (hi : A.ImplOK (fun S x => ∀ h₁ : St₁ = St₂, StOK S (cast h₁ x)) s impl) :
    A.ImplOK StOK s (cast (congrArg (Impl Run R.interp R.W s) h) impl) := by
  subst h
  have he : (fun S x => ∀ h₁ : St₁ = St₁, StOK S (cast h₁ x)) = StOK :=
    funext fun _ => funext fun _ => propext ⟨fun h => h rfl, fun h _ => h⟩
  rw [he] at hi
  exact hi

section
variable {M : Model} {A : Accounts M.at} {op : Name} {key : Nat × Array Ty} {args : List Nat}
  {succs : List LSite} {regs : List Nat} {s : Shape}
  {impl : Impl Run M.at.interp M.at.W s (M.at.St key)}

/-- What linking makes of a wrapper that is `ImplOK` is `InsnOK`. -/
theorem insnOK_linked {dst : Nat} {i : LInsn M.at} (h : A.ImplOK (A.StOK key) s impl)
    (hl : LinkedApp op dst key args succs regs s impl i) : A.InsnOK i := by
  cases hl with
  | pure hu => exact fun S => A.fnOK_uncurry (h S) hu
  | sem hu =>
    exact ⟨fun S => A.fnOK_uncurry (h S) hu, fun S => A.fnOK_const (fun _ _ => Spec.sat_fault) _⟩
  | loop hu hu₁ => exact ⟨fun S => A.fnOK_uncurry (h.1 S) hu, fun S => A.fnOK_uncurry (h.2 S) hu₁⟩

/-- What linking makes of a wrapper that is `ImplOK` is `TermOK`. -/
theorem termOK_linked {t : LTerm M.at} (h : A.ImplOK (A.StOK key) s impl)
    (hl : LinkedTermApp op key args succs regs s impl t) : A.TermOK t := by
  cases hl with
  | case hu => exact fun S => A.fnOK_uncurry (h S) hu
  | sem hu =>
    exact ⟨fun S => A.fnOK_uncurry (h S) hu, fun S => A.fnOK_const (fun _ _ => Spec.sat_fault) _⟩
  | loop hu hu₁ => exact ⟨fun S => A.fnOK_uncurry (h.1 S) hu, fun S => A.fnOK_uncurry (h.2 S) hu₁⟩

end

/-- A native instruction is certified: a constant holds no ref. -/
theorem insnOK_native {M : Model} (A : Accounts M.at) {i : LInsn M.at} (h : NativeInsn M i) :
    A.InsnOK i := by
  cases h with
  | fn _ ts r i =>
    show A.acct (Ty.fn ts r) (M.at.fnAt ts r i) = []
    rw [A.fn, RunModel.fnOf_fnAt]
    rfl
  | unit => exact A.unit
  | bool _ b => exact A.bool b
  | int _ i => exact A.int i
  | float _ x => exact A.float x
  | str _ x => exact A.str x
  | refNew | refGet | refSet | callCode => trivial

/-- **The certificate invariant** of a certified model: its wrappers are those that are
`ImplOK`, its instructions and terminators those that are `InsnOK` and `TermOK`. -/
def LinkInv.certified {M : Model} {A : Accounts M.at} (hc : M.Certified A) : LinkInv M where
  wrapper key s impl := A.ImplOK (A.StOK key) s impl
  insn := A.InsnOK
  term := A.TermOK
  table hk targs := Accounts.implOK_cast (M.stateOf_eq Run hk targs).symm (hc _ _ _ hk targs)
  native := insnOK_native A
  app := insnOK_linked
  termApp := termOK_linked

/-- **Linking against a certified model certifies the rules**: every instruction and terminator
of every function and region of a module linked against a certified model is certified. -/
theorem link_rulesOK {M : Model} {A : Accounts M.at} (hc : M.Certified A) {env : Env Unit}
    [base ≼ env] {α : Type} {m : Module env α} {lm : LModule M.at} (hl : link M m = .ok lm) :
    lm.RulesOK A :=
  link_inv (LinkInv.certified hc) hl

end

end Strata.Dyn.Exec
