/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Link

set_option autoImplicit false

/-!
# Validation at link time

`checkModule m` validates a linked module once, before it runs, and `WF m` says it succeeded.
A failure is a message naming the body, the block and the value at fault.  The machine runs
only well-formed modules, which is what lets it look values up and use them at their tags
without a check.

A block is checked in its entry context, `entryCtx b`: its scope, then its parameters.  Each
instruction must find its operands in the context at the tags its wrapper takes, and adds its
result; so a use is in scope only if it is a parameter, in the scope, or defined earlier in the
block.  Each edge into a block must supply its parameters' tags and have the block's scope in
its own context; an edge to the body's exit supplies exactly one value, of the body's result
code.  In detail:

* an operation's operands have the wrapper's tags, each successor receives its payload, and
  each region takes the arguments and yields the result of its signature, and sees its entry
  block's scope;
* `refNew`, `refGet` and `refSet` take a cell and its contents at the cell type's tags;
* `callCode` passes a code pointer the arguments its tags take;
* each function's entry block has an empty scope, and its parameters' tags are what linking
  recorded;
* every value a body defines, an instruction's result or a parameter of a block it enters, is an
  id below its slots, and a region has no more slots than the body it runs in.

Nothing here concerns cells or closures: a ref or a closure may be anywhere a value may, and
the machine checks a cell at each access and a closure at each call, since which function a
closure names is known only when it runs.  Nor does anything concern a rule's `Again`: its
state's Lean type is its rule's, which the wrapper's type fixes, and the operation runs again
on the operands, successors and regions it first ran on.
The lemmas at the end restate each check as the facts the machine needs.
-/

namespace Strata.Dyn.Exec

@[expose] public section

/-- A check: success, or what failed. -/
abbrev Check := Except String Unit

/-- `p` holds, or fail with `msg`. -/
def require (p : Prop) [Decidable p] (msg : String) : Check := if p then .ok () else .error msg

/-- Check `f` on each element of `l`. -/
def forAll {α : Type} (f : α → Check) : List α → Check
  | [] => .ok ()
  | x :: xs => do f x; forAll f xs

section
variable (M : RunModel)

/-- A tag, for a message: its head's environment name. -/
def tyName : Ty → String
  | .app h _ => (M.typeNames[h]?.map nameStr).getD s!"#{h}"
  | .list _ => "a list of types"

/-- `%v`, for a message. -/
def valName (v : Nat) : String := s!"%{v}"

/-- `v` is in scope at tag `t`. -/
def checkVal (Γ : Ctx) (v : Nat) (t : Ty) : Check :=
  match Γ.lookup v with
  | none => .error s!"{valName v} is not in scope"
  | some u => if u = t then .ok () else
    .error s!"{valName v} has type {tyName M u}, not {tyName M t}"

/-- `vs` have the leading tags of `ts`, and `rest` is what remains. -/
def checkArgs (Γ : Ctx) : List Nat → List Ty → List Ty → Check
  | [], ts, rest => if ts = rest then .ok () else .error "too few arguments"
  | v :: vs, t :: ts, rest => do checkVal M Γ v t; checkArgs Γ vs ts rest
  | _ :: _, [], _ => .error "too many arguments"

/-- Each of `l` is in scope at its tag. -/
def checkScope (Γ : Ctx) (l : Ctx) : Check :=
  forAll (fun p => checkVal M Γ p.1 p.2) l

end

section
variable {M : RunModel} (m : LModule M) (fn : LBody M)

/-- The context a block is checked in: its scope, then its parameters. -/
def entryCtx (b : LBlock M) : Ctx := ctxOf (ctxOf [] b.scope) b.params

/-- The ids below `fn`'s slots. -/
def checkFits (ps : Ctx) : Check :=
  forAll (fun p => require (p.1 < fn.slots)
    s!"{valName p.1} is beyond the {fn.slots} slots of {nameStr fn.name}") ps

/-- What a transfer to `t` supplies, and the scope it needs: a block's parameters and scope,
or the body's result. -/
def targetSig : LTarget → Option (List Ty × Ctx)
  | .block i => fn.blocks[i]?.map fun b => (b.paramTys, b.scope)
  | .exit => some ([fn.ret], [])

/-- The values a transfer to `t` binds: a block's parameters. -/
def targetParams : LTarget → Ctx
  | .block i => (fn.blocks[i]?.map (·.params)).getD []
  | .exit => []

/-- An edge along `s`, with a payload of tags `payload`. -/
def checkSite (Γ : Ctx) (s : LSite) (payload : List Ty) : Check :=
  match targetSig fn s.target with
  | none => .error "a transfer to no block"
  | some (ps, sc) => do
    checkArgs M Γ s.args ps payload
    checkScope M Γ sc
    checkFits fn (targetParams fn s.target)

/-- Edges along `ss`, with the payloads `ps`. -/
def checkSites (Γ : Ctx) : List LSite → List (List Ty) → Check
  | [], [] => .ok ()
  | s :: ss, p :: ps => do checkSite fn Γ s p; checkSites Γ ss ps
  | _, _ => .error "the wrong number of successors"

/-- Region `k`, run from body `fn`, takes arguments of tags `ts`, yields a value of tag `r`,
reads only values of `Γ`, and fits in `fn`'s slots. -/
def checkRegion (Γ : Ctx) (k : Nat) (ts : List Ty) (r : Ty) : Check :=
  match m.regions[k]? with
  | none => .error s!"no region {k}"
  | some f => match f.blocks[0]? with
    | none => .error s!"{nameStr f.name} has no blocks"
    | some b => (do
        require (b.paramTys = ts) "takes other arguments"
        require (f.ret = r) s!"yields {tyName M f.ret}, not {tyName M r}"
        checkScope M Γ b.scope
        require (f.slots ≤ fn.slots) s!"has more slots than {nameStr fn.name}"
        checkFits f b.params).mapError (s!"{nameStr f.name}: " ++ ·)

/-- Regions `ks`, at the signatures `rs`. -/
def checkRegions (Γ : Ctx) : List Nat → List (List Ty × Ty) → Check
  | [], [] => .ok ()
  | k :: ks, (ts, r) :: rs => do checkRegion m fn Γ k ts r; checkRegions Γ ks rs
  | _, _ => .error "the wrong number of regions"

/-- The tag of the instruction's result. -/
def insnTy (Γ : Ctx) : LInsn M → Except String Ty
  | .const _ v => return v.1
  | .pure _ ts r _ args => do
    checkArgs M Γ args ts []
    return r
  | .sem _ _ rs r ps re _ regs succs => do
    checkArgs M Γ re.args re.ts []
    checkRegions m fn Γ regs rs
    checkSites fn Γ succs ps
    return r
  | .refNew _ t v => do checkVal M Γ v t; return Ty.ref t
  | .refGet _ t c => do checkVal M Γ c (Ty.ref t); return t
  | .refSet _ t c v => do
    checkVal M Γ c (Ty.ref t)
    checkVal M Γ v t
    return M.unit
  | .callCode _ ts r f args => do
    checkVal M Γ f (Ty.fn ts r)
    checkArgs M Γ args ts []
    return r

/-- A terminator, in context `Γ`. -/
def checkTerm (Γ : Ctx) : LTerm M → Check
  | .case ts ps _ args succs => do
    checkArgs M Γ args ts []
    checkSites fn Γ succs ps
  | .sem _ rs ps re _ regs succs => do
    checkArgs M Γ re.args re.ts []
    checkRegions m fn Γ regs rs
    checkSites fn Γ succs ps

/-- Instructions `is`, then terminator `t`, in context `Γ`. -/
def checkCode (Γ : Ctx) : List (LInsn M) → LTerm M → Check
  | [], t => checkTerm m fn Γ t
  | i :: is, t =>
    if i.dst < fn.slots then
      match insnTy m fn Γ i with
      | .ok r => checkCode ((i.dst, r) :: Γ) is t
      | .error e => .error s!"{valName i.dst}: {e}"
    else .error s!"{valName i.dst} is beyond the {fn.slots} slots of {nameStr fn.name}"

/-- A block, in its entry context. -/
def checkBlock (b : LBlock M) : Check :=
  (checkCode m fn (entryCtx b) b.insns b.term).mapError
    (s!"{nameStr fn.name}, block {nameStr b.label.name}: " ++ ·)

/-- A function: its entry block reads nothing it does not define, its parameters are what
linking recorded and fit its slots, and every block checks. -/
def checkFunc : Check :=
  match fn.blocks[0]? with
  | none => .error s!"{nameStr fn.name} has no blocks"
  | some b => match b.scope with
    | [] => do
      require (fn.params = b.paramTys)
        s!"{nameStr fn.name}: its signature is not its entry block's"
      checkFits fn b.params
      forAll (checkBlock m fn) fn.blocks.toList
    | (v, _) :: _ =>
      .error s!"{nameStr fn.name}: the entry block reads {valName v}, which it does not define"

/-- A module: every function and every region body checks. -/
def checkModule : Check := do
  forAll (checkFunc m) m.funcs.toList
  forAll (fun f => forAll (checkBlock m f) f.blocks.toList) m.regions.toList

/-- `m` passed validation. -/
def WF : Prop := checkModule m = .ok ()

instance : Decidable (WF m) :=
  match h : checkModule m with
  | .ok () => isTrue h
  | .error _ => isFalse fun h₀ => nomatch h.symm.trans h₀

end

/-! ## What the checks give -/

section
variable {M : RunModel}

/-- A bind succeeds with `b` exactly when its first step succeeds with some `a` and the continuation
succeeds with `b` on `a`. -/
theorem bind_eq_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => nomatch h⟩
  | ok a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, h₀⟩ => by cases h; exact h₀⟩

/-- A check, then `y`, succeeds with `b` exactly when the check passes and `y` succeeds with `b`. -/
theorem seq_eq_ok {β : Type} {x : Check} {y : Except String β} {b : β} :
    (do x; y) = .ok b ↔ x = .ok () ∧ y = .ok b := by
  rw [bind_eq_ok]
  exact ⟨fun ⟨(), h, h₀⟩ => ⟨h, h₀⟩, fun ⟨h, h₀⟩ => ⟨(), h, h₀⟩⟩

/-- Rewriting a failure's message does not change what a computation succeeds with. -/
theorem mapError_eq_ok {α : Type} {x : Except String α} {f : String → String} {a : α} :
    x.mapError f = .ok a ↔ x = .ok a := by
  cases x with
  | error e => exact ⟨fun h => (nomatch h), fun h => nomatch h⟩
  | ok b => exact Iff.rfl

/-- `pure a` succeeds with `b` exactly when `a` is `b`. -/
theorem pure_eq_ok {α : Type} {a b : α} : (pure a : Except String α) = .ok b ↔ a = b :=
  ⟨fun h => Except.ok.inj h, fun h => h ▸ rfl⟩

/-- `forAll f l` passes exactly when `f` passes on every element of `l`. -/
theorem forAll_eq_ok {α : Type} {f : α → Check} {l : List α} :
    forAll f l = .ok () ↔ ∀ x ∈ l, f x = .ok () := by
  induction l with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | cons x xs ih => simp only [forAll, seq_eq_ok, ih, List.mem_cons, forall_eq_or_imp]

/-- `require p e` passes exactly when `p` holds. -/
theorem require_eq_ok {p : Prop} [Decidable p] {e : String} : require p e = .ok () ↔ p := by
  unfold require
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    exact ⟨fun h₀ => (nomatch h₀), fun h₀ => absurd h₀ h⟩

/-- `v` checks at tag `t` exactly when `Γ` gives `v` the tag `t`. -/
theorem checkVal_eq_ok {Γ : Ctx} {v : Nat} {t : Ty} :
    checkVal M Γ v t = .ok () ↔ Γ.lookup v = some t := by
  unfold checkVal
  split
  · rename_i h
    rw [h]
    exact ⟨fun h₀ => (nomatch h₀), fun h₀ => nomatch h₀⟩
  · rename_i u h
    rw [h, Option.some.injEq]
    split
    · rename_i hu
      exact ⟨fun _ => hu, fun _ => rfl⟩
    · rename_i hu
      exact ⟨fun h₀ => (nomatch h₀), fun h₀ => absurd h₀ hu⟩

/-- No values check against tags `ts`, leaving `rest`, exactly when `ts` is `rest`. -/
theorem checkArgs_nil {Γ : Ctx} {ts rest : List Ty} :
    checkArgs M Γ [] ts rest = .ok () ↔ ts = rest := by
  unfold checkArgs
  split
  · rename_i h
    exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    exact ⟨fun h₀ => (nomatch h₀), fun h₀ => absurd h₀ h⟩

/-- Values check against tags exactly when the first value has the first tag and the rest check
against the rest. -/
theorem checkArgs_cons {Γ : Ctx} {v : Nat} {vs : List Nat} {t : Ty} {ts rest : List Ty} :
    checkArgs M Γ (v :: vs) (t :: ts) rest = .ok () ↔
      Γ.lookup v = some t ∧ checkArgs M Γ vs ts rest = .ok () := by
  rw [← checkVal_eq_ok]
  exact seq_eq_ok

/-- Values never check against no tags: there are too many arguments. -/
theorem checkArgs_cons_nil {Γ : Ctx} {v : Nat} {vs : List Nat} {rest : List Ty} :
    checkArgs M Γ (v :: vs) [] rest ≠ .ok () :=
  fun h => nomatch h

/-- A scope checks exactly when `Γ` gives each of its values its tag. -/
theorem checkScope_eq_ok {Γ l : Ctx} :
    checkScope M Γ l = .ok () ↔ ∀ p ∈ l, Γ.lookup p.1 = some p.2 := by
  simp only [checkScope, forAll_eq_ok, checkVal_eq_ok]

variable {m : LModule M} {fn : LBody M} {Γ : Ctx}

/-- Ids fit exactly when each is below `fn`'s slots. -/
theorem checkFits_eq_ok {ps : Ctx} : checkFits fn ps = .ok () ↔ ∀ p ∈ ps, p.1 < fn.slots := by
  simp only [checkFits, forAll_eq_ok, require_eq_ok]

/-- An edge with payload `p` checks exactly when its target exists, its arguments have the leading
tags of the target's parameters with `p` the rest, `Γ` covers the target's scope, and the target's
parameters fit `fn`'s slots. -/
theorem checkSite_eq_ok {s : LSite} {p : List Ty} :
    checkSite fn Γ s p = .ok () ↔ ∃ ps sc, targetSig fn s.target = some (ps, sc) ∧
      checkArgs M Γ s.args ps p = .ok () ∧ checkScope M Γ sc = .ok () ∧
      ∀ q ∈ targetParams fn s.target, q.1 < fn.slots := by
  unfold checkSite
  split
  · rename_i h
    rw [h]
    exact ⟨fun h₀ => (nomatch h₀), fun ⟨_, _, h₀, _⟩ => nomatch h₀⟩
  · rename_i ps sc h
    rw [seq_eq_ok, seq_eq_ok, checkFits_eq_ok, h]
    refine ⟨fun ⟨h₁, h₂, h₃⟩ => ⟨ps, sc, rfl, h₁, h₂, h₃⟩, fun ⟨_, _, he, h₁, h₂, h₃⟩ => ?_⟩
    cases he
    exact ⟨h₁, h₂, h₃⟩

/-- Edges check against payloads exactly when the first edge checks with the first payload and the
rest check with the rest. -/
theorem checkSites_cons {s : LSite} {ss : List LSite} {p : List Ty} {ps : List (List Ty)} :
    checkSites fn Γ (s :: ss) (p :: ps) = .ok () ↔
      checkSite fn Γ s p = .ok () ∧ checkSites fn Γ ss ps = .ok () :=
  seq_eq_ok

/-- No edges never check against a payload: there are too few successors. -/
theorem checkSites_nil_cons {p : List Ty} {ps : List (List Ty)} :
    checkSites fn Γ [] (p :: ps) ≠ .ok () :=
  fun h => nomatch h

/-- Code that starts with instruction `i` checks exactly when `i`'s result fits `fn`'s slots, `i`
has some tag `r`, and the rest checks with `i`'s result bound at `r`. -/
theorem checkCode_cons {i : LInsn M} {is : List (LInsn M)} {t : LTerm M} :
    checkCode m fn Γ (i :: is) t = .ok () ↔ i.dst < fn.slots ∧
      ∃ r, insnTy m fn Γ i = .ok r ∧ checkCode m fn ((i.dst, r) :: Γ) is t = .ok () := by
  rw [checkCode]
  by_cases hd : i.dst < fn.slots
  · rw [ite_eq_left hd]
    cases h : insnTy m fn Γ i with
    | ok r => exact ⟨fun h₀ => ⟨hd, r, rfl, h₀⟩, fun ⟨_, r₂, h₁, h₂⟩ => by cases h₁; exact h₂⟩
    | error e => exact ⟨fun h₀ => (nomatch h₀), fun ⟨_, _, h₁, _⟩ => nomatch h₁⟩
  · rw [ite_eq_right hd]
    exact ⟨fun h₀ => (nomatch h₀), fun h₀ => absurd h₀.1 hd⟩

/-- Regions check against signatures exactly when the first region checks at the first signature and
the rest check at the rest. -/
theorem checkRegions_cons {k : Nat} {ks : List Nat} {ts : List Ty} {r : Ty}
    {rs : List (List Ty × Ty)} :
    checkRegions m fn Γ (k :: ks) ((ts, r) :: rs) = .ok () ↔
      checkRegion m fn Γ k ts r = .ok () ∧ checkRegions m fn Γ ks rs = .ok () :=
  seq_eq_ok

/-- What a region's check gives: its body and entry block, their signature, the scope, and its
slots. -/
theorem checkRegion_eq_ok {k : Nat} {ts : List Ty} {r : Ty} :
    checkRegion m fn Γ k ts r = .ok () ↔ ∃ f b, m.regions[k]? = some f ∧ f.blocks[0]? = some b ∧
      b.paramTys = ts ∧ f.ret = r ∧ checkScope M Γ b.scope = .ok () ∧ f.slots ≤ fn.slots ∧
      ∀ p ∈ b.params, p.1 < f.slots := by
  unfold checkRegion
  split
  · rename_i h
    exact ⟨fun h₀ => (nomatch h₀), fun ⟨_, _, h₀, _⟩ => by rw [h] at h₀; exact nomatch h₀⟩
  · rename_i f hf
    split
    · rename_i hb
      refine ⟨fun h₀ => (nomatch h₀), fun ⟨f₁, _, hf₁, hb₁, _⟩ => ?_⟩
      cases hf.symm.trans hf₁
      rw [hb] at hb₁
      exact nomatch hb₁
    · rename_i b hb
      simp only [mapError_eq_ok, seq_eq_ok, require_eq_ok, checkFits_eq_ok]
      refine ⟨fun ⟨h₁, h₂, h₄, h₅, h₆⟩ => ⟨f, b, hf, hb, h₁, h₂, h₄, h₅, h₆⟩, ?_⟩
      intro ⟨f₁, b₁, hf₁, hb₁, h₁, h₂, h₄, h₅, h₆⟩
      cases hf.symm.trans hf₁
      cases hb.symm.trans hb₁
      exact ⟨h₁, h₂, h₄, h₅, h₆⟩

/-- A constant's tag is its value's. -/
theorem insnTy_const {d : Nat} {v : Dyn M.interp} {r : Ty} :
    insnTy m fn Γ (.const d v) = .ok r ↔ v.1 = r := by
  simp only [insnTy, pure_eq_ok]

/-- A pure instruction has tag `r₁` exactly when its arguments have its operand tags and `r₁` is its
result tag. -/
theorem insnTy_pure {d : Nat} {ts : List Ty} {r r₁ : Ty} {f : Fn M.interp (M.interp r) ts}
    {args : List Nat} :
    insnTy m fn Γ (.pure d ts r f args) = .ok r₁ ↔ checkArgs M Γ args ts [] = .ok () ∧ r = r₁ := by
  simp only [insnTy, seq_eq_ok, pure_eq_ok]

/-- An operation instruction has tag `r₁` exactly when its arguments, regions and successors check
and `r₁` is its result tag. -/
theorem insnTy_sem {op : Name} {d : Nat} {rs : List (List Ty × Ty)} {r r₁ : Ty}
    {ps : List (List Ty)} {re : Rerun M rs ps (M.interp r)}
    {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) (M.interp r)) re.ts}
    {regs : List Nat} {succs : List LSite} :
    insnTy m fn Γ (.sem op d rs r ps re f regs succs) = .ok r₁ ↔
      checkArgs M Γ re.args re.ts [] = .ok () ∧ checkRegions m fn Γ regs rs = .ok () ∧
        checkSites fn Γ succs ps = .ok () ∧ r = r₁ := by
  simp only [insnTy, seq_eq_ok, pure_eq_ok]

/-- A `refNew` of contents `t` has tag `r` exactly when its operand has tag `t` and `r` is a ref to
`t`. -/
theorem insnTy_refNew {d : Nat} {t : Ty} {v : Nat} {r : Ty} :
    insnTy m fn Γ (.refNew d t v) = .ok r ↔ Γ.lookup v = some t ∧ Ty.ref t = r := by
  simp only [insnTy, seq_eq_ok, checkVal_eq_ok, pure_eq_ok]

/-- A `refGet` of contents `t` has tag `r` exactly when its cell is a ref to `t` and `r` is `t`. -/
theorem insnTy_refGet {d : Nat} {t : Ty} {c : Nat} {r : Ty} :
    insnTy m fn Γ (.refGet d t c) = .ok r ↔ Γ.lookup c = some (Ty.ref t) ∧ t = r := by
  simp only [insnTy, seq_eq_ok, checkVal_eq_ok, pure_eq_ok]

/-- A `callCode` has tag `r₁` exactly when its pointer has the function tag of its argument and
result tags, its arguments have those argument tags, and `r₁` is the result tag. -/
theorem insnTy_callCode {d : Nat} {ts : List Ty} {r r₁ : Ty} {f : Nat} {args : List Nat} :
    insnTy m fn Γ (.callCode d ts r f args) = .ok r₁ ↔ Γ.lookup f = some (Ty.fn ts r) ∧
      checkArgs M Γ args ts [] = .ok () ∧ r = r₁ := by
  simp only [insnTy, seq_eq_ok, checkVal_eq_ok, pure_eq_ok]

/-- A `refSet` of contents `t` has tag `r` exactly when its cell is a ref to `t`, its value has tag
`t`, and `r` is the unit tag. -/
theorem insnTy_refSet {d : Nat} {t : Ty} {c v : Nat} {r : Ty} :
    insnTy m fn Γ (.refSet d t c v) = .ok r ↔ Γ.lookup c = some (Ty.ref t) ∧
      Γ.lookup v = some t ∧ M.unit = r := by
  simp only [insnTy, seq_eq_ok, checkVal_eq_ok, pure_eq_ok]

/-- A `case` terminator checks exactly when its arguments have its operand tags and its successors
check with their payloads. -/
theorem checkTerm_case {ts : List Ty} {ps : List (List Ty)}
    {f : Fn M.interp (Exit M.interp ps) ts} {args : List Nat} {succs : List LSite} :
    checkTerm m fn Γ (.case ts ps f args succs) = .ok () ↔
      checkArgs M Γ args ts [] = .ok () ∧ checkSites fn Γ succs ps = .ok () := by
  simp only [checkTerm, seq_eq_ok]

/-- An operation terminator checks exactly when its arguments, regions and successors check. -/
theorem checkTerm_sem {op : Name} {rs : List (List Ty × Ty)} {ps : List (List Ty)}
    {re : Rerun M rs ps Empty}
    {f : Fn M.interp (Tree M.interp Run M.W rs ps (M.St re.key) Empty) re.ts}
    {regs : List Nat} {succs : List LSite} :
    checkTerm m fn Γ (.sem op rs ps re f regs succs) = .ok () ↔
      checkArgs M Γ re.args re.ts [] = .ok () ∧ checkRegions m fn Γ regs rs = .ok () ∧
        checkSites fn Γ succs ps = .ok () := by
  simp only [checkTerm, seq_eq_ok]

/-- In a well-formed module, every function's entry block has an empty scope and the
function's parameters, which fit its slots, and every block checks in its entry context. -/
theorem WF.func (hwf : WF m) {f : LBody M} (hf : f ∈ m.funcs) :
    (∃ b, f.blocks[0]? = some b ∧ b.scope = [] ∧ f.params = b.paramTys ∧
      ∀ p ∈ b.params, p.1 < f.slots) ∧
      ∀ b ∈ f.blocks, checkCode m f (entryCtx b) b.insns b.term = .ok () := by
  have h := forAll_eq_ok.mp (seq_eq_ok.mp hwf).1 f (Array.mem_def.mp hf)
  unfold checkFunc at h
  split at h
  · exact nomatch h
  · rename_i b hb
    split at h
    · rename_i hs
      obtain ⟨hsig, hfits, h⟩ := (seq_eq_ok.trans (and_congr_right' seq_eq_ok)).mp h
      exact ⟨⟨b, hb, hs, require_eq_ok.mp hsig, checkFits_eq_ok.mp hfits⟩, fun b₁ hb₁ =>
        mapError_eq_ok.mp (forAll_eq_ok.mp h b₁ (Array.mem_def.mp hb₁))⟩
    · exact nomatch h

/-- In a well-formed module, every block of every region checks in its entry context. -/
theorem WF.region (hwf : WF m) {f : LBody M} (hf : f ∈ m.regions) :
    ∀ b ∈ f.blocks, checkCode m f (entryCtx b) b.insns b.term = .ok () := fun b hb =>
  mapError_eq_ok.mp (forAll_eq_ok.mp (forAll_eq_ok.mp (seq_eq_ok.mp hwf).2 f
    (Array.mem_def.mp hf)) b (Array.mem_def.mp hb))

end

end

end Strata.Dyn.Exec
