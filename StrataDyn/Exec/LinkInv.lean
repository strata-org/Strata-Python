/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Link

set_option autoImplicit false

/-!
# A program logic for linking

`link_inv`: every instruction and terminator of every function and every region of a linked
module satisfies a link invariant (`LinkInv`).  An invariant is a predicate on linked
instructions and one on linked terminators, together with a predicate on wrappers that every
wrapper of the table satisfies; what linking makes of such a wrapper satisfies the invariant,
and so does every instruction that linking makes with no wrapper.  `link_rulesOK`
(`CertLink.lean`: a certified model's rules are certified) is an instance.

* `LinkedApp`, `LinkedTermApp`: what `linkApp` and `linkTermApp` make of a wrapper, uncurried in
  its operands.  `NativeInsn`: the instructions that linking makes with no wrapper.
* `LinkInv`: the invariant, and `link_inv`, that a linked module satisfies it (`LModule.All`).

The proof is private.  It is a Hoare logic over the link monad: a run that ends with no missing
rule started with none, keeps the collected regions satisfying the invariant, and returns a
result satisfying a postcondition.  `link` fails unless no rule is missing, so a missing rule's
terminator, `missingTerm`, need satisfy nothing.  A mutual induction follows `linkRegion` and
the definitions it calls.
-/

namespace Strata.Dyn.Exec

public section

variable {M : Model}

/-! ## Link computations -/

/-- Every region that the link state `st` has collected satisfies `R`. -/
private def LinkState.RegionsSat (R : LBody M.at → Prop) (st : LinkState M) : Prop :=
  ∀ g ∈ st.regions, R g

/-- **A postcondition of a link computation**: a run of `x` that ends with no missing rule
started with none, ends with collected regions that satisfy `R` if it started with such, and
returns a result that satisfies `P`. -/
private def LinkM.Ok (R : LBody M.at → Prop) {β : Type} (x : LinkM M β) (P : β → Prop) : Prop :=
  ∀ ctx st b st₁, x ctx st = .ok (b, st₁) → st₁.missing = #[] →
    st.missing = #[] ∧ (st.RegionsSat R → st₁.RegionsSat R) ∧ P b

namespace LinkM.Ok

variable {R : LBody M.at → Prop} {β γ : Type}

/-- `pure b` satisfies `P` when `b` does. -/
private theorem pure {b : β} {P : β → Prop} (h : P b) : LinkM.Ok R (Pure.pure b) P := by
  intro ctx st b₁ st₁ hx hm
  cases hx
  exact ⟨hm, id, h⟩

/-- A bind satisfies `P` when its first part satisfies `Q`, and its rest satisfies `P` given
`Q` of the first part's result. -/
private theorem bind {x : LinkM M β} {f : β → LinkM M γ} {Q : β → Prop} {P : γ → Prop}
    (hx : LinkM.Ok R x Q) (hf : ∀ b, LinkM.Ok R (f b) fun c => Q b → P c) :
    LinkM.Ok R (x >>= f) P := by
  intro ctx st c st₂ h hm
  change (x ctx st).bind (fun p => f p.1 ctx p.2) = .ok (c, st₂) at h
  cases hx₁ : x ctx st with
  | error => rw [hx₁] at h; cases h
  | ok p =>
    rw [hx₁] at h
    obtain ⟨hm₁, hr₁, hp⟩ := hf p.1 ctx p.2 c st₂ h hm
    obtain ⟨hm₀, hr₀, hq⟩ := hx ctx st p.1 p.2 hx₁ hm₁
    exact ⟨hm₀, hr₁ ∘ hr₀, hp hq⟩

/-- A weaker postcondition. -/
private theorem imp {x : LinkM M β} {P Q : β → Prop} (h : LinkM.Ok R x P) (hPQ : ∀ b, P b → Q b) :
    LinkM.Ok R x Q := fun ctx st b st₁ hx hm =>
  let ⟨h₁, h₂, h₃⟩ := h ctx st b st₁ hx hm
  ⟨h₁, h₂, hPQ b h₃⟩

/-- A bind satisfies `P` when its first part satisfies `Q`, and its rest satisfies `P` and keeps
the collected regions satisfying `R` given `Q` of the first part's result. -/
private theorem bind_dep {x : LinkM M β} {f : β → LinkM M γ} {Q : β → Prop} {P : γ → Prop}
    (hx : LinkM.Ok R x Q)
    (hf : ∀ b ctx st c st₁, f b ctx st = .ok (c, st₁) → st₁.missing = #[] →
      st.missing = #[] ∧ (Q b → st.RegionsSat R → st₁.RegionsSat R) ∧ P c) :
    LinkM.Ok R (x >>= f) P := by
  intro ctx st c st₂ h hm
  change (x ctx st).bind (fun p => f p.1 ctx p.2) = .ok (c, st₂) at h
  cases hx₁ : x ctx st with
  | error => rw [hx₁] at h; cases h
  | ok p =>
    rw [hx₁] at h
    obtain ⟨hm₁, hr₁, hp⟩ := hf p.1 ctx p.2 c st₂ h hm
    obtain ⟨hm₀, hr₀, hq⟩ := hx ctx st p.1 p.2 hx₁ hm₁
    exact ⟨hm₀, hr₁ hq ∘ hr₀, hp⟩

/-- A bind satisfies `P` when its first part satisfies `True` and its rest satisfies `P`. -/
private theorem bind_true {x : LinkM M β} {f : β → LinkM M γ} {P : γ → Prop}
    (hx : LinkM.Ok R x fun _ => True) (hf : ∀ b, LinkM.Ok R (f b) P) : LinkM.Ok R (x >>= f) P :=
  bind hx fun b => (hf b).imp fun _ h _ => h

/-- A map satisfies `P` when its argument satisfies `P` after the map. -/
private theorem map {x : LinkM M β} {g : β → γ} {P : γ → Prop}
    (hx : LinkM.Ok R x fun b => P (g b)) :
    LinkM.Ok R (g <$> x) P := by
  rw [map_eq_pure_bind]
  exact bind hx fun _ => pure id

/-- A throw satisfies every postcondition. -/
private theorem throw {e : Fault} {P : β → Prop} :
    LinkM.Ok R (MonadExcept.throw e : LinkM M β) P := by
  intro ctx st b st₁ h
  cases h

/-- A link error satisfies every postcondition. -/
private theorem linkError {msg : String} {P : β → Prop} :
    LinkM.Ok R (Exec.linkError msg : LinkM M β) P :=
  throw

/-- A bind after a link error satisfies every postcondition. -/
private theorem linkError_bind {msg : String} {f : β → LinkM M γ} {P : γ → Prop} :
    LinkM.Ok R ((Exec.linkError msg : LinkM M β) >>= f) P := by
  intro ctx st c st₁ h
  cases h

/-- Reading the context satisfies `True`. -/
private theorem read : LinkM.Ok R (MonadReader.read : LinkM M LinkCtx) fun _ => True := by
  intro ctx st b st₁ h hm
  cases h
  exact ⟨hm, id, trivial⟩

/-- Recording a missing rule satisfies every postcondition: a rule is missing after it. -/
private theorem addMissing {op : Name} {P : Unit → Prop} :
    LinkM.Ok R (Exec.addMissing (M := M) op) P := by
  intro ctx st b st₁ h hm
  cases h
  exfalso
  by_cases hc : st.missing.contains op = true
  · dsimp only at hm
    rw [ite_eq_left hc] at hm
    rw [hm] at hc
    simp at hc
  · dsimp only at hm
    rw [ite_eq_right hc] at hm
    simpa using congrArg Array.size hm

/-- A computation in a changed context satisfies what it does. -/
private theorem withReader {x : LinkM M β} {g : LinkCtx → LinkCtx} {P : β → Prop}
    (h : LinkM.Ok R x P) :
    LinkM.Ok R (MonadWithReader.withReader g x) P := fun ctx st b st₁ hx hm =>
  h (g ctx) st b st₁ hx hm

/-- A `mapM` whose every step satisfies `P` gives results that all do. -/
private theorem mapM {f : β → LinkM M γ} {P : γ → Prop} (hf : ∀ a, LinkM.Ok R (f a) P) :
    ∀ l : List β, LinkM.Ok R (l.mapM f) fun cs => ∀ c ∈ cs, P c
  | [] => pure (by simp)
  | a :: l => by
    rw [List.mapM_cons]
    refine bind (hf a) fun c => bind (mapM hf l) fun cs => pure ?_
    intro hcs hc d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hc
    · exact hcs d hd

/-- A `mapM` whose every step satisfies `True` does. -/
private theorem mapM_true {f : β → LinkM M γ} (hf : ∀ a, LinkM.Ok R (f a) fun _ => True)
    (l : List β) :
    LinkM.Ok R (l.mapM f) fun _ => True :=
  (mapM hf l).imp fun _ _ => trivial

/-- An array `mapM` whose every step satisfies `True` does. -/
private theorem arrayMapM_true {f : β → LinkM M γ} (hf : ∀ a, LinkM.Ok R (f a) fun _ => True)
    (xs : Array β) : LinkM.Ok R (xs.mapM f) fun _ => True := by
  rw [Array.mapM_eq_mapM_toList]
  exact map (mapM_true hf xs.toList)

end LinkM.Ok

/-! ## Steps that collect no region -/

section
variable {R : LBody M.at → Prop}

/-- Resolving a type collects no region. -/
private theorem tyCode_ok {env : Env Unit} {k : Kind} (t : TypeExpr env #[] k) :
    LinkM.Ok R (tyCode (M := M) t) fun _ => True := by
  unfold tyCode
  split
  · exact LinkM.Ok.pure trivial
  · exact LinkM.Ok.linkError

/-- Resolving a target collects no region. -/
private theorem linkSite_ok (labels : LabelMap Nat) (k : Target.Raw) :
    LinkM.Ok R (linkSite (M := M) labels k) fun _ => True := by
  unfold linkSite
  split
  · exact LinkM.Ok.pure trivial
  · split
    · exact LinkM.Ok.pure trivial
    · exact LinkM.Ok.linkError

/-- Resolving type arguments collects no region. -/
private theorem typeArgCodes_ok {env : Env Unit} {params : Array Kind}
    (typeArgs : TypeArgs env params) (n : Nat) :
    LinkM.Ok R (typeArgCodes (M := M) typeArgs n) fun _ => True := by
  unfold typeArgCodes
  refine LinkM.Ok.bind_true (LinkM.Ok.mapM_true (fun a => tyCode_ok _) _) fun cs => ?_
  split
  · exact LinkM.Ok.pure trivial
  · exact LinkM.Ok.linkError

/-- Resolving parameters collects no region. -/
private theorem linkParams_ok {env : Env Unit} (ps : List (ValDecl env)) :
    LinkM.Ok R (linkParams (M := M) ps) fun _ => True := by
  unfold linkParams
  exact LinkM.Ok.mapM_true
    (fun d => LinkM.Ok.bind_true (tyCode_ok _) fun _ => LinkM.Ok.pure trivial) ps

/-- Computing a body's scopes collects no region. -/
private theorem bodyScopes_ok {env : Env Unit} {α : Type} (labels : LabelMap Nat)
    (blocks : List (Block env α)) (outer : Ctx) :
    LinkM.Ok R (bodyScopes (M := M) labels blocks outer) fun _ => True := by
  unfold bodyScopes blockDefs
  refine LinkM.Ok.bind_true (LinkM.Ok.arrayMapM_true (fun b => ?_) _) fun _ => LinkM.Ok.pure trivial
  refine LinkM.Ok.bind_true (LinkM.Ok.bind_true (linkParams_ok _) fun _ => ?_) fun _ =>
    LinkM.Ok.pure trivial
  exact LinkM.Ok.bind_true (LinkM.Ok.mapM_true (fun i => LinkM.Ok.bind_true (tyCode_ok _) fun _ =>
    LinkM.Ok.pure trivial) _) fun _ => LinkM.Ok.pure trivial

end

/-! ## What linking makes -/

variable (M) in
/-- **An instruction that linking makes with no wrapper**: a literal's or a code pointer's
constant, or one of the machine's heap and call instructions. -/
inductive NativeInsn : LInsn M.at → Prop
  | fn (dst : Nat) (ts : List Ty) (r : Ty) (i : Nat) :
    NativeInsn (.const dst ⟨Ty.fn ts r, M.at.fnAt ts r i⟩)
  | unit (dst : Nat) : NativeInsn (.const dst ⟨M.unit, M.unitVal Run⟩)
  | bool (dst : Nat) (b : Bool) : NativeInsn (.const dst ⟨M.bool, M.ofBool Run b⟩)
  | int (dst : Nat) (i : Int) : NativeInsn (.const dst ⟨M.int, M.ofInt Run i⟩)
  | float (dst : Nat) (x : Float) : NativeInsn (.const dst ⟨M.float, M.ofFloat Run x⟩)
  | str (dst : Nat) (x : String) : NativeInsn (.const dst ⟨M.str, M.ofStr Run x⟩)
  | refNew (dst : Nat) (t : Ty) (v : Nat) : NativeInsn (.refNew dst t v)
  | refGet (dst : Nat) (t : Ty) (cell : Nat) : NativeInsn (.refGet dst t cell)
  | refSet (dst : Nat) (t : Ty) (cell v : Nat) : NativeInsn (.refSet dst t cell v)
  | callCode (dst : Nat) (ts : List Ty) (r : Ty) (f : Nat) (args : List Nat) :
    NativeInsn (.callCode dst ts r f args)

/-- **What `linkApp` makes of a wrapper**: `i` is the instruction `dst = op args` linked from the
wrapper `impl` of shape `s`, uncurried in its operands, with rule state `M.St key`, successors
`succs` and regions `regs`.  A pure wrapper gives a pure instruction; a rule's wrapper gives a
rule's instruction, whose tree for its `Again` is the wrapper's if the rule loops and linking's
`noAgain` if not. -/
inductive LinkedApp (op : Name) (dst : Nat) (key : Nat × Array Ty) (args : List Nat)
    (succs : List LSite) (regs : List Nat) :
    (s : Shape) → Impl Run M.at.interp M.at.W s (M.at.St key) → LInsn M.at → Prop
  | pure {as : List Ty} {var : Option Ty} {r : Ty}
    {f : Fn M.at.interp (VarFn M.at.interp var (M.at.interp r)) as} {ts : List Ty}
    {g : Fn M.at.interp (M.at.interp r) ts} :
    uncurry as var f args.length = some ⟨ts, g⟩ →
    LinkedApp op dst key args succs regs ⟨as, var, some r, [], []⟩ (.pure f)
      (.pure dst ts r g args)
  | sem {as : List Ty} {var : Option Ty} {r : Ty} {ps : List (List Ty)}
    {rs : List (List Ty × Ty)}
    {f : Fn M.at.interp
      (VarFn M.at.interp var (Tree M.at.interp Run M.at.W rs ps (M.at.St key) (M.at.interp r))) as}
    {ts : List Ty} {g : Fn M.at.interp (Tree M.at.interp Run M.at.W rs ps (M.at.St key)
      (M.at.interp r)) ts} :
    uncurry as var f args.length = some ⟨ts, g⟩ →
    LinkedApp op dst key args succs regs ⟨as, var, some r, ps, rs⟩ (.sem f)
      (.sem op dst rs r ps ⟨key, ts, args, Fn.const (noAgain (M := M)) ts⟩ g regs succs)
  | loop {as : List Ty} {var : Option Ty} {r : Ty} {ps : List (List Ty)}
    {rs : List (List Ty × Ty)}
    {f : Fn M.at.interp
      (VarFn M.at.interp var (Tree M.at.interp Run M.at.W rs ps (M.at.St key) (M.at.interp r))) as}
    {again : Fn M.at.interp (VarFn M.at.interp var
      (M.at.St key → Tree M.at.interp Run M.at.W rs ps (M.at.St key) (M.at.interp r))) as}
    {ts : List Ty} {g : Fn M.at.interp (Tree M.at.interp Run M.at.W rs ps (M.at.St key)
      (M.at.interp r)) ts}
    {g₁ : Fn M.at.interp
      (M.at.St key → Tree M.at.interp Run M.at.W rs ps (M.at.St key) (M.at.interp r)) ts} :
    uncurry as var f args.length = some ⟨ts, g⟩ →
    uncurry as var again args.length = some ⟨ts, g₁⟩ →
    LinkedApp op dst key args succs regs ⟨as, var, some r, ps, rs⟩ (.loop f again)
      (.sem op dst rs r ps ⟨key, ts, args, g₁⟩ g regs succs)

/-- **What `linkTermApp` makes of a wrapper**: `t` is the terminator `op args` linked from the
wrapper `impl` of shape `s`, as `LinkedApp` says for an instruction: a pure wrapper gives a case
terminator, and a rule's wrapper a rule's terminator. -/
inductive LinkedTermApp (op : Name) (key : Nat × Array Ty) (args : List Nat)
    (succs : List LSite) (regs : List Nat) :
    (s : Shape) → Impl Run M.at.interp M.at.W s (M.at.St key) → LTerm M.at → Prop
  | case {as : List Ty} {var : Option Ty} {ps : List (List Ty)}
    {f : Fn M.at.interp (VarFn M.at.interp var (Exit M.at.interp ps)) as} {ts : List Ty}
    {g : Fn M.at.interp (Exit M.at.interp ps) ts} :
    uncurry as var f args.length = some ⟨ts, g⟩ →
    LinkedTermApp op key args succs regs ⟨as, var, none, ps, []⟩ (.pure f)
      (.case ts ps g args succs)
  | sem {as : List Ty} {var : Option Ty} {ps : List (List Ty)} {rs : List (List Ty × Ty)}
    {f : Fn M.at.interp
      (VarFn M.at.interp var (Tree M.at.interp Run M.at.W rs ps (M.at.St key) Empty)) as}
    {ts : List Ty} {g : Fn M.at.interp (Tree M.at.interp Run M.at.W rs ps (M.at.St key) Empty) ts} :
    uncurry as var f args.length = some ⟨ts, g⟩ →
    LinkedTermApp op key args succs regs ⟨as, var, none, ps, rs⟩ (.sem f)
      (.sem op rs ps ⟨key, ts, args, Fn.const (noAgain (M := M)) ts⟩ g regs succs)
  | loop {as : List Ty} {var : Option Ty} {ps : List (List Ty)} {rs : List (List Ty × Ty)}
    {f : Fn M.at.interp
      (VarFn M.at.interp var (Tree M.at.interp Run M.at.W rs ps (M.at.St key) Empty)) as}
    {again : Fn M.at.interp (VarFn M.at.interp var
      (M.at.St key → Tree M.at.interp Run M.at.W rs ps (M.at.St key) Empty)) as}
    {ts : List Ty} {g : Fn M.at.interp (Tree M.at.interp Run M.at.W rs ps (M.at.St key) Empty) ts}
    {g₁ : Fn M.at.interp (M.at.St key → Tree M.at.interp Run M.at.W rs ps (M.at.St key) Empty) ts} :
    uncurry as var f args.length = some ⟨ts, g⟩ →
    uncurry as var again args.length = some ⟨ts, g₁⟩ →
    LinkedTermApp op key args succs regs ⟨as, var, none, ps, rs⟩ (.loop f again)
      (.sem op rs ps ⟨key, ts, args, g₁⟩ g regs succs)

section
variable {R : LBody M.at → Prop} {op : Name} {key : Nat × Array Ty} {args : List Nat}
  {succs : List LSite} {regs : List Nat}

/-- The proof that `linkApp` and `linkTermApp` make what `LinkedApp` and `LinkedTermApp` say:
the two have the same cases. -/
local macro "linked_tac" : tactic => `(tactic| (
  split
  next =>
    split
    next hu =>
      dsimp only
      split
      · exact LinkM.Ok.pure (by constructor; exact hu)
      · exact LinkM.Ok.linkError_bind
    next => exact LinkM.Ok.linkError
  next =>
    split
    next hu => exact LinkM.Ok.pure (.sem hu)
    next => exact LinkM.Ok.linkError
  next =>
    split
    next hu =>
      split
      next hu₁ =>
        split
        next he =>
          subst he
          exact LinkM.Ok.pure (.loop hu hu₁)
        next => exact LinkM.Ok.linkError
      next => exact LinkM.Ok.linkError
    next => exact LinkM.Ok.linkError
  next => exact LinkM.Ok.linkError))

/-- `linkApp` makes what `LinkedApp` says. -/
private theorem linkApp_linked {dst : Nat} (s : Shape)
    (impl : Impl Run M.at.interp M.at.W s (M.at.St key)) :
    LinkM.Ok R (linkApp op dst key args succs regs s impl)
      (LinkedApp op dst key args succs regs s impl) := by
  unfold linkApp
  linked_tac

/-- `linkTermApp` makes what `LinkedTermApp` says. -/
private theorem linkTermApp_linked (s : Shape)
    (impl : Impl Run M.at.interp M.at.W s (M.at.St key)) :
    LinkM.Ok R (linkTermApp op key args succs regs s impl)
      (LinkedTermApp op key args succs regs s impl) := by
  unfold linkTermApp
  linked_tac

/-- A linked constant is native. -/
private theorem linkConst_native {env : Env Unit} (dst : Nat) (type : TypeExpr env) (c : Const) :
    LinkM.Ok R (linkConst (M := M) dst type c) (NativeInsn M) := by
  cases c <;> unfold linkConst
  case func f =>
    refine LinkM.Ok.bind_true LinkM.Ok.read fun ctx => ?_
    split
    · refine LinkM.Ok.bind_true (tyCode_ok _) fun t => ?_
      split
      · refine LinkM.Ok.bind_true LinkM.Ok.read fun ctx => ?_
        split
        · exact LinkM.Ok.pure (.fn _ _ _ _)
        · exact LinkM.Ok.linkError
      · exact LinkM.Ok.linkError
    · exact LinkM.Ok.throw
  case unit => exact LinkM.Ok.pure (.unit _)
  case bool => exact LinkM.Ok.pure (.bool _ _)
  case int => exact LinkM.Ok.pure (.int _ _)
  case float => exact LinkM.Ok.pure (.float _ _)
  case str => exact LinkM.Ok.pure (.str _ _)
  case ghost => exact LinkM.Ok.linkError

end

/-! ## Link invariants -/

variable (M) in
/-- **A link invariant**: predicates `insn` and `term` on linked instructions and terminators,
and `wrapper` on wrappers, such that every wrapper of the table satisfies `wrapper`, as linking
casts it to its key's state type; what linking makes of a wrapper that satisfies `wrapper`
satisfies `insn` or `term`; and so does every instruction that linking makes with no
wrapper. -/
structure LinkInv where
  wrapper : (key : Nat × Array Ty) → (s : Shape) → Impl Run M.at.interp M.at.W s (M.at.St key) →
    Prop
  insn : LInsn M.at → Prop
  term : LTerm M.at → Prop
  table : ∀ {k : Nat} {n : Name} {o : OpImpl M.interp M.W} (hk : M.ops[k]? = some (n, o))
    (targs : Vector Ty o.typeArgc),
    wrapper (k, targs.toArray) (o.shape targs)
      (cast (congrArg (Impl Run M.at.interp M.at.W (o.shape targs))
        (M.stateOf_eq Run hk targs).symm) (o.fn Run targs))
  native : ∀ {i : LInsn M.at}, NativeInsn M i → insn i
  app : ∀ {op : Name} {dst : Nat} {key : Nat × Array Ty} {args : List Nat} {succs : List LSite}
    {regs : List Nat} {s : Shape} {impl : Impl Run M.at.interp M.at.W s (M.at.St key)}
    {i : LInsn M.at}, wrapper key s impl → LinkedApp op dst key args succs regs s impl i → insn i
  termApp : ∀ {op : Name} {key : Nat × Array Ty} {args : List Nat} {succs : List LSite}
    {regs : List Nat} {s : Shape} {impl : Impl Run M.at.interp M.at.W s (M.at.St key)}
    {t : LTerm M.at}, wrapper key s impl → LinkedTermApp op key args succs regs s impl t → term t

/-! ## Linking bodies -/

section
variable {env : Env Unit} {α : Type} (P : LinkInv M)

mutual

/-- Linking a region keeps the collected regions satisfying the invariant. -/
private theorem linkRegion_inv (fname : Name) (scope : Ctx) (retTy : Ty) :
    ∀ r : Dyn.Region env α,
      LinkM.Ok (·.All P.insn P.term) (linkRegion fname scope retTy r) fun _ => True
  | ⟨⟨blocks⟩⟩ => by
    rw [linkRegion]
    refine LinkM.Ok.bind_true (bodyScopes_ok _ _ _) fun sc =>
      LinkM.Ok.bind_dep (linkBlocks_inv _ _ 0 blocks) fun lbs ctx st b st₁ h hm => ?_
    cases h
    refine ⟨hm, fun hl hr g hg => ?_, trivial⟩
    rcases Array.mem_push.mp hg with hg | rfl
    · exact hr g hg
    · exact fun blk hblk => hl blk (Array.mem_def.mp hblk)

/-- Linking an instruction's regions keeps the collected regions satisfying the invariant. -/
private theorem linkRegions_inv (fname : Name) (Γ : Ctx) :
    ∀ (rs : List (Dyn.Region env α)) (sigs : List (List Ty × Ty)),
      LinkM.Ok (·.All P.insn P.term) (linkRegions fname Γ rs sigs) fun _ => True
  | [], [] => by
    rw [linkRegions]
    exact LinkM.Ok.pure trivial
  | r :: rs, sig :: sigs => by
    rw [linkRegions]
    exact LinkM.Ok.bind_true (linkRegion_inv fname Γ sig.2 r) fun _ =>
      LinkM.Ok.bind_true (linkRegions_inv fname Γ rs sigs) fun _ => LinkM.Ok.pure trivial
  | [], _ :: _ | _ :: _, [] => by
    unfold linkRegions
    exact LinkM.Ok.linkError

/-- Linked blocks satisfy the invariant. -/
private theorem linkBlocks_inv (labels : LabelMap Nat) (scopes : Array Ctx) (i : Nat) :
    ∀ bs : List (Block env α), LinkM.Ok (·.All P.insn P.term) (linkBlocks labels scopes i bs)
      fun lbs => ∀ b ∈ lbs, b.All P.insn P.term
  | [] => by
    rw [linkBlocks]
    exact LinkM.Ok.pure (by simp)
  | ⟨label, params, ⟨instrs⟩, term, _⟩ :: bs => by
    rw [linkBlocks]
    refine LinkM.Ok.bind_true (linkParams_ok _) fun ps =>
      LinkM.Ok.bind (linkInsns_inv _ _ instrs) fun p => ?_
    obtain ⟨insns, Γ⟩ := p
    refine LinkM.Ok.bind (linkTerm_inv _ _ term) fun t =>
      LinkM.Ok.bind (linkBlocks_inv _ _ _ bs) fun lbs => LinkM.Ok.pure ?_
    intro hl ht hi b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨hi, ht⟩
    · exact hl b hb

/-- Linked instructions satisfy the invariant. -/
private theorem linkInsns_inv (labels : LabelMap Nat) (Γ : Ctx) :
    ∀ is : List (Instruction env α),
      LinkM.Ok (·.All P.insn P.term) (linkInsns labels Γ is) fun p => ∀ i ∈ p.1, P.insn i
  | [] => by
    rw [linkInsns]
    exact LinkM.Ok.pure (by simp)
  | ins :: is => by
    rw [linkInsns]
    refine LinkM.Ok.bind (linkInsn_inv _ _ ins) fun li =>
      LinkM.Ok.bind (linkInsns_inv _ _ is) fun p => ?_
    obtain ⟨lis, Γ⟩ := p
    refine LinkM.Ok.pure ?_
    intro hl hi x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hi
    · exact hl x hx

/-- A linked instruction satisfies the invariant. -/
private theorem linkInsn_inv (labels : LabelMap Nat) (Γ : Ctx) :
    ∀ ins : Instruction env α, LinkM.Ok (·.All P.insn P.term) (linkInsn labels Γ ins) P.insn
  | .const _ d c => by
    rw [linkInsn]
    exact (linkConst_native _ _ c).imp fun _ => P.native
  | .apply _ d r typeArgs args succs ⟨regions⟩ => by
    rw [linkInsn]
    refine LinkM.Ok.bind_true (LinkM.Ok.mapM_true (linkSite_ok labels) _) fun sl => ?_
    split
    · exact LinkM.Ok.bind_true LinkM.Ok.addMissing fun _ => LinkM.Ok.pure (P.native (.unit _))
    · split
      · exact LinkM.Ok.linkError
      next n o hk =>
        exact LinkM.Ok.bind_true (typeArgCodes_ok _ _) fun targs =>
          LinkM.Ok.bind_true (linkRegions_inv _ _ regions _) fun regs =>
            (linkApp_linked _ _).imp fun _ => P.app (P.table hk targs)
    · dsimp only
      split
      case isFalse => exact LinkM.Ok.linkError_bind
      split
      all_goals first
        | exact LinkM.Ok.linkError
        | exact LinkM.Ok.bind_true (typeArgCodes_ok _ _) fun _ => LinkM.Ok.pure (P.native (by
            constructor))
        | refine LinkM.Ok.bind_true (typeArgCodes_ok _ _) fun _ => ?_
          split
          · exact LinkM.Ok.pure (P.native (.callCode _ _ _ _ _))
          · exact LinkM.Ok.linkError

/-- A linked terminator satisfies the invariant. -/
private theorem linkTerm_inv (labels : LabelMap Nat) (Γ : Ctx) :
    ∀ t : Terminator env α, LinkM.Ok (·.All P.insn P.term) (linkTerm labels Γ t) P.term
  | .apply _ r typeArgs args succs ⟨regions⟩ => by
    rw [linkTerm]
    refine LinkM.Ok.bind_true (LinkM.Ok.mapM_true (linkSite_ok labels) _) fun sl => ?_
    split
    · split
      · exact LinkM.Ok.linkError
      next n o hk =>
        exact LinkM.Ok.bind_true (typeArgCodes_ok _ _) fun targs =>
          LinkM.Ok.bind_true (linkRegions_inv _ _ regions _) fun regs =>
            (linkTermApp_linked _ _).imp fun _ => P.termApp (P.table hk targs)
    · exact LinkM.Ok.linkError
    · exact LinkM.Ok.bind (Q := fun _ => False) LinkM.Ok.addMissing fun _ =>
        LinkM.Ok.pure False.elim

end

/-- A linked function's body satisfies the invariant. -/
private theorem linkFunc_inv (f : Func env α) :
    LinkM.Ok (·.All P.insn P.term) (linkFunc f) (·.All P.insn P.term) := by
  unfold linkFunc
  refine LinkM.Ok.bind (LinkM.Ok.withReader (LinkM.Ok.bind_true (bodyScopes_ok _ _ _) fun _ =>
    linkBlocks_inv P _ _ 0 _)) fun lbs => LinkM.Ok.bind_true (tyCode_ok _) fun _ =>
      LinkM.Ok.pure ?_
  intro hl blk hblk
  exact hl blk (Array.mem_def.mp hblk)

end

/-- A bind of `Except` that succeeds has a first part that succeeds. -/
private theorem except_bind_ok {ε β γ : Type} {x : Except ε β} {f : β → Except ε γ} {c : γ}
    (h : (x >>= f) = .ok c) : ∃ b, x = .ok b ∧ f b = .ok c := by
  cases x with
  | error e => cases h
  | ok b => exact ⟨b, rfl, h⟩

/-- **Linking keeps a link invariant**: every instruction and terminator of every function and
every region of a module that links against `M` satisfies the invariant. -/
theorem link_inv (P : LinkInv M) {env : Env Unit} [base ≼ env] {α : Type} {m : Module env α}
    {lm : LModule M.at} (h : link M m = .ok lm) : lm.All P.insn P.term := by
  unfold link at h
  dsimp only at h
  split at h
  next funcs _ =>
    obtain ⟨sigs, -, h⟩ := except_bind_ok h
    obtain ⟨⟨fs, st⟩, hrun, h⟩ := except_bind_ok h
    dsimp only at h
    split at h
    next hm =>
      cases h
      have hst : st.missing = #[] := by simpa using hm
      obtain ⟨-, hr, hf⟩ := LinkM.Ok.mapM (fun f => linkFunc_inv P f) _ _ _ _ _ hrun hst
      exact ⟨fun g hg => hf g (Array.mem_def.mp hg), hr fun g hg => absurd hg (by simp)⟩
    next => cases h
  next => cases h

end

end Strata.Dyn.Exec
