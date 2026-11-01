/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec
public import StrataDyn.Exec.CertCapsProps
public import StrataDyn.Exec.EffectsProps
public import StrataPython.Dyn.Sem.Invariant
public import StrataPython.Dyn.Sem.WorldProps

set_option autoImplicit false

/-!
# The rule monad

`PyM σ e free α` is a computation of a rule at the effect `e`, generic in the machine's requests
and in the rule's exits, with the proofs that it reaches only the cells and closures it is given
and stays within `e`.  Every rule that
touches Python's state, except `globalCell` and `mkClosure`, runs one `PyM` computation, through `runRule` or
`runTotal`, or, when `free`, through `runRuleFree` or `runTotalFree`, which don't read the store
first.

* `PyLang` is Python's one `@[dyn_lang]` class: the parts of the world, the machine's cells and
  calls, and the tags of `Value`, of a global cell and of a function's result.
* A computation takes the operation's regions as `Handles`, its activation's `Start`, and two
  continuations: one for its result, and one for the exception that it raises.  `bind` composes
  continuations, so it builds no intermediate tree.
* `Proved f e` states two properties of `f`'s tree at the engine boundary (`treeOf`), where the
  table instantiates every rule.  First, for every spec `V` of the machine (`Exec.Spec`, over
  typings of the heap) that has the laws of `PyCertLaws`, the tree satisfies `V` from every
  typing; this gives each rule's certificate (`Model.OpCertified`), which ref-to-reg's soundness
  theorem takes.  Second, the tree stays within every level from `e` up.  Both hold for every
  region signature, every start, every handle that is itself proved (`HandlesOK`), and every pair
  of continuations that have both properties (`ContOK`).
* The `Refs` instances say where values hold refs: a `Value` holds none, the store holds the
  closure of each function object, and the module table its global cells (`modulesRefs`).
* `StartFree f`: `f` gives the same tree from every start.

The monad's operations (`pure'`, `bind'`, `tryCatch'`, `lift`) carry the proofs, so that every
computation written in `PyM` is proved by construction.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec Strata.Dyn.Exec.Effects

@[expose] public section

/-- Python's capabilities: the parts of the world, the global cells, the calls of translated
functions, and the tags of `Value`, of a global cell and of a function's result. -/
@[dyn_lang] class PyLang (σ : outParam Type) [Store σ] [Decode σ] (ε : Eff) where
  store : HasPart ε.W (ObjStore σ)
  modules : HasPart ε.W (Modules σ)
  handled : HasPart ε.W Handled
  depth : HasPart ε.W Depth
  guard : HasPart ε.W ReprGuard
  out : HasPart ε.W Output
  heap : HasHeap σ ε
  call : HasCall σ ε
  tagValue : TagOf σ Value
  tagCell : TagOf σ (Ref σ Value)
  tagExcept : TagOf σ (Except Value Value)

/-- The operation's regions, each adapted to values, in operand order. -/
abbrev Handles (ε : Eff) (E : Type) : Type := Array (Array Value → Sem ε E (Except Value Value))

/-- What a computation of a rule is, before its proofs: from the operation's regions and start,
and two continuations, one for a result and one for an exception, a tree. -/
abbrev PyFn (σ : Type) [Store σ] [Decode σ] (α : Type) : Type 1 :=
  ∀ {ε : Eff} {E : Type} [PyLang σ ε], Handles ε E → Start → {β : Type} →
    (α → Sem ε E β) → (Value → Sem ε E β) → Sem ε E β

section
variable {σ : Type} [Store σ] [Decode σ]

/-- The table's decoding. -/
abbrev Dec (σ : Type) [Store σ] [Decode σ] : Ty → Type := Decode.decode σ

/-- The requests at the engine boundary, for an operation with regions `rs`. -/
abbrev BEff (σ : Type) [Store σ] [Decode σ] (rs : List (List Ty × Ty)) : Eff :=
  MEff (Dec σ) σ (World σ) rs

/-- The tags that `PyLang` takes. -/
structure Tags (σ : Type) [Store σ] [Decode σ] where
  value : TagOf σ Value
  cell : TagOf σ (Ref σ Value)
  exc : TagOf σ (Except Value Value)

/-- `PyLang` at the engine boundary, with the tags `tg`. -/
@[reducible] def bInst (rs : List (List Ty × Ty)) (tg : Tags σ) : PyLang σ (BEff σ rs) :=
  PyLang.mk inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (HasHeap.mreq (I := Dec σ)) (HasCall.mreq (I := Dec σ)) tg.value tg.cell tg.exc

/-- A tree at the engine boundary. -/
abbrev BTree (σ : Type) [Store σ] [Decode σ] (rs : List (List Ty × Ty)) (ps : List (List Ty))
    (S R : Type) : Type :=
  Tree (Dec σ) σ (World σ) rs ps S R

/-- The signature of a translated function: it takes the args tuple and the kwargs dict, and
returns its result or its exception. -/
@[reducible] def funcSig {ε : Eff} [PyLang σ ε] : SigOf σ [Value, Value] (Except Value Value) :=
  ⟨([(TagOf.tag σ Value), (TagOf.tag σ Value)], TagOf.tag σ (Except Value Value)),
    ⟨by simp [(TagOf.ok : Decode.decode σ (TagOf.tag σ Value) = Value)],
      (TagOf.ok : Decode.decode σ (TagOf.tag σ (Except Value Value)) = Except Value Value)⟩⟩

/-! ## Where values hold refs

`Refs` (`Exec/CertCaps.lean`) gives the refs that a value holds.  A `Value` holds none: an
object is an id into the store.  The store holds the closure of each function object, and the
module table holds its global cells. -/

instance : Refs σ Value := ⟨fun _ => []⟩

/-- A function object holds its closure. -/
instance : Refs σ (FuncObj σ) := ⟨fun f => Refs.refs (σ := σ) f.closure⟩

/-- A payload holds the closure of a function object, and nothing else. -/
instance : Refs σ (ObjPayload σ) := ⟨fun
  | .func f => Refs.refs (σ := σ) f
  | _ => []⟩

/-- An object holds the refs of its payload. -/
instance : Refs σ (Obj σ) := ⟨fun o => Refs.refs (σ := σ) o.payload⟩

/-- The store holds the closures of its function objects. -/
instance : Refs σ (ObjStore σ) := ⟨fun st => Refs.refs (σ := σ) st.objs⟩

/-- The module table holds its global cells, each of the tag of `Value` in `tg`. -/
@[instance_reducible] def modulesRefs (tg : TagOf σ Value) : Refs σ (Modules σ) :=
  ⟨fun m => m.map.toList.flatMap fun e => e.2.cells.toList.map fun c => .cell c.2.loc tg.tag⟩

instance : Refs σ Handled := ⟨fun _ => []⟩
instance : Refs σ Depth := ⟨fun _ => []⟩
instance : Refs σ ReprGuard := ⟨fun _ => []⟩
instance : Refs σ Output := ⟨fun _ => []⟩

/-- `f` adds no closure to a payload: every closure of `f p` is one of `p`. -/
def KeepsClosures (f : ObjPayload σ → ObjPayload σ) : Prop :=
  ∀ p, ∀ l ∈ Refs.refs (σ := σ) (f p), l ∈ Refs.refs (σ := σ) p

/-- Proves `KeepsClosures f` for a function `f` that keeps a function payload's closure and makes
no function payload: by cases on the payload. -/
macro "keeps_closures" : tactic =>
  `(tactic| (intro p l hl; cases p <;> first | exact hl | exact absurd hl List.not_mem_nil))

omit [Decode σ] in
/-- A dict payload's change adds no closure. -/
theorem keepsClosures_modDict (f : DictTable → DictTable) :
    KeepsClosures (σ := σ) (PayloadG.modDict f) := by keeps_closures

omit [Decode σ] in
/-- A set payload's change adds no closure. -/
theorem keepsClosures_modSet (f : SetTable → SetTable) :
    KeepsClosures (σ := σ) (PayloadG.modSet f) := by keeps_closures

omit [Decode σ] in
/-- A list payload's change adds no closure. -/
theorem keepsClosures_modList (f : Array Value → Nat → Array Value × Nat) :
    KeepsClosures (σ := σ) (PayloadG.modList f) := by keeps_closures

/-- **What a computation relies on of a spec `V` of the machine at the engine boundary**, with
the tags `tg` (the capability specs, `Exec/CertCaps.lean`): its cell requests on `Value`s, its calls
of translated functions, and every part of the world. -/
structure PyCertLaws (rs : List (List Ty × Ty)) {E : Type} (tg : Tags σ)
    (V : Spec Typing (BEff σ rs) E) : Prop where
  heap : @HeapSpec _ _ σ _ _ V (HasHeap.mreq (I := Dec σ)) Value tg.value _
  call : @CallSpec _ _ σ _ _ V (HasCall.mreq (I := Dec σ)) [Value, Value] (Except Value Value)
    (@funcSig σ _ _ (BEff σ rs) (bInst rs tg)) _ _
  store : PartSpec (σ := σ) V (ObjStore σ)
  modules : @PartSpec _ _ σ _ V (Modules σ) _ (modulesRefs tg.value)
  handled : PartSpec (σ := σ) V Handled
  depth : PartSpec (σ := σ) V Depth
  guard : PartSpec (σ := σ) V ReprGuard
  out : PartSpec (σ := σ) V Output

/-- A tree satisfies `V` from every typing, and stays within `e` from every set of new cells,
relative to the start `s`. -/
def TreeOK {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S R : Type}
    (V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)) (s : Start) (e : Level)
    (t : BTree σ rs ps S R) : Prop :=
  (∀ g, V.Sat (fun _ _ => True) g t) ∧ ∀ N, Within spec s e (fun _ _ => True) N t

/-- Every handle's tree satisfies `V` and is within every level, on every argument. -/
def HandlesOK {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S : Type}
    (V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)) (s : Start)
    (hs : @Handles (BEff σ rs) (Out (Dec σ) ps S)) : Prop :=
  ∀ (i : Nat) (h : i < hs.size) (args : Array Value) (e : Level), TreeOK V s e (hs[i] args)

/-- A tree satisfies `V` with the post-condition `Q` from every typing, and stays within `e` with
the post-condition `QW` from every set of new cells, relative to the start `s`: what a
continuation must be. -/
def ContOK {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S R : Type}
    (V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)) (s : Start) (e : Level)
    (Q : Typing → R → Prop) (QW : Cells → R → Prop) (t : BTree σ rs ps S R) : Prop :=
  (∀ g, V.Sat Q g t) ∧ ∀ N, Within spec s e QW N t

/-- `f`'s tree at the engine boundary, with the continuations `k` and `ke`. -/
@[reducible] def treeOf {α : Type} (f : PyFn σ α) (rs : List (List Ty × Ty)) (ps : List (List Ty))
    (S : Type) (tg : Tags σ) (hs : @Handles (BEff σ rs) (Out (Dec σ) ps S)) (s : Start) {β : Type}
    (k : α → BTree σ rs ps S β) (ke : Value → BTree σ rs ps S β) : BTree σ rs ps S β :=
  @f (BEff σ rs) (Out (Dec σ) ps S) (bInst rs tg) hs s β k ke

/-- **`f` satisfies every spec that has the laws, and stays within `e`**, at the engine
boundary: at every level `e'` from `e` up, for every spec `V` with `PyCertLaws` and every handle
that is itself `TreeOK`, with continuations that satisfy `V` from every typing and are within
`e'` (with any post-conditions), `f`'s tree satisfies `V` from every typing and is within `e'`
too.  The `Sat` half holds from every typing because no computation takes a ref or a closure from
its caller: every one that it uses is read from the world, answered by the machine, or made,
inside one primitive. -/
def Proved {α : Type} (f : PyFn σ α) (e : Level) : Prop :=
  ∀ (rs : List (List Ty × Ty)) (ps : List (List Ty)) (S : Type) (tg : Tags σ)
    (V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)), PyCertLaws rs tg V →
    ∀ (s : Start) (hs : @Handles (BEff σ rs) (Out (Dec σ) ps S)), HandlesOK V s hs →
    ∀ (e' : Level), e.le e' → ∀ {β : Type} (Q : Typing → β → Prop) (QW : Cells → β → Prop)
      (k : α → BTree σ rs ps S β) (ke : Value → BTree σ rs ps S β),
      (∀ a, ContOK V s e' Q QW (k a)) → (∀ x, ContOK V s e' Q QW (ke x)) →
      ContOK V s e' Q QW (treeOf f rs ps S tg hs s k ke)

/-- `f` gives the same tree from every start. -/
def StartFree {α : Type} (f : PyFn σ α) : Prop :=
  ∀ {ε : Eff} {E : Type} [PyLang σ ε] (hs : Handles ε E) (s s' : Start) {β : Type}
    (k : α → Sem ε E β) (ke : Value → Sem ε E β), f hs s k ke = f hs s' k ke

namespace ContOK
variable {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S R : Type}
  {V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)} {s : Start} {e : Level}
  {Q : Typing → R → Prop} {QW : Cells → R → Prop}

/-- A fault. -/
theorem fault (f : Fault) : ContOK V s e Q QW (.stop (.fault f)) :=
  ⟨fun _ => Spec.sat_fault, fun _ => trivial⟩

/-- The `Within` half of a world update. -/
theorem within_update {f : World σ → World σ × BTree σ rs ps S R}
    (hs : e ≠ .writes → ∀ w, Same s w (f w).1)
    (hi : e = .pure → ∀ w₁ w₂, ImmEq s w₁ w₂ → ImmEq s (f w₁).1 (f w₂).1 ∧ (f w₁).2 = (f w₂).2)
    (hk : ∀ w N, Within spec s e QW N (f w).2) : ∀ N, Within spec s e QW N (.update f) :=
  fun N => ⟨hs, hi, fun w => by rw [Within.after_eq]; exact hk w N⟩

/-- A world update that keeps every possible world possible, that changes no protected state
below `writes`, and that, at `pure`, maps two worlds that `ImmEq` relates to two related worlds
and one continuation. -/
theorem update {f : World σ → World σ × BTree σ rs ps S R}
    (hw : ∀ g w, V.World g w → V.World g (f w).1)
    (hs : e ≠ .writes → ∀ w, Same s w (f w).1)
    (hi : e = .pure → ∀ w₁ w₂, ImmEq s w₁ w₂ → ImmEq s (f w₁).1 (f w₂).1 ∧ (f w₁).2 = (f w₂).2)
    (hk : ∀ w, ContOK V s e Q QW (f w).2) : ContOK V s e Q QW (.update f) :=
  ⟨fun g => Spec.sat_update.mpr fun w hw' => ⟨hw g w hw', (hk w).1 g⟩,
    fun N => ⟨hs, hi, fun w => by rw [Within.after_eq]; exact (hk w).2 N⟩⟩

/-- A read of the world, whose continuation a `pure` operation can't tell apart on worlds that
`ImmEq` relates. -/
theorem read {k : World σ → BTree σ rs ps S R} (hk : ∀ w, ContOK V s e Q QW (k w))
    (hp : e = .pure → ∀ w₁ w₂, ImmEq s w₁ w₂ → k w₁ = k w₂) :
    ContOK V s e Q QW (.update fun w => (w, k w)) :=
  update (fun _ _ h => h) (fun _ w => Same.refl s w) (fun he w₁ w₂ h => ⟨h, hp he w₁ w₂ h⟩) hk

/-- The `Within` half of a read of the world. -/
theorem within_read {k : World σ → BTree σ rs ps S R} (hkw : ∀ w N, Within spec s e QW N (k w))
    (hp : e = .pure → ∀ w₁ w₂, ImmEq s w₁ w₂ → k w₁ = k w₂) :
    ∀ N, Within spec s e QW N (.update fun w => (w, k w)) :=
  fun N => ⟨fun _ w => Same.refl s w, fun he w₁ w₂ h => ⟨h, hp he w₁ w₂ h⟩,
    fun w => by rw [Within.after_eq]; exact hkw w N⟩

/-- A read of the world whose continuation's `Sat` half may use that the world is possible. -/
theorem readWith {k : World σ → BTree σ rs ps S R}
    (hk : ∀ g w, V.World g w → V.Sat Q g (k w)) (hkw : ∀ w N, Within spec s e QW N (k w))
    (hp : e = .pure → ∀ w₁ w₂, ImmEq s w₁ w₂ → k w₁ = k w₂) :
    ContOK V s e Q QW (.update fun w => (w, k w)) :=
  ⟨fun g => Spec.sat_update.mpr fun w hw => ⟨hw, hk g w hw⟩, within_read hkw hp⟩

/-- An in-place update of the part `P` of the world, followed by `k` of its result: as `update`,
for the world with the part replaced by one whose refs are valid wherever the old part's are. -/
theorem modifyGetThe {P α : Type} [HasPart (World σ) P] [LawfulHasPart (World σ) P] [Refs σ P]
    (g : P → α × P) {k : α → BTree σ rs ps S R} (hp : PartSpec (σ := σ) V P)
    (hf : ∀ G (x : P), RefsOK (σ := σ) G x → RefsOK (σ := σ) G (g x).2)
    (hs : e ≠ .writes → ∀ w : World σ, Same s w (HasPart.set w (g (HasPart.get w)).2))
    (hi : e = .pure → ∀ w₁ w₂ : World σ, ImmEq s w₁ w₂ →
      ImmEq s (HasPart.set w₁ (g (HasPart.get w₁)).2) (HasPart.set w₂ (g (HasPart.get w₂)).2) ∧
        k (g (HasPart.get w₁)).1 = k (g (HasPart.get w₂)).1)
    (hk : ∀ a, ContOK V s e Q QW (k a)) :
    ContOK V s e Q QW ((modifyGetThe P g : BTree σ rs ps S α) >>= k) := by
  rw [modifyGetThe_eq]
  exact update (fun G w hw => hp.set G w _ hw (hf G _ (hp.get G w hw))) hs hi fun w => hk _

/-- A read of the part `P` of the world, followed by `k` of it. -/
theorem getThe {P : Type} [HasPart (World σ) P] {k : P → BTree σ rs ps S R}
    (hk : ∀ p, ContOK V s e Q QW (k p))
    (hp : e = .pure → ∀ w₁ w₂ : World σ, ImmEq s w₁ w₂ →
      k (HasPart.get w₁) = k (HasPart.get w₂)) :
    ContOK V s e Q QW ((getThe P : BTree σ rs ps S P) >>= k) :=
  read (k := fun w => k (HasPart.get w)) (fun _ => hk _) hp

/-- A read of the part `P` of the world, followed by `k` of it, whose `Sat` half may use that the
part's refs are valid. -/
theorem getTheWith {P : Type} [HasPart (World σ) P] [Refs σ P] {k : P → BTree σ rs ps S R}
    (hpart : PartSpec (σ := σ) V P)
    (hk : ∀ G (p : P), RefsOK (σ := σ) G p → V.Sat Q G (k p))
    (hkw : ∀ p N, Within spec s e QW N (k p))
    (hp : e = .pure → ∀ w₁ w₂ : World σ, ImmEq s w₁ w₂ →
      k (HasPart.get w₁) = k (HasPart.get w₂)) :
    ContOK V s e Q QW ((_root_.getThe P : BTree σ rs ps S P) >>= k) :=
  readWith (k := fun w => k (HasPart.get w)) (fun G w hw => hk G _ (hpart.get G w hw))
    (fun _ => hkw _) hp

/-- An in-place update of the part `P` of the world, followed by `k`. -/
theorem modifyThe {P : Type} [HasPart (World σ) P] [LawfulHasPart (World σ) P] [Refs σ P]
    (f : P → P) {k : BTree σ rs ps S R} (hp : PartSpec (σ := σ) V P)
    (hf : ∀ G (x : P), RefsOK (σ := σ) G x → RefsOK (σ := σ) G (f x))
    (hs : e ≠ .writes → ∀ w : World σ, Same s w (HasPart.set w (f (HasPart.get w))))
    (hi : e = .pure → ∀ w₁ w₂ : World σ, ImmEq s w₁ w₂ →
      ImmEq s (HasPart.set w₁ (f (HasPart.get w₁))) (HasPart.set w₂ (f (HasPart.get w₂))))
    (hk : ContOK V s e Q QW k) :
    ContOK V s e Q QW ((modifyThe P f : BTree σ rs ps S Unit) >>= fun _ => k) := by
  rw [modifyThe_eq]
  exact update (fun G w hw => hp.set G w _ hw (hf G _ (hp.get G w hw))) hs
    (fun he w₁ w₂ h => ⟨hi he w₁ w₂ h, rfl⟩) fun _ => hk

/-- A tree that satisfies `V` and is within every level, followed by a continuation that is
`ContOK` for every result. -/
theorem bind {R' : Type} {x : BTree σ rs ps S R'} {f : R' → BTree σ rs ps S R}
    (hx : TreeOK V s e x) (hf : ∀ a, ContOK V s e Q QW (f a)) :
    ContOK V s e Q QW (x.bind f) :=
  ⟨fun g => Spec.Sat.bind (Spec.Sat.mono (fun g a _ => (hf a).1 g) (hx.1 g)),
    fun N => Within.bind (mid := fun _ _ => True) (fun N a _ => (hf a).2 N) _ (hx.2 N)⟩

end ContOK

/-- The continuation for a result or an exception. -/
@[inline] def contOf {ε : Eff} {E α β : Type} (k : α → Sem ε E β) (ke : Value → Sem ε E β) :
    Except Value α → Sem ε E β
  | .ok a => k a
  | .error x => ke x

/-- `contOf` of two continuations that are `ContOK` is `ContOK` on every outcome. -/
theorem ContOK.cont {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S α R : Type}
    {V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)} {s : Start} {e : Level}
    {Q : Typing → R → Prop} {QW : Cells → R → Prop} {k : α → BTree σ rs ps S R}
    {ke : Value → BTree σ rs ps S R} (hk : ∀ a, ContOK V s e Q QW (k a))
    (hke : ∀ x, ContOK V s e Q QW (ke x)) (r : Except Value α) :
    ContOK V s e Q QW (contOf k ke r) := by
  cases r with
  | ok a => exact hk a
  | error x => exact hke x

end

/-- **The rule monad** at effect `e`: a computation with the proofs that it satisfies every spec
that has `PyCertLaws` and stays
within `e`, and, if `free`, that it gives the same tree from every start, so that a rule can run
it without reading the store first. -/
def PyM (σ : Type) [Store σ] [Decode σ] (e : Level) (free : Bool) (α : Type) : Type 1 :=
  { f : PyFn σ α // Proved @f e ∧ (free = true → StartFree @f) }

/-- Stop with a gap because a precondition of the model itself doesn't hold. -/
@[inline] def modelInvariant {ε : Eff} {E α : Type} (msg : String) : Sem ε E α :=
  semanticGap (modelInvariantPrefix ++ msg)

namespace PyM
variable {σ : Type} [Store σ] [Decode σ] {e : Level} {fr : Bool}

/-- A computation that returns `a`. -/
@[inline] def pure' {α : Type} (a : α) : PyM σ e fr α :=
  ⟨fun _ _ _ k _ => k a, by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _; exact hk a, by intro _; unfold StartFree; intros; rfl⟩

/-- `x`, then `f` of its result. -/
@[inline] def bind' {α β : Type} (x : PyM σ e fr α) (f : α → PyM σ e fr β) : PyM σ e fr β :=
  ⟨fun hs s _ k ke => x.1 hs s (fun a => (f a).1 hs s k ke) ke,
    by
      intro rs ps S tg V hc s hs hh e' he _ Q QW k ke hk hke
      exact x.2.1 rs ps S tg V hc s hs hh e' he Q QW _ ke
        (fun a => (f a).2.1 rs ps S tg V hc s hs hh e' he Q QW k ke hk hke) hke,
    by
      intro hfr _ _ _ hs s s' _ k ke
      show x.1 hs s _ ke = x.1 hs s' _ ke
      rw [x.2.2 hfr hs s s']
      exact congrArg (fun K => x.1 hs s' K ke) (funext fun a => (f a).2.2 hfr hs s s' k ke)⟩

instance : Monad (PyM σ e fr) where
  pure := pure'
  bind := bind'

/-- Raise `x`. -/
@[inline] def throw' {α : Type} (x : Value) : PyM σ e fr α :=
  ⟨fun _ _ _ _ ke => ke x, by
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hke; exact hke x, by intro _; unfold StartFree; intros; rfl⟩

/-- `x`, or `h` of the exception that it raises. -/
@[inline] def tryCatch' {α : Type} (x : PyM σ e fr α) (h : Value → PyM σ e fr α) :
    PyM σ e fr α :=
  ⟨fun hs s _ k ke => x.1 hs s k (fun v => (h v).1 hs s k ke),
    by
      intro rs ps S tg V hc s hs hh e' he _ Q QW k ke hk hke
      exact x.2.1 rs ps S tg V hc s hs hh e' he Q QW k _ hk
        (fun v => (h v).2.1 rs ps S tg V hc s hs hh e' he Q QW k ke hk hke),
    by
      intro hfr _ _ _ hs s s' _ k ke
      show x.1 hs s k _ = x.1 hs s' k _
      rw [x.2.2 hfr hs s s']
      exact congrArg (fun K => x.1 hs s' k K) (funext fun v => (h v).2.2 hfr hs s s' k ke)⟩

instance : MonadExcept Value (PyM σ e fr) where
  throw := throw'
  tryCatch := tryCatch'

/-- A computation at a lower level, at a higher one. -/
@[inline] def lift {e' : Level} (he : e.le e') {α : Type} (x : PyM σ e fr α) : PyM σ e' fr α :=
  ⟨x.1, fun rs ps S tg V hc s hs hh e'' he' =>
    x.2.1 rs ps S tg V hc s hs hh e'' (Level.le_trans he he'), x.2.2⟩

/-- A computation that needs no start, as one that may or may not. -/
@[inline] def relax {α : Type} (x : PyM σ e true α) : PyM σ e fr α :=
  ⟨x.1, x.2.1, fun _ => x.2.2 rfl⟩

/-- Run region `i` of the operation on `args`, at every level.  An index out of range is a
model-invariant gap: generic code never passes one. -/
@[inline] def region (i : Nat) (args : Array Value) : PyM σ e fr Value :=
  ⟨fun hs _ _ k ke => if h : i < hs.size then (hs[i] args).bind (contOf k ke) else
    modelInvariant s!"region {i} out of range", by
    intro rs ps S tg V hc s hs hh e' _ _ Q QW k ke hk hke
    show ContOK V s e' Q QW (if h : i < hs.size then _ else _)
    split
    · rename_i h; exact ContOK.bind (hh i h args e') (ContOK.cont hk hke)
    · exact ContOK.fault _,
    by intro _; unfold StartFree; intros; rfl⟩

/-- Stop with a gap. -/
@[inline] def gap {α : Type} (msg : String) : PyM σ e fr α :=
  ⟨fun _ _ _ _ _ => semanticGap msg, by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact ⟨fun _ => Spec.sat_fault, fun _ => trivial⟩,
    by intro _; unfold StartFree; intros; rfl⟩

/-- Stop because a precondition of the model itself doesn't hold: a model-invariant gap
(`Invariant.lean`). -/
@[inline] def failure {α : Type} (msg : String) : PyM σ e fr α :=
  ⟨fun _ _ _ _ _ => modelInvariant msg, by intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact ⟨fun _ => Spec.sat_fault, fun _ => trivial⟩,
    by intro _; unfold StartFree; intros; rfl⟩

end PyM

section
variable {σ : Type} [Store σ] [Decode σ] {ε : Eff} {E : Type} [PyLang σ ε] {e : Level}

/-- The start of an operation in the world `w`. -/
def startOf (w : ObjStore σ) : Start := ⟨w.size⟩

/-- **A rule** that runs `m`: it reads the start, runs `m` on the operation's regions `hs`, and
jumps along `err` with the exception that `m` raises. -/
@[inline] def runRule {α : Type} {fr : Bool} (err : Target E [Value]) (hs : Handles ε E)
    (m : PyM σ e fr α) : Sem ε E α := do
  let st ← getThe (ObjStore σ)
  m.1 hs (startOf st) pure (jump err)

/-- **A rule of an operation that can't raise**: as `runRule`, but an exception is a gap. -/
@[inline] def runTotal {α : Type} {fr : Bool} (op : String) (hs : Handles ε E)
    (m : PyM σ e fr α) : Sem ε E α := do
  let st ← getThe (ObjStore σ)
  m.1 hs (startOf st) pure fun _ => semanticGap s!"an exception in an operation that can't raise: {op}"

/-- **A rule that runs `m`, which needs no start**: as `runRule`, without reading the store. -/
@[inline] def runRuleFree {α : Type} (err : Target E [Value]) (hs : Handles ε E)
    (m : PyM σ e true α) : Sem ε E α :=
  m.1 hs ⟨0⟩ pure (jump err)

/-- **A rule of an operation that can't raise, that runs `m`, which needs no start**: as
`runTotal`, without reading the store. -/
@[inline] def runTotalFree {α : Type} (op : String) (hs : Handles ε E) (m : PyM σ e true α) :
    Sem ε E α :=
  m.1 hs ⟨0⟩ pure fun _ => semanticGap s!"an exception in an operation that can't raise: {op}"

/-- **A rule that runs `m` if `cond`, and else `mFree`, which needs no start**: `runRule` or
`runRuleFree`, so that the cases that need the start are the only ones that read it. -/
@[inline] def runRuleIf {α : Type} (cond : Bool) (err : Target E [Value]) (hs : Handles ε E)
    (m : PyM σ e false α) (mFree : PyM σ e true α) : Sem ε E α :=
  if cond then runRule err hs m else runRuleFree err hs mFree

end

end

end StrataPython.Dyn.Sem
