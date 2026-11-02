/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Sem
public import StrataDyn.Exec.Machine
public import StrataDyn.Exec.Spec

set_option autoImplicit false

/-!
# The effects of rules

`Within sp s e post N t` says that a rule's tree `t`, at the engine boundary, stays within the
effect `e` of `docs/Dyn.md` (`pure`, `reads`, `calls` or `writes`), relative to the operation's
start `s`, and ends with the post-condition `post`.  A language says what its world allows through
a `WorldSpec`: which worlds a `pure` operation can't tell apart (`immEq`), and which updates change no
state that an operation must leave alone (`same`: new objects, memo entries and bookkeeping parts
are allowed).  Cells are tracked along the tree: a cell that a `new` of the same activation (one run
of the rule, from its operands or from an `again` state) made is the operation's own.  A region's
run is not counted.

The theorems about these definitions are in `Exec/EffectsProps.lean`.
-/

namespace Strata.Dyn.Exec.Effects

@[expose] public section

/-- How much of the world an operation may touch, from least to most: the four effects of
`docs/Dyn.md`. -/
inductive Level where
  /-- Reads no mutable state, and changes none. -/
  | pure
  /-- May read mutable state, and changes none. -/
  | reads
  /-- May read mutable state and call functions (`call` requests), which may change it; the rule's
  own updates change no state that it must leave alone (`WorldSpec.same`), except inside a call
  bracket (`WorldSpec.inCall`), where a built-in that runs user code counts as a call.  Which
  functions it calls is part of its rule's meaning, not bounded by its effect. -/
  | calls
  /-- May change mutable state. -/
  | writes
  deriving DecidableEq, Repr, Inhabited

/-- The order of the levels. -/
def Level.rank : Level → Nat
  | .pure => 0 | .reads => 1 | .calls => 2 | .writes => 3

/-- `e` allows no more than `e'`. -/
def Level.le (e e' : Level) : Prop := e.rank ≤ e'.rank

instance (e e' : Level) : Decidable (e.le e') := inferInstanceAs (Decidable (_ ≤ _))

/-- What a language says about its world for the effects, relative to an operation's start `s`:
`immEq s w₁ w₂` holds when the two worlds agree on what a `pure` operation may read (immutable
state, and what the operation made itself); `same s w w'` holds when `w'` changes no mutable
state of `w` that an operation must leave alone (it may add new objects and memo entries, and
change bookkeeping parts).  `same s` is a preorder: it is reflexive, since a rule reads the world
with an update that gives the world back, and transitive, so that a run of updates that each keep
`same` keeps it relative to the world before the first one.  `inCall w` holds when `w` is inside a
call bracket: a built-in that runs user code counts as a call, so an update of such a world may
change anything at `calls` (`callBracket`); a language without such built-ins keeps the default.
`Within` can't tell a bracket's edge from another update that changes what `inCall` reads (the
marker), so a language that uses brackets must keep four rules: the marker changes only at the edges
of a call; an edge changes nothing that `same` guards; no other update reads the marker; and every
function that a call runs, runs with the marker lowered. Then every change of state at `calls` is
inside a call. -/
structure WorldSpec (W St : Type) where
  immEq : St → W → W → Prop
  same : St → W → W → Prop
  same_refl : ∀ s w, same s w w
  same_trans : ∀ s w₁ w₂ w₃, same s w₁ w₂ → same s w₂ w₃ → same s w₁ w₃
  inCall : W → Bool := fun _ => false

/-- A set of cell locations. -/
abbrev Cells := Nat → Prop

section
variable {I : Ty → Type} {σ : Type} [Store σ] {W St : Type} {rs : List (List Ty × Ty)}
  {ps : List (List Ty)} {S R : Type}

mutual
/-- **The effects** of a rule's tree at the engine boundary, at level `e`, relative to the
operation's start `s`, with the post-condition `post` on the new cells and the result at the
leaves.  `N` holds the cells that a `new` of this activation made, which the operation may read
and write at every level.  A region's run is not counted: its answer is any value.
- `writes`: anything;
- `calls`: no update of the world changes state it must leave alone, unless the world or the new
  world is inside a call bracket (`WorldSpec.inCall`), and no write to an older cell; calls are
  allowed;
- `reads`: as `calls`, and no call;
- `pure`: as `reads`, no read of an older cell, no oracle choice, and every update of the world
  maps two worlds that `immEq` relates to two worlds that it relates, with the same
  continuation, so that no update carries mutable state into what a later update sees.  From
  one heap, and with region answers that can't tell such worlds apart (`EnvImm`), the result then
  depends on the world only through what `immEq` keeps (`pure_reads_alike`). -/
def Within (sp : WorldSpec W St) (s : St) (e : Level) (post : Cells → R → Prop) :
    Cells → Tree I σ W rs ps S R → Prop
  | N, .ret a => post N a
  | _, .stop _ => True
  | N, .choose k => e ≠ .pure ∧ ∀ i, Within sp s e post N (k i)
  | N, .update f => (e ≠ .writes → ∀ w,
        (e = .calls ∧ (sp.inCall w || sp.inCall (f w).1) = true) ∨ sp.same s w (f w).1) ∧
      (e = .pure → ∀ w₁ w₂, sp.immEq s w₁ w₂ →
        sp.immEq s (f w₁).1 (f w₂).1 ∧ (f w₁).2 = (f w₂).2) ∧
      ∀ w, Within.after sp s e post N (f w)
  | N, .vis (.region _ _) k => ∀ o, Within sp s e post N (k o)
  | N, .vis (.call _ _ _ _) k => (e = .calls ∨ e = .writes) ∧ ∀ o, Within sp s e post N (k o)
  | N, .vis (.new _ _) k => ∀ r, Within sp s e post (fun l => N l ∨ l = r.loc) (k r)
  | N, .vis (.get _ l) k => (e = .pure → N l) ∧ ∀ v, Within sp s e post N (k v)
  | N, .vis (.set _ l _) k => (e = .writes ∨ N l) ∧ ∀ u, Within sp s e post N (k u)
  | N, .vis (.modify _ l _) k => (e = .writes ∨ N l) ∧ ∀ u, Within sp s e post N (k u)
  | N, .vis (.bind _ _ _ _ _) k => ∀ g, Within sp s e post N (k g)

/-- `Within` of an update's continuation. -/
def Within.after (sp : WorldSpec W St) (s : St) (e : Level) (post : Cells → R → Prop) (N : Cells) :
    W × Tree I σ W rs ps S R → Prop
  | (_, t) => Within sp s e post N t
end

/-- `e₀` is at most `e`: an instance, so that instance search can use a computation at `e₀`
where level `e` is expected. -/
class Level.AtLeast (e₀ e : Level) : Prop where
  le : e₀.le e

instance (e : Level) : Level.AtLeast .pure e := ⟨by cases e <;> decide⟩
instance : Level.AtLeast .reads .reads := ⟨by decide⟩
instance : Level.AtLeast .reads .calls := ⟨by decide⟩
instance : Level.AtLeast .reads .writes := ⟨by decide⟩
instance : Level.AtLeast .calls .calls := ⟨by decide⟩
instance : Level.AtLeast .calls .writes := ⟨by decide⟩
instance : Level.AtLeast .writes .writes := ⟨by decide⟩

end

/-! ## Every operand -/

@[expose] public section

/-- `P` holds of `f` applied to every operand list of the tags `ts`. -/
def FnAll {I : Ty → Type} {X : Type} (P : X → Prop) : (ts : List Ty) → Fn I X ts → Prop
  | [], x => P x
  | _ :: ts, f => ∀ a, FnAll P ts (f a)

/-- `P` holds of `f` applied to every variadic array, if the operation has one. -/
def VarAll {I : Ty → Type} {X : Type} (P : X → Prop) : (v : Option Ty) → VarFn I v X → Prop
  | none, x => P x
  | some _, f => ∀ xs, P (f xs)

end

/-! ## Readings

A reading runs a rule's tree at the machine's token against a heap, an oracle and an environment
that answers region and call requests: what `pure_reads_alike` compares. -/

namespace Reading

section
variable {I : Ty → Type} {W : Type} {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S R : Type}

/-- A heap that a reading answers cell requests from, as the machine keeps it: the cells, each a
value with its tag, and the captures cells. -/
structure RHeap (I : Ty → Type) where
  cells : Array (Dyn I)
  caps : Array (List (Dyn I))

/-- The value of tag `t` at location `l`, if the cell holds one. -/
def RHeap.read? (h : RHeap I) (t : Ty) (l : Nat) : Option (I t) :=
  match h.cells[l]? with
  | some d => if e : d.1 = t then some (e ▸ d.2) else none
  | none => none

/-- What a reading needs besides the heap: the answer of a region or call request (a fault, or
the answer, the heap and the world after it), and whether the machine accepts a bind (`none`) or
faults. -/
structure Env (I : Ty → Type) (W : Type) (rs : List (List Ty × Ty)) where
  answer : (q : MReq I rs) → RHeap I → W → Except Fault (q.Out Run × RHeap I × W)
  bind : (idx captured : Nat) → (ts : List Ty) → (r : Ty) → RHeap I → Option Fault

/-- How a reading ends: with a result, or stopped. -/
inductive Outcome (E R : Type) where
  | done (r : R)
  | stop (s : Stop E)

/-- A reading's end: the outcome, the heap and the world, and the number of choices drawn. -/
structure Ended (I : Ty → Type) (W E R : Type) where
  out : Outcome E R
  heap : RHeap I
  world : W
  drawn : Nat

mutual
/-- **A reading** of a rule's tree at the machine's token: cell and bind requests are answered from
the heap, choices from the oracle, and region and call requests by `env`.  It is a model of how the
machine answers them (`serve`), written to match it; no theorem relates the two. -/
def read (env : Env I W rs) (oracle : Nat → Nat) :
    Tree I Run W rs ps S R → Nat → RHeap I → W → Ended I W (Out I ps S) R
  | .ret a, d, h, w => ⟨.done a, h, w, d⟩
  | .stop s, d, h, w => ⟨.stop s, h, w, d⟩
  | .choose k, d, h, w => read env oracle (k (oracle d)) (d + 1) h w
  | .update f, d, h, w => read.after env oracle (f w) d h
  | .vis (.new t v) k, d, h, w =>
      read env oracle (k ⟨h.cells.size, trivial⟩) d { h with cells := h.cells.push ⟨t, v⟩ } w
  | .vis (.get t l) k, d, h, w =>
      match h.read? t l with
      | some v => read env oracle (k v) d h w
      | none => ⟨.stop (.fault (.badCell l)), h, w, d⟩
  | .vis (.set t l v) k, d, h, w =>
      match h.read? t l with
      | some _ => read env oracle (k ()) d { h with cells := h.cells.setIfInBounds l ⟨t, v⟩ } w
      | none => ⟨.stop (.fault (.badCell l)), h, w, d⟩
  | .vis (.modify t l g) k, d, h, w =>
      match h.read? t l with
      | some v => read env oracle (k ()) d { h with cells := h.cells.setIfInBounds l ⟨t, g v⟩ } w
      | none => ⟨.stop (.fault (.badCell l)), h, w, d⟩
  | .vis (.bind t v sig idx cap) k, d, h, w =>
      match env.bind idx cap (t :: sig.1) sig.2 h with
      | some f => ⟨.stop (.fault f), h, w, d⟩
      | none =>
        let old := if cap = 0 then [] else (h.caps[cap - 1]?).getD []
        read env oracle (k ⟨idx, h.caps.size + 1, trivial⟩) d
          { h with caps := h.caps.push (old ++ [⟨t, v⟩]) } w
  | .vis (.region slot args) k, d, h, w =>
      match env.answer (.region slot args) h w with
      | .ok (o, h', w') => read env oracle (k o) d h' w'
      | .error f => ⟨.stop (.fault f), h, w, d⟩
  | .vis (.call sig idx cap args) k, d, h, w =>
      match env.answer (.call sig idx cap args) h w with
      | .ok (o, h', w') => read env oracle (k o) d h' w'
      | .error f => ⟨.stop (.fault f), h, w, d⟩

/-- A reading that goes on after an update, in its new world. -/
def read.after (env : Env I W rs) (oracle : Nat → Nat) :
    W × Tree I Run W rs ps S R → Nat → RHeap I → Ended I W (Out I ps S) R
  | (w', t), d, h => read env oracle t d h w'
end

end

end Reading

section
variable {I : Ty → Type} {W St : Type} {rs : List (List Ty × Ty)} {ps : List (List Ty)} {S R : Type}

/-- An environment whose answers can't tell two worlds that `immEq` relates apart: on such worlds
and the same heap it gives the same fault, or the same answer and heap and related worlds. -/
def EnvImm (sp : WorldSpec W St) (s : St) (env : Reading.Env I W rs) : Prop :=
  ∀ (q : MReq I rs) (h : Reading.RHeap I) (w₁ w₂ : W), sp.immEq s w₁ w₂ →
    match env.answer q h w₁, env.answer q h w₂ with
    | .error f₁, .error f₂ => f₁ = f₂
    | .ok (o₁, h₁, w₁'), .ok (o₂, h₂, w₂') => o₁ = o₂ ∧ h₁ = h₂ ∧ sp.immEq s w₁' w₂'
    | _, _ => False

end

end

end Strata.Dyn.Exec.Effects
