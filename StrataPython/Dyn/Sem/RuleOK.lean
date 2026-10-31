/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Concrete

set_option autoImplicit false

/-!
# A rule satisfies every spec and stays within its effect

`RuleOK V Q e t` is what `#py_rule_theorems` proves of each rule's tree at the engine boundary:
the tree satisfies the spec `V` with the result condition `Q` from every typing, and it stays
within the operation's declared effect, from the world at its start or, for a rule that doesn't
read the start, from every start.  `ImplOK` states it for every operand, every spec that has
`PyCertLaws` and allows every exit, and every `Q` that holds of every result; `Table.lean` turns
it into the certificate at Python's model.

The theorems that give `RuleOK` for every rule that runs a `PyM` computation are in
`RuleOKProps.lean`.
-/

namespace StrataPython.Dyn.Sem

open Strata.Dyn.Exec Strata.Dyn.Exec.Effects

@[expose] public section

section
variable {σ : Type} [Store σ] [Decode σ] {rs : List (List Ty × Ty)} {ps : List (List Ty)}
  {S R : Type}

/-- From the world at its start, the tree stays within `e`: it reads the world first, and what
follows stays within `e` relative to that start; at `pure`, it is the same for worlds that a
`pure` operation can't tell apart. -/
def StartWithin (e : Level) (t : BTree σ rs ps S R) : Prop :=
  ∃ k : World σ → BTree σ rs ps S R, t = .update (fun w => (w, k w)) ∧
    (e = .pure → ∀ w₁ w₂ : World σ, ImmEq (startOf w₁.store) w₁ w₂ → k w₁ = k w₂) ∧
    ∀ (w : World σ) N, Within spec (startOf w.store) e (fun _ _ => True) N (k w)

/-- From every start, the tree stays within `e`: what a rule that doesn't read the start
gives. -/
def AnyStart (e : Level) (t : BTree σ rs ps S R) : Prop :=
  ∀ (s : Start) N, Within spec s e (fun _ _ => True) N t

/-- **A rule's tree satisfies `V` and is within `e`**: it satisfies `V` with the result condition
`Q` from every typing, and is within `e` from the world at its start, or from every start. -/
def RuleOK (V : Spec Typing (BEff σ rs) (Out (Dec σ) ps S)) (Q : Typing → R → Prop) (e : Level)
    (t : BTree σ rs ps S R) : Prop :=
  (∀ g, V.Sat Q g t) ∧ (StartWithin e t ∨ AnyStart e t)

end

/-- The rule of the operation `o` at the token `σ` and the type arguments `targs` satisfies `V`
and is within `e`, on every operand, for every spec `V` that has the laws and allows every exit,
and every `Q` that holds of every result.  A pure wrapper has no rule, so it has no `ImplAt`:
`dyn_cert` proves its certificate. -/
def ImplAt (interp : Interp) (σ : Type) [Store σ] (tg : @Tags σ _ ⟨interp σ⟩) (e : Level)
    (o : OpImpl interp (fun σ _ => World σ)) (targs : Vector Ty o.typeArgc) : Prop :=
  letI : Decode σ := ⟨interp σ⟩
  ∀ (V : Spec Typing (BEff σ (o.shape targs).regions) (Out (Dec σ) (o.shape targs).succs (o.St σ targs))),
    PyCertLaws _ tg V → (∀ g x, V.Exit g x) →
    ∀ (Q : Typing → Res (Dec σ) (o.shape targs).ret → Prop), (∀ g a, Q g a) →
    match o.fn σ targs with
    | .pure _ => False
    | .sem f => FnAll (fun h => VarAll (RuleOK V Q e) _ h) _ f
    | .loop f g => FnAll (fun h => VarAll (RuleOK V Q e) _ h) _ f ∧
      FnAll (fun h => VarAll (fun k => ∀ st, RuleOK V Q e (k st)) _ h) _ g

/-- **Every rule of the operation `o` satisfies every spec with the laws and is within `e`**, at
every token and type arguments, at the table's decoding `interp` and tags `tags`. -/
def ImplOK (interp : Interp) (tags : (σ : Type) → [Store σ] → @Tags σ _ ⟨interp σ⟩) (e : Level)
    (o : OpImpl interp (fun σ _ => World σ)) : Prop :=
  ∀ (σ : Type) [Store σ] (targs : Vector Ty o.typeArgc), ImplAt interp σ (tags σ) e o targs

/-- The `Within` half of `ImplAt`: the rule of the operation `o` at the token `σ` and the type
arguments `targs` is within `e` on every operand. -/
def ImplWithinAt (interp : Interp) (σ : Type) [Store σ] (e : Level)
    (o : OpImpl interp (fun σ _ => World σ)) (targs : Vector Ty o.typeArgc) : Prop :=
  letI : Decode σ := ⟨interp σ⟩
  let W (t : BTree σ (o.shape targs).regions (o.shape targs).succs (o.St σ targs)
      (Res (Dec σ) (o.shape targs).ret)) : Prop := StartWithin e t ∨ AnyStart e t
  match o.fn σ targs with
  | .pure _ => True
  | .sem f => FnAll (fun h => VarAll W _ h) _ f
  | .loop f g => FnAll (fun h => VarAll W _ h) _ f ∧
    FnAll (fun h => VarAll (fun k => ∀ st, W (k st)) _ h) _ g

/-- **Every rule of the operation `o` is within `e`**, at every token and type arguments. -/
def ImplWithin (interp : Interp) (e : Level) (o : OpImpl interp (fun σ _ => World σ)) : Prop :=
  ∀ (σ : Type) [Store σ] (targs : Vector Ty o.typeArgc), ImplWithinAt interp σ e o targs

section
variable {σ : Type} [Store σ] [Decode σ] {rs : List (List Ty × Ty)} {ps : List (List Ty)}
  {S : Type}

/-- What the machine answers to a new cell: a ref to a cell of the request's tag. -/
def pyPost (G : Typing) : (q : MReq (Dec σ) rs) → q.Out σ → Prop
  | .new t _, o => G.Valid o.loc t
  | _, _ => True

/-- **A spec of the machine at every token, with the laws**: every request and exit is allowed,
a new cell's ref is valid, and a world is possible when the closures of its store and the cells
of its module table are valid.  It shows that `ImplOK` is not vacuous, and gives `ImplWithin`
from it. -/
def pySpec (tg : Tags σ) (rs : List (List Ty × Ty)) (ps : List (List Ty)) (S : Type) :
    Spec Typing (BEff σ rs) (Out (Dec σ) ps S) where
  Ext := Typing.Extends
  Pre _ _ := True
  Post := pyPost
  World G w := RefsOK (σ := σ) G w.store ∧ @RefsOK σ _ (Modules σ) (modulesRefs tg.value) G w.modules
  Exit _ _ := True

end

end

end StrataPython.Dyn.Sem
