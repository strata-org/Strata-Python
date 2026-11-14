/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Exec.Machine

set_option autoImplicit false

/-!
# Modules whose functions have the same signatures

A translation of linked modules keeps each function at its index, with its name, its parameters'
tags and its result's.  `SameSigs` says so, and gives what the machine's check of a call needs
of the two modules: the check passes in one exactly when it passes in the other
(`SameSigs.callOK_iff`), and a failed check names the same function (`SameSigs.fnName_eq`).

A proof that relates the steps of two such modules analyses the machine's checks and a rule's
tree in both at once.  The eliminators here do it once, for any relation `P` between the two
outcomes: a cell check over heaps that agree on the cell (`Heap.cell_rec₂`), a call check
(`SameSigs.callee_rec₂`), and a rule's tree continued by the source's operation and by the
target's version of it (`mkInst`), which has another position, other edges and other operands
(`SameSigs.settle_rec₂`).
-/

namespace Strata.Dyn.Exec

@[expose] public section

variable {M : RunModel}

/-- The functions of `m₁` are as many as those of `m`, and each has the name, the parameters'
tags and the result tag of the function of `m` at its index. -/
structure SameSigs (m m₁ : LModule M) : Prop where
  size : m₁.funcs.size = m.funcs.size
  sig : ∀ i (hi : i < m.funcs.size) (hi₁ : i < m₁.funcs.size),
    (m₁.funcs[i]'hi₁).name = (m.funcs[i]'hi).name ∧
    (m₁.funcs[i]'hi₁).params = (m.funcs[i]'hi).params ∧
    (m₁.funcs[i]'hi₁).ret = (m.funcs[i]'hi).ret

variable {m m₁ : LModule M}

/-- The call check passes in `m₁` exactly when it passes in `m`, with the same captures, over
heaps with the same captures cells. -/
private theorem SameSigs.callOK_iff (h : SameSigs m m₁) {heap heap₁ : Heap M}
    (hc : heap₁.caps = heap.caps) {idx captured : Nat} {ts : List Ty} {r : Ty}
    {caps : List (Dyn M.interp)} :
    m₁.CallOK heap₁ idx captured ts r caps ↔ m.CallOK heap idx captured ts r caps := by
  have hcap : heap₁.captures? captured = heap.captures? captured := by
    unfold Heap.captures?; rw [hc]
  constructor
  · rintro ⟨hi₁, hcp, hp, hr⟩
    have hi : idx < m.funcs.size := h.size ▸ hi₁
    obtain ⟨-, hps, hrt⟩ := h.sig idx hi hi₁
    exact ⟨hi, hcap ▸ hcp, hps ▸ hp, hrt ▸ hr⟩
  · rintro ⟨hi, hcp, hp, hr⟩
    have hi₁ : idx < m₁.funcs.size := h.size.symm ▸ hi
    obtain ⟨-, hps, hrt⟩ := h.sig idx hi hi₁
    exact ⟨hi₁, hcap.symm ▸ hcp, hps.symm ▸ hp, hrt.symm ▸ hr⟩

/-- The two modules' functions have the same names, so a failed call check names the same
function. -/
private theorem SameSigs.fnName_eq (h : SameSigs m m₁) (i : Nat) : m₁.fnName i = m.fnName i := by
  unfold LModule.fnName
  by_cases hi : i < m.funcs.size
  · have hi₁ : i < m₁.funcs.size := h.size.symm ▸ hi
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi₁]
    simp only [Option.map_some, Option.getD_some, (h.sig i hi hi₁).1]
  · have hi₁ : ¬ i < m₁.funcs.size := by rw [h.size]; exact hi
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hi), Array.getElem?_eq_none (Nat.le_of_not_lt hi₁)]

/-! ## The machine's checks, in two machines -/

/-- **A cell check in two heaps.**  When location `l₁` of `heap₁` holds a value of tag `t`
exactly when location `l` of `heap` does, the two checks pass together or fail together. -/
theorem Heap.cell_rec₂ {R R₁ : Type} {P : R → R₁ → Prop} {heap heap₁ : Heap M} {l l₁ : Nat}
    {t : Ty} {ok : (hl : l < heap.cells.size) → (heap.cells[l]'hl).1 = t → R} {bad : Unit → R}
    {ok₁ : (hl : l₁ < heap₁.cells.size) → (heap₁.cells[l₁]'hl).1 = t → R₁} {bad₁ : Unit → R₁}
    (h : heap₁.Holds l₁ t ↔ heap.Holds l t)
    (hok : ∀ (hh : heap.Holds l t) (hh₁ : heap₁.Holds l₁ t),
      P (ok hh.lt hh.code) (ok₁ hh₁.lt hh₁.code))
    (hbad : P (bad ()) (bad₁ ())) : P (heap.cell l t ok bad) (heap₁.cell l₁ t ok₁ bad₁) := by
  by_cases hh : heap.Holds l t
  · rw [Heap.cell_pos hh, Heap.cell_pos (h.mpr hh)]
    exact hok hh (h.mpr hh)
  · rw [Heap.cell_neg hh, Heap.cell_neg fun hh₁ => hh (h.mp hh₁)]
    exact hbad

/-- **A call check in two modules** with the same signatures, of the same closure, over heaps
with the same captures cells.  The two checks pass together, with the same captures, or fail
together, naming the same function. -/
theorem SameSigs.callee_rec₂ (h : SameSigs m m₁) {R R₁ : Type} {P : R → R₁ → Prop}
    {heap heap₁ : Heap M} (hc : heap₁.caps = heap.caps) {idx idx₁ captured captured₁ : Nat}
    (hi : idx₁ = idx) (hcap : captured₁ = captured) {ts : List Ty} {r : Ty}
    {ok : (hi : idx < m.funcs.size) → (caps : List (Dyn M.interp)) →
      (m.funcs[idx]'hi).params = caps.map (·.1) ++ ts → (m.funcs[idx]'hi).ret = r → R}
    {bad : Unit → R}
    {ok₁ : (hi : idx₁ < m₁.funcs.size) → (caps : List (Dyn M.interp)) →
      (m₁.funcs[idx₁]'hi).params = caps.map (·.1) ++ ts → (m₁.funcs[idx₁]'hi).ret = r → R₁}
    {bad₁ : Unit → R₁}
    (hok : ∀ (caps : List (Dyn M.interp)) (hco : m.CallOK heap idx captured ts r caps)
      (hco₁ : m₁.CallOK heap₁ idx₁ captured₁ ts r caps),
      P (ok hco.1 caps hco.2.2.1 hco.2.2.2) (ok₁ hco₁.1 caps hco₁.2.2.1 hco₁.2.2.2))
    (hbad : m₁.fnName idx₁ = m.fnName idx → P (bad ()) (bad₁ ())) :
    P (m.callee heap idx captured ts r ok bad) (m₁.callee heap₁ idx₁ captured₁ ts r ok₁ bad₁) := by
  subst hi hcap
  by_cases hco : ∃ caps, m.CallOK heap idx₁ captured₁ ts r caps
  · obtain ⟨caps, hco⟩ := hco
    have hco₁ := (h.callOK_iff hc).mpr hco
    rw [LModule.callee_pos hco, LModule.callee_pos hco₁]
    exact hok caps hco hco₁
  · rw [LModule.callee_neg fun caps h₁ => hco ⟨caps, h₁⟩,
      LModule.callee_neg fun caps h₁ => hco ⟨caps, (h.callOK_iff hc).mp h₁⟩]
    exact hbad (h.fnName_eq idx₁)

/-! ## A rule's tree, in two machines -/

/-- The target's version of a source rule's operation: another position, other edges and other
operands.  Its rule has the same trees. -/
def mkInst (i : Inst M) (pc₁ : Nat) (succs₁ : List LSite) (args₁ : List Nat) : Inst M :=
  { i with pc := pc₁, succs := succs₁, rerun := { i.rerun with args := args₁ } }

/-- **A rule's tree, continued in two machines**: by the operation `i` in a module, and by the
target's version of `i` in a module with the same signatures, over heaps with the same captures
cells.  `P` holds of the two steps if it holds in each case of the tree: a result bound, an exit
along a successor, a run of the rule again, a fault, a region entered, a function called after
its check passed in both, and a pause at a request. -/
theorem SameSigs.settle_rec₂ (hs : SameSigs m m₁) {B B₁ : Ty} {hwf : WF m} {hwf₁ : WF m₁}
    {c c₁ : Core M} (hc : c₁.heap.caps = c.heap.caps) {i : Inst M} {pc₁ : Nat}
    {succs₁ : List LSite} {args₁ : List Nat} {hi : InstOK m c.top i}
    {hK : ContsOK m B c.top.func.ret c.conts}
    {hi₁ : InstOK m₁ c₁.top (mkInst i pc₁ succs₁ args₁)}
    {hK₁ : ContsOK m₁ B₁ c₁.top.func.ret c₁.conts} {d : Nat} {ev ev₁ : Event}
    {P : i.Tree → StepR m B → StepR m₁ B₁ → Prop}
    (ret : ∀ a, P (.ret a)
      (.next ev ⟨{ c with top := c.top.bind i.dst (resDyn i.ret a) (hi.dst_lt a) }, .exec, d, ()⟩
        (hi.next hK a))
      (.next ev₁ ⟨{ c₁ with top := c₁.top.bind i.dst (resDyn i.ret a) (hi₁.dst_lt a) }, .exec, d,
        ()⟩ (hi₁.next hK₁ a)))
    (exit : ∀ e, P (.stop (.jump (.exit e)))
      (transfer c (exitTo c.top i.succs e hi.sitesOK) (hi.exit hwf e) hK d ev)
      (transfer c₁ (exitTo c₁.top succs₁ e hi₁.sitesOK) (hi₁.exit hwf₁ e) hK₁ d ev₁))
    (again : ∀ st, P (.stop (.jump (.again st))) (.next ev ⟨c, .again ⟨i, st⟩, d, ()⟩ ⟨hi, hK⟩)
      (.next ev₁ ⟨c₁, .again ⟨mkInst i pc₁ succs₁ args₁, st⟩, d, ()⟩ ⟨hi₁, hK₁⟩))
    (fault : ∀ t f, P t (faultStep c f d) (faultStep c₁ f d))
    (region : ∀ j args k, P (.vis (.region j args) k) (visitRegion hwf c i hi hK d ev j args k)
      (visitRegion hwf₁ c₁ (mkInst i pc₁ succs₁ args₁) hi₁ hK₁ d ev₁ j args k))
    (call : ∀ sig idx captured args k caps (hco : m.CallOK c.heap idx captured sig.1 sig.2 caps)
      (hco₁ : m₁.CallOK c₁.heap idx captured sig.1 sig.2 caps),
      P (.vis (.call sig idx captured args) k)
        (.next ev ⟨c, .call (callFrame hwf idx hco.1 caps (Args.ofPayload sig.1 args))
            (.rule c.top ⟨i, .call sig idx captured args, sig.2, k⟩), d, ()⟩
          (hi.call hwf hK hco.1 hco.2.2.1 hco.2.2.2 args k))
        (.next ev₁ ⟨c₁, .call (callFrame hwf₁ idx hco₁.1 caps (Args.ofPayload sig.1 args))
            (.rule c₁.top ⟨mkInst i pc₁ succs₁ args₁, .call sig idx captured args, sig.2, k⟩), d,
            ()⟩
          (hi₁.call hwf₁ hK₁ hco₁.1 hco₁.2.2.1 hco₁.2.2.2 args k)))
    (request : ∀ t, P t (.next ev ⟨c, .request i t, d, ()⟩ ⟨hi, hK⟩)
      (.next ev₁ ⟨c₁, .request (mkInst i pc₁ succs₁ args₁) t, d, ()⟩ ⟨hi₁, hK₁⟩))
    (t : i.Tree) :
    P t (settle hwf c i hi hK d ev t)
      (settle hwf₁ c₁ (mkInst i pc₁ succs₁ args₁) hi₁ hK₁ d ev₁ t) := by
  cases t with
  | ret a => exact ret a
  | stop s =>
    cases s with
    | jump o =>
      cases o with
      | exit e => exact exit e
      | again st => exact again st
    | fault f => exact fault _ f
  | choose k => exact request _
  | update f => exact request _
  | vis q k =>
    cases q with
    | region j args => exact region j args k
    | call sig idx captured args =>
      simp only [settle, visitCall]
      refine hs.callee_rec₂ hc rfl rfl (call sig idx captured args k) fun e => ?_
      rw [e]
      exact fault _ _
    | new _ _ => exact request _
    | get _ _ => exact request _
    | set _ _ _ => exact request _
    | modify _ _ _ => exact request _
    | bind _ _ _ _ _ => exact request _

end

end Strata.Dyn.Exec
