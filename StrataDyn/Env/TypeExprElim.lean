/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env
import all StrataDyn.Env

set_option autoImplicit false

/-!
# Eliminating a type expression

`TypeExpr.elim` is the eliminator for a checked type expression, where `fold` is a plain
recursion over its syntax: it hands each case what the expression's well-formedness gives.
A variable comes with its kind and the proof that the scope has it at that kind, an
application with the checked reference its constructor resolves to, and the result is indexed
by the expression's kind, so a type is eliminated to a type and a list to a list.

Its laws follow: computation rules for an application (`elim_appK`, `elim_app`) and a list
literal (`elim_list`), and fusion, `elim_map`: a map that commutes with the three cases
(`ElimCommutes`) commutes with elimination, so a client lifts laws about its cases to every
expression without repeating the recursion over checked syntax.
-/

namespace Strata.Dyn

public section

/-- The stored reference at `r`'s arity. `TypeRef.decl` carries a caller-supplied annotation,
which a type expression does not record, so `elim` can only return the stored reference. -/
def TypeRef.canonical {α : Type} {env : Env α} {arity : Nat} (r : TypeRef env arity) :
    TypeRef env arity :=
  { TypeRef.ofRefBefore r.refBefore with
    matchArity := (TypeRef.ofRefBefore r.refBefore).matchArity.trans r.size_kinds }

/-- The canonical reference keeps the name. -/
@[simp] theorem TypeRef.name_canonical {α : Type} {env : Env α} {arity : Nat}
    (r : TypeRef env arity) : r.canonical.name = r.name := by rfl

/-- The canonical reference keeps the parameter kinds. -/
@[simp] theorem TypeRef.kinds_canonical {α : Type} {env : Env α} {arity : Nat}
    (r : TypeRef env arity) : r.canonical.kinds = r.kinds :=
  TypeRef.kinds_ofRefBefore r.refBefore

namespace TypeExpr

variable {α : Type} {env : Env α} {scope : Array Kind}

/-- Eliminated arguments retain the kinds of the application's parameters. -/
structure Arguments (β : Kind → Type _) (kinds : Array Kind) where
  values : Array ((k : Kind) × β k)
  kinds_eq : values.map Sigma.fst = kinds

/-- Read an argument at its declared kind, without a dynamic kind check. -/
def Arguments.get {β : Kind → Type _} {kinds : Array Kind}
    (args : Arguments β kinds) (i : Fin kinds.size) : β kinds[i] :=
  have hs : args.values.size = kinds.size := by
    simpa using congrArg Array.size args.kinds_eq
  have hi : i.val < args.values.size := by rw [hs]; exact i.isLt
  let a := args.values[i.val]'hi
  have hk : a.1 = kinds[i] := by
    have h := congrArg (fun ks => ks[i.val]?) args.kinds_eq
    simpa [Array.getElem?_eq_getElem hi,
      Array.getElem?_eq_getElem i.isLt, a] using h
  hk ▸ a.2

/-- Map a kind-indexed value without changing its kind. -/
@[expose] def mapValue {β γ : Kind → Type _} (f : ∀ k, β k → γ k) :
    ((k : Kind) × β k) → ((k : Kind) × γ k)
  | ⟨k, v⟩ => ⟨k, f k v⟩

/-- Interpret each argument, retaining its declared kind. -/
@[expose] def Arguments.map {β γ : Kind → Type _} {ks : Array Kind}
    (f : ∀ k, β k → γ k) (args : Arguments β ks) : Arguments γ ks :=
  ⟨args.values.map (mapValue f), (by
    simpa only [Array.map_map, Function.comp_def, mapValue] using args.kinds_eq)⟩

/-- Reading an argument with its kind recovers the stored value. -/
private theorem Arguments.get_value {β : Kind → Type _} {ks : Array Kind}
    (args : Arguments β ks) (i : Fin ks.size) (hi : i.val < args.values.size) :
    (⟨ks[i], args.get i⟩ : (k : Kind) × β k) = args.values[i.val] := by
  unfold Arguments.get
  apply Sigma.ext
  · simpa [Array.getElem?_eq_getElem hi] using
      (congrArg (fun xs => xs[i.val]?) args.kinds_eq).symm
  · exact eqRec_heq _ _

/-- Reading an interpreted argument is interpreting the argument read at the same index. -/
theorem Arguments.get_map {β γ : Kind → Type _} {ks : Array Kind}
    (f : ∀ k, β k → γ k) (args : Arguments β ks) (i : Fin ks.size) :
    (args.map f).get i = f ks[i] (args.get i) := by
  have hs : args.values.size = ks.size := by simpa using congrArg Array.size args.kinds_eq
  have hi : i.val < args.values.size := by simpa only [hs] using i.isLt
  have hi' : i.val < (args.map f).values.size := by simpa [Arguments.map] using hi
  have hm := (args.map f).get_value i hi'
  have hm' : (args.map f).values[i.val] = mapValue f args.values[i.val] :=
    Array.getElem_map (mapValue f) hi'
  have h := hm.trans (hm'.trans (congrArg (mapValue f) (args.get_value i hi).symm))
  exact eq_of_heq (Sigma.mk.inj h).2

section

variable {β : Kind → Type _}
  (var : (i : Nat) → (k : Kind) → scope[i]? = some k → β k)
  (app : {arity : Nat} → (r : TypeRef env arity) → Arguments β r.kinds → β .type)
  (list : Array ((k : Kind) × β k) → β .list)

/-- A list variable among a literal's elements has the kind the scope gives it. -/
private theorem WFElem.getElem?_var {R : Name → Array Kind → Prop} {j : Nat}
    (h : TypeExpr.WFElem R scope (.var j)) : scope[j]? = some (scope[j]?.getD .type) := by
  cases h with
  | ty h => cases h with | var h => simp [h]
  | splice h => simp [h]

mutual
private def elimRaw : (k : Kind) → (e : Raw) → WF (env.RefBefore env.size) scope k e → β k
  | .type, .var i, h => var i .type (wfType_var_iff.mp h)
  | .type, .app _ ⟨as⟩, h =>
    let args := elimArgs as fun a ha => h.args a (by simpa using ha)
    app (TypeRef.ofRefBefore h.refBefore)
      ⟨args.val.toArray, by
        apply Array.toList_inj.mp
        simpa only [Array.toList_map, List.toList_toArray] using
          args.property.trans (by
            simpa only [Array.toList_map, List.toList_toArray] using
              congrArg Array.toList (TypeRef.kinds_ofRefBefore h.refBefore).symm)⟩
  | .list, .list ⟨es⟩, h => list ⟨elimElems es fun a ha => h.elems a (by simpa using ha)⟩
  | .list, .var _, h => nomatch h
  | .list, .app .., h => nomatch h
  | .type, .list _, h => nomatch h

private def elimArgs : (as : List Raw) → (∀ a ∈ as, WFRel (env.RefBefore env.size) scope a) →
    { values : List ((k : Kind) × β k) // values.map Sigma.fst = as.map (Raw.kind scope) }
  | [], _ => ⟨[], rfl⟩
  | a :: as, h =>
    let rest := elimArgs as fun b hb => h b (by simp [hb])
    ⟨⟨a.kind scope, elimRaw _ a (h a (by simp))⟩ :: rest.val,
      by simp [rest.property]⟩

private def elimElems : (es : List Raw) → (∀ a ∈ es, WFElem (env.RefBefore env.size) scope a) →
    List ((k : Kind) × β k)
  | [], _ => []
  | .var j :: es, h =>
    ⟨_, var j _ (WFElem.getElem?_var (h _ (by simp)))⟩ :: elimElems es fun b hb => h b (by simp [hb])
  | .app n as :: es, h =>
    ⟨.type, elimRaw .type (.app n as) ((h _ (by simp)).wfType rfl)⟩ ::
      elimElems es fun b hb => h b (by simp [hb])
  -- No lists of lists: a literal is not an element.
  | .list l :: _, h => absurd (h (.list l) (by simp)).isElem (by simp [Raw.isElem])
end

/-- Eliminate a type expression at its kind: `var` for a variable in scope at that kind, `app`
for the checked reference its constructor resolves to, applied to its eliminated arguments with
their kinds, and `list` for a literal's elements, each a type or a list variable spliced in. -/
def elim {k : Kind} (e : TypeExpr env scope k) : β k :=
  elimRaw var app list k e.expr e.wf

end

end TypeExpr

namespace TypeList.Elem

variable {α : Type} {env : Env α} {scope : Array Kind} {β : Kind → Type _}
  (var : (i : Nat) → (k : Kind) → scope[i]? = some k → β k)
  (app : {arity : Nat} → (r : TypeRef env arity) → TypeExpr.Arguments β r.kinds → β .type)
  (list : Array ((k : Kind) × β k) → β .list)

/-- Eliminate one literal element, retaining whether it contributes a type or a splice. -/
def elim : TypeList.Elem env scope → ((k : Kind) × β k)
  | .ty t => ⟨.type, t.elim var app list⟩
  | .splice i h => ⟨.list, var i .list h⟩

end TypeList.Elem

namespace TypeExpr

/-! ### Computation rules -/

section Computation

variable {α : Type} {env : Env α} {scope : Array Kind}

variable {β : Kind → Type _}
  (var : (i : Nat) → (k : Kind) → scope[i]? = some k → β k)
  (app : {arity : Nat} → (r : TypeRef env arity) → Arguments β r.kinds → β .type)
  (list : Array ((k : Kind) × β k) → β .list)

/-- Eliminating the raw expressions of checked type arguments interprets each argument at its
kind. -/
private theorem elimArgs_values (as : List (TypeArg env scope)) (rs : List Raw)
    (he : rs = as.map TypeArg.expr)
    (h : ∀ a ∈ rs, WFRel (env.RefBefore env.size) scope a) :
    (elimArgs var app list rs h).val =
      as.map fun a => ⟨a.kind, a.val.elim var app list⟩ := by
  subst rs
  induction as with
  | nil => rfl
  | cons a as ih =>
    change ⟨a.expr.kind scope, elimRaw var app list _ a.expr _⟩ ::
      (elimArgs var app list (as.map TypeArg.expr) _).val = _
    rw [ih]
    simp only [List.map_cons]
    congr 1
    cases a with
    | mk k t =>
      obtain ⟨e, hw⟩ := t
      have hk : e.kind scope = k := hw.kind_eq
      cases hk
      rfl

/-- Eliminated application arguments, with their parameter kinds preserved. -/
def Arguments.ofTypeArgs {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeArg env scope) arity)
    (hk : args.toList.map TypeArg.kind = r.kinds.toList) : Arguments β r.canonical.kinds :=
  ⟨args.toArray.map (fun a => ⟨a.kind, a.val.elim var app list⟩), by
    rw [TypeRef.kinds_canonical]
    apply Array.toList_inj.mp
    simpa [Array.toList_map, Function.comp_def, Vector.toList] using hk⟩

/-- Type references with the same name and declaration are equal, whatever their stated arities. -/
private theorem typeRef_heq {a b : Nat} {r : TypeRef env a} {s : TypeRef env b}
    (hn : r.name = s.name) (hd : r.decl = s.decl) : HEq r s := by
  obtain ⟨n, d, ha, hr⟩ := r
  obtain ⟨n', d', hb, hs⟩ := s
  simp only at hn hd
  subst n' d' a b
  rfl

/-- Elimination uses the stored reference; a reference's caller-supplied annotation is not
part of a type expression. -/
@[simp] theorem elim_appK {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeArg env scope) arity)
    (hk : args.toList.map TypeArg.kind = r.kinds.toList) :
    (appK r args hk).elim var app list =
      app r.canonical (Arguments.ofTypeArgs var app list r args hk) := by
  unfold elim appK
  simp only [elimRaw]
  unfold TypeRef.canonical TypeRef.ofRefBefore Arguments.ofTypeArgs
  congr 1
  · simp
  · apply typeRef_heq <;> rfl
  · congr 1
    apply Array.toList_inj.mp
    simpa only [Array.toList_map, Vector.toList, List.toList_toArray] using
      elimArgs_values var app list args.toList _ (by simp [Vector.toList]) _

/-- Eliminating a type-only application interprets the stored reference on its eliminated
arguments, read as type arguments. -/
@[simp] theorem elim_app {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeExpr env scope) arity) (hk : r.kinds = .replicate arity .type) :
    (TypeExpr.app r args hk).elim var app list =
      app r.canonical (Arguments.ofTypeArgs var app list r (args.map .ty)
        (by simp [hk, Vector.toList_map, Function.comp_def, List.map_const'])) := by
  exact elim_appK var app list r _ _

/-- A variable's interpretation does not depend on which proof fixes its kind. -/
private theorem var_heq (i : Nat) {k k' : Kind}
    (h : scope[i]? = some k) (h' : scope[i]? = some k') :
    HEq (var i k h) (var i k' h') := by
  have hk := Option.some.inj (h.symm.trans h')
  cases hk
  rfl

/-- Eliminating the raw expressions of checked literal elements interprets each element, keeping
types and splices apart. -/
private theorem elimElems_values (es : List (TypeList.Elem env scope)) (rs : List Raw)
    (he : rs = es.map TypeList.Elem.expr)
    (h : ∀ e ∈ rs, WFElem (env.RefBefore env.size) scope e) :
    elimElems var app list rs h = es.map (TypeList.Elem.elim var app list) := by
  subst rs
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | ty t =>
      obtain ⟨e, hw⟩ := t
      cases hw with
      | var hv =>
        change _ :: elimElems var app list (es.map TypeList.Elem.expr) _ = _
        rw [ih]
        simp only [List.map_cons, TypeList.Elem.elim, elim, elimRaw, List.cons.injEq,
          Sigma.mk.injEq, hv, Option.getD_some, true_and, and_true]
        apply var_heq
      | app hr hs ha =>
        change _ :: elimElems var app list (es.map TypeList.Elem.expr) _ = _
        rw [ih]
        rfl
    | splice i hi =>
      change _ :: elimElems var app list (es.map TypeList.Elem.expr) _ = _
      rw [ih]
      simp only [List.map_cons, TypeList.Elem.elim, List.cons.injEq, Sigma.mk.injEq, hi,
        Option.getD_some, true_and, and_true]
      apply var_heq

/-- Eliminating a list literal interprets its elements and hands them to the list case. -/
@[simp] theorem elim_list (es : Array (TypeList.Elem env scope)) :
    (TypeList.lit es).elim var app list =
      list (es.map (TypeList.Elem.elim var app list)) := by
  unfold elim TypeList.lit
  simp only [elimRaw]
  congr 1
  apply Array.toList_inj.mp
  simpa only [Array.toList_map] using
    elimElems_values var app list es.toList _ (by simp) _

end Computation

/-! ### Fusion -/

section Fusion

variable {α : Type} {env : Env α} {scope : Array Kind} {β γ : Kind → Type _}
  (f : ∀ k, β k → γ k)
  (v : (i : Nat) → (k : Kind) → scope[i]? = some k → β k)
  (a : {arity : Nat} → (r : TypeRef env arity) → Arguments β r.kinds → β .type)
  (l : Array ((k : Kind) × β k) → β .list)
  (v' : (i : Nat) → (k : Kind) → scope[i]? = some k → γ k)
  (a' : {arity : Nat} → (r : TypeRef env arity) → Arguments γ r.kinds → γ .type)
  (l' : Array ((k : Kind) × γ k) → γ .list)

/-- The commutation condition for `elim_map`: `f` carries each interpretation case of `v`, `a`,
`l` to the corresponding case of `v'`, `a'`, `l'`, on variables directly, on applications and
list literals after mapping the interpreted arguments or elements. -/
structure ElimCommutes : Prop where
  var : ∀ i k h, f k (v i k h) = v' i k h
  app : ∀ {arity} (r : TypeRef env arity) args, f .type (a r args) = a' r (args.map f)
  list : ∀ es, f .list (l es) = l' (es.map (mapValue f))

mutual
/-- Mapping a raw elimination with a commuting `f` is eliminating with the mapped cases. -/
private theorem elimRaw_map (hc : ElimCommutes f v a l v' a' l') :
    ∀ k e (h : WF (env.RefBefore env.size) scope k e),
      f k (elimRaw v a l k e h) = elimRaw v' a' l' k e h
  | .type, .var i, h => hc.var i .type _
  | .type, .app n ⟨as⟩, h => by
    simp only [elimRaw, hc.app, Arguments.map]
    congr 2
    apply Array.toList_inj.mp
    simpa only [Array.toList_map, List.toList_toArray] using elimArgs_map hc as _
  | .list, .list ⟨es⟩, h => by
    simp only [elimRaw, hc.list]
    congr 1
    apply Array.toList_inj.mp
    simpa only [Array.toList_map] using elimElems_map hc es _
  | .list, .var _, h => nomatch h
  | .list, .app .., h => nomatch h
  | .type, .list _, h => nomatch h

/-- Mapping eliminated arguments with a commuting `f` is eliminating them with the mapped
cases. -/
private theorem elimArgs_map (hc : ElimCommutes f v a l v' a' l') :
    ∀ as (h : ∀ e ∈ as, WFRel (env.RefBefore env.size) scope e),
      ((elimArgs v a l as h).val.map (mapValue f)) = (elimArgs v' a' l' as h).val
  | [], _ => rfl
  | e :: es, h => by
    simp only [elimArgs, List.map_cons, mapValue, elimRaw_map hc, elimArgs_map hc]

/-- Mapping eliminated literal elements with a commuting `f` is eliminating them with the
mapped cases. -/
private theorem elimElems_map (hc : ElimCommutes f v a l v' a' l') :
    ∀ es (h : ∀ e ∈ es, WFElem (env.RefBefore env.size) scope e),
      (elimElems v a l es h).map (mapValue f) = elimElems v' a' l' es h
  | [], _ => rfl
  | .var i :: es, h => by
    simp only [elimElems, List.map_cons, mapValue, hc.var, elimElems_map hc]
  | .app n as :: es, h => by
    simp only [elimElems, List.map_cons, mapValue, elimRaw_map hc, elimElems_map hc]
  | .list xs :: _, h => absurd (h (.list xs) (by simp)).isElem (by simp [Raw.isElem])
end

/-- A map commuting with the three interpretation cases commutes with elimination. -/
theorem elim_map (hc : ElimCommutes f v a l v' a' l') {k : Kind} (t : TypeExpr env scope k) :
    f k (t.elim v a l) = t.elim v' a' l' := by
  exact elimRaw_map f v a l v' a' l' hc k t.expr t.wf

end Fusion

end TypeExpr

end
end Strata.Dyn
