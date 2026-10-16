/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataMantle.Env.Data

set_option autoImplicit false

/-!
# The type expression language without well-formedness criteria.
-/

namespace Strata.Mantle

public section

/-- A type expression, or a list of types.  A variable stands for a type or a list, as its
kind in the scope says.  A list variable as an element of a `.list` literal is a splice: the
list it stands for is spliced in.  Well formed, a list variable occurs only so, and every list
is a literal: `as` is written `[*as]`. -/
inductive TypeExpr.Raw where
/-- A variable, by de Bruijn level in the scope. -/
| var (deBruijnLevel : Nat)
| app (name : Name) (args : Array Raw)
/-- A list literal. -/
| list (elems : Array Raw)
deriving Inhabited, Repr

namespace TypeExpr.Raw

/-- Whether the expression is a type or a list, when `scope` gives the kind of each variable.
A variable out of scope counts as a type.  Every kind decision, the DSL's included, comes from
here; if type constructors gain result kinds, only the `.app` case changes. -/
@[expose]
def kind (scope : Array Kind) : Raw → Kind
  | .var i => scope[i]?.getD .type
  | .app .. => .type
  | .list _ => .list

/-- Whether the expression may be an element of a list literal: anything but a literal, so a
type or a list variable spliced in.  No lists of lists. -/
@[expose]
def isElem : Raw → Bool
  | .list _ => false
  | _ => true

/-- Whether the expression is a variable. -/
@[expose]
def isVar : Raw → Bool
  | .var _ => true
  | _ => false

/-! ### Equality -/

mutual
@[expose]
def beq : Raw → Raw → Bool
  | .var i, .var j => i == j
  | .app n ⟨as⟩, .app m ⟨bs⟩ => n == m && beqList as bs
  | .list ⟨as⟩, .list ⟨bs⟩ => beqList as bs
  | _, _ => false

@[expose]
def beqList : List Raw → List Raw → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

instance : BEq Raw := ⟨beq⟩

mutual
/-- `beq` implies equality. -/
private theorem eq_of_beq : ∀ {a b : Raw}, beq a b = true → a = b
  | .var _, .var _, h => by simp only [beq, beq_iff_eq] at h; simp [h]
  | .app _ ⟨_⟩, .app _ ⟨_⟩, h => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1, eqList_of_beqList h.2]
  | .list ⟨_⟩, .list ⟨_⟩, h => by
    simp only [beq] at h
    simp [eqList_of_beqList h]

/-- `beqList` implies equality of the lists. -/
private theorem eqList_of_beqList : ∀ {as bs : List Raw}, beqList as bs = true → as = bs
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [beqList, Bool.and_eq_true] at h
    simp [eq_of_beq h.1, eqList_of_beqList h.2]
end

mutual
/-- `beq` is reflexive. -/
private theorem beq_refl : ∀ (a : Raw), beq a a = true
  | .var _ => by simp [beq]
  | .app _ ⟨as⟩ => by
    simp only [beq, Bool.and_eq_true, beq_self_eq_true, true_and]
    exact beqList_refl as
  | .list ⟨as⟩ => beqList_refl as

/-- `beqList` is reflexive. -/
private theorem beqList_refl : ∀ (as : List Raw), beqList as as = true
  | [] => rfl
  | a :: as => by
    simp only [beqList, Bool.and_eq_true]
    exact ⟨beq_refl a, beqList_refl as⟩
end

instance : LawfulBEq Raw where
  eq_of_beq := eq_of_beq
  rfl := beq_refl _

instance : DecidableEq Raw := fun a b => decidable_of_iff ((a == b) = true) (by simp)

mutual
/-- A hash of the expression, structural, as `beq` compares. -/
def hash : Raw → UInt64
  | .var i => mixHash 11 (Hashable.hash i)
  | .app n ⟨as⟩ => mixHash (mixHash 13 (Hashable.hash n)) (hashList as)
  | .list ⟨es⟩ => mixHash 17 (hashList es)

/-- A hash of the expressions, in order. -/
def hashList : List Raw → UInt64
  | [] => 7
  | e :: es => mixHash (hash e) (hashList es)
end

instance : Hashable Raw := ⟨hash⟩

/-! ### Instantiation -/

/-- What an argument contributes to a list literal it is spliced into: a literal its elements,
and anything else itself. -/
@[expose]
def spliced : Raw → List Raw
  | .list ⟨es⟩ => es
  | e => [e]

mutual
/-- Replace each variable `i` by `args[i]`; a variable with no argument is left alone.  A
variable that is an element of a literal is spliced: if its argument is a literal, the
argument's elements take its place.  It is meant as a full simultaneous substitution, every
variable of the scope given an argument, as `TypeExpr.WF.instantiate` asks: a variable left
alone keeps its old de Bruijn level, which means something else in the arguments' scope. -/
@[expose]
def instantiate (args : Array Raw) : Raw → Raw
  | .var i => args[i]?.getD (.var i)
  | .app n ⟨as⟩ => .app n ⟨instantiateList args as⟩
  | .list ⟨es⟩ => .list ⟨instantiateElems args es⟩

@[expose]
def instantiateList (args : Array Raw) : List Raw → List Raw
  | [] => []
  | e :: es => instantiate args e :: instantiateList args es

/-- A literal's elements, instantiated, each variable's argument spliced in. -/
@[expose]
def instantiateElems (args : Array Raw) : List Raw → List Raw
  | [] => []
  | .var i :: es => (args[i]?.getD (.var i)).spliced ++ instantiateElems args es
  | e :: es => instantiate args e :: instantiateElems args es
end

/-- What one element of a literal instantiates to: a variable's argument spliced in, or the
instantiated element. -/
@[expose]
def instantiateElem (args : Array Raw) : Raw → List Raw
  | .var i => (args[i]?.getD (.var i)).spliced
  | e => [instantiate args e]

/-! ### The variables in scope -/

/-- The variables `i, i + 1, …` of kinds `ks`, each as an argument: a type variable itself, and
a list variable spliced into a literal of its own. -/
@[expose]
def varsFrom (i : Nat) : List Kind → List Raw
  | [] => []
  | .type :: ks => .var i :: varsFrom (i + 1) ks
  | .list :: ks => .list #[.var i] :: varsFrom (i + 1) ks

/-- The variables of `scope`, in order, each as an argument: the arguments that apply a type
constructor to its own parameters. -/
@[expose]
def vars (scope : Array Kind) : Array Raw := ⟨varsFrom 0 scope.toList⟩

/-! ### Folding -/

universe u

mutual

/-- Fold over the variables, applications and list literals in a type expression. -/
@[expose]
def fold {β : Type u} (var : Nat → β) (app : Name → Array β → β) (list : Array β → β) :
    Raw → β
  | .var i => var i
  | .app n ⟨as⟩ => app n ⟨foldList var app list as⟩
  | .list ⟨es⟩ => list ⟨foldList var app list es⟩

@[expose]
def foldList {β : Type u} (var : Nat → β) (app : Name → Array β → β) (list : Array β → β) :
    List Raw → List β
  | [] => []
  | e :: es => fold var app list e :: foldList var app list es
end

end TypeExpr.Raw

end

end Strata.Mantle
