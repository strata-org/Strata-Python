/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Core.Types
public import StrataDyn.TypeDenote
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote

set_option autoImplicit false

/-!
# Denotation preservation for Dyn-to-Core types

Dyn is interpreted directly by `TypeDenote.denote`. Core is interpreted compositionally,
with the same built-in carriers as `Lambda.SortDenote`, but arbitrary Lean types for variables
and semantic arguments for custom constructors. This permits arbitrary recursive carriers;
`core_eq_tyDenote` relates this interpretation to Core's sort-substitution-based `TyDenote`
when variable assignments and custom constructor interpretations agree.

`Laws` is the semantic obligation on a representation policy and on the carriers supplied for
nominal datatypes, not a consequence of well-formedness. The key theorems lift it: `preserves`
to every type expression, including type-list splices; `datatype_preserves` to one unfolding of
every member of every emitted block; `preserves_tyDenote` to Core's `TyDenote`, through
`core_eq_tyDenote`.

The meanings of Dyn constructors are a parameter, `TypeDenote.Constructors`, not yet the
run-time semantics of `StrataDyn/Exec`, whose model interprets tags and is indexed by the run
token. Connecting the two is a later step, and the function type `Fn` is handled there, since a
Core representation of closures belongs with the value lowering.
-/

namespace Strata.Dyn.CoreTypes.Denote

open Lambda

public section

/-- Meanings of non-built-in Core constructors, applied to argument meanings. -/
abbrev Constructors := String → List Type → Type

/-- Core's built-in carriers; custom constructors cannot override them. -/
def app (custom : Constructors) : String → List Type → Type
  | "bool", [] => Bool
  | "int", [] => Int
  | "real", [] => Strata.Util.Real
  | "string", [] => String
  | "arrow", [a, b] => a → b
  | name, args => custom name args

/-- A compositional Core interpretation, with arbitrary carriers for free type variables. -/
def core (custom : Constructors) (vars : TyIdentifier → Type) : LMonoTy → Type
  | .ftvar v => vars v
  | .bitvec n => BitVec n
  | .tcons name args => app custom name (args.map (core custom vars))

/-- On constructor applications, Core's denotation is compositional when its custom
constructor interpretation is. -/
private theorem sortDenote_tcons (tcInterp : TyConstrInterp) (custom : Constructors)
    (hc : ∀ name args, tcInterp name args = custom name (args.map (SortDenote tcInterp)))
    (name : String) (args : List LSort) :
    SortDenote tcInterp (.tcons name args) = app custom name (args.map (SortDenote tcInterp)) := by
  unfold SortDenote app
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> split <;> split <;> grind

/-- Agreement with Core's existing two-pass interpretation: variables denote the supplied
sorts, and custom constructors depend compositionally on their argument meanings. -/
theorem core_eq_tyDenote (tcInterp : TyConstrInterp) (custom : Constructors)
    (hc : ∀ name args, tcInterp name args = custom name (args.map (SortDenote tcInterp)))
    (ρ : TyVarVal) (vars : TyIdentifier → Type)
    (hv : ∀ v, vars v = SortDenote tcInterp (ρ v)) (t : LMonoTy) :
    core custom vars t = TyDenote tcInterp ρ t := by
  induction t using LMonoTy.rec (motive_2 := fun ts =>
      ts.map (core custom vars) = (LMonoTy.substTyVars.map ρ ts).map (SortDenote tcInterp)) with
  | ftvar v => simp only [core, TyDenote, LMonoTy.substTyVars, hv]
  | bitvec n => simp only [core, TyDenote, LMonoTy.substTyVars, SortDenote]
  | tcons name args ih =>
    simp only [core, TyDenote, LMonoTy.substTyVars, sortDenote_tcons tcInterp custom hc, ih]
  | nil => rfl
  | cons t ts iht ihts => simp only [List.map_cons, LMonoTy.substTyVars.map, iht, ihts]

/-- Interpret a translated type or type list. -/
def value (custom : Constructors) (vars : TyIdentifier → Type) {K : Signature} {V : Vars} :
    (k : Kind) → Value K V k → TypeDenote.Value k
  | .type, t => core custom vars t.val
  | .list, ts => ts.map (fun t => core custom vars t.val)

/-- Each constructor representation agrees with its independent Dyn meaning on all arguments.
This includes nominal datatypes: their recursive carriers are supplied, not constructed. -/
def Laws {α : Type} {env : Env α} (policy : Policy) (dyn : TypeDenote.Constructors env)
    (custom : Constructors) (vars : TyIdentifier → Type) : Prop :=
  ∀ {K : Signature} {V : Vars} (hK : ∀ n a, signature env policy n a → K n a)
    {arity : Nat} (r : TypeRef env arity) (args : TypeExpr.Arguments (Value K V) r.kinds),
    core custom vars (CoreTypes.apply policy hK r args).val = dyn r (args.map (value custom vars))

/-- Interpreting a flattened Core type list is flattening the interpreted elements: `value` on a
literal's splice agrees with Dyn's `splice` after interpreting each element. -/
private theorem splice_map (custom : Constructors) (vars : TyIdentifier → Type)
    {K : Signature} {V : Vars} (es : Array ((k : Kind) × Value K V k)) :
    value custom vars .list (es.toList.flatMap Value.splice) =
      (es.map (TypeExpr.mapValue (value custom vars))).toList.flatMap TypeDenote.splice := by
  simp only [value, List.map_flatMap, Array.toList_map, List.flatMap_map]
  congr 1
  funext x
  rcases x with ⟨k, x⟩
  cases k
  · rw [Value.splice_type]
    rfl
  · rw [Value.splice_list]
    rfl

/-- Dyn's generated nominal names cannot select a built-in Core carrier. -/
private theorem app_typeName (custom : Constructors) (n : Name) (ts : List Type) :
    app custom (typeName n) ts = custom (typeName n) ts := by
  have hlen := le_length_typeName n
  unfold app
  split <;> (try rfl) <;> (rename_i h; rw [h] at hlen; exfalso; revert hlen; decide)

/-- The nominal generator law: only agreement of constructor meanings after name translation
is required. The arguments are already interpreted; no source expression is translated here. -/
theorem core_apply_nominal {α : Type} {env : Env α} (policy : Policy)
    (custom : Constructors) (vars : TyIdentifier → Type) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {arity : Nat} (r : TypeRef env arity)
    (args : TypeExpr.Arguments (Value K V) r.kinds) (h : representation policy r = .nominal) :
    core custom vars (CoreTypes.apply policy hK r args).val =
      custom (typeName r.name)
        ((args.map (value custom vars)).values.toList.flatMap TypeDenote.splice) := by
  rw [apply_nominal policy hK r args h]
  simp only [core, app_typeName, List.map_map]
  exact congrArg (custom (typeName r.name)) (splice_map custom vars args.values)

/-- A concrete constructor's meaning is the meaning of its chosen representation. -/
theorem core_apply_concrete {α : Type} {env : Env α} (policy : Policy)
    (custom : Constructors) (vars : TyIdentifier → Type) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {arity : Nat} (r : TypeRef env arity)
    (args : TypeExpr.Arguments (Value K V) r.kinds) (c : Concrete r.kinds)
    (h : representation policy r = .concrete c) :
    core custom vars (CoreTypes.apply policy hK r args).val =
      core custom vars (c.apply (fun p hp => hK _ _ (signature_of_concrete h p hp)) args).val := by
  rw [apply_concrete policy hK r args c h]

/-- Translation preserves meaning: under a policy satisfying `Laws` and variable assignments
that agree, the Core interpretation of a translated type expression is its direct Dyn
denotation. -/
theorem preserves {α : Type} {env : Env α} (policy : Policy)
    (dyn : TypeDenote.Constructors env) (custom : Constructors) (vars : TyIdentifier → Type)
    (laws : Laws policy dyn custom vars) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {scope : Array Kind}
    (s : Scope K V scope) (ds : TypeDenote.Assignment scope)
    (hs : ∀ i k h, value custom vars k (s i k h) = ds i k h)
    {k : Kind} (t : TypeExpr env scope k) :
    value custom vars k (translate policy hK s t) = TypeDenote.denote dyn ds t := by
  rw [translate_eq]
  exact TypeExpr.elim_map (value custom vars) s (CoreTypes.apply policy hK) _ ds dyn _
    ⟨hs, laws hK, splice_map custom vars⟩ t

/-- Type-expression preservation stated directly in Core's existing denotation. -/
theorem preserves_tyDenote {α : Type} {env : Env α} (policy : Policy)
    (dyn : TypeDenote.Constructors env) (tcInterp : TyConstrInterp) (custom : Constructors)
    (hc : ∀ name args, tcInterp name args = custom name (args.map (SortDenote tcInterp)))
    (ρ : TyVarVal) (laws : Laws policy dyn custom (fun v => SortDenote tcInterp (ρ v)))
    {K : Signature} {V : Vars} (hK : ∀ n a, signature env policy n a → K n a) {scope : Array Kind}
    (s : Scope K V scope) (ds : TypeDenote.Assignment scope)
    (hs : ∀ i k h, value custom (fun v => SortDenote tcInterp (ρ v)) k (s i k h) = ds i k h)
    (t : TypeExpr env scope) :
    TyDenote tcInterp ρ (translateType policy hK s t).val = TypeDenote.denote dyn ds t := by
  rw [translateType_eq]
  exact (core_eq_tyDenote tcInterp custom hc ρ _ (fun _ => rfl) _).symm.trans
    (preserves policy dyn custom _ laws hK s ds hs t)

/-- The product of a constructor's fields, including the nullary constructor. -/
def fields (types : List Type) : Type := types.foldr Prod Unit

/-- The sum of the constructor alternatives. -/
def alternatives (types : List Type) : Type := types.foldr Sum Empty

/-- One unfolding of a Dyn declaration under an independent interpretation of its fields. -/
def dynBody {α : Type} {env : Env α} (dyn : TypeDenote.Constructors env)
    (d : Env.Datatype env) (ds : TypeDenote.Assignment (TyParam.kinds d.decl.params)) : Type :=
  alternatives (d.ctors.toList.map fun c =>
    fields (c.args.toList.map fun p => TypeDenote.denote dyn ds (k := .type) p.type))

/-- One unfolding of an emitted Core declaration, with recursive references left as carriers. -/
def coreBody (custom : Constructors) (vars : TyIdentifier → Type) (d : LDatatype Unit) : Type :=
  alternatives (d.constrs.map fun c => fields (c.args.map fun p => core custom vars p.2))

/-- Preservation of one unfolding of every member of every emitted block, for arbitrary
compatible assignments and recursive carriers: the `i`th Core datatype of the block of `g`
agrees with the `i`th member of `g`, whose variables stand for the block's binders for it
(`memberScope`). Apply memberwise for a mutual group; no fixed point is assumed. -/
theorem datatype_preserves {α : Type} {env : Env α} (policy : Policy)
    (dyn : TypeDenote.Constructors env) (custom : Constructors) (vars : TyIdentifier → Type)
    (laws : Laws policy dyn custom vars) (g : Env.Group env) (b : MutualDatatype Unit)
    (hb : block policy g = some b) (i : Nat) (hi : i < g.members.size)
    (ds : TypeDenote.Assignment (TyParam.kinds g.members[i].decl.params))
    (hs : ∀ j k hj, value custom vars k
      (memberScope policy (b[i]'(length_block hb ▸ hi)).typeArgs g.members[i] (kinds_block hb i hi)
        j k hj) = ds j k hj) :
    coreBody custom vars (b[i]'(length_block hb ▸ hi)) = dynBody dyn g.members[i] ds := by
  simp only [coreBody, dynBody, constrs_block hb i hi, translateType_eq, List.map_map,
    Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c _
  congr 1
  apply List.map_congr_left
  intro p _
  exact preserves policy dyn custom vars laws _ _ ds hs p.type

end
end Strata.Dyn.CoreTypes.Denote
