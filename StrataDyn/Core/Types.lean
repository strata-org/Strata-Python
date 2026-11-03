/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.Env
public import StrataDyn.Env.TypeExprElim
public import Strata.Languages.Core.TypeDecl

set_option autoImplicit false

/-!
# Dyn types represented in Core

A `Policy` chooses the representation of each primitive: nominal (an uninterpreted Core type
constructor) or `Concrete` (a Core type built from the arguments, such as `Int` as `int`, or the
function type as one opaque type, since calls are modelled by the value lowering). Datatypes
are always nominal, as their generic Core datatypes. Their binders are derived internally by
solving the equalities Core's uniformity check imposes; callers do not supply binder names.

Everything is a total function of the environment and policy:

* `translate policy hK scope t : Value K V k` eliminates a checked type expression into a Core
  type carrying its well-formedness, `TypeWF K V`: variables bound in `V`, constructors at
  the arities of the signature `K`, which must include `signature env policy`.
  A `Scope` says what each variable stands for: `Scope.closed`; `Scope.ofBinders`, one Core
  variable per parameter, which every type of a signature shares and `scheme` quantifies; and
  `Scope.ofArguments`, an instantiation, with the consumer's Core types checked once.
* `compile env policy : List Core.TypeDecl` emits the declarations the types need, in
  declaration order: a type constructor per nominal primitive, a datatype block per group.
* `Supported policy C entries C'` is the proposition that those declarations are well formed
  in a Core context, `DeclarationsWF` (`Supported.wf`), with datatype blocks certified by
  Core's executable checker; `C'` is the context Core's declaration rules build for them:
  datatypes, known types and generated functions (registering the names as program identifiers
  is the embedding program's step). `check` decides it, naming the first declaration that fails.
  That is the one place a Dyn environment is rejected: a datatype or nominal primitive with a list
  parameter, an empty datatype, a group whose members cannot share binders, a group Core's
  structural checks refuse, a Core name already taken, or a concrete representation using a
  constructor the context does not know.

Core has fixed-arity type constructors and no type-list kind, so a list parameter is fine
only where a concrete representation consumes it; a nominal constructor with a list parameter
has no declaration, and a list parameter cannot be a Core binder.  No values or operations are
translated; representation choices carry no claim about operation semantics.
-/

namespace Strata.Dyn.CoreTypes

open Lambda

public section

/-! ### Well-formed Core types -/

/-- Which Core type constructors exist, at which arities. -/
abbrev Signature := String → Nat → Prop

/-- Which Core type variables are bound. -/
abbrev Vars := TyIdentifier → Prop

/-- A Core type whose variables are bound and whose constructors have their declared arities. -/
inductive TypeWF (K : Signature) (V : Vars) : LMonoTy → Prop where
  | var {v : TyIdentifier} : V v → TypeWF K V (.ftvar v)
  | bitvec (width : Nat) : TypeWF K V (.bitvec width)
  | app {name : String} {args : List LMonoTy} : K name args.length →
      (∀ a ∈ args, TypeWF K V a) → TypeWF K V (.tcons name args)

/-- A well-formed type stays well formed under a larger signature and more variables. -/
theorem TypeWF.mono {K K' : Signature} {V V' : Vars} {t : LMonoTy}
    (hK : ∀ n a, K n a → K' n a) (hV : ∀ v, V v → V' v) (h : TypeWF K V t) : TypeWF K' V' t := by
  induction h with
  | var h => exact .var (hV _ h)
  | bitvec n => exact .bitvec n
  | app h _ ih => exact .app (hK _ _ h) ih

/-- A Core type together with its well-formedness. -/
abbrev Ty (K : Signature) (V : Vars) := { t : LMonoTy // TypeWF K V t }

namespace Ty

variable {K : Signature} {V : Vars}

def var (v : TyIdentifier) (h : V v) : Ty K V := ⟨.ftvar v, .var h⟩

def bitvec (width : Nat) : Ty K V := ⟨.bitvec width, .bitvec width⟩

def app (name : String) (args : List (Ty K V)) (h : K name args.length) : Ty K V :=
  ⟨.tcons name (args.map Subtype.val), .app (by simpa using h) fun a ha => by
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp ha
    exact t.property⟩

def mono {K' : Signature} {V' : Vars} (hK : ∀ n a, K n a → K' n a) (hV : ∀ v, V v → V' v)
    (t : Ty K V) : Ty K' V' :=
  ⟨t.val, t.property.mono hK hV⟩

end Ty

/-- What a Dyn expression of a kind translates to: a type to a Core type, a list to the Core
types of its elements. -/
@[expose, reducible] def Value (K : Signature) (V : Vars) : Kind → Type
  | .type => Ty K V
  | .list => List (Ty K V)

/-- The elements a translated argument contributes to a list literal. -/
def Value.splice {K : Signature} {V : Vars} : ((k : Kind) × Value K V k) → List (Ty K V)
  | ⟨.type, t⟩ => [t]
  | ⟨.list, ts⟩ => ts

/-- A translated type contributes itself. -/
theorem Value.splice_type {K : Signature} {V : Vars} (t : Ty K V) :
    Value.splice ⟨.type, t⟩ = [t] := by
  unfold Value.splice
  rfl

/-- A translated list contributes its elements. -/
theorem Value.splice_list {K : Signature} {V : Vars} (ts : List (Ty K V)) :
    Value.splice ⟨.list, ts⟩ = ts := by
  unfold Value.splice
  rfl

/-- The raw form of a translated expression, as a consumer supplies it. -/
@[expose] def Translated : Kind → Type
  | .type => LMonoTy
  | .list => List LMonoTy

/-! ### Deciding well-formedness

A consumer's own Core types enter at an instantiation; they are checked once, there. -/

mutual
def typeWF (K : Signature) (V : Vars) [∀ n a, Decidable (K n a)] [DecidablePred V] :
    LMonoTy → Bool
  | .ftvar v => decide (V v)
  | .bitvec _ => true
  | .tcons name args => decide (K name args.length) && typeWFList K V args

private def typeWFList (K : Signature) (V : Vars) [∀ n a, Decidable (K n a)] [DecidablePred V] :
    List LMonoTy → Bool
  | [] => true
  | t :: ts => typeWF K V t && typeWFList K V ts
end

/-- `typeWFList` is true exactly when `typeWF` is true of every element. -/
private theorem typeWFList_eq_true_iff {K : Signature} {V : Vars} [∀ n a, Decidable (K n a)]
    [DecidablePred V] : ∀ {ts : List LMonoTy},
      typeWFList K V ts = true ↔ ∀ t ∈ ts, typeWF K V t = true
  | [] => by simp [typeWFList]
  | t :: ts => by
    simp only [typeWFList, Bool.and_eq_true, typeWFList_eq_true_iff, List.mem_cons,
      forall_eq_or_imp]

/-- A positive `typeWF` answer is a `TypeWF` derivation: every variable is bound in `V` and every
constructor is applied at an arity `K` admits. -/
private theorem typeWF_of_decide {K : Signature} {V : Vars} [∀ n a, Decidable (K n a)] [DecidablePred V] :
    ∀ {t : LMonoTy}, typeWF K V t = true → TypeWF K V t
  | .ftvar v, h => .var (by simpa [typeWF] using h)
  | .bitvec n, _ => .bitvec n
  | .tcons name args, h => by
    simp only [typeWF, Bool.and_eq_true, decide_eq_true_eq, typeWFList_eq_true_iff] at h
    exact .app h.1 fun a ha => typeWF_of_decide (h.2 a ha)
termination_by t => sizeOf t
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ha
  omega

/-- The signature of a Core context: its known type constructors at their arities. -/
def contextSignature (C : LContext Core.CoreLParams) : Signature := fun n a =>
  C.knownTypes[n]? = some a

instance (C : LContext Core.CoreLParams) (n : String) (a : Nat) :
    Decidable (contextSignature C n a) :=
  inferInstanceAs (Decidable (C.knownTypes[n]? = some a))

/-! ### Names

Core names are the Dyn names' readable text, `Name.escaped`, which is injective
(`Name.escaped_inj`), under a prefix saying what the name declares; they appear in Core's
errors and SMT dumps. -/

/-- The Core name of a nominally represented Dyn type: a datatype, or an uninterpreted
primitive; `base.Except` is `$dyn.type.base.Except`. -/
def typeName (n : Name) : String := "$dyn.type" ++ n.escaped

/-- A nominal Core name is at least its prefix long, so it is none of Core's built-in names. -/
theorem le_length_typeName (n : Name) : 9 ≤ (typeName n).length := by
  rw [typeName, String.length_append]
  exact Nat.le_add_right 9 _

def constructorName (n : Name) : String := "$dyn.ctor" ++ n.escaped

def testerName (n : Name) : String := "$dyn.test" ++ n.escaped

/-- Core selectors are global functions, so each field is qualified by its constructor:
`$dyn.field.base.ok.value`. -/
def fieldName (ctor : Name) (field : String) : String :=
  "$dyn.field" ++ Name.escaped (.str ctor field)

/-- The Core type variable a generic scope binds for the Dyn type parameter `name`. -/
def binderName (name : String) : String := "$dyn.var." ++ name

/-- Distinct parameters get distinct Core variables. -/
theorem nodup_map_binderName {names : List String} (h : names.Nodup) :
    (names.map binderName).Nodup :=
  List.Pairwise.map binderName (fun _ _ ne eq => ne ((String.append_right_inj _).mp eq)) h

/-- The `i`th Core type variable of a datatype declaration. -/
def datatypeBinder (i : Nat) : String := "$dyn.param." ++ toString i

/-! ### Representations and policies -/

/-- A concrete Core representation of a type constructor with parameters of `kinds`: a total
function of the translated arguments, at their kinds, into well-formed Core types, under any
signature that has the constructors it `uses`.  It must be uniform in its arguments and
introduce no variables of its own.  These are representation choices, not claims about
operation semantics. -/
structure Concrete (kinds : Array Kind) where
  uses : List (String × Nat)
  apply : ∀ {K : Signature} {V : Vars}, (∀ p ∈ uses, K p.1 p.2) →
    TypeExpr.Arguments (Value K V) kinds → Ty K V

/-- How a type constructor is represented in Core. -/
inductive Representation (kinds : Array Kind) where
  /-- The Core type constructor `typeName` of the Dyn name, applied to the translated arguments:
  a datatype, or an uninterpreted primitive. -/
  | nominal
  | concrete (c : Concrete kinds)

/-- The representation of each primitive declaration's name and parameters, with its annotation
erased; `.nominal` is an uninterpreted constructor. -/
abbrev Policy := (d : TypeDecl Unit) → Representation d.kinds

/-- Represent every primitive by an uninterpreted constructor. -/
def uninterpreted : Policy := fun _ => .nominal

/-- A datatype is its Core datatype; a primitive is what the policy says. -/
def representation {α : Type} {env : Env α} (policy : Policy) {arity : Nat}
    (t : TypeRef env arity) : Representation t.kinds :=
  if (env.dataOf? t.name).isSome then .nominal else policy t.decl.erase

/-- The Core type constructors translations under the policy mention. A nominal constructor has
its arity; one with a list parameter, which has no fixed arity, is admitted at every arity, so
that translation is total, and is rejected where it would be declared, by `check`. -/
def signature {α : Type} (env : Env α) (policy : Policy) : Signature := fun n a =>
  ∃ (arity : Nat) (t : TypeRef env arity),
    match representation policy t with
    | .nominal => n = typeName t.name ∧ ((∀ k ∈ t.kinds, k = .type) → a = arity)
    | .concrete c => (n, a) ∈ c.uses

/-- The Core constructors a concrete representation uses are in the signature. -/
theorem signature_of_concrete {α : Type} {env : Env α} {policy : Policy} {arity : Nat}
    {r : TypeRef env arity} {c : Concrete r.kinds} (h : representation policy r = .concrete c) :
    ∀ p ∈ c.uses, signature env policy p.1 p.2 :=
  fun _ hp => ⟨arity, r, by rw [h]; exact hp⟩

/-- The Core type constructor of a nominal primitive. -/
def constructor {α : Type} {env : Env α} {arity : Nat} (t : TypeRef env arity) : TypeConstructor :=
  { name := typeName t.name, params := t.decl.paramNames }

inductive Error where
  /-- A scope was given the wrong number of arguments. -/
  | parameterCount (given expected : Nat)
  /-- A scope was given an argument of the wrong kind at a de Bruijn level. -/
  | parameterKind (level : Nat) (given expected : Kind)
  /-- A consumer's Core type is not well formed in the context. -/
  | illFormed (type : LMonoTy)
  /-- A list parameter cannot be a Core type variable. -/
  | listBinder (level : Nat) (name : String)
  /-- A datatype or a nominal primitive with a list parameter has no Core declaration. -/
  | listParameter (name : Name)
  | emptyDatatype (name : Name)
  /-- The alignment for the datatype group headed by `name` identifies two parameters of a
  member or leaves different parameter sets across members, including unused parameters. -/
  | unsharedBinders (name : Name)
  /-- The Core name of a declaration is already taken in the context. -/
  | duplicateType (name : Name)
  /-- A concrete representation uses a Core constructor the context does not know at that
  arity. -/
  | unknownType (name : Name) (constructor : String) (arity : Nat)
  /-- Core rejected the datatype group headed by `name`. -/
  | coreDatatype (name : Name) (reason : String)
  deriving DecidableEq, Repr

/-! ### Scopes -/

/-- Core's view of a Dyn scope: what each variable, by de Bruijn level and at its kind, stands
for.  The kinds index it, so a type expression is translated only under a scope made for its
kinds. -/
abbrev Scope (K : Signature) (V : Vars) (kinds : Array Kind) :=
  (i : Nat) → (k : Kind) → kinds[i]? = some k → Value K V k

namespace Scope

variable {K : Signature} {V : Vars}

/-- The scope of a closed type. -/
def closed : Scope K V #[] := fun _ _ h => absurd h (by simp)

/-- A scope binding one Core type variable per variable, named as given: the variables of a
generic signature.  Every type translated under it shares them, and `scheme` quantifies them. -/
def ofBinders (names : List TyIdentifier) :
    Scope K (· ∈ names) (Array.replicate names.length .type) :=
  fun i k h =>
    have hi : i < names.length := by simpa using (Array.getElem?_eq_some_iff.mp h).1
    have hk : k = .type := by simpa [Array.getElem?_replicate, hi] using h.symm
    hk ▸ (Ty.var names[i] (List.getElem_mem hi) : Value K (· ∈ names) .type)

/-- The kinds of a signature whose parameters are all type parameters. -/
private theorem kinds_eq_replicate {params : Array (Param Kind)} (h : ∀ p ∈ params, p.type = .type) :
    Param.kinds params = Array.replicate params.size .type := by
  apply Array.toList_inj.mp
  rw [Array.toList_replicate, ← Array.length_toList]
  show params.toList.map (·.type) = _
  exact List.map_eq_replicate_iff.mpr fun p hp => h p (by simpa using hp)

/-- The scope of a generic signature: one Core binder per type parameter, named from the
parameter, which every type of the signature shares and `scheme` quantifies.  A list parameter
has no Core binder.  The parameters are named distinctly, as a signature's are, so the Core
binders are too, as the result records; nothing here relies on that yet. -/
def generic (params : Array (Param Kind)) (distinct : (params.toList.map (·.name)).Nodup) :
    Except Error ((names : { ns : List TyIdentifier // ns.Nodup }) ×
      Scope K (· ∈ names.val) (Param.kinds params)) :=
  match hl : params.toList.zipIdx.find? (fun (p, _) => p.type == .list) with
  | some (p, i) => throw (.listBinder i p.name)
  | none =>
    have h : ∀ p ∈ params, p.type = .type := fun p hp => by
      have hp' : p ∈ params.toList.zipIdx.map Prod.fst := by
        rw [List.zipIdx_map_fst]; simpa using hp
      obtain ⟨⟨q, i⟩, hq, rfl⟩ := List.mem_map.mp hp'
      have := List.find?_eq_none.mp hl _ hq
      cases hk : q.type <;> simp_all
    let names := (params.toList.map (·.name)).map binderName
    have hk : Param.kinds params = Array.replicate names.length .type := by
      rw [kinds_eq_replicate h]; simp [names]
    pure ⟨⟨names, nodup_map_binderName distinct⟩, hk ▸ ofBinders names⟩

/-- A scope stays a scope under a larger signature and more variables. -/
def mono {K' : Signature} {V' : Vars} {kinds : Array Kind} (hK : ∀ n a, K n a → K' n a)
    (hV : ∀ v, V v → V' v) (s : Scope K V kinds) : Scope K' V' kinds :=
  fun i k h =>
    match k, s i k h with
    | .type, t => (t.mono hK hV : Ty K' V')
    | .list, ts => (ts.map (Ty.mono hK hV) : List (Ty K' V'))

/-- A scope from one value per variable, at the variables' kinds. -/
def ofValues {kinds : Array Kind} (values : List ((k : Kind) × Value K V k))
    (h : values.map Sigma.fst = kinds.toList) : Scope K V kinds :=
  fun i k hk =>
    have hk' : values[i]?.map Sigma.fst = some k := by
      rw [← List.getElem?_map, h, Array.getElem?_toList]; exact hk
    match hv : values[i]?, hk' with
    | some v, hk' => (Option.some.inj (by simpa [hv] using hk') : v.1 = k) ▸ v.2
    | none, hk' => absurd hk' (by simp)

/-- The well-formed form of a consumer's Core type or list, or the type that is not well
formed. -/
def check [∀ n a, Decidable (K n a)] [DecidablePred V] : (k : Kind) → Translated k →
    Except Error (Value K V k)
  | .type, t =>
    if h : typeWF K V t = true then pure ⟨t, typeWF_of_decide h⟩ else throw (.illFormed t)
  | .list, ts => ts.mapM fun t =>
    if h : typeWF K V t = true then pure ⟨t, typeWF_of_decide h⟩ else throw (.illFormed t)

/-- An instantiation: each variable stands for the given Core type or list, with the count,
kinds and well-formedness of the arguments checked once. -/
def ofArguments [∀ n a, Decidable (K n a)] [DecidablePred V] (kinds : Array Kind)
    (arguments : List ((k : Kind) × Translated k)) : Except Error (Scope K V kinds) := do
  let values ← arguments.mapM fun ⟨k, a⟩ => do
    let v ← check k a
    pure (⟨k, v⟩ : (k : Kind) × Value K V k)
  if h : values.map Sigma.fst = kinds.toList then
    return ofValues values h
  else
    match KindError.check? kinds (arguments.map Sigma.fst).toArray with
    | some (.count given expected) => throw (.parameterCount given expected)
    | some (.kind i given expected) => throw (.parameterKind i given expected)
    -- Unreachable: `values` has `arguments`' kinds, so a mismatch is a count or kind error.
    | none => throw (.parameterCount arguments.length kinds.size)

end Scope

/-- A type under the binders of a generic signature, closed over them. -/
def scheme {K : Signature} {names : List TyIdentifier} (t : Ty K (· ∈ names)) : LTy :=
  .forAll names t.val

/-! ### Translation -/

/-- Summing a constant `1` over a list gives its length. -/
private theorem sum_map_one {β : Type _} : ∀ (l : List β), (l.map fun _ => (1 : Nat)).sum = l.length
  | [] => rfl
  | _ :: l => by simp [sum_map_one l, Nat.add_comm]

/-- A nominal constructor's arguments, spliced: one Core type per argument when all parameters
are type parameters. -/
private theorem length_splice {K : Signature} {V : Vars} {kinds : Array Kind}
    (args : TypeExpr.Arguments (Value K V) kinds) (h : ∀ k ∈ kinds, k = .type) :
    (args.values.toList.flatMap Value.splice).length = kinds.size := by
  have hk : ∀ a ∈ args.values, a.1 = .type := fun a ha =>
    h a.1 (by rw [← args.kinds_eq]; exact Array.mem_map.mpr ⟨a, ha, rfl⟩)
  have : ∀ a ∈ args.values.toList, (Value.splice a).length = 1 := fun a ha => by
    obtain ⟨k, v⟩ := a
    have := hk ⟨k, v⟩ (by simpa using ha)
    simp only at this
    subst this
    rfl
  rw [List.length_flatMap, List.map_congr_left this, sum_map_one, Array.length_toList]
  simpa using congrArg Array.size args.kinds_eq

/-- Apply a constructor's representation to already translated arguments. -/
def apply {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {arity : Nat} (r : TypeRef env arity)
    (args : TypeExpr.Arguments (Value K V) r.kinds) : Ty K V :=
  match h : representation policy r with
  | .nominal =>
    Ty.app (typeName r.name) (args.values.toList.flatMap Value.splice)
      (hK _ _ ⟨arity, r, by
        rw [h]
        exact ⟨rfl, fun hk => (length_splice args hk).trans r.size_kinds⟩⟩)
  | .concrete c => c.apply (fun p hp => hK _ _ (signature_of_concrete h p hp)) args

/-- `apply` at a nominal constructor: its Core type constructor at the spliced arguments. -/
theorem apply_nominal {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {arity : Nat} (r : TypeRef env arity)
    (args : TypeExpr.Arguments (Value K V) r.kinds) (h : representation policy r = .nominal) :
    (apply policy hK r args).val =
      .tcons (typeName r.name) ((args.values.toList.flatMap Value.splice).map Subtype.val) := by
  unfold apply
  split
  · rfl
  · rename_i heq
    cases h.symm.trans heq

/-- `apply` at a concretely represented constructor: the representation at the arguments. -/
theorem apply_concrete {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {arity : Nat} (r : TypeRef env arity)
    (args : TypeExpr.Arguments (Value K V) r.kinds) (c : Concrete r.kinds)
    (h : representation policy r = .concrete c) :
    (apply policy hK r args).val =
      (c.apply (fun p hp => hK _ _ (signature_of_concrete h p hp)) args).val := by
  unfold apply
  split
  · rename_i heq
    cases h.symm.trans heq
  · rename_i heq
    cases Representation.concrete.inj (h.symm.trans heq)
    rfl

/-- Translate a type expression into a well-formed Core type under a signature that includes
`signature env policy`: each variable is what the scope says it stands for, each application its
constructor's representation of the translated arguments, and each literal the types of its
elements. -/
def translate {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {kinds : Array Kind} {k : Kind}
    (s : Scope K V kinds) (t : TypeExpr env kinds k) : Value K V k :=
  t.elim (β := Value K V) s (apply policy hK)
    (fun elems => elems.toList.flatMap Value.splice)

/-- `translate` is the type expression's eliminator, with `apply` at applications and splicing
at literals. -/
theorem translate_eq {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {kinds : Array Kind} {k : Kind}
    (s : Scope K V kinds) (t : TypeExpr env kinds k) :
    translate policy hK s t = t.elim (β := Value K V) s (apply policy hK)
      (fun elems => elems.toList.flatMap Value.splice) := by
  unfold translate
  rfl

/-- `translate`, at a type. -/
def translateType {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {kinds : Array Kind} (s : Scope K V kinds)
    (t : TypeExpr env kinds) : Ty K V :=
  translate policy hK s t

/-- Unfold `translateType` to `translate` at the type kind, for rewriting without unfolding. -/
theorem translateType_eq {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {kinds : Array Kind} (s : Scope K V kinds)
    (t : TypeExpr env kinds) : translateType policy hK s t = translate policy hK s t := by
  unfold translateType
  rfl

/-- `translate`, at a list of types. -/
def translateList {α : Type} {env : Env α} (policy : Policy) {K : Signature} {V : Vars}
    (hK : ∀ n a, signature env policy n a → K n a) {kinds : Array Kind} (s : Scope K V kinds)
    (l : TypeList env kinds) : List (Ty K V) :=
  translate policy hK s l

/-! ### Datatype groups

Core's uniformity check compares binder names across the group's members, while Dyn's members
name their parameters independently and may permute them in mutual references. Translate once
under provisional names to derive the equalities, then translate under the aligned names.
Binder selection is internal; the primitive policy is the only caller-supplied choice. A group
whose aligned parameter sets differ has no block: Core requires every member to declare the
same parameters, including unused ones, in any order. Each member must also keep its parameters
distinct. -/

section

variable {α : Type} {env : Env α}

/-- The scope a member's fields are translated under: the block's binders for the member, one
Core type variable per parameter. -/
def memberScope (policy : Policy) (names : List TyIdentifier) (d : Env.Datatype env)
    (h : TyParam.kinds d.decl.params = Array.replicate names.length .type) :
    Scope (signature env policy) (· ∈ names) (TyParam.kinds d.decl.params) :=
  h ▸ Scope.ofBinders names

/-- Translate a member under the names chosen internally for its parameters. -/
private def datatypeWithBinders (policy : Policy) (names : List TyIdentifier)
    (d : Env.Datatype env) : Option (LDatatype Unit) :=
  if h : TyParam.kinds d.decl.params = Array.replicate names.length .type then
    let scope := memberScope policy names d h
    let constrs : List (LConstr Unit) := d.ctors.toList.map fun c => {
      name := ⟨constructorName c.name, ()⟩
      args := c.args.toList.map fun p =>
        (⟨fieldName c.name p.name, ()⟩, (translateType policy (fun _ _ h => h) scope p.type).val)
      testerName := testerName c.name }
    if hne : constrs.length != 0 then
      some { name := typeName d.decl.name, typeArgs := names, constrs, constrs_ne := hne }
    else none
  else none

/-- Translate a group under provisional or aligned names, using the same member translation. -/
private def blockWithBinders (policy : Policy) (g : Env.Group env)
    (names : Array (List TyIdentifier)) : Option (MutualDatatype Unit) :=
  g.members.toList.zipIdx.mapM fun (d, i) =>
    datatypeWithBinders policy (names[i]?.getD []) d

/-- Binders named by member and parameter, before alignment. -/
private def provisionalBinders (g : Env.Group env) : Array (List TyIdentifier) :=
  g.members.zipIdx.map fun (d, i) => d.decl.paramNames.map fun p => datatypeBinder i ++ "." ++ p

/-- Equalities imposed by recursive applications: a member's formal against the variable
it is applied to; `formals` indexes the block's members' binders by Core name. -/
private def binderEquations (formals : Std.HashMap String (List TyIdentifier)) :
    LMonoTy → List (String × String)
  | .ftvar _ | .bitvec _ => []
  | .tcons n args =>
    let here := ((formals.getD n []).zip args).filterMap fun (formal, arg) =>
      match arg with
      | .ftvar actual => some (formal, actual)
      | _ => none
    here ++ args.attach.flatMap fun ⟨a, _⟩ => binderEquations formals a
termination_by ty => sizeOf ty
decreasing_by
  simp_wf
  have := List.sizeOf_lt_of_mem ‹_ ∈ _›
  omega

/-- Shared binders for a provisional block, by solving the equalities its recursive
applications impose: each class of identified parameters is one Core binder, numbered by first
appearance. `none` if a member identifies two parameters or fails to bind every class,
including those unused by fields: Core requires the same parameter set in every member. -/
private def alignBinders (block : MutualDatatype Unit) : Option (List (List TyIdentifier)) := do
  let vars := block.flatMap (·.typeArgs)
  let fields := block.flatMap fun d => d.constrs.flatMap fun c => c.args.map Prod.snd
  let formals : Std.HashMap String (List TyIdentifier) :=
    .ofList (block.map fun d => (d.name, d.typeArgs))
  let mut representative : Std.HashMap String String := .ofList (vars.map fun v => (v, v))
  for (a, b) in fields.flatMap (binderEquations formals) do
    if let (some ra, some rb) := (representative[a]?, representative[b]?) then
      representative := representative.map fun _ r => if r == rb then ra else r
  let index := vars.foldl (init := (∅ : Std.HashMap String Nat)) fun index v =>
    let r := representative.getD v v
    if index.contains r then index else index.insert r index.size
  let binder := fun v => (representative[v]?.bind (index[·]?)).map datatypeBinder
  let members := block.map fun d => d.typeArgs.filterMap binder
  let memberSets := members.map Std.HashSet.ofList
  if (members.zip memberSets).any (fun (vs, set) => set.size != vs.length) then none
  -- Each member set is a subset of the indexed classes, so cardinality decides coverage.
  if memberSets.any (fun set => set.size != index.size) then none
  return members

/-- Derive binder names from the translated recursive references; `none` when the members
cannot share binders. -/
private def datatypeBinders (policy : Policy) (g : Env.Group env) :
    Option (Array (List TyIdentifier)) :=
  (blockWithBinders policy g (provisionalBinders g) >>= alignBinders).map (·.toArray)

/-- The Core block of a group, if its members share binders and every member has a Core form. -/
def block (policy : Policy) (g : Env.Group env) : Option (MutualDatatype Unit) :=
  datatypeBinders policy g >>= blockWithBinders policy g

/-- A successful `mapM` in `Option` has one result per element, the image of the element at the
same index. -/
private theorem mapM_eq_some {β γ : Type} {f : β → Option γ} :
    ∀ {xs : List β} {ys : List γ}, xs.mapM f = some ys →
      ys.length = xs.length ∧ ∀ i : Nat, ys[i]? = xs[i]?.bind f
  | [], _, h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ => rfl⟩
  | _ :: xs, _, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨hl, hi⟩ := mapM_eq_some hys
    refine ⟨by simp only [List.length_cons, hl], fun i => ?_⟩
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.bind_some, hy]
    | succ i => simpa only [List.getElem?_cons_succ] using hi i

/-- A member's Core datatype binds the names it was translated under, one per parameter. -/
private theorem datatypeWithBinders_eq_some {policy : Policy} {names : List TyIdentifier}
    {d : Env.Datatype env} {out : LDatatype Unit}
    (h : datatypeWithBinders policy names d = some out) :
    out.typeArgs = names ∧ TyParam.kinds d.decl.params = Array.replicate names.length .type := by
  simp only [datatypeWithBinders] at h
  split at h <;> (try contradiction)
  split at h <;> (try contradiction)
  cases Option.some.inj h
  exact ⟨rfl, ‹_›⟩

/-- A block has one Core datatype per member of the group. -/
theorem length_block {policy : Policy} {g : Env.Group env} {b : MutualDatatype Unit}
    (hb : block policy g = some b) : b.length = g.members.size := by
  simp only [block, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
  obtain ⟨_, -, hb⟩ := hb
  exact ((mapM_eq_some hb).1).trans (by simp only [List.length_zipIdx, Array.length_toList])

/-- Each Core datatype of a block is the group's member at the same index, translated under
the block's binders for it. -/
private theorem datatypeWithBinders_block {policy : Policy} {g : Env.Group env}
    {b : MutualDatatype Unit} (hb : block policy g = some b) (i : Nat) (hi : i < g.members.size) :
    datatypeWithBinders policy (b[i]'(length_block hb ▸ hi)).typeArgs g.members[i] =
      some (b[i]'(length_block hb ▸ hi)) := by
  have hi' : i < b.length := length_block hb ▸ hi
  simp only [block, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
  obtain ⟨names, -, hb⟩ := hb
  have h := (mapM_eq_some hb).2 i
  simp only [List.getElem?_zipIdx, Array.getElem?_toList, Array.getElem?_eq_getElem hi,
    Option.map_some, Option.bind_some, List.getElem?_eq_getElem hi', Nat.zero_add] at h
  rw [← (datatypeWithBinders_eq_some h.symm).1] at h
  exact h.symm

/-- The block's binders for a member are one Core type variable per parameter of the member. -/
theorem kinds_block {policy : Policy} {g : Env.Group env} {b : MutualDatatype Unit}
    (hb : block policy g = some b) (i : Nat) (hi : i < g.members.size) :
    TyParam.kinds g.members[i].decl.params =
      Array.replicate (b[i]'(length_block hb ▸ hi)).typeArgs.length .type :=
  (datatypeWithBinders_eq_some (datatypeWithBinders_block hb i hi)).2

/-- Each Core datatype of a block has the constructors of the group's member at the same index,
named by `constructorName` and `testerName`, each field named by `fieldName` and typed by its
translation under the block's binders for the member (`memberScope`). -/
theorem constrs_block {policy : Policy} {g : Env.Group env} {b : MutualDatatype Unit}
    (hb : block policy g = some b) (i : Nat) (hi : i < g.members.size) :
    (b[i]'(length_block hb ▸ hi)).constrs = g.members[i].ctors.toList.map fun c => {
      name := ⟨constructorName c.name, ()⟩
      args := c.args.toList.map fun p => (⟨fieldName c.name p.name, ()⟩,
        (translateType policy (fun _ _ h => h)
          (memberScope policy (b[i]'(length_block hb ▸ hi)).typeArgs g.members[i]
            (kinds_block hb i hi)) p.type).val)
      testerName := testerName c.name } := by
  have h := datatypeWithBinders_block hb i hi
  simp only [datatypeWithBinders] at h
  split at h <;> (try contradiction)
  split at h <;> (try contradiction)
  exact (congrArg LDatatype.constrs (Option.some.inj h)).symm

end

/-! ### Declarations -/

/-- Well-formedness of type declarations, in order, from a context to the one Core's declaration
rules build from them: each declaration extends the context as Core's own typing rules do,
generated functions included. Datatype blocks are certified by Core's executable checker.
Decided at run time by `check`, not by kernel reduction: the Core context is a hash map. -/
inductive DeclarationsWF :
    LContext Core.CoreLParams → List Core.TypeDecl → LContext Core.CoreLParams → Prop where
  | nil (C) : DeclarationsWF C [] C
  | con {C C₁ C' ds} (d : TypeConstructor)
      (ok : C.addKnownTypeWithError { name := d.name, metadata := d.numargs } default = .ok C₁)
      (rest : DeclarationsWF C₁ ds C') :
      DeclarationsWF C (.con d :: ds) C'
  | data {C C₁ C' ds} (block : MutualDatatype Unit)
      (ok : C.addMutualBlock block = .ok C₁)
      (rest : DeclarationsWF C₁ ds C') :
      DeclarationsWF C (.data block :: ds) C'

/-- The Core declarations of a list of entries, in order. -/
def compileEntries {α : Type} {env : Env α} (policy : Policy) :
    List (Env.Entry env) → List Core.TypeDecl
  | [] => []
  | .type t :: es =>
    (match representation policy t with
      | .nominal => [.con (constructor t)]
      | .concrete _ => []) ++ compileEntries policy es
  | .data g :: es => (CoreTypes.block policy g).toList.map .data ++ compileEntries policy es
  | .insn _ :: es => compileEntries policy es

/-- The Core declarations an environment's types need under a policy, in declaration order. -/
def compile {α : Type} (env : Env α) (policy : Policy) : List Core.TypeDecl :=
  compileEntries policy env.entries.toList

/-- The entries are supported by the policy in a context: each declaration is well formed in
the context the previous ones extend it to, and the final context is the one Core's declaration
rules build for these declarations (datatypes, known types and generated functions); registering
the names as program identifiers is the embedding program's step.  `check` decides it at run
time; like `DeclarationsWF`, it is not kernel-reducible, the Core context being a hash map. -/
inductive Supported {α : Type} {env : Env α} (policy : Policy) :
    LContext Core.CoreLParams → List (Env.Entry env) → LContext Core.CoreLParams → Prop where
  | nil {C} : Supported policy C [] C
  | nominal {C C₁ C' es arity} (t : TypeRef env arity)
      (h : representation policy t = .nominal)
      (kinds : ∀ k ∈ t.kinds, k = .type)
      (ok : C.addKnownTypeWithError
        { name := (constructor t).name, metadata := (constructor t).numargs } default = .ok C₁)
      (rest : Supported policy C₁ es C') :
      Supported policy C (.type t :: es) C'
  | concrete {C C' es arity} (t : TypeRef env arity) (c : Concrete t.kinds)
      (h : representation policy t = .concrete c)
      (known : ∀ p ∈ c.uses, C.knownTypes[p.1]? = some p.2)
      (rest : Supported policy C es C') :
      Supported policy C (.type t :: es) C'
  | data {C C₁ C' es} (g : Env.Group env) (block : MutualDatatype Unit)
      (hb : CoreTypes.block policy g = some block)
      (ok : C.addMutualBlock block = .ok C₁)
      (rest : Supported policy C₁ es C') :
      Supported policy C (.data g :: es) C'
  | insn {C C' es isig} (r : InsnRef env isig) (rest : Supported policy C es C') :
      Supported policy C (.insn r :: es) C'

/-- When the policy supports a list of entries in a context, each declaration extending the
context as Core's declaration rules would (`check` decides this), the declarations
`compileEntries` emits for them are well formed in that same context and build the same final
context. -/
theorem Supported.wf {α : Type} {env : Env α} {policy : Policy} {C C' : LContext Core.CoreLParams}
    {es : List (Env.Entry env)} (h : Supported policy C es C') :
    DeclarationsWF C (compileEntries policy es) C' := by
  induction h with
  | nil => exact .nil _
  | nominal t h _ ok _ ih =>
    simp only [compileEntries, h, List.singleton_append]
    exact .con _ ok ih
  | concrete t c h _ _ ih =>
    simpa only [compileEntries, h, List.nil_append] using ih
  | data g block hb ok _ ih =>
    simp only [compileEntries, hb, Option.toList_some, List.map_cons, List.map_nil,
      List.singleton_append]
    exact .data block ok ih
  | insn r _ ih => simpa only [compileEntries] using ih

/-- Why a group has no Core block: a member without constructors, a member with a parameter
that is not a type parameter, or members that cannot share binders. -/
private def groupRejection {α : Type} {env : Env α} (g : Env.Group env) : Error :=
  match g.members.toList.find? (fun d => d.ctors.size == 0) with
  | some d => .emptyDatatype d.decl.name
  | none =>
    match g.members.toList.find? (fun d => d.decl.params.any (·.type.kind == .list)) with
    | some d => .listParameter d.decl.name
    | none => .unsharedBinders g.first.decl.name

/-- Decide `Supported`, with the final context the one Core's declaration rules build (datatypes,
known types and generated functions; the embedding program registers the names as program
identifiers), or report the first declaration without a well-formed Core form. A group Core's
executable checker refuses is reported with its error.
The cost grows quickly with the number of datatypes, almost all of it in Core's block checker,
`addMutualBlock`; the group alignment itself rescans a group's binders once per recursive
reference, quadratic in a group's size but small beside Core. -/
def check {α : Type} {env : Env α} (policy : Policy) :
    (C : LContext Core.CoreLParams) → (es : List (Env.Entry env)) →
    Except Error { C' : LContext Core.CoreLParams // Supported policy C es C' }
  | C, [] => pure ⟨C, .nil⟩
  | C, .type t :: es =>
    match h : representation policy t with
    | .nominal => do
      if hk : ∀ k ∈ t.kinds, k = .type then
        match ok : C.addKnownTypeWithError
            { name := (constructor t).name, metadata := (constructor t).numargs } default with
        | .ok C₁ =>
          let ⟨C', rest⟩ ← check policy C₁ es
          pure ⟨C', .nominal t h hk ok rest⟩
        | .error _ => throw (.duplicateType t.name)
      else throw (.listParameter t.name)
    | .concrete c => do
      match hu : c.uses.find? (fun p => C.knownTypes[p.1]? != some p.2) with
      | some p => throw (.unknownType t.name p.1 p.2)
      | none =>
        let ⟨C', rest⟩ ← check policy C es
        pure ⟨C', .concrete t c h (fun p hp => by simpa using List.find?_eq_none.mp hu p hp) rest⟩
  | C, .data g :: es => do
    match hb : CoreTypes.block policy g with
    | none => throw (groupRejection g)
    | some block =>
      match ok : C.addMutualBlock block with
      | .ok C₁ =>
        let ⟨C', rest⟩ ← check policy C₁ es
        pure ⟨C', .data g block hb ok rest⟩
      | .error e => throw (.coreDatatype g.first.decl.name (toString e))
  | C, .insn r :: es => do
    let ⟨C', rest⟩ ← check policy C es
    pure ⟨C', .insn r rest⟩

/-- `check` over an environment's entries. -/
def checkEnv {α : Type} (env : Env α) (policy : Policy) (C : LContext Core.CoreLParams) :
    Except Error { C' : LContext Core.CoreLParams // Supported policy C env.entries.toList C' } :=
  check policy C env.entries.toList

end

end Strata.Dyn.CoreTypes
