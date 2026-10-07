/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all StrataMantle.Util.Array
import StrataMantle.Env.WF
public import StrataMantle.Env.Data
public import StrataMantle.Env.TypeExprRaw
import StrataMantle.Env.DataProps
import StrataMantle.Env.TypeExprRawProps

set_option autoImplicit false

/-!
# Environments, checked

An environment `Env α` pairs an `Env.Raw α` with its well-formedness proof, so every
value of this type is an environment in which each type reference resolves to a
declaration that appears earlier.  The operations below are the only way to build one:

* `empty`: the environment with no declarations.
* `addType`, `addInsn`: extend a signature by one type or instruction declaration.
* `addTypes`, `addData`, `addInsns`: extend it by a batch of declarations at once.
* `addType?`, `addInsns?`: the same extensions, deciding their obligations with the
  checker and failing instead of asking for proofs.

Each declaration is annotated with a value of an arbitrary type `α`, which well-formedness
does not read.
-/

open Strata (IndexMap)

namespace Strata.Mantle

variable {α : Type}

/-- A well-formed environment whose declarations are annotated with `α`.  The fields are
private.  `empty` and the `add*` operations are the only way to build one. -/
public structure Env (α : Type) where
  private mk ::
  private raw : Env.Raw α
  private wf : raw.WF

namespace Env

public protected def mem (env : Env α) (name : Name) : Bool := name ∈ env.raw

public instance : Membership Name (Env α) where
  mem s n := s.mem n

public instance (n : Name) (s : Env α) : Decidable (n ∈ s) :=
  inferInstanceAs (Decidable (_ = _))

theorem mem_raw_of_mem {s : Env α} {n : Name} (p : n ∈ s) : n ∈ s.raw :=
  of_decide_eq_true p

theorem not_mem_raw_of_not_mem {s : Env α} {n : Name} (p : n ∉ s) : n ∉ s.raw :=
  fun h => p (decide_eq_true h)

/-- The declaration data named `name`, if any. -/
protected def rawGet? (env : Env α) (name : Name) : Option (Decl.Raw α) := env.raw[name]?

/-- The declaration data named `name`, given that there is one. -/
protected def rawGet (env : Env α) (name : Name) (p : name ∈ env) : Decl.Raw α :=
  env.raw[name]'(mem_raw_of_mem p)

/-- `name` is declared in `s` as `d`. -/
def Resolves (s : Env α) (name : Name) (d : Decl.Raw α) : Prop := s.rawGet? name = some d

theorem resolves_iff_rawGet? {s : Env α} {n : Name} {d : Decl.Raw α} :
    s.Resolves n d ↔ s.rawGet? n = some d := Iff.rfl

/-- A name resolves to at most one declaration. -/
theorem Resolves.unique {s : Env α} {n : Name} {d e : Decl.Raw α}
    (hd : s.Resolves n d) (he : s.Resolves n e) : d = e := by
  rw [resolves_iff_rawGet?] at hd he
  exact Option.some.inj (hd.symm.trans he)

/-- `rawGet?` is the lookup of the underlying `Env.Raw`. -/
theorem rawGet?_eq_raw (s : Env α) (n : Name) : s.rawGet? n = s.raw[n]? := rfl

theorem mem_iff_mem_raw {s : Env α} {n : Name} : n ∈ s ↔ n ∈ s.raw :=
  ⟨mem_raw_of_mem, decide_eq_true⟩

/-- `name` resolves to a type declaration of arity `arity` declared before position
`i`.  A declaration at position `i` may refer only to such types. -/
public def RefBefore (s : Env α) (i : Nat) (name : Name) (arity : Nat) : Prop :=
  s.raw.RefBefore i name arity

/-- Widening the position bound keeps a reference valid. -/
public theorem RefBefore.mono {s : Env α} {i j : Nat} {name : Name} {arity : Nat} (h : i ≤ j)
    (hr : s.RefBefore i name arity) : s.RefBefore j name arity :=
  Env.Raw.RefBefore.mono h hr

/-- The number of declarations.  The next declaration added takes position `size`. -/
public def size (s : Env α) : Nat := s.raw.decls.keys.size

/-- The type declarations, as a view. -/
def types (s : Env α) : Raw.SubEnv α (TypeDecl α) := s.raw.types

/-- The instruction declarations, as a view. -/
def insns (s : Env α) : Raw.SubEnv α (InsnDecl.Raw α) := s.raw.insns

theorem types_eq (s : Env α) : s.types = s.raw.types := rfl

theorem insns_eq (s : Env α) : s.insns = s.raw.insns := rfl

/-! ### The empty environment -/

/-- The environment with no declarations. -/
public def empty : Env α := ⟨Raw.empty, Raw.wf_empty⟩

public instance : EmptyCollection (Env α) := ⟨empty⟩

public instance : Inhabited (Env α) := ⟨empty⟩

/-- Normalises `∅` to `empty`. -/
@[simp] public theorem emptyCollection_eq : (∅ : Env α) = empty := rfl

theorem raw_empty : (empty : Env α).raw = Raw.empty := rfl

@[simp] public theorem size_empty : (Env.empty (α := α)).size = 0 := by
  simp [size, raw_empty, Raw.keys_empty]

@[simp, grind .] public theorem not_mem_empty (n : Name) : n ∉ (Env.empty (α := α)) := by
  simp [mem_iff_mem_raw, raw_empty]

theorem rawGet?_empty (n : Name) : (Env.empty (α := α)).rawGet? n = none := by
  simp [rawGet?_eq_raw, raw_empty, Raw.get?_empty]

theorem not_resolves_empty (n : Name) (d : Decl.Raw α) :
    ¬ (Env.empty (α := α)).Resolves n d := by
  rw [resolves_iff_rawGet?, rawGet?_empty]
  simp

theorem mem_of_resolves {s : Env α} {n : Name} {d : Decl.Raw α}
    (h : s.Resolves n d) : n ∈ s := by
  rw [resolves_iff_rawGet?] at h
  rw [rawGet?_eq_raw] at h
  exact mem_iff_mem_raw.mpr (IndexMap.mem_of_getElem?_eq_some h)

/-! ### Extending an environment -/

/-- Add a type declaration, whose parameters are named distinctly. -/
public def addType (s : Env α) (d : TypeDecl α) (fresh : d.name ∉ s)
    (distinct : d.paramNames.Nodup := by decide) : Env α :=
  ⟨s.raw.append (.type d) (not_mem_raw_of_not_mem fresh),
    s.wf.append (d := .type d) (not_mem_raw_of_not_mem fresh)
      (Decl.Raw.wf_type_iff.mpr distinct)⟩

section
variable (s : Env α) (d : TypeDecl α) (fresh : d.name ∉ s) {distinct : d.paramNames.Nodup}

/-- `addType` appends the declaration. -/
theorem raw_addType :
    (s.addType d fresh distinct).raw = s.raw.append (.type d) (not_mem_raw_of_not_mem fresh) :=
  rfl

/-- `addType` adds one declaration. -/
@[simp] public theorem size_addType : (s.addType d fresh distinct).size = s.size + 1 := by
  simp [size, raw_addType, Raw.keys_append]

/-- What a name resolves to after `addType`. -/
theorem rawGet?_addType (n : Name) :
    (s.addType d fresh distinct).rawGet? n =
      if d.name == n then some (.type d) else s.rawGet? n := by
  simp [rawGet?_eq_raw, raw_addType, Raw.get?_append]

/-- The added type resolves under its own name. -/
theorem resolves_addType_self : (s.addType d fresh distinct).Resolves d.name (.type d) := by
  rw [resolves_iff_rawGet?, rawGet?_addType]
  simp

end

/-- Adding a declaration leaves what every other name resolves to alone. -/
theorem resolves_addType_of_ne {s : Env α} {d : TypeDecl α} {fresh : d.name ∉ s}
    {distinct : d.paramNames.Nodup} {n : Name} {e : Decl.Raw α} (hne : d.name ≠ n) :
    (s.addType d fresh distinct).Resolves n e ↔ s.Resolves n e := by
  rw [resolves_iff_rawGet?, resolves_iff_rawGet?, rawGet?_addType, if_neg (by simpa using hne)]

@[simp, grind =] public theorem mem_addType {s : Env α} {d : TypeDecl α} {fresh : d.name ∉ s}
    {distinct : d.paramNames.Nodup} {n : Name} :
    n ∈ s.addType d fresh distinct ↔ d.name = n ∨ n ∈ s := by
  simp [mem_iff_mem_raw, raw_addType]

/-! ### Extending by evaluation -/

-- Module-internal: `add?`, `ofArray?` and `addData?` accept unchecked alias declarations.

/-- Whether `d` is admissible as the next declaration of `s`. -/
def check (s : Env α) (d : Decl.Raw α) : Bool := Raw.checkDecl s.raw s.size d.name d

/-- Add a declaration, or `none` if its name is taken or it fails `check`. -/
def add? (s : Env α) (d : Decl.Raw α) : Option (Env α) :=
  if fresh : d.name ∈ s then
    none
  else if h : s.check d = true then
    some ⟨s.raw.append d (not_mem_raw_of_not_mem fresh),
      s.wf.appendChecked (d := d) (not_mem_raw_of_not_mem fresh) h⟩
  else
    none

theorem add?_eq_none_iff {s : Env α} {d : Decl.Raw α} :
    s.add? d = none ↔ d.name ∈ s ∨ s.check d = false := by
  unfold add?
  split
  · simp_all
  · split <;> simp_all

theorem rawGet?_of_add?_eq_some {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s')
    (n : Name) : s'.rawGet? n = if d.name == n then some d else s.rawGet? n := by
  unfold add? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain rfl : s' = _ := Option.some.inj h.symm
      simp [rawGet?_eq_raw, Raw.get?_append]
    · exact absurd h (by simp)

theorem resolves_of_add?_eq_some {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s') :
    s'.Resolves d.name d := by
  rw [resolves_iff_rawGet?, rawGet?_of_add?_eq_some h]
  simp

theorem resolves_add?_of_ne {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s')
    {n : Name} {e : Decl.Raw α} (hne : d.name ≠ n) : s'.Resolves n e ↔ s.Resolves n e := by
  rw [resolves_iff_rawGet?, resolves_iff_rawGet?, rawGet?_of_add?_eq_some h,
    if_neg (by simpa using hne)]

theorem size_of_add?_eq_some {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s') :
    s'.size = s.size + 1 := by
  unfold add? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain rfl : s' = _ := Option.some.inj h.symm
      simp [size, Raw.keys_append]
    · exact absurd h (by simp)

/-- What a successful `add?` declares: the name it added, and whatever was already there. -/
theorem mem_add?_eq_some {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s')
    {n : Name} : n ∈ s' ↔ n = d.name ∨ n ∈ s := by
  unfold add? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain rfl : s' = _ := Option.some.inj h.symm
      rw [mem_iff_mem_raw, Raw.mem_append, mem_iff_mem_raw, eq_comm]
    · exact absurd h (by simp)

theorem mem_of_add?_eq_some {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s') :
    d.name ∈ s' := by
  unfold add? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain rfl : s' = _ := Option.some.inj h.symm
      exact mem_iff_mem_raw.mpr (Raw.mem_append.mpr (Or.inl rfl))
    · exact absurd h (by simp)

/-! ### Building from an array -/

/-- Build an environment from an array of declarations, in order.  `none` if two declarations
share a name, or a declaration is not well formed against those before it. -/
def ofArray? : Array (Decl.Raw α) → Option (Env α)
  | ⟨l⟩ =>
    if p : Raw.DistinctDecls ⟨l⟩ then
      if h : Raw.checkFrom (Raw.ofAscArray ⟨l⟩ p) 0 l = true then
        some ⟨Raw.ofAscArray ⟨l⟩ p, Raw.wf_ofAscArray ⟨l⟩ p h⟩
      else
        none
    else
      none

theorem vals_of_ofArray?_eq_some {ds : Array (Decl.Raw α)} {s : Env α}
    (h : ofArray? ds = some s) :
    s.raw.decls.vals = ds := by
  obtain ⟨l⟩ := ds
  rw [ofArray?] at h
  split at h
  · split at h
    · obtain rfl : s = _ := Option.some.inj h.symm
      exact Raw.vals_ofAscArray _ _
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem size_of_ofArray?_eq_some {ds : Array (Decl.Raw α)} {s : Env α}
    (h : ofArray? ds = some s) : s.size = ds.size := by
  have hv := vals_of_ofArray?_eq_some h
  simp [size, s.raw.declsWF, hv]

/-- The `i`-th declaration is stored under its own name. -/
theorem rawGet?_of_ofArray?_eq_some {ds : Array (Decl.Raw α)} {s : Env α}
    (h : ofArray? ds = some s) (i : Nat) (hi : i < ds.size) : s.rawGet? (ds[i]'hi).name = some (ds[i]'hi) := by
  have hv := vals_of_ofArray?_eq_some h
  have hlt : i < s.raw.decls.vals.size := by rw [hv]; exact hi
  have heq : s.raw.decls.vals[i]'hlt = ds[i]'hi :=
    Option.some.inj (by rw [← Array.getElem?_eq_getElem hlt, hv, Array.getElem?_eq_getElem hi])
  have hget := s.raw.getElem?_getElem_vals i hlt
  rwa [heq] at hget

/-- The `i`-th declaration of the array resolves under its own name. -/
theorem resolves_of_ofArray?_eq_some {ds : Array (Decl.Raw α)} {s : Env α}
    (h : ofArray? ds = some s) (i : Nat) (hi : i < ds.size) :
    s.Resolves (ds[i]'hi).name (ds[i]'hi) :=
  rawGet?_of_ofArray?_eq_some h i hi

/-- A type that `s` resolves is a valid reference before the end of `s`. -/
theorem refBefore_of_resolves {s : Env α} {n : Name} {d : TypeDecl α}
    (h : s.raw.typeOf? n = some d) : s.RefBefore s.size n d.arity := by
  have hm : n ∈ s.raw.decls := by
    unfold Env.Raw.typeOf? at h
    cases hx : s.raw.decls[n]? with
    | none => rw [hx] at h; simp at h
    | some e => exact IndexMap.mem_of_getElem?_eq_some hx
  have hs : (IndexMap.idxOf? s.raw.decls n).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]
    simpa using hm
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
  have hjlt : j < s.size :=
    (Array.getElem?_eq_some_iff.mp (IndexMap.getElem?_keys_of_idxOf?_eq_some hj)).1
  exact Raw.refBefore_iff.mpr ⟨j, d, hj, hjlt, h, rfl⟩

/-- A stored declaration is named by the key it is stored under. -/
theorem name_of_rawGet? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.rawGet? n = some d) :
    d.name = n := by
  rw [rawGet?_eq_raw] at h
  have h' : s.raw.decls[n]? = some d := h
  have hmem : n ∈ s.raw.decls := IndexMap.mem_of_getElem?_eq_some h'
  rw [IndexMap.getElem?_eq_some_getElem hmem] at h'
  rw [← Option.some.inj h']
  exact Raw.name_getElem s.raw hmem

theorem isSome_rawGet? {s : Env α} {n : Name} : (s.rawGet? n).isSome ↔ n ∈ s := by
  rw [rawGet?_eq_raw, mem_iff_mem_raw]
  show (s.raw.decls[n]?).isSome = true ↔ n ∈ s.raw.decls
  rw [IndexMap.isSome_getElem?_eq_contains]
  simp

theorem rawGet?_eq_none_iff {s : Env α} {n : Name} : s.rawGet? n = none ↔ n ∉ s := by
  rw [rawGet?_eq_raw, ← Option.not_isSome_iff_eq_none, mem_iff_mem_raw]
  show ¬ (s.raw.decls[n]?).isSome = true ↔ ¬ n ∈ s.raw.decls
  rw [IndexMap.isSome_getElem?_eq_contains]
  simp

/-- Every declaration an environment stores is well formed against the whole environment. -/
theorem declWF_of_rawGet? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.rawGet? n = some d) :
    Decl.Raw.WF (s.RefBefore s.size) d := by
  have h' : s.raw[n]? = some d := by rw [rawGet?_eq_raw] at h; exact h
  have hs : (IndexMap.idxOf? s.raw.decls n).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]
    simpa using IndexMap.mem_of_getElem?_eq_some h'
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
  have hkey : s.raw.decls.keys[i]? = some n := IndexMap.getElem?_keys_of_idxOf?_eq_some hi
  have hlt : i < s.size := (Array.getElem?_eq_some_iff.mp hkey).1
  exact (s.wf.declWF i n d hkey h').mono fun _ _ hr =>
    Raw.RefBefore.mono (Nat.le_of_lt hlt) hr

/-- A stored declaration sits at a position whose key is the name it was looked up
under. -/
theorem idx_of_rawGet? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.rawGet? n = some d) :
    ∃ i, i < s.size ∧ s.raw.decls.keys[i]? = some n := by
  have h' : s.raw[n]? = some d := by rw [rawGet?_eq_raw] at h; exact h
  have hs : (IndexMap.idxOf? s.raw.decls n).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]
    simpa using IndexMap.mem_of_getElem?_eq_some h'
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
  have hkey : s.raw.decls.keys[i]? = some n := IndexMap.getElem?_keys_of_idxOf?_eq_some hi
  exact ⟨i, (Array.getElem?_eq_some_iff.mp hkey).1, hkey⟩

/-- A stored declaration passes `checkAlias` at its own position. -/
theorem checkAlias_of_rawGet? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.rawGet? n = some d) :
    ∃ i, s.raw.checkAlias i n d = true := by
  obtain ⟨i, -, hkey⟩ := idx_of_rawGet? h
  exact ⟨i, s.wf.aliasWF i n d hkey h⟩

/-- A name stored as a member alias denotes a type. -/
theorem isSome_typeOf?_of_dataRest {s : Env α} {n mn hd : Name} {i : Nat}
    (h : s.rawGet? n = some (.dataRest mn hd i)) : (s.raw.typeOf? n).isSome := by
  obtain ⟨j, hj⟩ := checkAlias_of_rawGet? h
  exact Raw.isSome_typeOf?_of_checkAlias h hj

/-! ### Extension

`s₁ ⊆ s₂` when `s₂` has the declarations of `s₁` at the same positions, and possibly more
after them.  A name that resolves in `s₁` resolves the same way in `s₂`. -/

/-- `Prefix s₁ s₂` holds when the declarations of `s₁` are a prefix of those of `s₂`.
It is written `s₁ ⊆ s₂`. -/
public def Prefix (s₁ s₂ : Env α) : Prop :=
  s₁.raw.decls.vals.toList <+: s₂.raw.decls.vals.toList

public instance : HasSubset (Env α) := ⟨Prefix⟩

theorem subset_iff {s₁ s₂ : Env α} :
    s₁ ⊆ s₂ ↔ s₁.raw.decls.vals.toList <+: s₂.raw.decls.vals.toList := Iff.rfl

/-- The keys of `s₁` are a prefix of those of `s₂`. -/
theorem keys_prefix_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) :
    s₁.raw.decls.keys.toList <+: s₂.raw.decls.keys.toList := by
  rw [s₁.raw.declsWF, s₂.raw.declsWF, Array.toList_map, Array.toList_map]
  exact (subset_iff.mp h).map _

theorem size_eq_size_vals (s : Env α) : s.size = s.raw.decls.vals.size := by
  simp [size, s.raw.declsWF]

public theorem size_le_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) :
    s₁.size ≤ s₂.size := by
  rw [size_eq_size_vals, size_eq_size_vals]
  simpa using (subset_iff.mp h).length_le

/-- Positions below `s₁`'s size hold the same declaration in both. -/
theorem getElem?_vals_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {i : Nat}
    (hi : i < s₁.raw.decls.vals.size) :
    s₂.raw.decls.vals[i]? = s₁.raw.decls.vals[i]? := by
  have hi2 : i < s₂.raw.decls.vals.size :=
    Nat.lt_of_lt_of_le hi (by simpa using (subset_iff.mp h).length_le)
  rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi2]
  have hg := ((subset_iff.mp h).getElem (i := i) (by simpa using hi)).symm
  rw [Array.getElem_toList] at hg
  exact congrArg some hg

theorem getElem?_keys_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {i : Nat}
    (hi : i < s₁.raw.decls.keys.size) :
    s₂.raw.decls.keys[i]? = s₁.raw.decls.keys[i]? := by
  have hp := keys_prefix_of_subset h
  have hi2 : i < s₂.raw.decls.keys.size := Nat.lt_of_lt_of_le hi (by simpa using hp.length_le)
  rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hi2]
  have hg := (hp.getElem (i := i) (by simpa using hi)).symm
  rw [Array.getElem_toList] at hg
  exact congrArg some hg

/-! #### Transfer -/

/-- A name keeps its position in an extension. -/
theorem idxOf?_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} {j : Nat}
    (hj : IndexMap.idxOf? s₁.raw.decls n = some j) :
    IndexMap.idxOf? s₂.raw.decls n = some j := by
  have hk1 : s₁.raw.decls.keys[j]? = some n := IndexMap.getElem?_keys_of_idxOf?_eq_some hj
  obtain ⟨hj2, hkey⟩ :=
    Array.getElem?_eq_some_iff.mp ((getElem?_keys_of_subset h (Array.getElem?_eq_some_iff.mp hk1).1).trans hk1)
  have := IndexMap.idxOf?_getElem_keys s₂.raw.decls j hj2
  rwa [hkey] at this

/-- A name that resolves in a prefix resolves the same way in the extension. -/
theorem rawGet?_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} {d : Decl.Raw α}
    (hd : s₁.rawGet? n = some d) : s₂.rawGet? n = some d := by
  have hmem : n ∈ s₁.raw.decls := IndexMap.mem_of_getElem?_eq_some hd
  have hs : (IndexMap.idxOf? s₁.raw.decls n).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]; simpa using hmem
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
  have hk1 : s₁.raw.decls.keys[j]? = some n := IndexMap.getElem?_keys_of_idxOf?_eq_some hj
  have hv1 : s₁.raw.decls.vals[j]? = some d := by
    -- the `Env` lookup is the `IndexMap` lookup; restate it there to use the bridge
    have hd' : s₁.raw.decls[n]? = some d := hd
    rw [IndexMap.getElem?_eq_bind_idxOf?, hj] at hd'
    simpa using hd'
  have hv2 : s₂.raw.decls.vals[j]? = some d :=
    (getElem?_vals_of_subset h (Array.getElem?_eq_some_iff.mp hv1).1).trans hv1
  obtain ⟨hj2, hkey⟩ :=
    Array.getElem?_eq_some_iff.mp ((getElem?_keys_of_subset h (Array.getElem?_eq_some_iff.mp hk1).1).trans hk1)
  have hget := IndexMap.getElem?_getElem_keys s₂.raw.decls j hj2
  rw [hkey] at hget
  show s₂.raw.decls[n]? = some d
  rw [hget]
  exact hv2

/-- What a prefix resolves, the extension resolves the same way. -/
theorem Resolves.mono {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} {d : Decl.Raw α}
    (hd : s₁.Resolves n d) : s₂.Resolves n d :=
  rawGet?_of_subset h hd

public theorem mem_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} (hn : n ∈ s₁) :
    n ∈ s₂ :=
  mem_of_resolves
    (rawGet?_of_subset h (IndexMap.getElem?_eq_some_getElem (mem_raw_of_mem hn)))

/-- What a name's type resolves to survives an extension. -/
theorem typeOf?_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} {t : TypeDecl α}
    (ht : s₁.raw.typeOf? n = some t) : s₂.raw.typeOf? n = some t := by
  have stable : ∀ {k : Name} {e : Decl.Raw α}, s₁.raw.decls[k]? = some e →
      s₂.raw.decls[k]? = some e := fun hk => rawGet?_of_subset h hk
  unfold Env.Raw.typeOf? at ht ⊢
  cases hx : s₁.raw.decls[n]? with
  | none => rw [hx] at ht; simp at ht
  | some e =>
    rw [hx] at ht
    rw [stable hx]
    cases e with
    | type tt => exact ht
    | dataHead g => exact ht
    | dataRest m hd i =>
      simp only [Option.bind_some, Env.Raw.typeOfDecl?] at ht ⊢
      cases hh : s₁.raw.decls[hd]? with
      | none => rw [hh] at ht; simp at ht
      | some eh => rw [hh] at ht; rw [stable hh]; exact ht
    | insn _ =>
      simp only [Option.bind_some, Env.Raw.typeOfDecl?] at ht
      exact absurd ht (by simp)

/-- A reference valid in a prefix is valid in the extension. -/
public theorem refBefore_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {i : Nat} {n : Name}
    {a : Nat}
    (hr : s₁.RefBefore i n a) : s₂.RefBefore i n a := by
  obtain ⟨j, t, hj, hji, hget, ha⟩ := Raw.refBefore_iff.mp hr
  exact Raw.refBefore_iff.mpr
    ⟨j, t, idxOf?_of_subset h hj, hji, typeOf?_of_subset h hget, ha⟩

/-! #### Order -/

@[refl] public theorem Prefix.refl (s : Env α) : s ⊆ s := List.prefix_refl _

public theorem Prefix.trans {s₁ s₂ s₃ : Env α} (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₃) :
    s₁ ⊆ s₃ :=
  List.IsPrefix.trans h₁ h₂

@[simp] public theorem empty_subset (s : Env α) : empty ⊆ s := by
  show _ <+: _
  simp [raw_empty]

/-- An environment is determined by its `raw` field. -/
theorem eq_of_raw_eq {s₁ s₂ : Env α} (h : s₁.raw = s₂.raw) : s₁ = s₂ := by
  cases s₁; cases s₂; subst h; rfl

public theorem subset_antisymm {s₁ s₂ : Env α} (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₁) :
    s₁ = s₂ := by
  have hv : s₁.raw.decls.vals = s₂.raw.decls.vals :=
    Array.ext' ((subset_iff.mp h₁).eq_of_length_le (subset_iff.mp h₂).length_le)
  have hk : s₁.raw.decls.keys = s₂.raw.decls.keys := by
    rw [s₁.raw.declsWF, s₂.raw.declsWF, hv]
  exact eq_of_raw_eq (Raw.eq_of_decls_eq (IndexMap.eq_of_keys_vals_eq hk hv))

/-! #### Extending an environment extends it -/

@[simp] public theorem subset_addType (s : Env α) (d : TypeDecl α) (fresh : d.name ∉ s)
    {distinct : d.paramNames.Nodup} : s ⊆ s.addType d fresh distinct := by
  show _ <+: _
  simp only [raw_addType, Raw.vals_append, Array.toList_push]
  exact List.prefix_append _ _

theorem subset_of_add?_eq_some {s s' : Env α} {d : Decl.Raw α}
    (h : s.add? d = some s') : s ⊆ s' := by
  unfold add? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain rfl : s' = _ := Option.some.inj h.symm
      show _ <+: _
      simp only [Raw.vals_append, Array.toList_push]
      exact List.prefix_append _ _
    · exact absurd h (by simp)

/-! ### Extending by a batch -/

/-- Append a batch whose result is well formed. -/
def appendBatch (s : Env α) : (ds : Array (Decl.Raw α)) → (fresh : s.raw.FreshList ds.toList) →
    (s.raw.appendList ds.toList fresh).WF → Env α
  | ⟨ds⟩, fresh, h => ⟨s.raw.appendList ds fresh, h⟩

section
variable {s : Env α} {ds : Array (Decl.Raw α)} {fresh : s.raw.FreshList ds.toList}
  {h : (s.raw.appendList ds.toList fresh).WF}

theorem raw_appendBatch : (s.appendBatch ds fresh h).raw = s.raw.appendList ds.toList fresh := by
  cases ds; rfl

/-- `appendBatch` appends the batch to the declarations. -/
theorem vals_appendBatch : (s.appendBatch ds fresh h).raw.decls.vals = s.raw.decls.vals ++ ds := by
  rw [raw_appendBatch, Raw.vals_appendList]

theorem size_appendBatch : (s.appendBatch ds fresh h).size = s.size + ds.size := by
  simp [size, raw_appendBatch, Raw.keys_appendList]

theorem subset_appendBatch : s ⊆ s.appendBatch ds fresh h := by
  show _ <+: _
  simp only [raw_appendBatch, Raw.vals_appendList, Array.toList_append]
  exact List.prefix_append _ _

theorem rawGet?_appendBatch (n : Name) :
    (s.appendBatch ds fresh h).rawGet? n = (s.rawGet? n).or (ds.find? (·.name == n)) := by
  rw [← Array.find?_toList, rawGet?, raw_appendBatch]
  exact Raw.get?_appendList _ fresh n

theorem resolves_appendBatch {j : Nat} {d : Decl.Raw α} (hd : ds[j]? = some d) :
    (s.appendBatch ds fresh h).Resolves d.name d := by
  rw [← Array.getElem?_toList] at hd
  rw [Resolves, rawGet?, raw_appendBatch]
  exact Raw.get?_appendList_of_getElem? hd

theorem mem_appendBatch {n : Name} :
    n ∈ s.appendBatch ds fresh h ↔ n ∈ s ∨ ∃ d ∈ ds, d.name = n := by
  rw [mem_iff_mem_raw, raw_appendBatch, Raw.mem_appendList, mem_iff_mem_raw]
  simp only [Array.mem_toList_iff]

end

/-! ### Adding types

* `FreshNames`: the freshness condition on a batch of names.
* `addTypes`: extend an environment by a batch of type declarations. -/

/-- The names are distinct and none is declared in `s`. -/
@[expose] public def FreshNames (s : Env α) (ns : Array Name) : Prop :=
  ns.toList.Nodup ∧ ∀ n ∈ ns, n ∉ s

@[simp, grind =] public theorem freshNames_iff {s : Env α} {ns : Array Name} :
    s.FreshNames ns ↔ ns.toList.Nodup ∧ ∀ n ∈ ns, n ∉ s := Iff.rfl

/-- Freshness against an environment whose names are all in `L`, as one Boolean check.  When
`ns` and `L` are literals, `decide` proves `h`.  The kernel does not unfold `Array.map`, so
`decide` fails on an `ns` written as one. -/
public theorem FreshNames.of_list {s : Env α} {ns : Array Name} (L : List Name)
    (hs : ∀ {n}, n ∈ s → n ∈ L)
    (h : ns.toList.Nodup ∧ ns.toList.all (fun n => decide (n ∉ L)) = true) :
    s.FreshNames ns :=
  ⟨h.1, fun n hn hm => by
    simpa [hs hm] using List.all_eq_true.mp h.2 n (Array.mem_toList_iff.mpr hn)⟩

theorem freshList_of_freshNames {s : Env α} {ds : Array (Decl.Raw α)}
    (h : s.FreshNames (ds.map (·.name))) : s.raw.FreshList ds.toList :=
  ⟨by simpa [List.Nodup, List.pairwise_map] using h.1, fun d hd =>
    not_mem_raw_of_not_mem (h.2 d.name (Array.mem_map_of_mem (Array.mem_toList_iff.mp hd)))⟩

/-- `ds` may be added to `s` as a batch of types: their names are distinct and none is
declared in `s`, and each names its parameters distinctly. -/
@[expose] public def FreshTypes (s : Env α) (ds : Array (TypeDecl α)) : Prop :=
  s.FreshNames (ds.map (·.name)) ∧ ∀ d ∈ ds.toList, d.paramNames.Nodup

/-- Add a batch of type declarations. -/
public def addTypes (s : Env α) (ds : Array (TypeDecl α)) (fresh : s.FreshTypes ds) : Env α :=
  s.appendBatch (ds.map .type) (freshList_of_freshNames (by rw [Array.map_map]; exact fresh.1))
    (s.wf.appendList _ _ (Raw.checkFrom_types _ _ _ fresh.2))

section
variable {s : Env α} {ds : Array (TypeDecl α)} {fresh : s.FreshTypes ds}

theorem raw_addTypes :
    (s.addTypes ds fresh).raw = s.raw.appendList (ds.map .type).toList
      (freshList_of_freshNames (by rw [Array.map_map]; exact fresh.1)) := raw_appendBatch

@[simp] public theorem size_addTypes : (s.addTypes ds fresh).size = s.size + ds.size := by
  simp [addTypes, size_appendBatch]

@[simp] public theorem subset_addTypes : s ⊆ s.addTypes ds fresh := subset_appendBatch

@[simp, grind =] public theorem mem_addTypes {n : Name} :
    n ∈ s.addTypes ds fresh ↔ n ∈ ds.map (·.name) ∨ n ∈ s := by
  rw [addTypes, mem_appendBatch]
  simp only [Array.mem_map]
  constructor
  · rintro (h | ⟨_, ⟨d, hd, rfl⟩, rfl⟩)
    · exact .inr h
    · exact .inl ⟨d, hd, rfl⟩
  · rintro (⟨d, hd, rfl⟩ | h)
    · exact .inr ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    · exact .inl h

theorem rawGet?_addTypes_of_getElem? {j : Nat} {d : TypeDecl α} (hd : ds[j]? = some d) :
    (s.addTypes ds fresh).rawGet? d.name = some (.type d) := by
  have : (ds.map Decl.Raw.type)[j]? = some (.type d) := by simp [hd]
  exact resolves_appendBatch this

end

end Env


/-! ## Refinement -/

/--
`t ⊑ s`: `s` refines `t`.

Every reference in `t` is a reference in `s`, possibly elaborated or expanded.  It is
currently defined as `t ⊆ s`, which means `t` is a prefix of `s`; that will be addressed as the
tools mature.
-/
public class RefinedBy (t s : Env α) : Prop where
  /-- `t`'s declarations are a prefix of `s`'s. -/
  subset : t ⊆ s

@[inherit_doc] scoped infix:50 " ⊑ " => RefinedBy

/-- `s ⊒ t`: `s` refines `t`, the same as `t ⊑ s`.  Input only; terms print with `⊑`. -/
scoped syntax:50 term:51 " ⊒ " term:51 : term
macro_rules | `($s ⊒ $t) => `(RefinedBy $t $s)

/-- Every environment refines itself. -/
public instance (priority := high) RefinedBy.refl {t : Env α} : t ⊑ t := ⟨Env.Prefix.refl _⟩

/-! ## The type language, checked

* `TypeRef`: a reference to a type declaration of an environment.
* `TypeExpr`: a type expression whose references all resolve in an environment. -/

/-- `name` is declared in `s` as a type of shape `d`.  This holds for primitive types and
datatypes alike. -/
public def Env.ResolvesType (s : Env α) (name : Name) (d : TypeDecl α) : Prop :=
  s.raw.typeOf? name = some d

/-- Where the constructor named `name` sits, if `name` is declared in `s` as the instruction
that is a datatype's constructor: which group, which datatype of it, and which constructor. -/
public def Env.ctorAddr? (s : Env α) (name : Name) : Option CtorAddr := s.raw.ctorAddr? name

/-- What a prefix resolves, the extension resolves the same way. -/
public theorem Env.ResolvesType.mono {s t : Env α} (h : s ⊆ t) {n : Name} {d : TypeDecl α}
    (hd : s.ResolvesType n d) : t.ResolvesType n d :=
  Env.typeOf?_of_subset h hd

@[simp] public theorem Env.resolvesType_addType_self (s : Env α) (d : TypeDecl α)
    (fresh : d.name ∉ s) {distinct : d.paramNames.Nodup} :
    (s.addType d fresh distinct).ResolvesType d.name d := by
  unfold Env.ResolvesType Env.Raw.typeOf?
  rw [show (s.addType d fresh distinct).raw.decls[d.name]? = some (.type d) from
    Env.resolves_iff_rawGet?.mp (Env.resolves_addType_self s d fresh)]
  rfl

/-- A reference to a type declaration of `env` taking `arity` arguments. -/
public structure TypeRef (env : Env α) (arity : Nat) where
  name : Name
  decl : TypeDecl α
  matchArity : decl.arity = arity
  resolves : env.ResolvesType name decl

/-- A type reference is valid before the end of the environment. -/
public theorem TypeRef.refBefore {env : Env α} {arity : Nat} (r : TypeRef env arity) :
    env.RefBefore env.size r.name arity := by
  obtain ⟨n, d, ha, hr⟩ := r
  cases ha
  exact Env.refBefore_of_resolves hr

/-! ## Payload types of a datatype group

A group's payloads are written against two environments:

* `s`, the environment the group extends.
* `t`, which is `s` with the group's members added as plain types by `Env.addTypes`.

The operations:

* `DataTy`: a payload type.
* `DataTy.ok`: whether a payload is admissible in a member.
* `Env.admissible`: whether constructor lists make a datatype group. -/

/-- A payload type of a datatype group that extends `s`, whose members are the new types of
`t`. -/
public inductive DataTy (s t : Env α) where
  /-- The member's parameter at this de Bruijn level. -/
  | var (level : Nat)
  /-- A type `s` already declares, which the group cannot be. -/
  | ext {arity : Nat} (r : TypeRef s arity) (args : Array (DataTy s t))
  /-- A type of `t`, which may be one of the group's own members. -/
  | ref {arity : Nat} (r : TypeRef t arity) (args : Array (DataTy s t))

namespace DataTy

variable {s t : Env α}

mutual
/-- The type expression a payload stands for. -/
@[expose] public def toRaw : DataTy s t → TypeExpr.Raw
  | .var l => .var l
  | .ext r ⟨as⟩ => .app r.name ⟨toRawList as⟩
  | .ref r ⟨as⟩ => .app r.name ⟨toRawList as⟩

@[expose] public def toRawList : List (DataTy s t) → List TypeExpr.Raw
  | [] => []
  | e :: es => toRaw e :: toRawList es
end

/-- The list form is `List.map`. -/
public theorem toRawList_eq_map : ∀ as : List (DataTy s t), toRawList as = as.map toRaw
  | [] => rfl
  | a :: as => by simp [toRawList, toRawList_eq_map as]

/-- A variable stands for the variable. -/
@[simp] public theorem toRaw_var (l : Nat) : (DataTy.var l : DataTy s t).toRaw = .var l := rfl

/-- A type the group extends stands for its name applied to what its arguments stand for. -/
@[simp] public theorem toRaw_ext {a : Nat} (r : TypeRef s a) (as : Array (DataTy s t)) :
    (DataTy.ext r as).toRaw = .app r.name (as.map toRaw) := by
  obtain ⟨as⟩ := as
  simp [toRaw, toRawList_eq_map]

/-- A type of the group stands for its name applied to what its arguments stand for. -/
@[simp] public theorem toRaw_ref {a : Nat} (r : TypeRef t a) (as : Array (DataTy s t)) :
    (DataTy.ref r as).toRaw = .app r.name (as.map toRaw) := by
  obtain ⟨as⟩ := as
  simp [toRaw, toRawList_eq_map]

mutual
/-- Whether a payload is admissible in a member with parameter positivities `pol`:

* every application has its constructor's arity;
* every variable is in scope;
* where `rec` is false (under a parameter declared `.non`), nothing refers into `t` and no
  parameter the member declared `.pos` occurs.

`ok` reduces in the kernel. -/
@[expose] public def ok (pol : Array (Param Positivity)) (rec : Bool) : DataTy s t → Bool
  | .var l => decide (l < pol.size) && (rec || pol[l]?.map (·.type) != some .pos)
  | .ext r ⟨as⟩ => match r.decl.params with | ⟨ps⟩ => okArgs pol rec ps as
  | .ref r ⟨as⟩ => rec && match r.decl.params with | ⟨ps⟩ => okArgs pol rec ps as

@[expose] public def okArgs (pol : Array (Param Positivity)) (rec : Bool) :
    List (Param Positivity) → List (DataTy s t) → Bool
  | [], [] => true
  | ⟨_, .pos⟩ :: ps, e :: es => ok pol rec e && okArgs pol rec ps es
  | ⟨_, .non⟩ :: ps, e :: es => ok pol false e && okArgs pol rec ps es
  | _, _ => false
end

end DataTy

namespace Env

variable {τ : Type}

/-- The members a group's header and constructor lists describe, pairwise. -/
@[expose] public def membersOf : List (TypeDecl α) → List (Array (Ctor α τ)) →
    List (DatatypeDecl α τ)
  | d :: ds, cs :: css =>
    { ann := d.ann, name := d.name, params := d.params, ctors := cs } :: membersOf ds css
  | _, _ => []

/-- `membersOf` on arrays. -/
@[expose] public def members : Array (TypeDecl α) → Array (Array (Ctor α τ)) →
    Array (DatatypeDecl α τ)
  | ⟨ds⟩, ⟨css⟩ => ⟨membersOf ds css⟩

/-- Every constructor name the lists declare, in order. -/
@[expose] public def ctorNames (ctors : Array (Array (Ctor α τ))) : Array Name :=
  ctors.flatMap fun cs => cs.map (·.name)

/-- On a literal, `ctorNames` is the list of the constructors' names. -/
@[simp, grind =] public theorem ctorNames_mk (l : List (Array (Ctor α τ))) :
    ctorNames ⟨l⟩ = ⟨l.flatMap fun cs => cs.toList.map (·.name)⟩ := by
  simp [ctorNames]

@[simp, grind =] public theorem mem_ctorNames {ctors : Array (Array (Ctor α τ))} {n : Name} :
    n ∈ ctorNames ctors ↔ ∃ cs ∈ ctors, ∃ c ∈ cs, c.name = n := by
  simp [ctorNames]

/-- The name of each member's case instruction, in order. -/
@[expose] public def caseNames (hdr : Array (TypeDecl α)) : Array Name :=
  hdr.map (·.name.caseName)

/-- On a literal, `caseNames` is the list of the members' case names. -/
@[simp, grind =] public theorem caseNames_mk (l : List (TypeDecl α)) :
    caseNames ⟨l⟩ = ⟨l.map (·.name.caseName)⟩ := by
  simp [caseNames]

/-- Whether `ctors` make a datatype group of the header `hdr`:

* there is at least one member;
* there is one constructor list per member;
* every payload is `ok` at its member's parameters;
* no constructor binds a name twice: its member's parameters and its fields are named
  distinctly;
* no case instruction binds a name twice: its member's parameters, `scrutinee` and the last
  component of each constructor's name, which names its successor, are distinct.

It reduces in the kernel, so `decide` proves it when it holds. -/
@[expose] public def admissible {s t : Env α} (hdr : Array (TypeDecl α))
    (ctors : Array (Array (Ctor α (DataTy s t)))) : Bool :=
  decide (0 < hdr.size) && decide (ctors.size = hdr.size) &&
    ((members hdr ctors).toList.all fun m =>
      m.ctors.toList.all fun c =>
        c.args.toList.all (fun p => DataTy.ok m.params true p.type) &&
          decide (m.params.toList.map (·.name) ++ c.args.toList.map (·.name)).Nodup) &&
    (members hdr ctors).toList.all fun m =>
      decide (m.params.toList.map (·.name) ++ ["scrutinee"] ++
        m.ctors.toList.map (·.name.lastString)).Nodup

end Env

/-! ### What `ok` buys

The lemmas below show that `ok` implies `TypeExpr.Raw.checkPayload` and `varPositive`, for
abstract resolvers. -/

namespace DataTy

variable {s t : Env α} {P : Name → Option (Array (Param Positivity))} {R N : Name → Nat → Bool}

theorem length_toRawList :
    ∀ as : List (DataTy s t), (toRawList as).length = as.length
  | [] => rfl
  | _ :: as => by simp [toRawList, length_toRawList as]

/-- An admissible argument list has one argument per parameter. -/
theorem length_of_okArgs {pol : Array (Param Positivity)} {rec : Bool} :
    ∀ {ps : List (Param Positivity)} {as : List (DataTy s t)}, okArgs pol rec ps as = true →
      as.length = ps.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [okArgs] at h
  | ⟨_, p⟩ :: _, [], h => by cases p <;> simp [okArgs] at h
  | ⟨_, .pos⟩ :: _, _ :: _, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp [length_of_okArgs h.2]
  | ⟨_, .non⟩ :: _, _ :: _, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp [length_of_okArgs h.2]

mutual
/-- Under a `.non` parameter a payload is checked against `N` alone, and mentions no
parameter its member declared `.pos`. -/
theorem check_of_ok_false (hN : ∀ {a} (r : TypeRef s a), N r.name r.decl.params.size = true)
    {pol : Array (Param Positivity)} : ∀ (e : DataTy s t), ok pol false e = true →
      TypeExpr.Raw.check N pol.size (toRaw e) = true ∧
        ∀ k, pol[k]?.map (·.type) = some .pos → TypeExpr.Raw.varOccurs k (toRaw e) = false
  | .var l, h => by
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq, Bool.false_or, bne_iff_ne, ne_eq] at h
    refine ⟨by simpa [toRaw, TypeExpr.Raw.check] using h.1, fun k hk => ?_⟩
    simp only [toRaw, TypeExpr.Raw.varOccurs, beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    exact h.2 hk
  | .ext r ⟨as⟩, h => by
    simp only [ok] at h
    have has := checkList_of_okArgs_false hN as _ h
    simp only [toRaw, TypeExpr.Raw.check, TypeExpr.Raw.varOccurs, Bool.and_eq_true]
    refine ⟨⟨?_, has.1⟩, has.2⟩
    rw [length_toRawList, length_of_okArgs h]
    simpa using hN r
  | .ref _ ⟨_⟩, h => by simp [ok] at h

theorem checkList_of_okArgs_false
    (hN : ∀ {a} (r : TypeRef s a), N r.name r.decl.params.size = true)
    {pol : Array (Param Positivity)} : ∀ (as : List (DataTy s t)) (ps : List (Param Positivity)),
      okArgs pol false ps as = true →
      TypeExpr.Raw.checkList N pol.size (toRawList as) = true ∧
        ∀ k, pol[k]?.map (·.type) = some .pos →
          TypeExpr.Raw.varOccursList k (toRawList as) = false
  | [], _, _ => by simp [toRawList, TypeExpr.Raw.checkList, TypeExpr.Raw.varOccursList]
  | _ :: _, [], h => by simp [okArgs] at h
  | e :: as, ⟨_, p⟩ :: ps, h => by
    have h' : ok pol false e = true ∧ okArgs pol false ps as = true := by
      cases p <;> simpa [okArgs] using h
    have he := check_of_ok_false hN e h'.1
    have has := checkList_of_okArgs_false hN as ps h'.2
    simp only [toRawList, TypeExpr.Raw.checkList, TypeExpr.Raw.varOccursList,
      Bool.and_eq_true, Bool.or_eq_false_iff]
    exact ⟨⟨he.1, has.1⟩, fun k hk => ⟨he.2 k hk, has.2 k hk⟩⟩
end

mutual
/-- An admissible payload passes `checkPayload`. -/
theorem checkPayload_of_ok (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true ∧ N r.name r.decl.params.size = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true)
    {pol : Array (Param Positivity)} : ∀ (e : DataTy s t),
    ok pol true e = true → TypeExpr.Raw.checkPayload P R N pol.size (toRaw e) = true
  | .var _, h => by
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at h
    simpa [toRaw, TypeExpr.Raw.checkPayload] using h.1
  | .ext r ⟨as⟩, h => by
    simp only [ok] at h
    obtain ⟨hp, hr, -⟩ := hext r
    simp only [toRaw, TypeExpr.Raw.checkPayload, hp, length_toRawList, length_of_okArgs h,
      Array.length_toList, Bool.and_eq_true, beq_self_eq_true, true_and]
    exact ⟨hr, checkPayloadArgs_of_okArgs hext hnew as _ h⟩
  | .ref r ⟨as⟩, h => by
    simp only [ok, Bool.true_and] at h
    obtain ⟨hp, hr⟩ := hnew r
    simp only [toRaw, TypeExpr.Raw.checkPayload, hp, length_toRawList, length_of_okArgs h,
      Array.length_toList, Bool.and_eq_true, beq_self_eq_true, true_and]
    exact ⟨hr, checkPayloadArgs_of_okArgs hext hnew as _ h⟩

theorem checkPayloadArgs_of_okArgs (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true ∧ N r.name r.decl.params.size = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true)
    {pol : Array (Param Positivity)} :
    ∀ (as : List (DataTy s t)) (ps : List (Param Positivity)), okArgs pol true ps as = true →
      TypeExpr.Raw.checkPayloadArgs P R N pol.size ps (toRawList as) = true
  | [], [], _ => rfl
  | [], ⟨_, p⟩ :: _, h => by cases p <;> simp [okArgs] at h
  | _ :: _, [], h => by simp [okArgs] at h
  | e :: as, ⟨_, .pos⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.checkPayloadArgs, Bool.and_eq_true]
    exact ⟨checkPayload_of_ok hext hnew e h.1, checkPayloadArgs_of_okArgs hext hnew as ps h.2⟩
  | e :: as, ⟨_, .non⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.checkPayloadArgs, Bool.and_eq_true]
    exact ⟨(check_of_ok_false (fun r => (hext r).2.2) e h.1).1,
      checkPayloadArgs_of_okArgs hext hnew as ps h.2⟩
end

mutual
/-- An admissible payload keeps every parameter its member declared `.pos` in positions
declared `.pos`. -/
theorem varPositive_of_ok (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true ∧ N r.name r.decl.params.size = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true)
    {pol : Array (Param Positivity)} {k : Nat} (hk : pol[k]?.map (·.type) = some .pos) :
    ∀ {rec : Bool} (e : DataTy s t), ok pol rec e = true →
      TypeExpr.Raw.varPositive P k (toRaw e) = true
  | _, .var _, _ => by simp [toRaw, TypeExpr.Raw.varPositive]
  | _, .ext r ⟨as⟩, h => by
    simp only [ok] at h
    simp only [toRaw, TypeExpr.Raw.varPositive, (hext r).1, length_toRawList,
      length_of_okArgs h, Array.length_toList, beq_self_eq_true, Bool.true_and]
    exact varPositiveArgs_of_okArgs hext hnew hk as _ h
  | false, .ref _ ⟨_⟩, h => by simp [ok] at h
  | true, .ref r ⟨as⟩, h => by
    simp only [ok, Bool.true_and] at h
    simp only [toRaw, TypeExpr.Raw.varPositive, (hnew r).1, length_toRawList,
      length_of_okArgs h, Array.length_toList, beq_self_eq_true, Bool.true_and]
    exact varPositiveArgs_of_okArgs hext hnew hk as _ h

theorem varPositiveArgs_of_okArgs (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true ∧ N r.name r.decl.params.size = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.params.size = true)
    {pol : Array (Param Positivity)} {k : Nat} (hk : pol[k]?.map (·.type) = some .pos) :
    ∀ {rec : Bool} (as : List (DataTy s t)) (ps : List (Param Positivity)),
      okArgs pol rec ps as = true →
      TypeExpr.Raw.varPositiveArgs P k ps (toRawList as) = true
  | _, [], [], _ => rfl
  | _, [], ⟨_, p⟩ :: _, h => by cases p <;> simp [okArgs] at h
  | _, _ :: _, [], h => by simp [okArgs] at h
  | _, e :: as, ⟨_, .pos⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.varPositiveArgs, Bool.and_eq_true]
    exact ⟨varPositive_of_ok hext hnew hk e h.1, varPositiveArgs_of_okArgs hext hnew hk as ps h.2⟩
  | _, e :: as, ⟨_, .non⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.varPositiveArgs, Bool.and_eq_true, Bool.not_eq_true',
      (check_of_ok_false (fun r => (hext r).2.2) e h.1).2 k hk, true_and]
    exact varPositiveArgs_of_okArgs hext hnew hk as ps h.2
end

end DataTy

/-! ## Adding a datatype group

* `addData`: extend an environment by a mutual group of datatypes.
* `resolvesType_addData`, `TypeRef.ofAddData`: carry what `s.addTypes hdr fresh` resolves
  into the environment with the group. -/

namespace Env

section membersOf

variable {τ : Type}

theorem length_membersOf : ∀ (ds : List (TypeDecl α)) (css : List (Array (Ctor α τ))),
    ds.length = css.length → (membersOf ds css).length = ds.length
  | [], [], _ => rfl
  | _ :: ds, _ :: css, h => by simp [membersOf, length_membersOf ds css (by simpa using h)]

theorem map_toTypeDecl_membersOf :
    ∀ (ds : List (TypeDecl α)) (css : List (Array (Ctor α τ))), ds.length = css.length →
      (membersOf ds css).map (·.toTypeDecl) = ds
  | [], [], _ => rfl
  | d :: ds, _ :: css, h => by
    simp only [membersOf, List.map_cons, map_toTypeDecl_membersOf ds css (by simpa using h)]
    rfl

theorem flatMap_ctorNames_membersOf :
    ∀ (ds : List (TypeDecl α)) (css : List (Array (Ctor α τ))), ds.length = css.length →
      (membersOf ds css).flatMap (fun m => m.ctors.toList.map (·.name)) =
        css.flatMap (fun cs => cs.toList.map (·.name))
  | [], [], _ => rfl
  | _ :: ds, _ :: css, h => by
    simp [membersOf, flatMap_ctorNames_membersOf ds css (by simpa using h)]

theorem toList_members (ds : Array (TypeDecl α)) (css : Array (Array (Ctor α τ))) :
    (members ds css).toList = membersOf ds.toList css.toList := by
  cases ds; cases css; rfl

/-- A member is a header entry paired with a constructor list. -/
theorem mem_membersOf : ∀ {ds : List (TypeDecl α)} {css : List (Array (Ctor α τ))}
    {m : DatatypeDecl α τ}, m ∈ membersOf ds css →
      ∃ d ∈ ds, m.params = d.params
  | d :: ds, cs :: css, m, h => by
    simp only [membersOf, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨d, List.mem_cons_self, rfl⟩
    · obtain ⟨d', hd', he⟩ := mem_membersOf h
      exact ⟨d', List.mem_cons_of_mem _ hd', he⟩
  | [], _, _, h => by simp [membersOf] at h
  | _ :: _, [], _, h => by simp [membersOf] at h

/-- Member `i` is header entry `i` with constructor list `i`. -/
theorem getElem?_membersOf : ∀ {ds : List (TypeDecl α)} {css : List (Array (Ctor α τ))}
    {i : Nat} {d : TypeDecl α} {cs : Array (Ctor α τ)}, ds[i]? = some d → css[i]? = some cs →
      (membersOf ds css)[i]? =
        some { ann := d.ann, name := d.name, params := d.params, ctors := cs }
  | _ :: _, _ :: _, 0, _, _, hd, hc => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hd hc
    subst hd hc; rfl
  | _ :: ds, _ :: css, i + 1, _, _, hd, hc => by
    simp only [List.getElem?_cons_succ] at hd hc
    simpa [membersOf] using getElem?_membersOf hd hc
  | [], _, _, _, _, hd, _ => by simp at hd
  | _ :: _, [], _, _, _, _, hc => by simp at hc

end membersOf

section group

variable {s t : Env α} {hdr : Array (TypeDecl α)} {ctors : Array (Array (Ctor α (DataTy s t)))}

/-- An admissible group has a member. -/
public theorem pos_of_admissible (h : admissible hdr ctors = true) : 0 < hdr.size := by
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1

/-- An admissible group has one constructor list per member. -/
public theorem size_of_admissible (h : admissible hdr ctors = true) : ctors.size = hdr.size := by
  simp only [admissible, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-- The unchecked group that header and constructors stand for. -/
def dataGroup (hdr : Array (TypeDecl α)) (ctors : Array (Array (Ctor α (DataTy s t))))
    (h : admissible hdr ctors = true) : DataGroup α TypeExpr.Raw :=
  ⟨(members hdr ctors).map (DatatypeDecl.mapTy DataTy.toRaw), by
    rw [Array.size_map, ← Array.length_toList, toList_members,
      length_membersOf hdr.toList ctors.toList (by simp [size_of_admissible h])]
    simpa using pos_of_admissible h⟩

variable {h : admissible hdr ctors = true}

theorem size_dataGroup : (dataGroup hdr ctors h).members.size = hdr.size := by
  simp [dataGroup, ← Array.length_toList, toList_members,
    length_membersOf hdr.toList ctors.toList (by simp [size_of_admissible h])]

/-- The group's members present exactly the header's types. -/
theorem map_toTypeDecl_dataGroup :
    (dataGroup hdr ctors h).members.map (·.toTypeDecl) = hdr := by
  apply Array.toList_inj.mp
  have : ((membersOf hdr.toList ctors.toList).map (·.toTypeDecl)) = hdr.toList :=
    map_toTypeDecl_membersOf hdr.toList ctors.toList (by simp [size_of_admissible h])
  simpa [dataGroup, toList_members, Function.comp_def, DatatypeDecl.mapTy, DatatypeDecl.toTypeDecl]
    using this

theorem toTypeDecl_dataGroup_getElem? {j : Nat} {m : DatatypeDecl α TypeExpr.Raw}
    (hm : (dataGroup hdr ctors h).members[j]? = some m) : hdr[j]? = some m.toTypeDecl := by
  rw [← map_toTypeDecl_dataGroup (h := h), Array.getElem?_map, hm]
  rfl

theorem first_toTypeDecl_dataGroup :
    hdr[0]? = some (dataGroup hdr ctors h).first.toTypeDecl :=
  toTypeDecl_dataGroup_getElem? (Array.getElem?_eq_getElem (dataGroup hdr ctors h).nonEmpty)

theorem names_dataGroup :
    (dataGroup hdr ctors h).names = hdr.map (·.name) ++ (ctorNames ctors ++ caseNames hdr) := by
  have hl : hdr.toList.length = ctors.toList.length := by simp [size_of_admissible h]
  have hn : (dataGroup hdr ctors h).members.toList.map (·.name) = hdr.toList.map (·.name) := by
    have := congrArg (fun a => a.toList.map (·.name)) (map_toTypeDecl_dataGroup (h := h))
    simpa [Function.comp_def, DatatypeDecl.toTypeDecl] using this
  have hk : (dataGroup hdr ctors h).members.toList.map (·.name.caseName) =
      hdr.toList.map (·.name.caseName) := by
    have := congrArg (fun a => a.toList.map (·.name.caseName)) (map_toTypeDecl_dataGroup (h := h))
    simpa [Function.comp_def, DatatypeDecl.toTypeDecl] using this
  apply Array.toList_inj.mp
  simp only [DataGroup.names, ctorNames, caseNames, Array.toList_append, Array.toList_map,
    Array.toList_flatMap, hn, hk]
  rw [← flatMap_ctorNames_membersOf _ _ hl]
  simp [dataGroup, toList_members, DatatypeDecl.mapTy, Ctor.mapTy, List.flatMap_map,
    Function.comp_def]

end group

/-! ### The extended environment agrees with the members as plain types -/

section agree

variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {h : admissible hdr ctors = true}

/-- `addTypes` does not change the type a name of `s` denotes. -/
theorem typeOf?_of_addTypes_of_mem {n : Name} {d : TypeDecl α} (hn : n ∈ s.raw)
    (hd : (s.addTypes hdr fresh).raw.typeOf? n = some d) : s.raw.typeOf? n = some d := by
  -- every declaration of the batch is a plain type
  have nogroup : ∀ (k : Name),
      (((s.addTypes hdr fresh).raw.decls[k]?).bind Decl.Raw.asGroup) =
        ((s.raw.decls[k]?).bind Decl.Raw.asGroup) := by
    intro k
    show (((s.addTypes hdr fresh).raw)[k]?).bind _ = ((s.raw)[k]?).bind _
    rw [raw_addTypes, Raw.get?_appendList, Array.toList_map]
    cases hk : s.raw[k]? with
    | some e => rfl
    | none =>
      simp only [Option.none_or, Option.bind_none]
      cases hf : (hdr.toList.map Decl.Raw.type).find? (·.name == k) with
      | none => rfl
      | some e =>
        obtain ⟨x, -, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
        rfl
  obtain ⟨e, he⟩ : ∃ e, s.raw.decls[n]? = some e :=
    ⟨_, IndexMap.getElem?_eq_some_getElem hn⟩
  have he' : (s.addTypes hdr fresh).raw.decls[n]? = some e := by
    show ((s.addTypes hdr fresh).raw)[n]? = some e
    rw [raw_addTypes, Raw.get?_appendList]
    show (s.raw.decls[n]?).or _ = some e
    rw [he]
    rfl
  unfold Raw.typeOf? at hd ⊢
  rw [he'] at hd
  rw [he]
  cases e with
  | dataRest _ hh i =>
    simp only [Option.bind_some, Raw.typeOfDecl?] at hd ⊢
    rwa [nogroup hh] at hd
  | _ => exact hd

/-- The group's names are fresh in `s`. -/
theorem freshNames_dataGroup
    (cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)) :
    s.FreshNames ((dataGroup hdr ctors h).decls.map (·.name)) := by
  rw [DataGroup.decls_names, names_dataGroup]
  refine ⟨Array.nodup_toList.mpr (Array.nodup_append.mpr
    ⟨Array.nodup_toList.mp fresh.1.1, Array.nodup_toList.mp cfresh.1, ?_⟩), ?_⟩
  · intro a ha b hb hab
    subst hab
    exact cfresh.2 a hb (mem_addTypes.mpr (.inl ha))
  · intro n hn
    rcases Array.mem_append.mp hn with hn | hn
    · exact fresh.1.2 n hn
    · exact fun hs => cfresh.2 n hn (mem_addTypes.mpr (.inr hs))

/-- **Agreement.**  Every type `s.addTypes hdr fresh` gives a name, the environment with the
group also gives it, among the types declared before the group ends. -/
theorem typesBefore_dataGroup {fG : s.raw.FreshList (dataGroup hdr ctors h).decls.toList}
    {n : Name} {d : TypeDecl α} (hd : (s.addTypes hdr fresh).raw.typeOf? n = some d) :
    ((s.raw.appendList _ fG).types.before (s.size + hdr.size))[n]? = some d := by
  by_cases hn : n ∈ s.raw
  · exact Raw.typesBefore_appendList
      (Raw.typesBefore_of_typeOf? (typeOf?_of_addTypes_of_mem hn hd) (by simp [size]))
  -- otherwise `n` is one of the header's, and resolves to it
  have hget : (s.addTypes hdr fresh).raw.decls[n]? =
      (hdr.toList.map Decl.Raw.type).find? (·.name == n) := by
    show ((s.addTypes hdr fresh).raw)[n]? = _
    rw [raw_addTypes, Raw.get?_appendList, Raw.not_getElem?_of_not_mem hn, Option.none_or,
      Array.toList_map]
  unfold Raw.typeOf? at hd
  rw [hget] at hd
  cases hf : (hdr.toList.map Decl.Raw.type).find? (·.name == n) with
  | none => rw [hf] at hd; simp at hd
  | some e =>
    rw [hf] at hd
    have hpred := List.find?_some hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hf)
    simp only [Option.bind_some, Raw.typeOfDecl?, Option.some.injEq] at hd
    subst hd
    obtain rfl : x.name = n := by simpa using hpred
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
    have hj' : hdr[j]? = some x := by simpa using hj
    have hjlt : j < hdr.size := (Array.getElem?_eq_some_iff.mp hj').1
    obtain ⟨m, hm⟩ : ∃ m, (dataGroup hdr ctors h).members[j]? = some m :=
      ⟨_, Array.getElem?_eq_getElem (by rw [size_dataGroup]; exact hjlt)⟩
    have hmx : m.toTypeDecl = x := by
      have := toTypeDecl_dataGroup_getElem? hm
      rw [hj'] at this
      exact (Option.some.inj this).symm
    have hhead : (s.raw.appendList _ fG).decls[(dataGroup hdr ctors h).first.name]? =
        some (.dataHead (dataGroup hdr ctors h)) :=
      Raw.get?_appendList_of_getElem? (DataGroup.decls_getElem?_zero _)
    -- the declaration `decls` puts at position `j`, and what it denotes there
    obtain ⟨D, hD, hDname, hDty⟩ : ∃ D, (dataGroup hdr ctors h).decls.toList[j]? = some D ∧
        D.name = x.name ∧ (s.raw.appendList _ fG).typeOfDecl? D = some x := by
      by_cases hj0 : j = 0
      · subst hj0
        have hfx : (dataGroup hdr ctors h).first.toTypeDecl = x := by
          have := first_toTypeDecl_dataGroup (h := h)
          rw [hj'] at this
          exact (Option.some.inj this).symm
        refine ⟨_, DataGroup.decls_getElem?_zero _, ?_, ?_⟩
        · rw [← hfx]; rfl
        · simp [Raw.typeOfDecl?, hfx]
      · refine ⟨_, DataGroup.decls_getElem?_of_member _ hm hj0, ?_, ?_⟩
        · rw [← hmx]; rfl
        · simp [Raw.typeOfDecl?, hhead, DataGroup.member?, hm, hmx]
    rw [Raw.getElem?_types_before, ← hDname, Raw.idxOf?_appendList_of_getElem? hD,
      Option.bind_some, if_pos (by simp only [size]; omega), Raw.get?_appendList_of_getElem? hD,
      Option.bind_some]
    exact hDty

/-- The group is an admissible definition in the extended environment. -/
theorem checkWith_dataGroup (fG : s.raw.FreshList (dataGroup hdr ctors h).decls.toList) :
    (dataGroup hdr ctors h).checkWith
      ((s.raw.appendList _ fG).paramsBefore
        (s.raw.decls.keys.size + (dataGroup hdr ctors h).members.size))
      (Raw.RefBefore.check (s.raw.appendList _ fG)
        (s.raw.decls.keys.size + (dataGroup hdr ctors h).members.size))
      (Raw.RefBefore.check (s.raw.appendList _ fG) s.raw.decls.keys.size) = true := by
  rw [size_dataGroup]
  have hext : ∀ {a} (r : TypeRef s a),
      (s.raw.appendList _ fG).paramsBefore (s.raw.decls.keys.size + hdr.size) r.name =
          some r.decl.params ∧
        Raw.RefBefore.check (s.raw.appendList _ fG) (s.raw.decls.keys.size + hdr.size) r.name
          r.decl.params.size = true ∧
        Raw.RefBefore.check (s.raw.appendList _ fG) s.raw.decls.keys.size r.name
          r.decl.params.size = true := by
    intro a r
    have h1 : ((s.raw.appendList _ fG).types.before (s.raw.decls.keys.size + hdr.size))[r.name]? =
        some r.decl :=
      Raw.typesBefore_appendList (Raw.typesBefore_of_typeOf? r.resolves (by omega))
    have h2 : ((s.raw.appendList _ fG).types.before s.raw.decls.keys.size)[r.name]? =
        some r.decl :=
      Raw.typesBefore_appendList (Raw.typesBefore_of_typeOf? r.resolves (Nat.le_refl _))
    simp only [Raw.paramsBefore, Raw.RefBefore.check, h1, h2, Option.map_some]
    simp [TypeDecl.arity]
  have hnew : ∀ {a} (r : TypeRef (s.addTypes hdr fresh) a),
      (s.raw.appendList _ fG).paramsBefore (s.raw.decls.keys.size + hdr.size) r.name =
          some r.decl.params ∧
        Raw.RefBefore.check (s.raw.appendList _ fG) (s.raw.decls.keys.size + hdr.size) r.name
          r.decl.params.size = true := by
    intro a r
    have h1 := typesBefore_dataGroup (fG := fG) r.resolves
    simp only [size] at h1
    simp only [Raw.paramsBefore, Raw.RefBefore.check, h1, Option.map_some]
    simp [TypeDecl.arity]
  have hadm := h
  simp only [admissible, List.all_eq_true, Array.mem_toList_iff, Bool.and_eq_true] at hadm
  obtain ⟨⟨-, hadm⟩, -⟩ := hadm
  replace hadm := fun m hm c hc => (hadm m hm c hc).1
  simp only [DataGroup.checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true]
  intro m' hm' c' hc' p' hp'
  simp only [dataGroup, Array.mem_map] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  simp only [DatatypeDecl.mapTy, Array.mem_map] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  simp only [Ctor.mapTy, Array.mem_map] at hp'
  obtain ⟨p, hp, rfl⟩ := hp'
  have hok := hadm m hm c hc p hp
  refine ⟨DataTy.checkPayload_of_ok hext hnew p.type hok, ?_⟩
  intro ⟨⟨x, pol⟩, k⟩ hk
  cases pol with
  | non => rfl
  | pos =>
    have hk' := Array.mk_mem_zipIdx_iff_getElem?.mp hk
    simp only [DatatypeDecl.mapTy] at hk'
    exact DataTy.varPositive_of_ok hext hnew (by simp [hk']) p.type hok

/-- The group binds no name twice. -/
theorem checkNames_dataGroup : (dataGroup hdr ctors h).checkNames = true := by
  have hadm := h
  simp only [admissible, List.all_eq_true, Array.mem_toList_iff, Bool.and_eq_true,
    decide_eq_true_eq] at hadm
  obtain ⟨⟨⟨-, hsz⟩, hadm⟩, hcase⟩ := hadm
  simp only [DataGroup.checkNames, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true,
    decide_eq_true_eq]
  intro m' hm'
  simp only [dataGroup, Array.mem_map] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  -- every member names its parameters as its header entry does
  have hpm : m.paramNames.Nodup := by
    rw [← Array.mem_toList_iff, toList_members] at hm
    obtain ⟨d, hd, hdm⟩ := mem_membersOf hm
    simpa [DatatypeDecl.paramNames, TypeDecl.paramNames, hdm] using fresh.2 d hd
  refine ⟨⟨by simpa [DatatypeDecl.mapTy, DatatypeDecl.paramNames] using hpm, fun c' hc' => ?_⟩,
    ?_⟩
  · simp only [DatatypeDecl.mapTy, Array.mem_map] at hc'
    obtain ⟨c, hc, rfl⟩ := hc'
    simpa [DatatypeDecl.mapTy, DatatypeDecl.paramNames, Ctor.mapTy, Param.mapTy,
      Function.comp_def] using (hadm m hm c hc).2
  · simpa [DatatypeDecl.mapTy, DatatypeDecl.paramNames, Ctor.mapTy, Function.comp_def]
      using hcase m hm

end agree

/-- Add a mutual group of datatypes.  `hdr` declares the members.  `ctors` lists each
member's constructors, with payloads written against `s.addTypes hdr fresh`.  The result
resolves every type that `s.addTypes hdr fresh` resolves, in the same way, and declares one
instruction per constructor, with the signature `Env.ctorSig` describes, and each member's
case instruction `T.case`, with the signature `Env.caseSig` describes. -/
public def addData (s : Env α) (hdr : Array (TypeDecl α)) (fresh : s.FreshTypes hdr)
    (ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh)))))
    (cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr))
    (adm : admissible hdr ctors = true := by decide) : Env α :=
  s.appendBatch (dataGroup hdr ctors adm).decls
    (freshList_of_freshNames (freshNames_dataGroup cfresh))
    (s.wf.appendList _ _ (Raw.checkFrom_group _ checkNames_dataGroup (checkWith_dataGroup _)))

section

variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
  {adm : admissible hdr ctors = true}

@[simp] public theorem subset_addData : s ⊆ s.addData hdr fresh ctors cfresh adm :=
  subset_appendBatch

/-- The names a group adds: its members, its constructors and its case instructions. -/
@[simp, grind =] public theorem mem_addData {n : Name} :
    n ∈ s.addData hdr fresh ctors cfresh adm ↔
      n ∈ hdr.map (·.name) ∨ n ∈ ctorNames ctors ++ caseNames hdr ∨ n ∈ s := by
  have := (Array.mem_map (f := (·.name))
    (xs := (dataGroup hdr ctors adm).decls) (b := n))
  rw [DataGroup.decls_names, names_dataGroup, Array.mem_append] at this
  rw [addData, mem_appendBatch, ← this, or_comm, or_assoc]

/-- `addData` resolves every type that `s.addTypes hdr fresh` resolves, in the same way. -/
public theorem resolvesType_addData {n : Name} {d : TypeDecl α}
    (hd : (s.addTypes hdr fresh).ResolvesType n d) :
    (s.addData hdr fresh ctors cfresh adm).ResolvesType n d :=
  Raw.typeOf?_of_typesBefore (typesBefore_dataGroup hd)

end

/-- Each type of a batch resolves to its own declaration. -/
public theorem resolvesType_addTypes {s : Env α} {ds : Array (TypeDecl α)}
    {fresh : s.FreshTypes ds} {j : Nat} {d : TypeDecl α}
    (hd : ds[j]? = some d) : (s.addTypes ds fresh).ResolvesType d.name d := by
  unfold ResolvesType Raw.typeOf?
  rw [show (s.addTypes ds fresh).raw.decls[d.name]? = some (.type d) from
    rawGet?_addTypes_of_getElem? hd]
  rfl

end Env

/-- The reference to the `j`th type `addTypes` added. -/
@[expose] public def TypeRef.ofAddTypes (s : Env α) (ds : Array (TypeDecl α))
    (fresh : s.FreshTypes ds) (j : Nat) (hj : j < ds.size := by decide) :
    TypeRef (s.addTypes ds fresh) ds[j].arity :=
  ⟨ds[j].name, ds[j], rfl, Env.resolvesType_addTypes (Array.getElem?_eq_getElem hj)⟩

/-- The reference to the `j`th type `addTypes` added names it. -/
@[simp] public theorem TypeRef.name_ofAddTypes (s : Env α) (ds : Array (TypeDecl α))
    (fresh : s.FreshTypes ds) (j : Nat) (hj : j < ds.size) :
    (TypeRef.ofAddTypes s ds fresh j hj).name = ds[j].name := rfl

/-- A reference into `s.addTypes hdr fresh`, carried into the environment with the group. -/
@[expose] public def TypeRef.ofAddData {s : Env α} {hdr : Array (TypeDecl α)}
    {fresh : s.FreshTypes hdr}
    {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
    {cfresh : (s.addTypes hdr fresh).FreshNames (Env.ctorNames ctors ++ Env.caseNames hdr)}
    {adm : Env.admissible hdr ctors = true} {a : Nat}
    (r : TypeRef (s.addTypes hdr fresh) a) :
    TypeRef (s.addData hdr fresh ctors cfresh adm) a :=
  ⟨r.name, r.decl, r.matchArity, Env.resolvesType_addData r.resolves⟩

/-- Carrying a reference into the environment with the group keeps its name. -/
@[simp] public theorem TypeRef.name_ofAddData {s : Env α} {hdr : Array (TypeDecl α)}
    {fresh : s.FreshTypes hdr}
    {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
    {cfresh : (s.addTypes hdr fresh).FreshNames (Env.ctorNames ctors ++ Env.caseNames hdr)}
    {adm : Env.admissible hdr ctors = true} {a : Nat}
    (r : TypeRef (s.addTypes hdr fresh) a) :
    (TypeRef.ofAddData (cfresh := cfresh) (adm := adm) r).name = r.name := rfl


/-- A type expression whose references all resolve in `env`, under `scope` type
variables.  It is built with `var` and `app`, and read with `fold`. -/
public structure TypeExpr (env : Env α) (scope : Nat) where
  private expr : TypeExpr.Raw
  private wf : TypeExpr.WFRel (env.RefBefore env.size) scope expr

namespace TypeExpr

/-- The `i`-th type variable. -/
public def var {env : Env α} {scope : Nat} (i : Nat) (h : i < scope) : TypeExpr env scope :=
  ⟨.var i, .var h⟩

/-- Erasing the check of a type variable gives the variable. -/
theorem expr_var {env : Env α} {scope : Nat} (i : Nat) (h : i < scope) :
    (var (env := env) (scope := scope) i h).expr = .var i := by
  simp [var]

/-- Apply a declared type constructor to checked arguments. -/
public def app {env : Env α} {scope arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeExpr env scope) arity) : TypeExpr env scope :=
  ⟨.app r.name (args.toArray.map (·.expr)),
   .app (by simpa using r.refBefore)
     (by
       intro a ha
       obtain ⟨e, -, rfl⟩ := Array.mem_map.mp ha
       exact e.wf)⟩

/-- Erasing the check of an application applies the name to the erased arguments. -/
theorem expr_app {env : Env α} {scope arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeExpr env scope) arity) :
    (app r args).expr = .app r.name (args.toArray.map (·.expr)) := by
  simp [app]

/-- Check a raw type expression against `env` by evaluation. -/
def check? (env : Env α) (scope : Nat) (e : TypeExpr.Raw) : Option (TypeExpr env scope) :=
  if h : TypeExpr.Raw.checkAt env.raw env.size scope e = true then
    some ⟨e, TypeExpr.Raw.wfRel_of_checkAt e h⟩
  else
    none

/-- What `check?` accepts, it returns unchanged. -/
theorem expr_of_check?_eq_some {env : Env α} {scope : Nat} {e : TypeExpr.Raw}
    {f : TypeExpr env scope} (h : check? env scope e = some f) : f.expr = e := by
  unfold check? at h
  split at h
  · obtain rfl : f = _ := Option.some.inj h.symm
    rfl
  · exact absurd h (by simp)

/-- Reinterpret against a larger environment. -/
public def ofSubset {s t : Env α} (h : s ⊆ t) {scope : Nat} (e : TypeExpr s scope) :
    TypeExpr t scope :=
  ⟨e.expr,
   e.wf.mono (fun _ _ hr => (Env.refBefore_of_subset h hr).mono (Env.size_le_of_subset h))
     (Nat.le_refl scope)⟩

theorem expr_ofSubset {s t : Env α} (h : s ⊆ t) {scope : Nat}
    (e : TypeExpr s scope) : (e.ofSubset h).expr = e.expr := by
  simp [ofSubset]

/-! ### Reading the raw expression

* `toRaw`: the raw type expression a checked one stands for, which `InsnSig.ext_toRaw`
  compares. -/

/-- The raw type expression `e` stands for. -/
public def toRaw {env : Env α} {scope : Nat} (e : TypeExpr env scope) : TypeExpr.Raw := e.expr

/-- A variable stands for the variable. -/
@[simp] public theorem toRaw_var {env : Env α} {scope : Nat} (i : Nat) (h : i < scope) :
    (var (env := env) (scope := scope) i h).toRaw = .var i := by
  simp [toRaw, expr_var]

/-- An application stands for its constructor's name applied to what its arguments stand
for. -/
@[simp] public theorem toRaw_app {env : Env α} {scope arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeExpr env scope) arity) :
    (app r args).toRaw = .app r.name (args.toArray.map (·.toRaw)) := by
  simp [toRaw, expr_app]

/-- Reinterpreting changes nothing an expression stands for. -/
@[simp] public theorem toRaw_ofSubset {s t : Env α} (h : s ⊆ t) {scope : Nat}
    (e : TypeExpr s scope) : (e.ofSubset h).toRaw = e.toRaw := by
  simp [toRaw, expr_ofSubset]

/-- `toRaw` is the erasure. -/
theorem toRaw_eq_expr {env : Env α} {scope : Nat} (e : TypeExpr env scope) :
    e.toRaw = e.expr := rfl

/-! ### Equality

Two type expressions are equal when their erasures are, and equality is decidable. -/

theorem eq_iff_expr_eq {env : Env α} {scope : Nat} {a b : TypeExpr env scope} :
    a = b ↔ a.expr = b.expr := by
  constructor
  · intro h; simp [h]
  · obtain ⟨ea, wa⟩ := a
    obtain ⟨eb, wb⟩ := b
    intro h
    simp only at h
    cases h
    rfl

-- A separate definition: an instance body is exposed and cannot reach the private field.
/-- Decide equality of type expressions. -/
public def decEq {env : Env α} {scope : Nat} (a b : TypeExpr env scope) : Decidable (a = b) :=
  decidable_of_iff (a.expr = b.expr) eq_iff_expr_eq.symm

public instance {env : Env α} {scope : Nat} : DecidableEq (TypeExpr env scope) := decEq

/-! ### Instantiation

* `instantiate`: substitute closed types for the type variables of an expression. -/

/-- Replace the type variables of `e` by the closed types `args`. -/
public def instantiate {env : Env α} {n : Nat} (args : Vector (TypeExpr env 0) n)
    (e : TypeExpr env n) : TypeExpr env 0 :=
  ⟨e.expr.instantiate (args.toArray.map (·.expr)),
   e.wf.instantiate
     (fun a ha => by
       obtain ⟨f, -, rfl⟩ := Array.mem_map.mp ha
       exact f.wf)
     (by simp)⟩

theorem expr_instantiate {env : Env α} {n : Nat} (args : Vector (TypeExpr env 0) n)
    (e : TypeExpr env n) :
    (e.instantiate args).expr = e.expr.instantiate (args.toArray.map (·.expr)) := by
  simp [instantiate]

/-- A closed expression instantiates to itself. -/
@[simp] public theorem instantiate_empty {env : Env α} (e : TypeExpr env 0) :
    e.instantiate #v[] = e :=
  eq_iff_expr_eq.mpr (by simp [expr_instantiate, Raw.instantiate_empty])

/-! ### Folding

* `fold`: a structural fold over a type expression. -/

/-- Replace every variable by `var` of its level and every application by `app` of the
constructor's name and its folded arguments. -/
public def fold {env : Env α} {scope : Nat} {β : Type _} (var : Nat → β)
    (app : Name → Array β → β) (e : TypeExpr env scope) : β :=
  e.expr.fold var app

/-- Folding a variable applies `var` to its level. -/
@[simp] public theorem fold_var {env : Env α} {scope : Nat} {β : Type _} (v : Nat → β)
    (a : Name → Array β → β) (i : Nat) (h : i < scope) :
    (var (env := env) (scope := scope) i h).fold v a = v i := by
  simp [fold, expr_var, Raw.fold]

/-- Folding an application applies `app` to the constructor's name and the folded
arguments. -/
@[simp] public theorem fold_app {env : Env α} {scope arity : Nat} {β : Type _} (v : Nat → β)
    (a : Name → Array β → β) (r : TypeRef env arity) (args : Vector (TypeExpr env scope) arity) :
    (app r args).fold v a = a r.name (args.toArray.map (·.fold v a)) := by
  simp [fold, expr_app, Raw.fold_app, Array.map_map, Function.comp_def]

/-! ### Reading a datatype back

* `ctors?`: the constructors of a datatype, with payload types at its type arguments.
* `ctorPayloads?`: the payload types of every constructor.
* `ctorArgs?`: the payload types of one constructor. -/

/-- Checked arguments from raw ones that are known to be well formed. -/
private def ofRawArgs {env : Env α} {scope : Nat} (as : Array TypeExpr.Raw)
    (h : ∀ a ∈ as, WFRel (env.RefBefore env.size) scope a) :
    Array (TypeExpr env scope) :=
  as.attach.map (fun a => ⟨a.val, h a.val a.property⟩)

@[simp] private theorem size_ofRawArgs {env : Env α} {scope : Nat} {as : Array TypeExpr.Raw}
    {h : ∀ a ∈ as, WFRel (env.RefBefore env.size) scope a} :
    (ofRawArgs (env := env) (scope := scope) as h).size = as.size := by
  simp [ofRawArgs]

private def rawCtors? {env : Env α} :
    (e : TypeExpr.Raw) → WFRel (env.RefBefore env.size) 0 e →
      Option (Array (Name × Array (TypeExpr env 0)))
  | .var _, _ => none
  | .app n as, h => do
    let (g, i) ← env.raw.dataOf? n
    let m ← g.member? i
    if ha : as.size = m.arity then
      let args : Vector (TypeExpr env 0) m.arity := ⟨ofRawArgs as h.args, by simp [ha]⟩
      m.ctors.mapM fun c =>
        (c.args.mapM (fun p => check? env m.arity p.type)).map
          (fun ps => (c.name, ps.map (·.instantiate args)))
    else
      none

/-- The constructors of the datatype `e` is: each name, with its payload types at `e`'s own
type arguments.  `none` for a primitive type, and for a datatype whose group has a member the
environment does not name. -/
public def ctors? {env : Env α} (e : TypeExpr env 0) :
    Option (Array (Name × Array (TypeExpr env 0))) :=
  rawCtors? e.expr e.wf

/-- The payload types of every constructor, in declaration order. -/
public def ctorPayloads? {env : Env α} (e : TypeExpr env 0) :
    Option (Array (Array (TypeExpr env 0))) :=
  e.ctors?.map (·.map (·.2))

/-- The payload types of the constructor named `c`, if `e` is a datatype with one.  A `some`
result means `c` is a constructor of `e`. -/
public def ctorArgs? {env : Env α} (e : TypeExpr env 0) (c : Name) :
    Option (Array (TypeExpr env 0)) :=
  e.ctors?.bind fun cs => (cs.find? (·.1 == c)).map (·.2)

end TypeExpr

/-- Carry a type reference into an extension. -/
public def TypeRef.ofSubset {s t : Env α} {arity : Nat} (h : s ⊆ t)
    (r : TypeRef s arity) : TypeRef t arity :=
  ⟨r.name, r.decl, r.matchArity, r.resolves.mono h⟩

@[simp] public theorem name_TypeRef_ofSubset {s t : Env α} {arity : Nat} (h : s ⊆ t)
    (r : TypeRef s arity) :
    (r.ofSubset h).name = r.name := by
  simp [TypeRef.ofSubset]

@[simp] public theorem decl_TypeRef_ofSubset {s t : Env α} {arity : Nat} (h : s ⊆ t)
    (r : TypeRef s arity) :
    (r.ofSubset h).decl = r.decl := by
  simp [TypeRef.ofSubset]

/-! ### Normal forms under reinterpretation

`simp` pushes `ofSubset` down to the references and compares applications by name: it proves
two signatures built alike equal (`InsnRef.cast`). -/

/-- Carrying a reference twice is carrying it once. -/
@[simp] public theorem TypeRef.ofSubset_ofSubset {s t u : Env α} {arity : Nat} (h₁ : s ⊆ t)
    (h₂ : t ⊆ u) (r : TypeRef s arity) :
    (r.ofSubset h₁).ofSubset h₂ = r.ofSubset (Env.Prefix.trans h₁ h₂) := by
  simp [TypeRef.ofSubset]

namespace TypeExpr

/-- Reinterpreting a type variable gives the variable. -/
@[simp] public theorem ofSubset_var {s t : Env α} (h : s ⊆ t) {scope : Nat} (i : Nat)
    (hi : i < scope) : (var (env := s) i hi).ofSubset h = var i hi :=
  eq_iff_expr_eq.mpr (by simp [expr_ofSubset, expr_var])

/-- Reinterpreting an application reinterprets the reference and the arguments. -/
@[simp] public theorem ofSubset_app {s t : Env α} (h : s ⊆ t) {scope arity : Nat}
    (r : TypeRef s arity) (args : Vector (TypeExpr s scope) arity) :
    (app r args).ofSubset h = app (r.ofSubset h) (args.map (·.ofSubset h)) :=
  eq_iff_expr_eq.mpr (by
    simp [expr_ofSubset, expr_app, Array.map_map, Function.comp_def])

/-- Two applications are equal when they apply the same name to equal arguments. -/
@[simp] public theorem app_eq_app_iff {env : Env α} {scope arity : Nat}
    {r₁ r₂ : TypeRef env arity} {a₁ a₂ : Vector (TypeExpr env scope) arity} :
    app r₁ a₁ = app r₂ a₂ ↔ r₁.name = r₂.name ∧ a₁ = a₂ := by
  rw [eq_iff_expr_eq, expr_app, expr_app, TypeExpr.Raw.app.injEq,
    Array.map_inj_right (fun _ _ h => eq_iff_expr_eq.mpr h), Vector.toArray_inj]

end TypeExpr

/-! ## Region signatures, checked

`RegionSig env scope` is a region signature well formed against `env` under `scope` type
variables.  A region binds no type variables of its own. -/

/-- The checked signature of a region: the types of its entry block's parameters, and the
type its exit takes.  It is built with `of` and read through `params` and
`returnType`. -/
public structure RegionSig (env : Env α) (scope : Nat) where
  private raw : RegionSig.Raw
  private wf : raw.WF (env.RefBefore env.size) scope

namespace RegionSig

variable {env : Env α} {scope : Nat}

/-- The region's parameters, checked. -/
public def params (r : RegionSig env scope) : Array (Param (TypeExpr env scope)) :=
  r.raw.params.attach.map fun p =>
    ⟨p.val.name, ⟨p.val.type, RegionSig.Raw.wf_params r.wf p.val p.property⟩⟩

/-- The type the region's exit takes, checked. -/
public def returnType (r : RegionSig env scope) : TypeExpr env scope :=
  ⟨r.raw.returnType, RegionSig.Raw.wf_returnType r.wf⟩

/-- Erasing the checked parameters gives the raw ones. -/
@[simp] theorem map_params (r : RegionSig env scope) :
    r.params.map (fun p => (⟨p.name, p.type.expr⟩ : Param TypeExpr.Raw)) = r.raw.params := by
  apply Array.ext
  · simp [params]
  · intro i _ _
    simp [params]

/-- Erasing the checked return type gives the raw one. -/
@[simp] theorem expr_returnType (r : RegionSig env scope) :
    r.returnType.expr = r.raw.returnType := rfl

/-- The parameters' names are the raw parameters' names. -/
@[simp] theorem paramNames_params (r : RegionSig env scope) :
    r.params.toList.map (·.name) = r.raw.paramNames := by
  rw [RegionSig.Raw.paramNames, ← map_params, Array.toList_map, List.map_map]
  rfl

/-- A region signature from checked parameter types and a checked return type. -/
public def of (params : Array (Param (TypeExpr env scope))) (returnType : TypeExpr env scope)
    (distinct : (params.toList.map (·.name)).Nodup := by decide) : RegionSig env scope where
  raw := { params := params.map (fun p => ⟨p.name, p.type.expr⟩), returnType := returnType.expr }
  wf := RegionSig.Raw.wf_mk
    (fun p hp => by
      obtain ⟨q, -, rfl⟩ := Array.mem_map.mp hp
      exact q.type.wf)
    returnType.wf
    (by simpa [RegionSig.Raw.paramNames, Function.comp_def] using distinct)

/-- `of` keeps the parameters it was given. -/
@[simp] public theorem params_of (params : Array (Param (TypeExpr env scope)))
    (returnType : TypeExpr env scope) (distinct : (params.toList.map (·.name)).Nodup) :
    (of params returnType distinct).params = params := by
  apply Array.ext
  · simp [RegionSig.params, of]
  · intro i _ _
    simp [RegionSig.params, of]

/-- `of` keeps the return type it was given. -/
@[simp] public theorem returnType_of (params : Array (Param (TypeExpr env scope)))
    (returnType : TypeExpr env scope) (distinct : (params.toList.map (·.name)).Nodup) :
    (of params returnType distinct).returnType = returnType := by
  simp only [RegionSig.returnType, of]

/-- The checked form of a well-formed raw region signature. -/
def ofWF (r : RegionSig.Raw) (h : r.WF (env.RefBefore env.size) scope) : RegionSig env scope :=
  ⟨r, h⟩

/-- `ofWF` changes no data. -/
@[simp] theorem raw_ofWF (r : RegionSig.Raw) (h : r.WF (env.RefBefore env.size) scope) :
    (ofWF r h).raw = r := rfl

/-- Reinterpret against a larger environment. -/
public def ofSubset {s t : Env α} (h : s ⊆ t) (r : RegionSig s scope) :
    RegionSig t scope :=
  ⟨r.raw,
   r.wf.mono fun _ _ hr => (Env.refBefore_of_subset h hr).mono (Env.size_le_of_subset h)⟩

/-- Reinterpreting changes no data. -/
@[simp] theorem raw_ofSubset {s t : Env α} (h : s ⊆ t) (r : RegionSig s scope) :
    (r.ofSubset h).raw = r.raw := rfl

/-- Reinterpreting reinterprets each parameter. -/
@[simp] public theorem params_ofSubset {s t : Env α} (h : s ⊆ t) (r : RegionSig s scope) :
    (r.ofSubset h).params = r.params.map (fun p => ⟨p.name, p.type.ofSubset h⟩) := by
  apply Array.ext
  · simp [RegionSig.params, ofSubset]
  · intro i _ _
    simp [RegionSig.params, ofSubset, TypeExpr.ofSubset]

/-- Reinterpreting reinterprets the return type. -/
@[simp] public theorem returnType_ofSubset {s t : Env α} (h : s ⊆ t) (r : RegionSig s scope) :
    (r.ofSubset h).returnType = r.returnType.ofSubset h := by
  simp only [RegionSig.returnType, ofSubset, TypeExpr.ofSubset]

/-- Region signatures with the same raw data are equal. -/
theorem eq_of_raw_eq {a b : RegionSig env scope} (h : a.raw = b.raw) : a = b := by
  obtain ⟨ra, wa⟩ := a
  obtain ⟨rb, wb⟩ := b
  simp only at h
  subst h
  rfl

/-- Reinterpreting `of` reinterprets its parameter types and its return type. -/
@[simp] public theorem ofSubset_of {s t : Env α} (h : s ⊆ t)
    (params : Array (Param (TypeExpr s scope))) (returnType : TypeExpr s scope)
    (distinct : (params.toList.map (·.name)).Nodup) :
    (of params returnType distinct).ofSubset h =
      of (params.map fun p => ⟨p.name, p.type.ofSubset h⟩) (returnType.ofSubset h)
        (by simpa [Function.comp_def] using distinct) :=
  eq_of_raw_eq (by
    simp [of, ofSubset, Array.map_map, Function.comp_def, TypeExpr.expr_ofSubset])

/-- Two region signatures built by `of` are equal when their parameters and return types
are. -/
@[simp] public theorem of_eq_of_iff {ps₁ ps₂ : Array (Param (TypeExpr env scope))}
    {r₁ r₂ : TypeExpr env scope} {d₁ : (ps₁.toList.map (·.name)).Nodup}
    {d₂ : (ps₂.toList.map (·.name)).Nodup} :
    of ps₁ r₁ d₁ = of ps₂ r₂ d₂ ↔ ps₁ = ps₂ ∧ r₁ = r₂ := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg RegionSig.params h,
      by simpa using congrArg RegionSig.returnType h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

end RegionSig

/-! ## Instruction signatures, checked -/

/-- An instruction declaration without its name, with every type expression checked against
`env`. -/
public structure InsnSig (env : Env α) where
  /-- The declaration's annotation.  It is part of the signature an `InsnRef` resolves to. -/
  ann : α
  /-- The type variables the signature binds, by de Bruijn level: `.var i` is
  `typeParams[i]`. -/
  typeParams : Array String := #[]
  -- Stored, so that operand types at scope `0` fix it and the defaults can fire.
  /-- How many type variables the signature binds: the scope its type expressions are
  written in. -/
  typeArgc : Nat := typeParams.size
  argTypes : Array (Param (TypeExpr env typeArgc))
  /-- The trailing variadic operands, if the instruction takes any: their name and the type
  of each. -/
  variadic : Option (Param (TypeExpr env typeArgc)) := none
  /-- What the instruction returns, or `none` if it ends its block: a terminal instruction
  never falls through and produces no result. -/
  returnType : Option (TypeExpr env typeArgc)
  /-- The regions the instruction takes, each named and with its own signature under the
  instruction's type variables. -/
  regions : Array (Param (RegionSig env typeArgc)) := #[]
  /-- The successors the instruction may transfer to, each named and with the types of the
  values it passes, under the instruction's type variables.  A use site supplies one block
  per successor, in this order. -/
  succs : Array (Param (Array (TypeExpr env typeArgc))) := #[]
  /-- One name per type variable. -/
  size_typeParams : typeParams.size = typeArgc := by rfl
  -- Written out, not via `InsnDecl.Raw.paramNames`, so the default `decide` reduces.
  /-- No name is bound twice among the type parameters, arguments, variadic, regions and
  successors. -/
  distinct : (typeParams.toList ++ argTypes.toList.map (·.name) ++
    (variadic.map (·.name)).toList ++ regions.toList.map (·.name) ++
    succs.toList.map (·.name)).Nodup := by decide

namespace InsnSig

/-- Whether the instruction ends its block: it has no return type. -/
@[expose, reducible] public def terminal {env : Env α} (s : InsnSig env) : Bool :=
  s.returnType.isNone

/-- The declaration this signature describes, under `name`, marked as the constructor at
`kind`, an ordinary instruction unless it says otherwise. -/
def decl {env : Env α} (s : InsnSig env) (name : Name) (kind : InsnKind := .decl) :
    InsnDecl.Raw α where
  ann := s.ann
  name := name
  typeParams := s.typeParams
  argTypes := s.argTypes.map (fun p => ⟨p.name, p.type.expr⟩)
  variadic := s.variadic.map (fun p => ⟨p.name, p.type.expr⟩)
  returnType := s.returnType.map (·.expr)
  regions := s.regions.map (fun p => ⟨p.name, p.type.raw⟩)
  succs := s.succs.map (fun p => ⟨p.name, p.type.map (·.expr)⟩)
  kind := kind

/-- The erased declaration is well formed in `env`. -/
theorem wf {env : Env α} (s : InsnSig env) (name : Name) (kind : InsnKind := .decl) :
    InsnDecl.Raw.WF (env.RefBefore env.size) (s.decl name kind) := by
  obtain ⟨ann, typeParams, _, argTypes, variadic, returnType, regions, succs, rfl,
    distinct⟩ := s
  refine InsnDecl.Raw.wf_mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [decl, Array.mem_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    simpa [decl] using q.type.wf
  · intro v hv
    simp only [decl, Option.mem_def, Option.map_eq_some_iff] at hv
    obtain ⟨q, -, rfl⟩ := hv
    exact q.type.wf
  · intro t ht
    simp only [decl, Option.mem_def, Option.map_eq_some_iff] at ht
    obtain ⟨u, -, rfl⟩ := ht
    exact u.wf
  · intro r hr
    simp only [decl, Array.mem_map] at hr
    obtain ⟨q, -, rfl⟩ := hr
    exact q.type.wf
  · intro p hp t ht
    simp only [decl, Array.mem_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    simp only [Array.mem_map] at ht
    obtain ⟨u, -, rfl⟩ := ht
    exact u.wf
  · simpa [decl, InsnDecl.Raw.paramNames, Function.comp_def] using distinct

/-- The checked form of a well-formed raw declaration. -/
def ofWF {env : Env α} (d : InsnDecl.Raw α)
    (h : InsnDecl.Raw.WF (env.RefBefore env.size) d) : InsnSig env where
  ann := d.ann
  typeParams := d.typeParams
  argTypes := d.argTypes.attach.map fun p =>
    ⟨p.val.name, ⟨p.val.type, InsnDecl.Raw.wf_argTypes h p.val p.property⟩⟩
  variadic := d.variadic.attach.map fun v =>
    ⟨v.val.name, ⟨v.val.type, InsnDecl.Raw.wf_variadic h v.val (Option.mem_def.mpr v.property)⟩⟩
  returnType := d.returnType.attach.map fun t =>
    ⟨t.val, InsnDecl.Raw.wf_returnType h t.val (Option.mem_def.mpr t.property)⟩
  regions := d.regions.attach.map fun r =>
    ⟨r.val.name, RegionSig.ofWF r.val.type (InsnDecl.Raw.wf_regions h r.val r.property)⟩
  succs := d.succs.attach.map fun s =>
    ⟨s.val.name, s.val.type.attach.map fun t =>
      ⟨t.val, InsnDecl.Raw.wf_succs h s.val s.property t.val t.property⟩⟩
  distinct := by
    simpa [InsnDecl.Raw.paramNames, Function.comp_def, Array.map_attach_eq_pmap,
      List.map_pmap, List.pmap_eq_map]
      using InsnDecl.Raw.wf_paramNames h

/-- Erasing `ofWF` gives back the declaration. -/
theorem decl_ofWF {env : Env α} (d : InsnDecl.Raw α)
    (h : InsnDecl.Raw.WF (env.RefBefore env.size) d) :
    (ofWF d h).decl d.name d.kind = d := by
  simp [decl, ofWF]

/-- `decl_ofWF` at any name equal to the declaration's own. -/
theorem decl_ofWF_of_name {env : Env α} {d : InsnDecl.Raw α} {n : Name}
    (h : InsnDecl.Raw.WF (env.RefBefore env.size) d) (hn : d.name = n) :
    (ofWF d h).decl n d.kind = d := by
  subst hn; exact decl_ofWF d h

/-- Reinterpret against a larger environment. -/
@[expose] public def ofSubset {s t : Env α} (h : s ⊆ t) (i : InsnSig s) : InsnSig t where
  ann := i.ann
  typeParams := i.typeParams
  typeArgc := i.typeArgc
  argTypes := i.argTypes.map (fun p => ⟨p.name, p.type.ofSubset h⟩)
  variadic := i.variadic.map (fun p => ⟨p.name, p.type.ofSubset h⟩)
  returnType := i.returnType.map (·.ofSubset h)
  regions := i.regions.map (fun p => ⟨p.name, p.type.ofSubset h⟩)
  succs := i.succs.map (fun p => ⟨p.name, p.type.map (·.ofSubset h)⟩)
  size_typeParams := i.size_typeParams
  distinct := by simpa [Function.comp_def] using i.distinct

/-- Reinterpreting changes no data. -/
theorem decl_ofSubset {s t : Env α} (h : s ⊆ t) (i : InsnSig s) (name : Name)
    (kind : InsnKind := .decl) :
    (i.ofSubset h).decl name kind = i.decl name kind := by
  simp [decl, ofSubset, Array.map_map, Function.comp_def, TypeExpr.expr_ofSubset]

/-- A declaration is named by the name it was erased under. -/
theorem name_decl {env : Env α} (i : InsnSig env) (name : Name)
    (kind : InsnKind := .decl) : (i.decl name kind).name = name := by
  simp [decl]

/-- A signature is determined by the declaration it erases to. -/
theorem eq_of_decl_eq {env : Env α} {s₁ s₂ : InsnSig env} {n : Name} {k : InsnKind}
    (h : s₁.decl n k = s₂.decl n k) : s₁ = s₂ := by
  obtain ⟨ann₁, tp₁, _, args₁, var₁, ret₁, reg₁, succ₁, rfl, d₁⟩ := s₁
  obtain ⟨ann₂, tp₂, _, args₂, var₂, ret₂, reg₂, succ₂, rfl, d₂⟩ := s₂
  simp only [decl, InsnDecl.Raw.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hargs, hvar, hret, hreg, hsucc, -⟩ := h
  have hp : ∀ {n : Nat} {a b : Param (TypeExpr env n)}, a.name = b.name →
      a.type.expr = b.type.expr → a = b := by
    intro n a b h1 h2
    obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b
    simp only at h1 h2
    rw [h1, TypeExpr.eq_iff_expr_eq.mpr h2]
  have hargs' : args₁ = args₂ := by
    apply Array.ext (by simpa using congrArg Array.size hargs)
    intro k h1 h2
    have := congrArg (·[k]?) hargs
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq, Param.mk.injEq] at this
    exact hp this.1 this.2
  have hvar' : var₁ = var₂ := by
    cases var₁ <;> cases var₂ <;> simp only [Option.map_none, Option.map_some,
      Option.some.injEq, Param.mk.injEq, reduceCtorEq] at hvar ⊢
    exact hp hvar.1 hvar.2
  have hret' : ret₁ = ret₂ := by
    cases ret₁ <;> cases ret₂ <;> simp only [Option.map_none, Option.map_some,
      Option.some.injEq, reduceCtorEq] at hret ⊢
    exact TypeExpr.eq_iff_expr_eq.mpr hret
  have hreg' : reg₁ = reg₂ := by
    apply Array.ext (by simpa using congrArg Array.size hreg)
    intro k h1 h2
    have := congrArg (·[k]?) hreg
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq, Param.mk.injEq] at this
    generalize reg₁[k] = a at this ⊢
    generalize reg₂[k] = b at this ⊢
    obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b
    simp only at this
    rw [this.1, RegionSig.eq_of_raw_eq this.2]
  have hsucc' : succ₁ = succ₂ := by
    apply Array.ext (by simpa using congrArg Array.size hsucc)
    intro k h1 h2
    have := congrArg (·[k]?) hsucc
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h2, Option.map_some, Option.some.injEq, Param.mk.injEq] at this
    generalize succ₁[k] = a at this ⊢
    generalize succ₂[k] = b at this ⊢
    obtain ⟨_, ts₁⟩ := a; obtain ⟨_, ts₂⟩ := b
    simp only at this
    rw [this.1]
    congr 1
    apply Array.ext (by simpa using congrArg Array.size this.2)
    intro l g1 g2
    have := congrArg (·[l]?) this.2
    simp only [Array.getElem?_map, Array.getElem?_eq_getElem g1,
      Array.getElem?_eq_getElem g2, Option.map_some, Option.some.injEq] at this
    exact TypeExpr.eq_iff_expr_eq.mpr this
  subst hargs' hvar' hret' hreg' hsucc'
  rfl

/-- Two signatures are equal when everything they declare stands for the same raw data: the
same annotation, type parameters, argument and variadic names and types, return type (or
its absence), regions and successors.  `simp` proves these for a signature written
differently, such as one `addData` derives. -/
public theorem ext_toRaw {env : Env α} {s₁ s₂ : InsnSig env} (hann : s₁.ann = s₂.ann)
    (htp : s₁.typeParams = s₂.typeParams)
    (hargs : s₁.argTypes.map (fun p => (p.name, p.type.toRaw)) =
      s₂.argTypes.map (fun p => (p.name, p.type.toRaw)))
    (hvar : s₁.variadic.map (fun p => (p.name, p.type.toRaw)) =
      s₂.variadic.map (fun p => (p.name, p.type.toRaw)))
    (hret : s₁.returnType.map (·.toRaw) = s₂.returnType.map (·.toRaw))
    (hregions : s₁.regions.map (fun p => (p.name,
        p.type.params.map (fun q => (q.name, q.type.toRaw)), p.type.returnType.toRaw)) =
      s₂.regions.map (fun p => (p.name,
        p.type.params.map (fun q => (q.name, q.type.toRaw)), p.type.returnType.toRaw)))
    (hsuccs : s₁.succs.map (fun p => (p.name, p.type.map (·.toRaw))) =
      s₂.succs.map (fun p => (p.name, p.type.map (·.toRaw)))) : s₁ = s₂ := by
  simp only [TypeExpr.toRaw_eq_expr] at hargs hvar hret hregions hsuccs
  apply eq_of_decl_eq (n := .base) (k := .decl)
  -- each field of the erasure is the corresponding hypothesis, re-paired
  have hraw : ∀ {scope : Nat},
      (fun p : Param (RegionSig env scope) => (⟨p.name, p.type.raw⟩ : Param RegionSig.Raw)) =
        fun x => ⟨x.name, ⟨x.type.params.map (fun y => ⟨y.name, y.type.expr⟩),
          x.type.returnType.expr⟩⟩ := by
    intro scope
    funext p
    rw [RegionSig.map_params]
    rfl
  have hargs' := congrArg (Array.map (fun x => (⟨x.1, x.2⟩ : Param TypeExpr.Raw))) hargs
  have hregions' := congrArg (Array.map (fun x => (⟨x.1,
    ⟨x.2.1.map (fun y => (⟨y.1, y.2⟩ : Param TypeExpr.Raw)), x.2.2⟩⟩ : Param RegionSig.Raw)))
    hregions
  have hvar' := congrArg (Option.map (fun x => (⟨x.1, x.2⟩ : Param TypeExpr.Raw))) hvar
  have hsuccs' :=
    congrArg (Array.map (fun x => (⟨x.1, x.2⟩ : Param (Array TypeExpr.Raw)))) hsuccs
  simp only [Array.map_map, Option.map_map, Function.comp_def] at hargs' hvar' hregions' hsuccs'
  simp only [decl, InsnDecl.Raw.mk.injEq, and_true, true_and]
  refine ⟨hann, htp, hargs', hvar', hret, ?_, hsuccs'⟩
  rw [hraw, hraw]
  exact hregions'

/-- The operand types an operation demands at these type arguments: one per declared
parameter, then the variadic's type for each trailing operand.  `none` when there are too few
operands, or too many and no variadic. -/
@[expose] public def operandTypes? {env : Env α} (isig : InsnSig env)
    (typeArgs : Vector (TypeExpr env 0) isig.typeArgc) (argc : Nat) :
    Option (Array (TypeExpr env 0)) :=
  let fixed := isig.argTypes.map (fun p => p.type.instantiate typeArgs)
  if argc = fixed.size then
    some fixed
  else
    match isig.variadic with
    | some v =>
      if fixed.size ≤ argc then
        some (fixed ++ Array.replicate (argc - fixed.size) (v.type.instantiate typeArgs))
      else
        none
    | none => none

end InsnSig

/-! ## Declarations, checked

* `Env.ResolvesInsn`, `InsnRef`: a reference to an instruction declaration, a datatype's
  constructor included.
* `InsnRef.cast`: the same reference, at an equal signature.
* `InsnRef.ctorAddr?`: which constructor the instruction is, if it is one.
* `Decl`: a declaration of a signature, as a type or instruction reference. -/

/-- `name` is declared in `s` as the instruction with signature `isig`, of whichever kind. -/
public def Env.ResolvesInsn (s : Env α) (name : Name) (isig : InsnSig s) : Prop :=
  ∃ k, s.Resolves name (.insn (isig.decl name k))

/-- A reference to an instruction of `env` with signature `isig`: the name
resolves, and what it resolves to is exactly that signature's declaration. -/
public structure InsnRef (env : Env α) (isig : InsnSig env) where
  name : Name
  resolves : env.ResolvesInsn name isig

/-- Carry an instruction reference into an extension. -/
public def InsnRef.ofSubset {s t : Env α} (h : s ⊆ t) {isig : InsnSig s} (r : InsnRef s isig) :
    InsnRef t (isig.ofSubset h) :=
  ⟨r.name, by
    obtain ⟨k, hc⟩ := r.resolves
    exact ⟨k, by rw [InsnSig.decl_ofSubset h isig r.name k]; exact hc.mono h⟩⟩

@[simp] public theorem name_InsnRef_ofSubset {s t : Env α} (h : s ⊆ t) {isig : InsnSig s}
    (r : InsnRef s isig) : (r.ofSubset h).name = r.name := by
  simp [InsnRef.ofSubset]

/-- The same reference, at an equal signature.  `simp` proves the equality when both are built
from `TypeExpr.app`, `TypeExpr.var`, `RegionSig.of` and `ofSubset`. -/
@[expose] public def InsnRef.cast {env : Env α} {s₁ s₂ : InsnSig env} (h : s₁ = s₂)
    (r : InsnRef env s₁) : InsnRef env s₂ :=
  ⟨r.name, h ▸ r.resolves⟩

/-- Casting keeps the name. -/
@[simp] public theorem InsnRef.name_cast {env : Env α} {s₁ s₂ : InsnSig env} (h : s₁ = s₂)
    (r : InsnRef env s₁) : (r.cast h).name = r.name := rfl

/-- Which constructor the instruction is, if it is a datatype's constructor. -/
public def InsnRef.ctorAddr? {env : Env α} {isig : InsnSig env} (r : InsnRef env isig) :
    Option CtorAddr :=
  env.ctorAddr? r.name

/-- A declaration of `env`: a reference to a type, or to an instruction, a datatype's
constructor included. -/
public inductive Decl (env : Env α) where
  | type {arity : Nat} (r : TypeRef env arity)
  | insn {isig : InsnSig env} (r : InsnRef env isig)

namespace Decl

/-- The name referred to. -/
@[expose] public def name {env : Env α} : Decl env → Name
  | .type r => r.name
  | .insn r => r.name

/-- The name of a declaration is declared. -/
theorem mem_of_decl {env : Env α} (d : Decl env) : d.name ∈ env := by
  -- Each case's resolution says the lookup succeeded, which is membership.
  have key : ∀ {n : Name} {e : Decl.Raw α}, env.raw.decls[n]? = some e → n ∈ env :=
    fun hk => Env.mem_of_resolves (Env.resolves_iff_rawGet?.mpr hk)
  cases d with
  | type r =>
    have hres := r.resolves
    unfold Env.ResolvesType Env.Raw.typeOf? at hres
    cases hx : env.raw.decls[r.name]? with
    | none => rw [hx] at hres; simp at hres
    | some e => exact key hx
  | insn r => obtain ⟨_, hc⟩ := r.resolves; exact Env.mem_of_resolves hc

/-- Carry a declaration into an extension. -/
public def ofSubset {s t : Env α} (h : s ⊆ t) : Decl s → Decl t
  | .type r => .type (r.ofSubset h)
  | .insn r => .insn (r.ofSubset h)

@[simp] public theorem name_ofSubset {s t : Env α} (h : s ⊆ t) (d : Decl s) :
    (d.ofSubset h).name = d.name := by
  cases d <;> simp [ofSubset, name]

/-- A declaration of `env` is declared in `env`. -/
public theorem mem {env : Env α} (d : Decl env) : d.name ∈ env :=
  mem_of_decl d

end Decl

namespace Env

/-! ### Typesafe lookup

* `get?`, `get`: look a declaration up by name, as a `Decl`. -/

/-- The declaration named `name`, checked. -/
public def get? (s : Env α) (name : Name) : Option (Decl s) :=
  match h : s.rawGet? name with
  | none => none
  | some (.type d) =>
    some (.type ⟨name, d, rfl, by simp [Env.ResolvesType, Env.Raw.typeOf?, Env.Raw.typeOfDecl?, show
      s.raw.decls[name]? = some (.type d) from h]⟩)
  -- A datatype head is a type reference, as a primitive is.
  | some (.dataHead g) =>
    some (.type ⟨name, g.first.toTypeDecl, rfl, by
      simp [Env.ResolvesType, Env.Raw.typeOf?, Env.Raw.typeOfDecl?, show
        s.raw.decls[name]? = some (.dataHead g) from h]⟩)
  -- A member past the head is a type too; `aliasWF` says its group has it.
  | some (.dataRest mn hd i) =>
    have hs : (s.raw.typeOf? name).isSome := isSome_typeOf?_of_dataRest h
    some (.type ⟨name, (s.raw.typeOf? name).get hs, rfl, (Option.some_get hs).symm⟩)
  -- A constructor is an instruction like any other.
  | some (.insn d) =>
    have hwf : InsnDecl.Raw.WF (s.RefBefore s.size) d :=
      Decl.Raw.wf_insn_iff.mp (declWF_of_rawGet? h)
    have hname : d.name = name := by simpa using name_of_rawGet? h
    some (.insn (isig := InsnSig.ofWF d hwf)
      ⟨name, ⟨d.kind, by rw [InsnSig.decl_ofWF_of_name hwf hname]; exact h⟩⟩)

-- Not `@[simp]`: the left-hand side, `Decl.name` of a variable, would match everywhere.
/-- A lookup answers under the name asked for. -/
public theorem name_get? {s : Env α} {n : Name} {d : Decl s} (h : s.get? n = some d) :
    d.name = n := by
  unfold get? at h
  split at h
  · exact absurd h (by simp)
  all_goals (obtain rfl : d = _ := Option.some.inj h.symm; rfl)

@[simp] public theorem isSome_get? {s : Env α} {n : Name} : (s.get? n).isSome ↔ n ∈ s := by
  constructor
  · intro hs
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hs
    have := Decl.mem_of_decl d
    rwa [name_get? hd] at this
  · intro hm
    unfold get?
    split <;> rename_i h <;> simp_all [← isSome_rawGet?]

/-- The declaration named `name`, checked, given that there is one. -/
public def get (s : Env α) (name : Name) (p : name ∈ s) : Decl s :=
  (s.get? name).get (isSome_get?.mpr p)

public theorem get?_eq_some_get {s : Env α} {n : Name} (p : n ∈ s) :
    s.get? n = some (s.get n p) :=
  (Option.some_get _).symm

/-- Add an instruction declaration under `name`. -/
public def addInsn (s : Env α) (name : Name) (isig : InsnSig s) (fresh : name ∉ s) : Env α :=
  ⟨s.raw.append (.insn (isig.decl name)) (not_mem_raw_of_not_mem (by simpa [InsnSig.name_decl] using fresh)),
   s.wf.append (d := .insn (isig.decl name))
     (not_mem_raw_of_not_mem (by simpa [InsnSig.name_decl] using fresh))
     (Decl.Raw.wf_insn_iff.mpr (isig.wf name))⟩

theorem raw_addInsn (s : Env α) (name : Name) (isig : InsnSig s) (fresh : name ∉ s) :
    (s.addInsn name isig fresh).raw =
      s.raw.append (.insn (isig.decl name)) (not_mem_raw_of_not_mem (by simpa [InsnSig.name_decl] using fresh)) := rfl

@[simp] public theorem size_addInsn (s : Env α) (name : Name) (isig : InsnSig s)
    (fresh : name ∉ s) :
    (s.addInsn name isig fresh).size = s.size + 1 := by
  simp [size, raw_addInsn, Raw.keys_append]

theorem rawGet?_addInsn (s : Env α) (name : Name) (isig : InsnSig s) (fresh : name ∉ s)
    (n : Name) :
    (s.addInsn name isig fresh).rawGet? n =
      if name == n then some (.insn (isig.decl name)) else s.rawGet? n := by
  simp [rawGet?_eq_raw, raw_addInsn, Raw.get?_append, InsnSig.name_decl]

theorem resolves_addInsn_self (s : Env α) (name : Name) (isig : InsnSig s)
    (fresh : name ∉ s) : (s.addInsn name isig fresh).Resolves name (.insn (isig.decl name)) := by
  rw [resolves_iff_rawGet?, rawGet?_addInsn]
  simp

theorem resolves_addInsn_of_ne {s : Env α} {name : Name} {isig : InsnSig s}
    {fresh : name ∉ s} {n : Name} {e : Decl.Raw α} (hne : name ≠ n) :
    (s.addInsn name isig fresh).Resolves n e ↔ s.Resolves n e := by
  rw [resolves_iff_rawGet?, resolves_iff_rawGet?, rawGet?_addInsn, if_neg (by simpa using hne)]

@[simp, grind =] public theorem mem_addInsn {s : Env α} {name : Name} {isig : InsnSig s} {fresh : name ∉ s}
    {n : Name} : n ∈ s.addInsn name isig fresh ↔ name = n ∨ n ∈ s := by
  simp [mem_iff_mem_raw, raw_addInsn, InsnSig.name_decl]

@[simp] public theorem subset_addInsn (s : Env α) (name : Name) (isig : InsnSig s)
    (fresh : name ∉ s) : s ⊆ s.addInsn name isig fresh := by
  show _ <+: _
  simp only [raw_addInsn, Raw.vals_append, Array.toList_push]
  exact List.prefix_append _ _

theorem resolvesInsn_addInsn_self (s : Env α) (name : Name) (isig : InsnSig s)
    (fresh : name ∉ s) :
    (s.addInsn name isig fresh).ResolvesInsn name
      (isig.ofSubset (subset_addInsn s name isig fresh)) :=
  ⟨.decl, by rw [InsnSig.decl_ofSubset]; exact resolves_addInsn_self s name isig fresh⟩

/-! ### Extending by evaluation, and by a batch

* `addType?`: add a type declaration, deciding its obligations.
* `addInsns?`: add a batch of instruction declarations, deciding their obligations. -/

-- One batch, not repeated `add?`: a group's head is well formed only once its aliases follow.
/-- Add the declarations as one batch.  `none` if their names are not distinct and fresh, or
one is not well formed in the environment that has the whole batch. -/
def addAll? (s : Env α) : Array (Decl.Raw α) → Option (Env α)
  | ⟨l⟩ =>
    if fresh : s.raw.FreshList l then
      if h : Raw.checkFrom (s.raw.appendList l fresh) s.size l = true then
        some (s.appendBatch ⟨l⟩ fresh (s.wf.appendList l fresh h))
      else none
    else none

theorem addAll?_eq_some {s t : Env α} {ds : Array (Decl.Raw α)} (h : s.addAll? ds = some t) :
    ∃ fresh hc, t = s.appendBatch ds fresh hc := by
  obtain ⟨l⟩ := ds
  rw [addAll?] at h
  split at h
  · split at h
    · exact ⟨_, _, (Option.some.inj h).symm⟩
    · simp at h
  · simp at h

theorem subset_of_addAll?_eq_some {s t : Env α} {ds : Array (Decl.Raw α)}
    (h : s.addAll? ds = some t) : s ⊆ t := by
  obtain ⟨_, _, rfl⟩ := addAll?_eq_some h
  exact subset_appendBatch

/-- Every declaration of a batch resolves in the result under its own name. -/
theorem resolves_of_addAll?_eq_some {s t : Env α} (ds : Array (Decl.Raw α))
    (h : s.addAll? ds = some t) (i : Nat) (d : Decl.Raw α) (hi : ds[i]? = some d) :
    t.Resolves d.name d := by
  obtain ⟨_, _, rfl⟩ := addAll?_eq_some h
  exact resolves_appendBatch hi

/-- What a successful batch declares: every name in it, and whatever was already there. -/
theorem mem_addAll?_eq_some {s t : Env α} {ds : Array (Decl.Raw α)}
    (h : s.addAll? ds = some t) {n : Name} :
    n ∈ t ↔ n ∈ ds.map (·.name) ∨ n ∈ s := by
  obtain ⟨_, _, rfl⟩ := addAll?_eq_some h
  rw [mem_appendBatch, Array.mem_map]
  exact or_comm

/-- Add a type declaration, deciding freshness. -/
public def addType? (s : Env α) (d : TypeDecl α) : Option (Env α) := s.add? (.type d)

public theorem subset_of_addType?_eq_some {s t : Env α} {d : TypeDecl α}
    (h : s.addType? d = some t) : s ⊆ t :=
  subset_of_add?_eq_some h

/-- The name a type declaration adds. -/
public theorem mem_addType?_eq_some {s t : Env α} {d : TypeDecl α}
    (h : s.addType? d = some t) {n : Name} : n ∈ t ↔ n = d.name ∨ n ∈ s :=
  mem_add?_eq_some h

/-- What the name of a successfully added type declaration resolves to. -/
public theorem resolvesType_of_addType?_eq_some {s t : Env α} {d : TypeDecl α}
    (h : s.addType? d = some t) : t.ResolvesType d.name d := by
  have hr := resolves_iff_rawGet?.mp (resolves_of_add?_eq_some h)
  simp only [Decl.Raw.name_type] at hr
  unfold ResolvesType Env.Raw.typeOf?
  rw [show t.raw.decls[d.name]? = some (.type d) from hr]
  rfl

/-- Add a mutual group of datatypes.  `none` if one of its names is taken, or the group is
not an admissible definition. -/
def addData? (s : Env α) (g : DataGroup α TypeExpr.Raw) : Option (Env α) :=
  s.addAll? g.decls

theorem subset_of_addData?_eq_some {s t : Env α} {g : DataGroup α TypeExpr.Raw}
    (h : s.addData? g = some t) : s ⊆ t :=
  subset_of_addAll?_eq_some h

/-- The names a group adds: its head, its members, its constructors and its case
instructions. -/
theorem mem_addData?_eq_some {s t : Env α} {g : DataGroup α TypeExpr.Raw}
    (h : s.addData? g = some t) {n : Name} : n ∈ t ↔ n ∈ g.names ∨ n ∈ s := by
  rw [mem_addAll?_eq_some h, DataGroup.decls_names]

/-- What the group's head resolves to: the type its first member declares. -/
theorem resolvesType_of_addData?_eq_some {s t : Env α} {g : DataGroup α TypeExpr.Raw}
    (h : s.addData? g = some t) :
    t.ResolvesType g.first.name g.first.toTypeDecl := by
  unfold addData? at h
  have hr := resolves_iff_rawGet?.mp
    (resolves_of_addAll?_eq_some _ h 0 (.dataHead g)
      (by rw [← Array.getElem?_toList]; exact DataGroup.decls_getElem?_zero g))
  simp only [Decl.Raw.name_dataHead] at hr
  unfold ResolvesType Env.Raw.typeOf?
  rw [show t.raw.decls[g.first.name]? = some (.dataHead g) from hr]
  rfl

/-- Add a batch of instruction declarations.  `none` if their names are not distinct and
fresh in `s`, or one fails the checker. -/
public def addInsns? (s : Env α) (ops : Array (Name × InsnSig s)) : Option (Env α) :=
  s.addAll? (ops.map fun p => .insn (p.2.decl p.1))

public theorem subset_of_addInsns?_eq_some {s t : Env α} {ops : Array (Name × InsnSig s)}
    (h : s.addInsns? ops = some t) : s ⊆ t :=
  subset_of_addAll?_eq_some h

/-- The names a batch of operations adds. -/
public theorem mem_addInsns?_eq_some {s t : Env α} {ops : Array (Name × InsnSig s)}
    (h : s.addInsns? ops = some t) {n : Name} :
    n ∈ t ↔ n ∈ ops.map (·.1) ∨ n ∈ s := by
  rw [mem_addAll?_eq_some h]
  simp [InsnSig.name_decl]

/-! ### A reference per operation of a batch

* `resolvesInsn_of_addInsns?_eq_some`: each operation of an accepted batch resolves. -/

-- Read off the construction: deciding it would need equality on annotations.

/-- Each operation of a batch `addInsns?` accepted resolves under its own name, with its own
signature lifted into the result. -/
public theorem resolvesInsn_of_addInsns?_eq_some {s t : Env α}
    {ops : Array (Name × InsnSig s)} (h : s.addInsns? ops = some t) (i : Nat)
    (hi : i < ops.size) :
    t.ResolvesInsn ops[i].1 (ops[i].2.ofSubset (subset_of_addInsns?_eq_some h)) := by
  have hget : (ops.map fun p => Decl.Raw.insn (p.2.decl p.1))[i]? =
      some (.insn (ops[i].2.decl ops[i].1)) := by
    rw [Array.getElem?_map, Array.getElem?_eq_getElem hi]
    rfl
  have := resolves_of_addAll?_eq_some _ h i _ hget
  rw [Decl.Raw.name_insn, InsnSig.name_decl] at this
  exact ⟨.decl, by rw [InsnSig.decl_ofSubset]; exact this⟩

/-! ### A batch of operations, total

* `addInsns`: add a batch of instruction declarations.
* `InsnRef.ofAddInsns`: the reference to each operation of the batch. -/

/-- The declarations a batch of operations stands for, in order. -/
def insnDecls {s : Env α} (ops : Array (Name × InsnSig s)) : Array (InsnDecl.Raw α) :=
  ops.map fun p => p.2.decl p.1

theorem map_name_insnDecls {s : Env α} (ops : Array (Name × InsnSig s)) :
    ((insnDecls ops).map Decl.Raw.insn).map (fun d : Decl.Raw α => d.name) =
      ops.map (fun p : Name × InsnSig s => p.1) := by
  simp [insnDecls, Function.comp_def, InsnSig.name_decl]

/-- Add a batch of instruction declarations. -/
public def addInsns (s : Env α) (ops : Array (Name × InsnSig s))
    (fresh : s.FreshNames (ops.map (·.1))) : Env α :=
  s.appendBatch ((insnDecls ops).map .insn)
    (freshList_of_freshNames (by rw [map_name_insnDecls]; exact fresh))
    (s.wf.appendList_insns _ _ fun d hd => by
      obtain ⟨p, -, rfl⟩ := Array.mem_map.mp hd
      exact ⟨p.2.wf p.1, rfl⟩)

section
variable {s : Env α} {ops : Array (Name × InsnSig s)} {fresh : s.FreshNames (ops.map (·.1))}

@[simp] public theorem subset_addInsns : s ⊆ s.addInsns ops fresh := subset_appendBatch

/-- The names a batch of operations adds. -/
@[simp, grind =] public theorem mem_addInsns {n : Name} :
    n ∈ s.addInsns ops fresh ↔ n ∈ ops.map (·.1) ∨ n ∈ s := by
  have := Array.mem_map (f := fun d : Decl.Raw α => d.name)
    (xs := (insnDecls ops).map Decl.Raw.insn) (b := n)
  rw [map_name_insnDecls] at this
  rw [addInsns, mem_appendBatch, ← this, or_comm]

/-- Operation `i` of the batch resolves under its own name, with its own signature lifted
into the result. -/
public theorem resolvesInsn_addInsns (i : Nat) (hi : i < ops.size := by decide) :
    (s.addInsns ops fresh).ResolvesInsn ops[i].1 (ops[i].2.ofSubset subset_addInsns) := by
  have hget : ((insnDecls ops).map Decl.Raw.insn)[i]? =
      some (.insn (ops[i].2.decl ops[i].1)) := by
    rw [insnDecls, Array.map_map, Array.getElem?_map, Array.getElem?_eq_getElem hi]
    rfl
  have : (s.addInsns ops fresh).Resolves _ _ := resolves_appendBatch hget
  rw [Decl.Raw.name_insn, InsnSig.name_decl] at this
  exact ⟨.decl, by rw [InsnSig.decl_ofSubset]; exact this⟩

end

end Env

/-- The reference to operation `i` of a batch `addInsns` added. -/
@[expose] public def InsnRef.ofAddInsns {s : Env α} (ops : Array (Name × InsnSig s))
    (fresh : s.FreshNames (ops.map (·.1))) (i : Nat) (hi : i < ops.size := by decide) :
    InsnRef (s.addInsns ops fresh) (ops[i].2.ofSubset Env.subset_addInsns) :=
  ⟨ops[i].1, Env.resolvesInsn_addInsns i hi⟩

/-- The reference to the type declaration `addType` just added. -/
public def TypeRef.ofAddType (s : Env α) (d : TypeDecl α) (fresh : d.name ∉ s)
    (distinct : d.paramNames.Nodup := by decide) :
    TypeRef (s.addType d fresh distinct) d.arity :=
  ⟨d.name, d, rfl, Env.resolvesType_addType_self s d fresh⟩

@[simp] public theorem TypeRef.name_ofAddType (s : Env α) (d : TypeDecl α)
    (fresh : d.name ∉ s) (distinct : d.paramNames.Nodup) :
    (TypeRef.ofAddType s d fresh distinct).name = d.name := by
  simp [TypeRef.ofAddType]

@[simp] public theorem TypeRef.decl_ofAddType (s : Env α) (d : TypeDecl α)
    (fresh : d.name ∉ s) (distinct : d.paramNames.Nodup) :
    (TypeRef.ofAddType s d fresh distinct).decl = d := by
  simp [TypeRef.ofAddType]

/-- The reference to the instruction declaration `addInsn` just added. -/
public def InsnRef.ofAddInsn (s : Env α) (name : Name) (isig : InsnSig s) (fresh : name ∉ s) :
    InsnRef (s.addInsn name isig fresh) (isig.ofSubset (Env.subset_addInsn s name isig fresh)) :=
  ⟨name, Env.resolvesInsn_addInsn_self s name isig fresh⟩

@[simp] public theorem InsnRef.name_ofAddInsn (s : Env α) (name : Name) (isig : InsnSig s)
    (fresh : name ∉ s) : (InsnRef.ofAddInsn s name isig fresh).name = name := by
  simp [InsnRef.ofAddInsn]

/-! ## A datatype's constructors, as instructions

`addData` declares one instruction per constructor, its signature derived from the group:

* `Env.ctorSig`: constructor `j` of member `i`'s signature.  Its type parameters are the
  datatype's, its arguments the payload, and it returns the datatype at its own parameters.
* `InsnRef.ofAddData`: the reference to it.

The lemmas describe the signature through `TypeExpr.toRaw`: with `InsnSig.ext_toRaw`, `simp`
proves a signature written out by hand equal to it. -/

namespace Env

section ctor

variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
  {adm : admissible hdr ctors = true}

/-- Member `i`, from its header entry and its constructor list. -/
def memberAt (adm : admissible hdr ctors = true) (i : Nat) (hi : i < ctors.size) :
    DatatypeDecl α TypeExpr.Raw :=
  DatatypeDecl.mapTy DataTy.toRaw
    { ann := (hdr[i]'(size_of_admissible adm ▸ hi)).ann,
      name := (hdr[i]'(size_of_admissible adm ▸ hi)).name,
      params := (hdr[i]'(size_of_admissible adm ▸ hi)).params, ctors := ctors[i] }

/-- Constructor `j` of member `i`'s instruction, as the group declares it. -/
def ctorInsnDecl (adm : admissible hdr ctors = true) (i j : Nat) (hi : i < ctors.size)
    (hj : j < ctors[i].size) : InsnDecl.Raw α :=
  (dataGroup hdr ctors adm).ctorDecl i (memberAt adm i hi) j
    (Ctor.mapTy DataTy.toRaw ctors[i][j])

/-- The group `addData` stores gives constructor `j` of member `i` the instruction
`ctorInsnDecl` describes. -/
theorem ctorInsn?_dataGroup {i j : Nat} (hi : i < ctors.size) (hj : j < ctors[i].size) :
    (dataGroup hdr ctors adm).ctorInsn? i j = some (ctorInsnDecl adm i j hi hj) := by
  have hih : i < hdr.size := size_of_admissible adm ▸ hi
  have hm : (members hdr ctors)[i]? =
      some ⟨hdr[i].ann, hdr[i].name, hdr[i].params, ctors[i]⟩ := by
    rw [← Array.getElem?_toList, toList_members]
    exact getElem?_membersOf (by simp [hih]) (by simp [hi])
  simp [DataGroup.ctorInsn?, DataGroup.member?, dataGroup, Array.getElem?_map, hm,
    DatatypeDecl.mapTy, ctorInsnDecl, memberAt, Array.getElem?_eq_getElem hj]

/-- `addData` stores each constructor's instruction under the constructor's name. -/
theorem rawGet?_ctor {i j : Nat} (hi : i < ctors.size) (hj : j < ctors[i].size) :
    (s.addData hdr fresh ctors cfresh adm).rawGet? (ctorInsnDecl adm i j hi hj).name =
      some (.insn (ctorInsnDecl adm i j hi hj)) := by
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp
    (DataGroup.mem_decls_of_ctorInsn? (ctorInsn?_dataGroup (adm := adm) hi hj))
  exact resolves_appendBatch hk

end ctor

/-- The signature `addData` derives for constructor `j` of member `i`: the member's type
parameters, by name; the constructor's payload as its arguments; and the member applied to its
own parameters as its result.  No variadic, regions or successors, and not terminal. -/
public def ctorSig {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
    {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
    {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
    {adm : admissible hdr ctors = true} (i j : Nat) (hi : i < ctors.size := by decide)
    (hj : j < ctors[i].size := by decide) : InsnSig (s.addData hdr fresh ctors cfresh adm) :=
  InsnSig.ofWF (ctorInsnDecl adm i j hi hj)
    (Decl.Raw.wf_insn_iff.mp (declWF_of_rawGet? (rawGet?_ctor hi hj)))

section ctorSig

variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
  {adm : admissible hdr ctors = true} {i j : Nat} {hi : i < ctors.size} {hj : j < ctors[i].size}

/-- A constructor's instruction is annotated as the constructor is. -/
@[simp] public theorem ann_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).ann = ctors[i][j].ann := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, Ctor.mapTy]

/-- Its type parameters are its datatype's, by name and in order. -/
@[simp] public theorem typeParams_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).typeParams =
      (hdr[i]'(size_of_admissible adm ▸ hi)).params.map (·.name) := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, memberAt, DatatypeDecl.mapTy]

/-- Its arguments are the constructor's payload. -/
@[simp] public theorem argTypes_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).argTypes.map
        (fun p => (p.name, p.type.toRaw)) =
      ctors[i][j].args.map (fun p => (p.name, p.type.toRaw)) := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, Ctor.mapTy, Param.mapTy,
    Array.map_attach_eq_pmap, Array.map_pmap, Function.comp_def, TypeExpr.toRaw_eq_expr]

/-- It takes no variadic arguments. -/
@[simp] public theorem variadic_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).variadic = none := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl]

/-- It returns its datatype, applied to its own parameters. -/
@[simp] public theorem returnType_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).returnType.map TypeExpr.toRaw =
      some (TypeExpr.Raw.app (hdr[i]'(size_of_admissible adm ▸ hi)).name
        (TypeExpr.Raw.vars (hdr[i]'(size_of_admissible adm ▸ hi)).arity)) := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, memberAt, DatatypeDecl.mapTy,
    DatatypeDecl.arity, TypeDecl.arity, TypeExpr.toRaw_eq_expr]

/-- It takes no regions. -/
@[simp] public theorem regions_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).regions = #[] := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl]

/-- It has no successors. -/
@[simp] public theorem succs_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).succs = #[] := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl]

end ctorSig

end Env

/-- The reference to constructor `j` of member `i` of the group `addData` added: an
instruction, with the signature `addData` derived for it. -/
@[expose] public def InsnRef.ofAddData {s : Env α} {hdr : Array (TypeDecl α)}
    {fresh : s.FreshTypes hdr}
    {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
    {cfresh : (s.addTypes hdr fresh).FreshNames (Env.ctorNames ctors ++ Env.caseNames hdr)}
    {adm : Env.admissible hdr ctors = true} (i j : Nat) (hi : i < ctors.size := by decide)
    (hj : j < ctors[i].size := by decide) :
    InsnRef (s.addData hdr fresh ctors cfresh adm) (Env.ctorSig i j hi hj) :=
  ⟨ctors[i][j].name, by
    refine ⟨.ctor ⟨(hdr[0]'(Env.pos_of_admissible adm)).name, i, j⟩, ?_⟩
    have h := Env.rawGet?_ctor (cfresh := cfresh) (adm := adm) hi hj
    have hn : (Env.ctorInsnDecl adm i j hi hj).name = ctors[i][j].name := rfl
    have hc : (Env.ctorInsnDecl adm i j hi hj).kind =
        .ctor ⟨(hdr[0]'(Env.pos_of_admissible adm)).name, i, j⟩ := by
      have := Env.first_toTypeDecl_dataGroup (h := adm)
      simp only [Array.getElem?_eq_getElem (Env.pos_of_admissible adm), Option.some.injEq]
        at this
      simp [Env.ctorInsnDecl, DataGroup.ctorDecl, this, DatatypeDecl.toTypeDecl]
    rw [← hn, ← hc, Env.ctorSig, InsnSig.decl_ofWF]
    exact h⟩

section
variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {cfresh : (s.addTypes hdr fresh).FreshNames (Env.ctorNames ctors ++ Env.caseNames hdr)}
  {adm : Env.admissible hdr ctors = true} {i j : Nat} {hi : i < ctors.size}
  {hj : j < ctors[i].size}

/-- A constructor's instruction is named as the constructor is. -/
@[simp] public theorem InsnRef.name_ofAddData :
    (InsnRef.ofAddData (cfresh := cfresh) (adm := adm) i j hi hj).name = ctors[i][j].name := rfl

/-- A constructor's instruction is the `j`th constructor of the group's `i`th member. -/
public theorem InsnRef.ctorAddr?_ofAddData :
    (InsnRef.ofAddData (cfresh := cfresh) (adm := adm) i j hi hj).ctorAddr? =
      some ⟨(hdr[0]'(Env.pos_of_admissible adm)).name, i, j⟩ := by
  have h := Env.rawGet?_ctor (cfresh := cfresh) (adm := adm) hi hj
  have hn : (Env.ctorInsnDecl adm i j hi hj).name = ctors[i][j].name := rfl
  have hc0 : (Env.ctorInsnDecl adm i j hi hj).kind =
      .ctor ⟨(hdr[0]'(Env.pos_of_admissible adm)).name, i, j⟩ := by
    have := Env.first_toTypeDecl_dataGroup (h := adm)
    simp only [Array.getElem?_eq_getElem (Env.pos_of_admissible adm), Option.some.injEq]
      at this
    simp [Env.ctorInsnDecl, DataGroup.ctorDecl, this, DatatypeDecl.toTypeDecl]
  rw [hn] at h
  simp only [InsnRef.ctorAddr?, Env.ctorAddr?, Env.Raw.ctorAddr?, name_ofAddData]
  rw [show (s.addData hdr fresh ctors cfresh adm).raw.decls[ctors[i][j].name]? =
    some (.insn (Env.ctorInsnDecl adm i j hi hj)) from h]
  simp [hc0, InsnKind.ctor?]
end

/-! ## A datatype's case instructions

`addData` declares each member's case instruction `T.case`, its signature derived from the
group, so the name is claimed with the group:

* `Env.caseSig`: member `i`'s case instruction's signature.  Terminal; its type parameters are
  the datatype's; its one argument `scrutinee` is the datatype at its own parameters; it has
  one successor per constructor, in declaration order, named by the last component of the
  constructor's name and receiving its payload; and it has no return type.
* `InsnRef.ofAddDataCase`: the reference to it.

As for constructors, the lemmas describe the signature through `TypeExpr.toRaw`. -/

namespace Env

section case

variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
  {adm : admissible hdr ctors = true}

/-- Member `i`'s case instruction, as the group declares it. -/
def caseInsnDecl (adm : admissible hdr ctors = true) (i : Nat) (hi : i < ctors.size) :
    InsnDecl.Raw α :=
  (dataGroup hdr ctors adm).caseDecl i (memberAt adm i hi)

/-- The group `addData` stores gives member `i` the case instruction `caseInsnDecl`
describes. -/
theorem caseInsn?_dataGroup {i : Nat} (hi : i < ctors.size) :
    (dataGroup hdr ctors adm).caseInsn? i =
      some (caseInsnDecl adm i hi) := by
  have hih : i < hdr.size := size_of_admissible adm ▸ hi
  have hm : (members hdr ctors)[i]? =
      some ⟨hdr[i].ann, hdr[i].name, hdr[i].params, ctors[i]⟩ := by
    rw [← Array.getElem?_toList, toList_members]
    exact getElem?_membersOf (by simp [hih]) (by simp [hi])
  simp [DataGroup.caseInsn?, DataGroup.member?, dataGroup, Array.getElem?_map, hm,
    caseInsnDecl, memberAt]

/-- `addData` stores each member's case instruction under its name. -/
theorem rawGet?_case {i : Nat} (hi : i < ctors.size) :
    (s.addData hdr fresh ctors cfresh adm).rawGet? (caseInsnDecl adm i hi).name =
      some (.insn (caseInsnDecl adm i hi)) := by
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.mp
    (DataGroup.mem_decls_of_caseInsn? (caseInsn?_dataGroup (adm := adm) hi))
  exact resolves_appendBatch hk

end case

/-- The signature `addData` derives for member `i`'s case instruction: terminal; the member's
type parameters, by name; one argument `scrutinee`, the member applied to its own parameters;
one successor per constructor, in declaration order, named by the last component of the
constructor's name and receiving its payload.  No return type, variadic or regions. -/
public def caseSig {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
    {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
    {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
  {adm : admissible hdr ctors = true} (i : Nat)
    (hi : i < ctors.size := by decide) :
    InsnSig (s.addData hdr fresh ctors cfresh adm) :=
  InsnSig.ofWF (caseInsnDecl adm i hi)
    (Decl.Raw.wf_insn_iff.mp (declWF_of_rawGet? (rawGet?_case hi)))

section caseSig

variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
  {adm : admissible hdr ctors = true} {i : Nat} {hi : i < ctors.size}

/-- A case instruction is annotated as its datatype is. -/
@[simp] public theorem ann_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).ann =
      (hdr[i]'(size_of_admissible adm ▸ hi)).ann := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl, memberAt, DatatypeDecl.mapTy]

/-- Its type parameters are its datatype's, by name and in order. -/
@[simp] public theorem typeParams_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).typeParams =
      (hdr[i]'(size_of_admissible adm ▸ hi)).params.map (·.name) := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl, memberAt, DatatypeDecl.mapTy]

/-- Its one argument is the scrutinee: the datatype, applied to its own parameters. -/
@[simp] public theorem argTypes_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).argTypes.map
        (fun p => (p.name, p.type.toRaw)) =
      #[("scrutinee", .app (hdr[i]'(size_of_admissible adm ▸ hi)).name
        (TypeExpr.Raw.vars (hdr[i]'(size_of_admissible adm ▸ hi)).arity))] := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl, memberAt, DatatypeDecl.mapTy,
    DatatypeDecl.arity, TypeDecl.arity, TypeExpr.toRaw_eq_expr]

/-- It takes no variadic arguments. -/
@[simp] public theorem variadic_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).variadic = none := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl]

/-- It returns nothing: it ends its block. -/
@[simp] public theorem returnType_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).returnType = none := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl]

/-- It takes no regions. -/
@[simp] public theorem regions_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).regions = #[] := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl]

/-- Its successors are the datatype's constructors, in order, each named by the last component
of the constructor's name and receiving its payload. -/
@[simp] public theorem succs_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).succs.map
        (fun p => (p.name, p.type.map (·.toRaw))) =
      ctors[i].map (fun c => (c.name.lastString, c.args.map (·.type.toRaw))) := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl, memberAt, DatatypeDecl.mapTy,
    Ctor.mapTy, Param.mapTy, Array.map_attach_eq_pmap, Array.map_pmap, Function.comp_def,
    TypeExpr.toRaw_eq_expr]

end caseSig

end Env

/-- The reference to member `i`'s case instruction of the group `addData` added, with the
signature `addData` derived for it. -/
@[expose] public def InsnRef.ofAddDataCase {s : Env α} {hdr : Array (TypeDecl α)}
    {fresh : s.FreshTypes hdr}
    {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
    {cfresh : (s.addTypes hdr fresh).FreshNames (Env.ctorNames ctors ++ Env.caseNames hdr)}
    {adm : Env.admissible hdr ctors = true} (i : Nat)
    (hi : i < ctors.size := by decide) :
    InsnRef (s.addData hdr fresh ctors cfresh adm) (Env.caseSig i hi) :=
  ⟨(hdr[i]'(Env.size_of_admissible adm ▸ hi)).name.caseName, by
    refine ⟨.case ⟨(hdr[0]'(Env.pos_of_admissible adm)).name, i⟩, ?_⟩
    have h := Env.rawGet?_case (cfresh := cfresh) (adm := adm) hi
    have hn : (Env.caseInsnDecl adm i hi).name =
        (hdr[i]'(Env.size_of_admissible adm ▸ hi)).name.caseName := rfl
    have hk : (Env.caseInsnDecl adm i hi).kind =
        .case ⟨(hdr[0]'(Env.pos_of_admissible adm)).name, i⟩ := by
      have := Env.first_toTypeDecl_dataGroup (h := adm)
      simp only [Array.getElem?_eq_getElem (Env.pos_of_admissible adm), Option.some.injEq]
        at this
      simp [Env.caseInsnDecl, DataGroup.caseDecl, this, DatatypeDecl.toTypeDecl]
    rw [← hn, ← hk, Env.caseSig, InsnSig.decl_ofWF]
    exact h⟩

/-- A case instruction is named `T.case`, for its datatype `T`. -/
@[simp] public theorem InsnRef.name_ofAddDataCase {s : Env α} {hdr : Array (TypeDecl α)}
    {fresh : s.FreshTypes hdr}
    {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
    {cfresh : (s.addTypes hdr fresh).FreshNames (Env.ctorNames ctors ++ Env.caseNames hdr)}
    {adm : Env.admissible hdr ctors = true} {i : Nat}
    {hi : i < ctors.size} :
    (InsnRef.ofAddDataCase (cfresh := cfresh) (adm := adm) i hi).name =
      (hdr[i]'(Env.size_of_admissible adm ▸ hi)).name.caseName := rfl

end Strata.Mantle
