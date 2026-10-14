/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all StrataMantle.Util.Array
import StrataMantle.Env.WF
public import StrataMantle.Util.NameMap
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

An environment's fields are private.  Clients read it through its lookups:

* `typeOf?`, `dataOf?`: the type and the datatype a name names.
* `DeclaresInsn`: the instruction a name names, as a checked signature and a kind.
* `annOf?`, `ctorAddr?`: the annotation a name is declared with, and which constructor it is.

Each has lemmas for `empty` and the `add*` operations.  The raw declarations they read are
private.

Checked forms and references carry to every environment that keeps their lookups
(`KeepsTypes`, `KeepsInsns`, `carry`); `ofSubset` carries them along an extension.  Refinement,
`t ≤ s`, is in `StrataMantle.Env.Refine`.
-/

open Strata (IndexMap)

namespace Strata.Mantle

variable {α : Type}

/-- A well-formed environment whose declarations are annotated with `α`.  The fields are
private.  `empty` and the `add*` operations are the only way to build one, and the lookups
(`typeOf?`, `dataOf?`, `DeclaresInsn`, `annOf?`, `ctorAddr?`) the way to read one. -/
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

/-- The declaration `name` names, if any. -/
protected def declOf? (env : Env α) (name : Name) : Option (Decl.Raw α) := env.raw[name]?

/-- The type `name` names, if any: a type declaration, or a datatype as the type declaration of
its member. -/
public protected def typeOf? (env : Env α) (name : Name) : Option (TypeDecl α) :=
  env.raw.typeOf? name

/-- The datatype `name` names, if any: the group that declares it, and which member of the group
it is. -/
public protected def dataOf? (env : Env α) (name : Name) :
    Option (DataGroup α TypeExpr.Raw × Nat) :=
  env.raw.dataOf? name

/-- The instruction `name` names, if any, of whichever kind. -/
protected def insnOf? (env : Env α) (name : Name) : Option (InsnDecl.Raw α) :=
  (env.declOf? name).bind Decl.Raw.asInsn

/-- A name names an instruction exactly when it is declared as one. -/
theorem insnOf?_eq_some_iff {s : Env α} {n : Name} {d : InsnDecl.Raw α} :
    s.insnOf? n = some d ↔ s.declOf? n = some (.insn d) := by
  unfold Env.insnOf?
  cases s.declOf? n with
  | none => simp
  | some e => cases e <;> simp [Decl.Raw.asInsn]

/-- The declaration data named `name`, given that there is one. -/
protected def rawGet (env : Env α) (name : Name) (p : name ∈ env) : Decl.Raw α :=
  env.raw[name]'(mem_raw_of_mem p)

/-- `name` is declared in `s` as `d`. -/
def Resolves (s : Env α) (name : Name) (d : Decl.Raw α) : Prop := s.declOf? name = some d

theorem resolves_iff_declOf? {s : Env α} {n : Name} {d : Decl.Raw α} :
    s.Resolves n d ↔ s.declOf? n = some d := Iff.rfl

/-- A name resolves to at most one declaration. -/
theorem Resolves.unique {s : Env α} {n : Name} {d e : Decl.Raw α}
    (hd : s.Resolves n d) (he : s.Resolves n e) : d = e := by
  rw [resolves_iff_declOf?] at hd he
  exact Option.some.inj (hd.symm.trans he)

/-- `declOf?` is the lookup of the underlying `Env.Raw`. -/
theorem declOf?_eq_raw (s : Env α) (n : Name) : s.declOf? n = s.raw[n]? := rfl

theorem mem_iff_mem_raw {s : Env α} {n : Name} : n ∈ s ↔ n ∈ s.raw :=
  ⟨mem_raw_of_mem, decide_eq_true⟩

/-- `name` resolves to a type declaration whose arguments have kinds `kinds`, declared before
position `i`.  A declaration at position `i` may refer only to such types. -/
public def RefBefore (s : Env α) (i : Nat) (name : Name) (kinds : Array Kind) : Prop :=
  s.raw.RefBefore i name kinds

/-- Widening the position bound keeps a reference valid. -/
public theorem RefBefore.mono {s : Env α} {i j : Nat} {name : Name} {kinds : Array Kind}
    (h : i ≤ j) (hr : s.RefBefore i name kinds) : s.RefBefore j name kinds :=
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

/-- The empty environment names nothing. -/
@[simp] theorem declOf?_empty (n : Name) : (Env.empty (α := α)).declOf? n = none := by
  simp [declOf?_eq_raw, raw_empty, Raw.get?_empty]

theorem not_resolves_empty (n : Name) (d : Decl.Raw α) :
    ¬ (Env.empty (α := α)).Resolves n d := by
  rw [resolves_iff_declOf?, declOf?_empty]
  simp

theorem mem_of_resolves {s : Env α} {n : Name} {d : Decl.Raw α}
    (h : s.Resolves n d) : n ∈ s := by
  rw [resolves_iff_declOf?] at h
  rw [declOf?_eq_raw] at h
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

/-- What a name names after `addType`. -/
theorem declOf?_addType (n : Name) :
    (s.addType d fresh distinct).declOf? n =
      if d.name == n then some (.type d) else s.declOf? n := by
  simp [declOf?_eq_raw, raw_addType, Raw.get?_append]

/-- The added type resolves under its own name. -/
theorem resolves_addType_self : (s.addType d fresh distinct).Resolves d.name (.type d) := by
  rw [resolves_iff_declOf?, declOf?_addType]
  simp

end

/-- Adding a declaration leaves what every other name resolves to alone. -/
theorem resolves_addType_of_ne {s : Env α} {d : TypeDecl α} {fresh : d.name ∉ s}
    {distinct : d.paramNames.Nodup} {n : Name} {e : Decl.Raw α} (hne : d.name ≠ n) :
    (s.addType d fresh distinct).Resolves n e ↔ s.Resolves n e := by
  rw [resolves_iff_declOf?, resolves_iff_declOf?, declOf?_addType, ite_eq_right (by simpa using hne)]

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

theorem declOf?_of_add?_eq_some {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s')
    (n : Name) : s'.declOf? n = if d.name == n then some d else s.declOf? n := by
  unfold add? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · obtain rfl : s' = _ := Option.some.inj h.symm
      simp [declOf?_eq_raw, Raw.get?_append]
    · exact absurd h (by simp)

theorem resolves_of_add?_eq_some {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s') :
    s'.Resolves d.name d := by
  rw [resolves_iff_declOf?, declOf?_of_add?_eq_some h]
  simp

theorem resolves_add?_of_ne {s s' : Env α} {d : Decl.Raw α} (h : s.add? d = some s')
    {n : Name} {e : Decl.Raw α} (hne : d.name ≠ n) : s'.Resolves n e ↔ s.Resolves n e := by
  rw [resolves_iff_declOf?, resolves_iff_declOf?, declOf?_of_add?_eq_some h,
    ite_eq_right (by simpa using hne)]

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
def ofArray? (ds : Array (Decl.Raw α)) : Option (Env α) :=
  if p : Raw.DistinctDecls ds then
    if h : (Raw.ofAscArray ds p).check = true then
      some ⟨Raw.ofAscArray ds p, Raw.wf_ofAscArray ds p h⟩
    else
      none
  else
    none

theorem vals_of_ofArray?_eq_some {ds : Array (Decl.Raw α)} {s : Env α}
    (h : ofArray? ds = some s) :
    s.raw.decls.vals = ds := by
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
theorem declOf?_of_ofArray?_eq_some {ds : Array (Decl.Raw α)} {s : Env α}
    (h : ofArray? ds = some s) (i : Nat) (hi : i < ds.size) :
    s.declOf? (ds[i]'hi).name = some (ds[i]'hi) := by
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
  declOf?_of_ofArray?_eq_some h i hi

/-- A type that `s` resolves is a valid reference before the end of `s`. -/
theorem refBefore_of_resolves {s : Env α} {n : Name} {d : TypeDecl α}
    (h : s.raw.typeOf? n = some d) : s.RefBefore s.size n d.kinds := by
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
theorem name_of_declOf? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.declOf? n = some d) :
    d.name = n := by
  rw [declOf?_eq_raw] at h
  have h' : s.raw.decls[n]? = some d := h
  have hmem : n ∈ s.raw.decls := IndexMap.mem_of_getElem?_eq_some h'
  rw [IndexMap.getElem?_eq_some_getElem hmem] at h'
  rw [← Option.some.inj h']
  exact Raw.name_getElem s.raw hmem

theorem isSome_declOf? {s : Env α} {n : Name} : (s.declOf? n).isSome ↔ n ∈ s := by
  rw [declOf?_eq_raw, mem_iff_mem_raw]
  show (s.raw.decls[n]?).isSome = true ↔ n ∈ s.raw.decls
  rw [IndexMap.isSome_getElem?_eq_contains]
  simp

theorem declOf?_eq_none_iff {s : Env α} {n : Name} : s.declOf? n = none ↔ n ∉ s := by
  rw [declOf?_eq_raw, ← Option.not_isSome_iff_eq_none, mem_iff_mem_raw]
  show ¬ (s.raw.decls[n]?).isSome = true ↔ ¬ n ∈ s.raw.decls
  rw [IndexMap.isSome_getElem?_eq_contains]
  simp

/-- Every declaration an environment stores is well formed against the whole environment. -/
theorem declWF_of_declOf? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.declOf? n = some d) :
    Decl.Raw.WF (s.RefBefore s.size) d := by
  have h' : s.raw[n]? = some d := by rw [declOf?_eq_raw] at h; exact h
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
theorem idx_of_declOf? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.declOf? n = some d) :
    ∃ i, i < s.size ∧ s.raw.decls.keys[i]? = some n := by
  have h' : s.raw[n]? = some d := by rw [declOf?_eq_raw] at h; exact h
  have hs : (IndexMap.idxOf? s.raw.decls n).isSome := by
    rw [IndexMap.isSome_idxOf?_eq_contains]
    simpa using IndexMap.mem_of_getElem?_eq_some h'
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hs
  have hkey : s.raw.decls.keys[i]? = some n := IndexMap.getElem?_keys_of_idxOf?_eq_some hi
  exact ⟨i, (Array.getElem?_eq_some_iff.mp hkey).1, hkey⟩

/-- A stored declaration passes `checkAlias` at its own position. -/
theorem checkAlias_of_declOf? {s : Env α} {n : Name} {d : Decl.Raw α} (h : s.declOf? n = some d) :
    ∃ i, s.raw.checkAlias i n d = true := by
  obtain ⟨i, -, hkey⟩ := idx_of_declOf? h
  exact ⟨i, s.wf.aliasWF i n d hkey h⟩

/-- A name stored as a member alias denotes a type. -/
theorem isSome_typeOf?_of_dataRest {s : Env α} {n mn hd : Name} {i : Nat}
    (h : s.declOf? n = some (.dataRest mn hd i)) : (s.raw.typeOf? n).isSome := by
  obtain ⟨j, hj⟩ := checkAlias_of_declOf? h
  exact Raw.isSome_typeOf?_of_checkAlias h hj

/-- A name declared as a type names it as a type. -/
theorem typeOf?_of_type {s : Env α} {n : Name} {d : TypeDecl α}
    (h : s.declOf? n = some (.type d)) : s.typeOf? n = some d :=
  Option.bind_eq_some_iff.mpr ⟨_, h, rfl⟩

/-- A name declared as a group's head names its first member as a type. -/
theorem typeOf?_of_dataHead {s : Env α} {n : Name} {g : DataGroup α TypeExpr.Raw}
    (h : s.declOf? n = some (.dataHead g)) : s.typeOf? n = some g.first.toTypeDecl :=
  Option.bind_eq_some_iff.mpr ⟨_, h, rfl⟩

/-- A name declared as an instruction names no type. -/
theorem typeOf?_of_insn {s : Env α} {n : Name} {d : InsnDecl.Raw α}
    (h : s.declOf? n = some (.insn d)) : s.typeOf? n = none := by
  show (s.declOf? n).bind s.raw.typeOfDecl? = none
  rw [h]
  rfl

/-- An undeclared name names no type. -/
theorem typeOf?_of_none {s : Env α} {n : Name} (h : s.declOf? n = none) :
    s.typeOf? n = none := by
  show (s.declOf? n).bind s.raw.typeOfDecl? = none
  rw [h]
  rfl

/-- A name declared as a group's head names the group's first member. -/
theorem dataOf?_of_dataHead {s : Env α} {n : Name} {g : DataGroup α TypeExpr.Raw}
    (h : s.declOf? n = some (.dataHead g)) : s.dataOf? n = some (g, 0) := by
  unfold Env.dataOf? Raw.dataOf?
  rw [show s.raw.decls[n]? = some (.dataHead g) from h]

/-- A name declared as a type names no datatype. -/
theorem dataOf?_of_type {s : Env α} {n : Name} {d : TypeDecl α}
    (h : s.declOf? n = some (.type d)) : s.dataOf? n = none := by
  unfold Env.dataOf? Raw.dataOf?
  rw [show s.raw.decls[n]? = some (.type d) from h]

/-- A name declared as an instruction names no datatype. -/
theorem dataOf?_of_insn {s : Env α} {n : Name} {d : InsnDecl.Raw α}
    (h : s.declOf? n = some (.insn d)) : s.dataOf? n = none := by
  unfold Env.dataOf? Raw.dataOf?
  rw [show s.raw.decls[n]? = some (.insn d) from h]

/-- An undeclared name names no datatype. -/
theorem dataOf?_of_none {s : Env α} {n : Name} (h : s.declOf? n = none) :
    s.dataOf? n = none := by
  unfold Env.dataOf? Raw.dataOf?
  rw [show s.raw.decls[n]? = none from h]

/-! ### Lookups after adding one declaration

`s'` is `s` with one more declaration `e₀`, under the fresh name `a`, that neither heads nor
joins a group: a type or an instruction. -/

section
variable {s s' : Env α} {a : Name} {e₀ : Decl.Raw α}
  (hget : ∀ m, s'.declOf? m = if a == m then some e₀ else s.declOf? m) (ha : a ∉ s)
  (hg : e₀.asGroup = none)
include hget ha hg

/-- A declaration resolves to the same type in `s'` as in `s`. -/
theorem typeOfDecl?_of_declOf?_eq (e : Decl.Raw α) :
    s'.raw.typeOfDecl? e = s.raw.typeOfDecl? e := by
  cases e with
  | dataRest m h i =>
    show ((s'.raw.decls[h]?).bind _).bind _ = ((s.raw.decls[h]?).bind _).bind _
    rw [show s'.raw.decls[h]? = _ from hget h]
    split
    · next hh =>
      rw [show s.raw.decls[h]? = none from declOf?_eq_none_iff.mpr (beq_iff_eq.mp hh ▸ ha)]
      simp [hg]
    · rfl
  | _ => rfl

/-- `s'` names the types `s` names, and `e₀`'s. -/
theorem typeOf?_of_declOf?_eq (n : Name) :
    s'.typeOf? n = if a == n then s.raw.typeOfDecl? e₀ else s.typeOf? n := by
  show ((s'.declOf? n).bind s'.raw.typeOfDecl?) = _
  rw [hget n, funext (typeOfDecl?_of_declOf?_eq hget ha hg)]
  split <;> rfl

omit hg in
/-- `s'` names the datatypes `s` names, and no other. -/
theorem dataOf?_of_declOf?_eq (hg : e₀.asGroup = none)
    (hrest : ∀ m h i, e₀ ≠ .dataRest m h i) (n : Name) :
    s'.dataOf? n = if a == n then none else s.dataOf? n := by
  unfold Env.dataOf? Raw.dataOf?
  rw [show s'.raw.decls[n]? = _ from hget n]
  by_cases hc : (a == n) = true
  · rw [ite_eq_left hc, ite_eq_left hc]
    cases e₀ with
    | dataHead g => simp at hg
    | dataRest m h i => exact absurd rfl (hrest m h i)
    | _ => rfl
  · rw [ite_eq_right hc, ite_eq_right hc, show s.raw.decls[n]? = s.declOf? n from rfl]
    cases s.declOf? n with
    | none => rfl
    | some e =>
      cases e with
      | dataRest m h i =>
        show ((s'.raw.decls[h]?).bind _).map _ = ((s.raw.decls[h]?).bind _).map _
        rw [show s'.raw.decls[h]? = _ from hget h]
        split
        · next hh =>
          rw [show s.raw.decls[h]? = none from declOf?_eq_none_iff.mpr (beq_iff_eq.mp hh ▸ ha)]
          simp [hg]
        · rfl
      | _ => rfl

end

/-- The empty environment names no type. -/
@[simp] public theorem typeOf?_empty (n : Name) : (Env.empty (α := α)).typeOf? n = none :=
  typeOf?_of_none (declOf?_empty n)

/-- The empty environment names no datatype. -/
@[simp] public theorem dataOf?_empty (n : Name) : (Env.empty (α := α)).dataOf? n = none :=
  dataOf?_of_none (declOf?_empty n)

/-- What type a name names after `addType`. -/
public theorem typeOf?_addType (s : Env α) (d : TypeDecl α) (fresh : d.name ∉ s)
    {distinct : d.paramNames.Nodup} (n : Name) :
    (s.addType d fresh distinct).typeOf? n = if d.name == n then some d else s.typeOf? n :=
  typeOf?_of_declOf?_eq (declOf?_addType s d fresh) fresh rfl n

/-- `addType` adds no datatype. -/
public theorem dataOf?_addType (s : Env α) (d : TypeDecl α) (fresh : d.name ∉ s)
    {distinct : d.paramNames.Nodup} (n : Name) :
    (s.addType d fresh distinct).dataOf? n = if d.name == n then none else s.dataOf? n :=
  dataOf?_of_declOf?_eq (declOf?_addType s d fresh) fresh rfl (fun _ _ _ => nofun) n

/-- A name that names a type is declared. -/
public theorem mem_of_typeOf? {s : Env α} {n : Name} {d : TypeDecl α} (h : s.typeOf? n = some d) :
    n ∈ s := by
  obtain ⟨_, he, -⟩ := Option.bind_eq_some_iff.mp h
  exact mem_of_resolves he

/-! ### Extension

`s₁ ⊆ s₂` when `s₂` has the declarations of `s₁` at the same positions, and possibly more
after them.  A name that resolves in `s₁` resolves the same way in `s₂`.  Every operation that
extends an environment proves `⊆`. -/

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
theorem declOf?_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} {d : Decl.Raw α}
    (hd : s₁.declOf? n = some d) : s₂.declOf? n = some d := by
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
  declOf?_of_subset h hd

public theorem mem_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} (hn : n ∈ s₁) :
    n ∈ s₂ :=
  mem_of_resolves
    (declOf?_of_subset h (IndexMap.getElem?_eq_some_getElem (mem_raw_of_mem hn)))

/-- What a name's type resolves to survives an environment that keeps every lookup. -/
theorem typeOf?_of_declOf? {s₁ s₂ : Env α}
    (stable : ∀ {k : Name} {e : Decl.Raw α}, s₁.declOf? k = some e → s₂.declOf? k = some e)
    {n : Name} {t : TypeDecl α}
    (ht : s₁.raw.typeOf? n = some t) : s₂.raw.typeOf? n = some t := by
  obtain ⟨e, he, ht⟩ := Option.bind_eq_some_iff.mp ht
  refine Option.bind_eq_some_iff.mpr ⟨e, stable he, ?_⟩
  cases e with
  | dataRest _ hd _ =>
    -- A member past the head looks up its group's head.
    obtain ⟨g, hg, hm⟩ := Option.bind_eq_some_iff.mp ht
    obtain ⟨eh, heh, hgrp⟩ := Option.bind_eq_some_iff.mp hg
    exact Option.bind_eq_some_iff.mpr ⟨g, Option.bind_eq_some_iff.mpr ⟨eh, stable heh, hgrp⟩, hm⟩
  | type _ | dataHead _ | insn _ => exact ht

/-- What datatype a name is survives an environment that keeps every lookup. -/
theorem dataOf?_of_declOf? {s₁ s₂ : Env α}
    (stable : ∀ {k : Name} {e : Decl.Raw α}, s₁.declOf? k = some e → s₂.declOf? k = some e)
    {n : Name} {g : DataGroup α TypeExpr.Raw} {i : Nat}
    (hd : s₁.raw.dataOf? n = some (g, i)) : s₂.raw.dataOf? n = some (g, i) := by
  unfold Raw.dataOf? at hd ⊢
  split at hd
  next hx =>
    rw [show s₂.raw.decls[n]? = _ from stable hx]
    exact hd
  next hx =>
    rw [show s₂.raw.decls[n]? = _ from stable hx]
    -- A member past the head looks up its group's head.
    obtain ⟨g', hg', hgi⟩ := Option.map_eq_some_iff.mp hd
    obtain ⟨eh, heh, hgrp⟩ := Option.bind_eq_some_iff.mp hg'
    exact Option.map_eq_some_iff.mpr ⟨g', Option.bind_eq_some_iff.mpr ⟨eh, stable heh, hgrp⟩, hgi⟩
  next => exact absurd hd (by simp)

/-- What type a name names survives an extension. -/
public theorem typeOf?_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name} {t : TypeDecl α}
    (ht : s₁.typeOf? n = some t) : s₂.typeOf? n = some t :=
  typeOf?_of_declOf? (declOf?_of_subset h) ht

/-- What datatype a name names survives an extension. -/
public theorem dataOf?_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {n : Name}
    {g : DataGroup α TypeExpr.Raw} {i : Nat} (hd : s₁.dataOf? n = some (g, i)) :
    s₂.dataOf? n = some (g, i) :=
  dataOf?_of_declOf? (declOf?_of_subset h) hd

/-- A reference valid in a prefix is valid in the extension. -/
public theorem refBefore_of_subset {s₁ s₂ : Env α} (h : s₁ ⊆ s₂) {i : Nat} {n : Name}
    {a : Array Kind}
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

theorem declOf?_appendBatch (n : Name) :
    (s.appendBatch ds fresh h).declOf? n = (s.declOf? n).or (ds.find? (·.name == n)) := by
  rw [← Array.find?_toList, Env.declOf?, raw_appendBatch]
  exact Raw.get?_appendList _ fresh n

theorem resolves_appendBatch {j : Nat} {d : Decl.Raw α} (hd : ds[j]? = some d) :
    (s.appendBatch ds fresh h).Resolves d.name d := by
  rw [← Array.getElem?_toList] at hd
  rw [Resolves, Env.declOf?, raw_appendBatch]
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

/-- Freshness against an environment whose names are all in the ordered set `S`, as one check:
adding `ns` to `S` succeeds.  When `S` is a literal tree, the kernel checks `h` by adding
`ns` alone. -/
public theorem FreshNames.of_insert {s : Env α} {ns : Array Name} (S : NameSet)
    (ho : S.Ordered) (hs : ∀ {n}, n ∈ s → n ∈ S) (h : (S.insertAll? ns).isSome = true) :
    s.FreshNames ns := by
  obtain ⟨hnd, hS⟩ := (NameSet.insertAll?_isSome_iff ho).mp h
  exact ⟨hnd, fun n hn hm => hS n hn (hs hm)⟩

/-- `of_insert`, from the set the insertion gives. -/
public theorem FreshNames.of_insertAll? {s : Env α} {ns : Array Name} {S T : NameSet}
    (ho : S.Ordered) (hs : ∀ {n}, n ∈ s → n ∈ S) (h : S.insertAll? ns = some T) :
    s.FreshNames ns :=
  of_insert S ho hs (Option.isSome_iff_exists.mpr ⟨T, h⟩)

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
    (s.wf.appendList _ _ (Raw.checkAppend_types _ _ _ fresh.2))

section
variable {s : Env α} {ds : Array (TypeDecl α)} {fresh : s.FreshTypes ds}

theorem raw_addTypes :
    (s.addTypes ds fresh).raw = s.raw.appendList (ds.map .type).toList
      (freshList_of_freshNames (by rw [Array.map_map]; exact fresh.1)) := raw_appendBatch

@[simp] public theorem size_addTypes : (s.addTypes ds fresh).size = s.size + ds.size := by
  simp [addTypes, size_appendBatch]

@[simp] public theorem subset_addTypes : s ⊆ s.addTypes ds fresh := subset_appendBatch

/-- Membership in an array, as in the list of the array it equals: a step of the DSL's
per-stage membership proofs. -/
public theorem mem_toList_of_eq {a b : Array Name} (h : a = b) {n : Name} :
    n ∈ a ↔ n ∈ b.toList := by
  rw [h, Array.mem_toList_iff]

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

theorem declOf?_addTypes_of_getElem? {j : Nat} {d : TypeDecl α} (hd : ds[j]? = some d) :
    (s.addTypes ds fresh).declOf? d.name = some (.type d) := by
  have : (ds.map Decl.Raw.type)[j]? = some (.type d) := by simp [hd]
  exact resolves_appendBatch this

end

end Env

/-! ## The type language, checked

* `TypeRef`: a reference to a type declaration of an environment.
* `TypeExpr`: a type expression whose references all resolve in an environment, indexed by its
  kind: a type by default, or a list of types.  Its operations, equality, instantiation,
  folding and reinterpretation, are written once for both kinds.
* `TypeList`: a list of types, the argument of a list parameter: a `TypeExpr` of kind `.list`.
* `TypeArg`: an argument of a type constructor, a `TypeExpr` of either kind with its kind.
* `Variadic`, below: an instruction's trailing operands, typed as a `TypeArg` is. -/

/-- `name` is declared in `s` as a type of shape `d`, up to its annotation.  This holds for
primitive types and datatypes alike. -/
public def Env.ResolvesType (s : Env α) (name : Name) (d : TypeDecl α) : Prop :=
  ∃ d', s.raw.typeOf? name = some d' ∧ d'.erase = d.erase

/-- Where the constructor named `name` sits, if `name` is declared in `s` as the instruction
that is a datatype's constructor: which group, which datatype of it, and which constructor. -/
public def Env.ctorAddr? (s : Env α) (name : Name) : Option CtorAddr := s.raw.ctorAddr? name

namespace Env

/-- A name whose stored type declaration is `d` resolves to `d`. -/
theorem resolvesType_of_typeOf? {s : Env α} {n : Name} {d : TypeDecl α}
    (h : s.raw.typeOf? n = some d) : s.ResolvesType n d := ⟨d, h, rfl⟩


end Env

@[simp] public theorem Env.resolvesType_addType_self (s : Env α) (d : TypeDecl α)
    (fresh : d.name ∉ s) {distinct : d.paramNames.Nodup} :
    (s.addType d fresh distinct).ResolvesType d.name d :=
  Env.resolvesType_of_typeOf? (Env.typeOf?_of_type (Env.resolves_addType_self s d fresh))

/-- A reference to a type declaration of `env` taking `arity` arguments.  `decl` is the
declaration up to its annotation: `decl.ann` need not be the stored one, and `carry` keeps it,
so refinement ties it to neither environment.  `Env.annOf?` reads the stored annotation. -/
public structure TypeRef (env : Env α) (arity : Nat) where
  name : Name
  decl : TypeDecl α
  matchArity : decl.arity = arity
  resolves : env.ResolvesType name decl

/-- The kind of each argument the referenced type takes. -/
@[expose] public def TypeRef.kinds {env : Env α} {arity : Nat} (r : TypeRef env arity) :
    Array Kind :=
  r.decl.kinds

/-- A reference has one kind per argument. -/
public theorem TypeRef.size_kinds {env : Env α} {arity : Nat} (r : TypeRef env arity) :
    r.kinds.size = arity := by
  simpa [TypeRef.kinds, TypeDecl.kinds, TypeDecl.arity] using r.matchArity

/-- A type with no parameters has no kinds. -/
public theorem TypeRef.kinds_zero {env : Env α} (r : TypeRef env 0) :
    r.kinds = .replicate 0 .type := by
  have h : r.decl.params = #[] := Array.size_eq_zero_iff.mp r.matchArity
  simp [TypeRef.kinds, TypeDecl.kinds, h]

/-- A reference has the kinds its declaration has.  This is how a caller that cannot unfold
`r` proves `TypeExpr.app`'s kinds, from a lemma `hd` giving `r`'s declaration: `h` then holds
by `rfl`, on that declaration.  Nothing is rewritten in the caller's goal, so the proof does
not look at the arguments. -/
public theorem TypeRef.kinds_of_decl {env : Env α} {arity : Nat} {r : TypeRef env arity}
    {d : TypeDecl α} (hd : r.decl = d) {ks : Array Kind} (h : d.kinds = ks) : r.kinds = ks := by
  rw [TypeRef.kinds, hd]
  exact h

/-- `kinds_of_decl`, in the form of `TypeExpr.appK`'s kinds, over lists. -/
public theorem TypeRef.kinds_toList_of_decl {env : Env α} {arity : Nat}
    {r : TypeRef env arity} {d : TypeDecl α} (hd : r.decl = d) {ks : List Kind}
    (h : ks = d.kinds.toList) : ks = r.kinds.toList := by
  rw [TypeRef.kinds, hd]
  exact h

/-- A type reference is valid before the end of the environment. -/
public theorem TypeRef.refBefore {env : Env α} {arity : Nat} (r : TypeRef env arity) :
    env.RefBefore env.size r.name r.kinds := by
  obtain ⟨n, d, rfl, d', hr, he⟩ := r
  have hb := Env.refBefore_of_resolves hr
  rwa [TypeDecl.kinds_eq_of_erase_eq he] at hb

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
  /-- The member's parameter at this de Bruijn level: a type variable, or a list variable for a
  list parameter, spliced into a literal; `[*as]` is the whole list. -/
  | var (level : Nat)
  /-- A type `s` already declares, which the group cannot be. -/
  | ext {arity : Nat} (r : TypeRef s arity) (args : Array (DataTy s t))
  /-- A type of `t`, which may be one of the group's own members. -/
  | ref {arity : Nat} (r : TypeRef t arity) (args : Array (DataTy s t))
  /-- A list literal. -/
  | list (elems : Array (DataTy s t))

namespace DataTy

variable {s t : Env α}

/-- Whether a payload is a type or a list, when `scope` gives the kind of each parameter.  A
parameter out of scope counts as a type, as in `TypeExpr.Raw.kind`. -/
@[expose] public def kind (scope : Array Kind) : DataTy s t → Kind
  | .var l => scope[l]?.getD .type
  | .list _ => .list
  | _ => .type

/-- Whether a payload may be an element of a list literal: anything but a literal, so a type or
a list parameter spliced in. -/
@[expose] public def isElem : DataTy s t → Bool
  | .list _ => false
  | _ => true

mutual
/-- The type expression a payload stands for. -/
@[expose] public def toRaw : DataTy s t → TypeExpr.Raw
  | .var l => .var l
  | .ext r ⟨as⟩ => .app r.name ⟨toRawList as⟩
  | .ref r ⟨as⟩ => .app r.name ⟨toRawList as⟩
  | .list ⟨es⟩ => .list ⟨toRawList es⟩

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

/-- A list's raw forms, element by element. -/
public theorem toRawList_cons_eq_of {a : DataTy s t} {as : List (DataTy s t)}
    {b : TypeExpr.Raw} {bs : List TypeExpr.Raw} (h₁ : a.toRaw = b) (h₂ : toRawList as = bs) :
    toRawList (a :: as) = b :: bs := by
  simp only [toRawList, h₁, h₂]

/-- An extended type's raw form, from its name's and its arguments'. -/
public theorem toRaw_ext_of {a : Nat} {r : TypeRef s a} {as : List (DataTy s t)} {n : Name}
    {rs : List TypeExpr.Raw} (hn : r.name = n) (ha : toRawList as = rs) :
    (DataTy.ext r ⟨as⟩).toRaw = .app n ⟨rs⟩ := by
  simp only [toRaw, hn, ha]

/-- A type of the group's environment's raw form, from its name's and its arguments'. -/
public theorem toRaw_ref_of {a : Nat} {r : TypeRef t a} {as : List (DataTy s t)} {n : Name}
    {rs : List TypeExpr.Raw} (hn : r.name = n) (ha : toRawList as = rs) :
    (DataTy.ref r ⟨as⟩).toRaw = .app n ⟨rs⟩ := by
  simp only [toRaw, hn, ha]

/-- A literal's raw form, from its elements'. -/
public theorem toRaw_list_of {es : List (DataTy s t)} {rs : List TypeExpr.Raw}
    (h : toRawList es = rs) : (DataTy.list ⟨es⟩).toRaw = .list ⟨rs⟩ := by
  simp only [toRaw, h]

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

/-- A list literal stands for the literal of what its elements stand for. -/
@[simp] public theorem toRaw_list (es : Array (DataTy s t)) :
    (DataTy.list es).toRaw = .list (es.map toRaw) := by
  obtain ⟨es⟩ := es
  simp [toRaw, toRawList_eq_map]

/-- A payload stands for an expression of its own kind. -/
public theorem kind_toRaw (scope : Array Kind) :
    ∀ e : DataTy s t, e.toRaw.kind scope = e.kind scope
  | .var _ | .ext _ ⟨_⟩ | .ref _ ⟨_⟩ | .list ⟨_⟩ => rfl

mutual
/-- Whether a payload is admissible in a member with parameters `pol`:

* every application has its constructor's arguments, each of the kind its parameter declares;
* a parameter of the member outside a literal is one of its types, so a list parameter is
  written `[*as]`;
* every element of a list literal is a type or a parameter spliced in;
* every variable is in scope;
* where `rec` is false (under a parameter declared `.non`), nothing refers into `t` and no
  parameter the member declared `.pos` occurs.

`ok` reduces in the kernel. -/
@[expose] public def ok (pol : Array (Param TyParam)) (rec : Bool) : DataTy s t → Bool
  | .var l =>
    (TyParam.kinds pol)[l]? == some .type && (rec || pol[l]?.map (·.type.polarity) != some .pos)
  | .ext r ⟨as⟩ => match r.decl.params with | ⟨ps⟩ => okArgs pol rec ps as
  | .ref r ⟨as⟩ => rec && match r.decl.params with | ⟨ps⟩ => okArgs pol rec ps as
  | .list ⟨es⟩ => okList pol rec es

@[expose] public def okArgs (pol : Array (Param TyParam)) (rec : Bool) :
    List (Param TyParam) → List (DataTy s t) → Bool
  | [], [] => true
  | ⟨_, ⟨.pos, k⟩⟩ :: ps, e :: es =>
    e.kind (TyParam.kinds pol) == k && ok pol rec e && okArgs pol rec ps es
  | ⟨_, ⟨.non, k⟩⟩ :: ps, e :: es =>
    e.kind (TyParam.kinds pol) == k && ok pol false e && okArgs pol rec ps es
  | _, _ => false

@[expose] public def okList (pol : Array (Param TyParam)) (rec : Bool) :
    List (DataTy s t) → Bool
  | [] => true
  | e :: es =>
    (match e with
     | .var l => decide (l < pol.size) && (rec || pol[l]?.map (·.type.polarity) != some .pos)
     | _ => e.isElem && ok pol rec e) && okList pol rec es
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

/-- A group's constructor and case names, as a list: what the kernel reduces to compare them
with a literal, since it does not reduce `Array.map`. -/
public theorem toList_ctorNames_append_caseNames (ctors : Array (Array (Ctor α τ)))
    (hdr : Array (TypeDecl α)) :
    (ctorNames ctors ++ caseNames hdr).toList =
      ctors.toList.flatMap (fun cs => cs.toList.map (·.name)) ++
        hdr.toList.map (·.name.caseName) := by
  cases ctors
  cases hdr
  simp

/-- Whether `ctors` make a datatype group of the header `hdr`:

* there is at least one member;
* there is one constructor list per member;
* every payload is a type, and `ok` at its member's parameters;
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
        c.args.toList.all (fun p =>
          p.type.kind (TyParam.kinds m.params) == .type && DataTy.ok m.params true p.type) &&
          decide (m.params.toList.map (·.name) ++ c.args.toList.map (·.name)).Nodup) &&
    (members hdr ctors).toList.all fun m =>
      decide (m.params.toList.map (·.name) ++ ["scrutinee"] ++
        m.ctors.toList.map (·.name.lastString)).Nodup

end Env

/-! ### What `ok` buys

The lemmas below show that `ok` implies `TypeExpr.Raw.checkPayload` and `varPositive`, for
abstract resolvers. -/

namespace DataTy

variable {s t : Env α} {P : Name → Option (Array (Param TyParam))}
  {R N : Name → Array Kind → Bool}

theorem length_toRawList :
    ∀ as : List (DataTy s t), (toRawList as).length = as.length
  | [] => rfl
  | _ :: as => by simp [toRawList, length_toRawList as]

/-- An admissible argument list has one argument per parameter, of its kind. -/
theorem kinds_of_okArgs {pol : Array (Param TyParam)} {rec : Bool} :
    ∀ {ps : List (Param TyParam)} {as : List (DataTy s t)}, okArgs pol rec ps as = true →
      as.map (kind (TyParam.kinds pol)) = ps.map (·.type.kind)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [okArgs] at h
  | ⟨_, ⟨p, _⟩⟩ :: _, [], h => by cases p <;> simp [okArgs] at h
  | ⟨_, ⟨.pos, _⟩⟩ :: _, _ :: _, h => by
    simp only [okArgs, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1.1, kinds_of_okArgs h.2]
  | ⟨_, ⟨.non, _⟩⟩ :: _, _ :: _, h => by
    simp only [okArgs, Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1.1, kinds_of_okArgs h.2]

/-- An admissible argument list has one argument per parameter. -/
theorem length_of_okArgs {pol : Array (Param TyParam)} {rec : Bool} {ps : List (Param TyParam)}
    {as : List (DataTy s t)} (h : okArgs pol rec ps as = true) : as.length = ps.length := by
  simpa using congrArg List.length (kinds_of_okArgs h)

/-- What an admissible application's arguments stand for has the kinds its head declares. -/
theorem kinds_toRawList_of_okArgs {pol : Array (Param TyParam)} {rec : Bool} {d : TypeDecl α}
    {as : List (DataTy s t)} (h : okArgs pol rec d.params.toList as = true) :
    (⟨(toRawList as).map (TypeExpr.Raw.kind (TyParam.kinds pol))⟩ : Array Kind) = d.kinds := by
  rw [toRawList_eq_map, List.map_map,
    show TypeExpr.Raw.kind (TyParam.kinds pol) ∘ toRaw =
        kind (s := s) (t := t) (TyParam.kinds pol) from funext (kind_toRaw _),
    kinds_of_okArgs h]
  rfl

/-- What an element stands for may be an element of a list literal. -/
theorem isElem_toRaw {e : DataTy s t} (h : e.isElem = true) : e.toRaw.isElem = true := by
  cases e <;> simp_all [isElem, toRaw, TypeExpr.Raw.isElem]

/-- What the elements of an admissible list literal stand for are elements. -/
theorem isElem_of_okList {pol : Array (Param TyParam)} {rec : Bool} :
    ∀ {es : List (DataTy s t)}, okList pol rec es = true →
      ∀ a ∈ toRawList es, a.isElem = true
  | [], _ => by simp [toRawList]
  | e :: es, h => by
    simp only [okList, Bool.and_eq_true] at h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · cases e
      case var => rfl
      all_goals exact isElem_toRaw ((Bool.and_eq_true _ _).mp h.1).1
    · exact isElem_of_okList h.2 a ha

mutual
/-- Under a `.non` parameter a payload is checked against `N` alone, and mentions no
parameter its member declared `.pos`. -/
theorem check_of_ok_false (hN : ∀ {a} (r : TypeRef s a), N r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} : ∀ (e : DataTy s t), ok pol false e = true →
      TypeExpr.Raw.check N (TyParam.kinds pol) (toRaw e) = true ∧
        ∀ k, pol[k]?.map (·.type.polarity) = some .pos → TypeExpr.Raw.varOccurs k (toRaw e) = false
  | .var l, h => by
    simp only [ok, Bool.and_eq_true, Bool.false_or, bne_iff_ne, ne_eq] at h
    refine ⟨by simpa [toRaw, TypeExpr.Raw.check] using h.1, fun k hk => ?_⟩
    simp only [toRaw, TypeExpr.Raw.varOccurs, beq_eq_false_iff_ne, ne_eq]
    rintro rfl
    exact h.2 hk
  | .ext r ⟨as⟩, h => by
    simp only [ok] at h
    have has := checkList_of_okArgs_false hN as _ h
    simp only [toRaw, TypeExpr.Raw.check, TypeExpr.Raw.varOccurs, Bool.and_eq_true]
    refine ⟨⟨?_, has.1⟩, has.2⟩
    rw [kinds_toRawList_of_okArgs h]
    exact hN r
  | .ref _ ⟨_⟩, h => by simp [ok] at h
  | .list ⟨es⟩, h => by
    simp only [ok] at h
    have hes := checkElems_of_okList_false hN es h
    simp only [toRaw, TypeExpr.Raw.check, TypeExpr.Raw.varOccurs, Bool.and_eq_true,
      List.all_eq_true]
    exact ⟨⟨hes.1, isElem_of_okList h⟩, hes.2⟩

/-- The argument form of `check_of_ok_false`. -/
theorem checkList_of_okArgs_false
    (hN : ∀ {a} (r : TypeRef s a), N r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} : ∀ (as : List (DataTy s t)) (ps : List (Param TyParam)),
      okArgs pol false ps as = true →
      TypeExpr.Raw.checkList N (TyParam.kinds pol) (toRawList as) = true ∧
        ∀ k, pol[k]?.map (·.type.polarity) = some .pos →
          TypeExpr.Raw.varOccursList k (toRawList as) = false
  | [], _, _ => by simp [toRawList, TypeExpr.Raw.checkList, TypeExpr.Raw.varOccursList]
  | _ :: _, [], h => by simp [okArgs] at h
  | e :: as, ⟨_, ⟨p, _⟩⟩ :: ps, h => by
    have h' : ok pol false e = true ∧ okArgs pol false ps as = true := by
      cases p <;> simp only [okArgs, Bool.and_eq_true] at h <;> exact ⟨h.1.2, h.2⟩
    have he := check_of_ok_false hN e h'.1
    have has := checkList_of_okArgs_false hN as ps h'.2
    simp only [toRawList, TypeExpr.Raw.checkList, TypeExpr.Raw.varOccursList,
      Bool.and_eq_true, Bool.or_eq_false_iff]
    exact ⟨⟨he.1, has.1⟩, fun k hk => ⟨he.2 k hk, has.2 k hk⟩⟩

/-- The list-literal form of `check_of_ok_false`. -/
theorem checkElems_of_okList_false
    (hN : ∀ {a} (r : TypeRef s a), N r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} : ∀ (es : List (DataTy s t)), okList pol false es = true →
      TypeExpr.Raw.checkElems N (TyParam.kinds pol) (toRawList es) = true ∧
        ∀ k, pol[k]?.map (·.type.polarity) = some .pos →
          TypeExpr.Raw.varOccursList k (toRawList es) = false
  | [], _ => by simp [toRawList, TypeExpr.Raw.checkElems, TypeExpr.Raw.varOccursList]
  | e :: es, h => by
    have he := check_of_ok_false hN (pol := pol) e
    simp only [okList, Bool.and_eq_true] at h
    have hes := checkElems_of_okList_false hN es h.2
    simp only [toRawList, TypeExpr.Raw.checkElems, TypeExpr.Raw.varOccursList,
      Bool.and_eq_true, Bool.or_eq_false_iff]
    cases e
    case var l =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.false_or, bne_iff_ne, ne_eq] at h
      refine ⟨⟨by simpa [toRaw] using h.1.1, hes.1⟩, fun k hk => ⟨?_, hes.2 k hk⟩⟩
      simp only [toRaw, TypeExpr.Raw.varOccurs, beq_eq_false_iff_ne, ne_eq]
      rintro rfl
      exact h.1.2 hk
    all_goals
      have h₁ := he ((Bool.and_eq_true _ _).mp h.1).2
      exact ⟨⟨h₁.1, hes.1⟩, fun k hk => ⟨h₁.2 k hk, hes.2 k hk⟩⟩
end

mutual
/-- An admissible payload passes `checkPayload`. -/
theorem checkPayload_of_ok (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true ∧ N r.name r.decl.kinds = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} : ∀ (e : DataTy s t),
    ok pol true e = true →
      TypeExpr.Raw.checkPayload P R N (TyParam.kinds pol) (toRaw e) = true
  | .var _, h => by
    simp only [ok, Bool.and_eq_true] at h
    simpa [toRaw, TypeExpr.Raw.checkPayload] using h.1
  | .ext r ⟨as⟩, h => by
    simp only [ok] at h
    obtain ⟨hp, hr, -⟩ := hext r
    simp only [toRaw, TypeExpr.Raw.checkPayload, hp, length_toRawList, length_of_okArgs h,
      Array.length_toList, kinds_toRawList_of_okArgs h, Bool.and_eq_true, beq_self_eq_true,
      true_and]
    exact ⟨hr, checkPayloadArgs_of_okArgs hext hnew as _ h⟩
  | .ref r ⟨as⟩, h => by
    simp only [ok, Bool.true_and] at h
    obtain ⟨hp, hr⟩ := hnew r
    simp only [toRaw, TypeExpr.Raw.checkPayload, hp, length_toRawList, length_of_okArgs h,
      Array.length_toList, kinds_toRawList_of_okArgs h, Bool.and_eq_true, beq_self_eq_true,
      true_and]
    exact ⟨hr, checkPayloadArgs_of_okArgs hext hnew as _ h⟩
  | .list ⟨es⟩, h => by
    simp only [ok] at h
    simp only [toRaw, TypeExpr.Raw.checkPayload, Bool.and_eq_true, List.all_eq_true]
    exact ⟨checkPayloadList_of_okList hext hnew es h, isElem_of_okList h⟩

/-- The argument form of `checkPayload_of_ok`. -/
theorem checkPayloadArgs_of_okArgs (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true ∧ N r.name r.decl.kinds = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} :
    ∀ (as : List (DataTy s t)) (ps : List (Param TyParam)), okArgs pol true ps as = true →
      TypeExpr.Raw.checkPayloadArgs P R N (TyParam.kinds pol) ps (toRawList as) = true
  | [], [], _ => rfl
  | [], ⟨_, ⟨p, _⟩⟩ :: _, h => by cases p <;> simp [okArgs] at h
  | _ :: _, [], h => by simp [okArgs] at h
  | e :: as, ⟨_, ⟨.pos, _⟩⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.checkPayloadArgs, Bool.and_eq_true]
    exact ⟨checkPayload_of_ok hext hnew e h.1.2, checkPayloadArgs_of_okArgs hext hnew as ps h.2⟩
  | e :: as, ⟨_, ⟨.non, _⟩⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.checkPayloadArgs, Bool.and_eq_true]
    exact ⟨(check_of_ok_false (fun r => (hext r).2.2) e h.1.2).1,
      checkPayloadArgs_of_okArgs hext hnew as ps h.2⟩

/-- The list-literal form of `checkPayload_of_ok`. -/
theorem checkPayloadList_of_okList (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true ∧ N r.name r.decl.kinds = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} : ∀ (es : List (DataTy s t)), okList pol true es = true →
      TypeExpr.Raw.checkPayloadList P R N (TyParam.kinds pol) (toRawList es) = true
  | [], _ => by simp [toRawList, TypeExpr.Raw.checkPayloadList]
  | e :: es, h => by
    have he := checkPayload_of_ok hext hnew (pol := pol) e
    simp only [okList, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.checkPayloadList, Bool.and_eq_true]
    refine ⟨?_, checkPayloadList_of_okList hext hnew es h.2⟩
    cases e
    case var l => simpa [toRaw] using ((Bool.and_eq_true _ _).mp h.1).1
    all_goals exact he ((Bool.and_eq_true _ _).mp h.1).2
end

mutual
/-- An admissible payload keeps every parameter its member declared `.pos` in positions
declared `.pos`. -/
theorem varPositive_of_ok (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true ∧ N r.name r.decl.kinds = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} {k : Nat} (hk : pol[k]?.map (·.type.polarity) = some .pos) :
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
  | _, .list ⟨es⟩, h => by
    simp only [ok] at h
    simp only [toRaw, TypeExpr.Raw.varPositive]
    exact varPositiveList_of_okList hext hnew hk es h

/-- The argument form of `varPositive_of_ok`. -/
theorem varPositiveArgs_of_okArgs (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true ∧ N r.name r.decl.kinds = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} {k : Nat} (hk : pol[k]?.map (·.type.polarity) = some .pos) :
    ∀ {rec : Bool} (as : List (DataTy s t)) (ps : List (Param TyParam)),
      okArgs pol rec ps as = true →
      TypeExpr.Raw.varPositiveArgs P k ps (toRawList as) = true
  | _, [], [], _ => rfl
  | _, [], ⟨_, ⟨p, _⟩⟩ :: _, h => by cases p <;> simp [okArgs] at h
  | _, _ :: _, [], h => by simp [okArgs] at h
  | _, e :: as, ⟨_, ⟨.pos, _⟩⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.varPositiveArgs, Bool.and_eq_true]
    exact ⟨varPositive_of_ok hext hnew hk e h.1.2,
      varPositiveArgs_of_okArgs hext hnew hk as ps h.2⟩
  | _, e :: as, ⟨_, ⟨.non, _⟩⟩ :: ps, h => by
    simp only [okArgs, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.varPositiveArgs, Bool.and_eq_true, Bool.not_eq_true',
      (check_of_ok_false (fun r => (hext r).2.2) e h.1.2).2 k hk, true_and]
    exact varPositiveArgs_of_okArgs hext hnew hk as ps h.2

/-- The list-literal form of `varPositive_of_ok`. -/
theorem varPositiveList_of_okList (hext : ∀ {a} (r : TypeRef s a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true ∧ N r.name r.decl.kinds = true)
    (hnew : ∀ {a} (r : TypeRef t a), P r.name = some r.decl.params ∧
      R r.name r.decl.kinds = true)
    {pol : Array (Param TyParam)} {k : Nat} (hk : pol[k]?.map (·.type.polarity) = some .pos) :
    ∀ {rec : Bool} (es : List (DataTy s t)), okList pol rec es = true →
      TypeExpr.Raw.varPositiveList P k (toRawList es) = true
  | _, [], _ => rfl
  | rec, e :: es, h => by
    have he := varPositive_of_ok hext hnew hk (rec := rec) e
    simp only [okList, Bool.and_eq_true] at h
    simp only [toRawList, TypeExpr.Raw.varPositiveList, Bool.and_eq_true]
    refine ⟨?_, varPositiveList_of_okList hext hnew hk es h.2⟩
    cases e
    case var => simp [toRaw, TypeExpr.Raw.varPositive]
    all_goals exact he ((Bool.and_eq_true _ _).mp h.1).2
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
public def dataGroup (hdr : Array (TypeDecl α)) (ctors : Array (Array (Ctor α (DataTy s t))))
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
      Option.bind_some, ite_eq_left (by simp only [size]; omega), Raw.get?_appendList_of_getElem? hD,
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
          r.decl.kinds = true ∧
        Raw.RefBefore.check (s.raw.appendList _ fG) s.raw.decls.keys.size r.name
          r.decl.kinds = true := by
    intro a r
    obtain ⟨d, hd, he⟩ := r.resolves
    have hp := TypeDecl.params_eq_of_erase_eq he
    have h1 : ((s.raw.appendList _ fG).types.before (s.raw.decls.keys.size + hdr.size))[r.name]? =
        some d :=
      Raw.typesBefore_appendList (Raw.typesBefore_of_typeOf? hd (by omega))
    have h2 : ((s.raw.appendList _ fG).types.before s.raw.decls.keys.size)[r.name]? =
        some d :=
      Raw.typesBefore_appendList (Raw.typesBefore_of_typeOf? hd (Nat.le_refl _))
    simp only [Raw.paramsBefore, Raw.RefBefore.check, h1, h2, Option.map_some]
    simp [TypeDecl.kinds, hp]
  have hnew : ∀ {a} (r : TypeRef (s.addTypes hdr fresh) a),
      (s.raw.appendList _ fG).paramsBefore (s.raw.decls.keys.size + hdr.size) r.name =
          some r.decl.params ∧
        Raw.RefBefore.check (s.raw.appendList _ fG) (s.raw.decls.keys.size + hdr.size) r.name
          r.decl.kinds = true := by
    intro a r
    obtain ⟨d, hd, he⟩ := r.resolves
    have hp := TypeDecl.params_eq_of_erase_eq he
    have h1 := typesBefore_dataGroup (fG := fG) hd
    simp only [size] at h1
    simp only [Raw.paramsBefore, Raw.RefBefore.check, h1, Option.map_some]
    simp [TypeDecl.kinds, hp]
  have hadm := h
  simp only [admissible, List.all_eq_true, Array.mem_toList_iff, Bool.and_eq_true] at hadm
  obtain ⟨⟨-, hadm⟩, -⟩ := hadm
  simp only [DataGroup.checkWith, Array.all_eq_true_iff_forall_mem, Bool.and_eq_true]
  intro m' hm' c' hc' p' hp'
  simp only [dataGroup, Array.mem_map] at hm'
  obtain ⟨m, hm, rfl⟩ := hm'
  simp only [DatatypeDecl.mapTy, Array.mem_map] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  simp only [Ctor.mapTy, Array.mem_map] at hp'
  obtain ⟨p, hp, rfl⟩ := hp'
  obtain ⟨hkind, hok⟩ := (hadm m hm c hc).1 p hp
  refine ⟨⟨by simpa [Param.mapTy, DatatypeDecl.mapTy, DataTy.kind_toRaw] using hkind,
    DataTy.checkPayload_of_ok hext hnew p.type hok⟩, ?_⟩
  intro ⟨⟨x, ⟨pol, _⟩⟩, k⟩ hk
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
    (s.wf.appendList _ _ (Raw.checkAppend_group _ checkNames_dataGroup (checkWith_dataGroup _)))

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
  let ⟨d', hd', he⟩ := hd
  ⟨d', Raw.typeOf?_of_typesBefore (typesBefore_dataGroup hd'), he⟩

/-- `addData` names every type that `s.addTypes hdr fresh` names, as it does. -/
public theorem typeOf?_addData_of_addTypes {n : Name} {d : TypeDecl α}
    (hd : (s.addTypes hdr fresh).typeOf? n = some d) :
    (s.addData hdr fresh ctors cfresh adm).typeOf? n = some d :=
  Raw.typeOf?_of_typesBefore (typesBefore_dataGroup hd)

/-- Each datatype of the group is named, as a type, by its header declaration. -/
public theorem typeOf?_addData {j : Nat} {d : TypeDecl α} (hd : hdr[j]? = some d) :
    (s.addData hdr fresh ctors cfresh adm).typeOf? d.name = some d :=
  typeOf?_addData_of_addTypes (typeOf?_of_type (declOf?_addTypes_of_getElem? hd))

/-- The group is named after its first datatype. -/
theorem name_first_dataGroup :
    (hdr[0]'(pos_of_admissible adm)).name = (dataGroup hdr ctors adm).first.name := by
  have h := first_toTypeDecl_dataGroup (h := adm)
  rw [Array.getElem?_eq_getElem (pos_of_admissible adm)] at h
  exact congrArg TypeDecl.name (Option.some.inj h)

/-- The group's first datatype names the group. -/
theorem declOf?_addData_head :
    (s.addData hdr fresh ctors cfresh adm).declOf? (hdr[0]'(pos_of_admissible adm)).name =
      some (.dataHead (dataGroup hdr ctors adm)) := by
  rw [name_first_dataGroup]
  exact resolves_appendBatch (j := 0) (by
    rw [← Array.getElem?_toList]
    exact DataGroup.decls_getElem?_zero (dataGroup hdr ctors adm))

/-- Each datatype of the group is that member of the group. -/
public theorem dataOf?_addData {j : Nat} (hj : j < hdr.size) :
    (s.addData hdr fresh ctors cfresh adm).dataOf? hdr[j].name =
      some (dataGroup hdr ctors adm, j) := by
  obtain ⟨m, hm⟩ : ∃ m, (dataGroup hdr ctors adm).members[j]? = some m :=
    ⟨_, Array.getElem?_eq_getElem (size_dataGroup (h := adm) ▸ hj)⟩
  have hn : hdr[j].name = m.name := by
    have h := toTypeDecl_dataGroup_getElem? hm
    rw [Array.getElem?_eq_getElem hj] at h
    exact congrArg TypeDecl.name (Option.some.inj h)
  by_cases hj₀ : j = 0
  · subst hj₀
    exact dataOf?_of_dataHead declOf?_addData_head
  · have hrest : (s.addData hdr fresh ctors cfresh adm).declOf? hdr[j].name =
        some (.dataRest hdr[j].name (dataGroup hdr ctors adm).first.name j) := by
      rw [hn]
      exact resolves_appendBatch
        (by rw [← Array.getElem?_toList]; exact DataGroup.decls_getElem?_of_member _ hm hj₀)
    have hhead := declOf?_addData_head (cfresh := cfresh) (adm := adm)
    rw [name_first_dataGroup (ctors := ctors) (adm := adm)] at hhead
    unfold Env.dataOf? Raw.dataOf?
    rw [show (s.addData hdr fresh ctors cfresh adm).raw.decls[hdr[j].name]? = _ from hrest]
    show ((Env.declOf? _ _).bind Decl.Raw.asGroup).map _ = _
    rw [hhead]
    rfl

end

/-- Each type of a batch resolves to its own declaration. -/
public theorem resolvesType_addTypes {s : Env α} {ds : Array (TypeDecl α)}
    {fresh : s.FreshTypes ds} {j : Nat} {d : TypeDecl α}
    (hd : ds[j]? = some d) : (s.addTypes ds fresh).ResolvesType d.name d :=
  resolvesType_of_typeOf? (typeOf?_of_type (declOf?_addTypes_of_getElem? hd))

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


/-- A type expression of kind `k`, a type or a list of types, whose references all resolve in
`env`, in `scope`: the kinds of the variables in scope, by de Bruijn level.  It carries the one
judgment `TypeExpr.WF` at `k`.  It is a type unless `k` says otherwise; a list is a `TypeList`,
always a literal, so each list has one spelling and equality is structural.  `TypeExpr env` is a
closed type.  A type is built with `var`, `app` and `appK`, a list with `TypeList.var`,
`TypeList.lit` and `TypeList.ofTypes`; either is read with `fold`, a list as its literal's
elements with `toElems`, and a closed list as types with `elems`. -/
public structure TypeExpr (env : Env α) (scope : Array Kind := #[]) (k : Kind := .type) where
  private expr : TypeExpr.Raw
  private wf : TypeExpr.WF (env.RefBefore env.size) scope k expr

/-- A list of types whose references all resolve in `env`, in `scope`: a type expression of kind
`.list`, the argument of a list parameter. -/
public abbrev TypeList (env : Env α) (scope : Array Kind := #[]) : Type :=
  TypeExpr env scope .list

/-- An element of a list literal: a type, or a list variable spliced in. -/
public inductive TypeList.Elem (env : Env α) (scope : Array Kind := #[]) where
  | ty (t : TypeExpr env scope)
  /-- `*j`: the elements of list variable `j`. -/
  | splice (j : Nat) (h : scope[j]? = some .list)

/-- An argument of a declared type constructor: a type expression of either kind, with its kind.
It is built with `ty` and `list`, which match as constructors do. -/
public structure TypeArg (env : Env α) (scope : Array Kind := #[]) where
  /-- Whether the argument is a type or a list. -/
  kind : Kind
  val : TypeExpr env scope kind

namespace TypeArg

variable {env : Env α} {scope : Array Kind}

/-- A type, as an argument. -/
@[match_pattern] public abbrev ty (t : TypeExpr env scope) : TypeArg env scope := ⟨.type, t⟩

/-- A list of types, as an argument. -/
@[match_pattern] public abbrev list (l : TypeList env scope) : TypeArg env scope := ⟨.list, l⟩

end TypeArg

namespace TypeExpr

variable {env : Env α} {scope : Array Kind} {k : Kind}

/-- The type variable `i`.  A list variable is a `TypeList.var`. -/
public def var (i : Nat) (h : scope[i]? = some .type) : TypeExpr env scope :=
  ⟨.var i, wfType_var_iff.mpr h⟩

/-- Erasing the check of a type variable gives the variable. -/
theorem expr_var (i : Nat) (h : scope[i]? = some .type) :
    (var (env := env) i h).expr = .var i := by
  simp [var]

end TypeExpr

namespace TypeList

variable {env : Env α} {scope : Array Kind}

/-- The raw form of an element: the type, or the list variable. -/
def Elem.expr : Elem env scope → TypeExpr.Raw
  | .ty t => t.expr
  | .splice j _ => .var j

/-- An element's raw form is a well-formed element. -/
theorem Elem.wf : ∀ e : Elem env scope, TypeExpr.WFElem (env.RefBefore env.size) scope e.expr
  | .ty t => .ty t.wf
  | .splice _ h => .splice h

/-- The list literal of `es`, each a type or a splice. -/
public def lit (es : Array (Elem env scope)) : TypeList env scope :=
  ⟨.list (es.map (·.expr)),
   .list fun a ha => by obtain ⟨e, -, rfl⟩ := Array.mem_map.mp ha; exact e.wf⟩

/-- The list variable `j`: the literal `[*j]`, which splices it in, since every list is a
literal. -/
public abbrev var (j : Nat) (h : scope[j]? = some .list) : TypeList env scope :=
  lit #[.splice j h]

/-- The list literal of the types `ts`. -/
@[expose] public def ofTypes (ts : Array (TypeExpr env scope)) : TypeList env scope :=
  lit (ts.map .ty)

private def rawElems : (e : TypeExpr.Raw) →
    TypeExpr.WFList (env.RefBefore env.size) #[] e → Array (TypeExpr env)
  | .list es, h => es.attach.map fun (a : {x // x ∈ es}) => ⟨a.1, h.elems_closed a.1 a.2⟩
  | _, _ => #[]

end TypeList

-- `append` and `toElems` are in `TypeExpr`, as `elems` is, so that dot notation finds them on a
-- list that `instantiate` or `carry` returns.
namespace TypeExpr

variable {env : Env α} {scope : Array Kind}

/-- The elements of two literals, one after the other. -/
private def rawAppend : TypeExpr.Raw → TypeExpr.Raw → TypeExpr.Raw
  | .list a, .list b => .list (a ++ b)
  | a, _ => a

/-- Appending two well-formed lists gives a well-formed list: each of its elements is an
element of one of them. -/
private theorem wf_rawAppend {R : Name → Array Kind → Prop} {a b : TypeExpr.Raw}
    (ha : TypeExpr.WFList R scope a) (hb : TypeExpr.WFList R scope b) :
    TypeExpr.WFList R scope (rawAppend a b) := by
  cases ha with
  | list hes₁ =>
    cases hb with
    | list hes₂ =>
      exact .list fun x hx => (Array.mem_append.mp hx).elim (hes₁ x) (hes₂ x)

/-- `l₁`'s elements, then `l₂`'s: since every list is a literal, a list parameter's argument
can be spliced among other elements. -/
public def append (l₁ l₂ : TypeExpr env scope .list) : TypeExpr env scope .list :=
  ⟨rawAppend l₁.expr l₂.expr, wf_rawAppend l₁.wf l₂.wf⟩

public instance : Append (TypeExpr env scope .list) := ⟨append⟩

/-- Appending appends the raw literals. -/
private theorem expr_append (l₁ l₂ : TypeExpr env scope .list) :
    (l₁ ++ l₂).expr = rawAppend l₁.expr l₂.expr :=
  rfl

/-- `append` is `++`. -/
@[simp] public theorem append_eq (l₁ l₂ : TypeExpr env scope .list) : append l₁ l₂ = l₁ ++ l₂ :=
  rfl

end TypeExpr

-- In `TypeExpr`, so that dot notation finds it on a list that `instantiate` or `carry` returns.
/-- The elements of a closed list: with no variable in scope, every list is a literal of
types. -/
public def TypeExpr.elems {env : Env α} (l : TypeList env) : Array (TypeExpr env) :=
  TypeList.rawElems l.expr l.wf

namespace TypeArg

variable {env : Env α} {scope : Array Kind}

/-- A type argument is a type. -/
@[simp] public theorem kind_ty (t : TypeExpr env scope) : (TypeArg.ty t).kind = .type :=
  rfl

/-- A list argument is a list. -/
@[simp] public theorem kind_list (l : TypeList env scope) :
    (TypeArg.list l).kind = .list := rfl

/-- The raw form of an argument. -/
def expr (a : TypeArg env scope) : TypeExpr.Raw := a.val.expr

/-- An argument's raw form is well formed. -/
theorem wfRel (a : TypeArg env scope) : TypeExpr.WFRel (env.RefBefore env.size) scope a.expr :=
  a.val.wf.wfRel

/-- An argument's raw form has the argument's kind. -/
theorem kind_expr (a : TypeArg env scope) : a.expr.kind scope = a.kind :=
  a.val.wf.kind_eq

/-- The checked form of a well-formed raw expression, of its kind. -/
def ofWF (e : TypeExpr.Raw) (h : TypeExpr.WFRel (env.RefBefore env.size) scope e) :
    TypeArg env scope :=
  ⟨e.kind scope, e, h⟩

/-- `ofWF` keeps the raw expression. -/
@[simp] theorem expr_ofWF (e : TypeExpr.Raw)
    (h : TypeExpr.WFRel (env.RefBefore env.size) scope e) : (ofWF e h).expr = e := rfl

end TypeArg

/-- Arguments for the variables of `params`, in `scope`: one per variable, each of its
variable's kind.  An application of an instruction supplies them for its signature's scope.
Built with `⟨args, rfl⟩` when the arguments are written out, and with `check?` otherwise. -/
public structure TypeArgs (env : Env α) (params : Array Kind) (scope : Array Kind := #[]) where
  args : Array (TypeArg env scope)
  -- Over lists, so that `rfl` proves it: `Array.map` does not reduce.
  kinds : args.toList.map TypeArg.kind = params.toList

namespace TypeArgs

variable {env : Env α} {params scope : Array Kind}

/-- `args`, if each has its variable's kind, or the first way they do not fit: the one check
`KindError.check?` decides both. -/
@[expose] public def check? (params : Array Kind) (args : Array (TypeArg env scope)) :
    Except KindError (TypeArgs env params scope) :=
  match h : KindError.check? params (args.map (·.kind)) with
  | some e => .error e
  | none => .ok ⟨args, by simpa using congrArg Array.toList (KindError.check?_eq_none_iff.mp h)⟩

/-- Types for the variables of a scope of `n` types. -/
public def ofTypes {n : Nat} (ts : Vector (TypeExpr env scope) n) :
    TypeArgs env (.replicate n .type) scope :=
  ⟨ts.toArray.map .ty, by simp [Function.comp_def, List.map_const']⟩

/-- There is one argument per variable. -/
public theorem size_args (a : TypeArgs env params scope) : a.args.size = params.size := by
  simpa using congrArg List.length a.kinds

/-- Each argument's raw form is well formed, of its variable's kind. -/
theorem wf (a : TypeArgs env params scope) (i : Nat) (hi : i < params.size) :
    ∃ e, (a.args.map (·.expr))[i]? = some e ∧
      TypeExpr.WF (env.RefBefore env.size) scope params[i] e := by
  have hi₁ : i < a.args.size := a.size_args ▸ hi
  have hk := congrArg (·[i]?) a.kinds
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hi₁,
    Array.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at hk
  exact ⟨a.args[i].expr, by simp [Array.getElem?_eq_getElem hi₁],
    TypeExpr.WF.of_wfRel a.args[i].wfRel ((TypeArg.kind_expr _).trans hk)⟩

end TypeArgs

namespace TypeExpr

variable {env : Env α} {scope : Array Kind} {k : Kind}

/-- Apply a declared type constructor to checked arguments, each of the kind its parameter
declares.  `rfl` proves `hk` when `r`'s declaration is visible. -/
-- `hk` is over lists, so that `rfl` proves it: `Array.map` does not reduce.
public def appK {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeArg env scope) arity)
    (hk : args.toList.map TypeArg.kind = r.kinds.toList := by rfl) : TypeExpr env scope :=
  ⟨.app r.name (args.toArray.map (·.expr)),
   .app r.refBefore (by simpa using congrArg List.length hk) fun i h => by
     have hlen : arity = r.kinds.size := by simpa using congrArg List.length hk
     have hi : i < arity := by simpa using h
     have hki : (args[i]'hi).kind = r.kinds[i]'(hlen ▸ hi) := by
       simpa [hi, hlen ▸ hi] using congrArg (·[i]?) hk
     have he : (args.toArray.map (·.expr))[i]'h = (args[i]'hi).val.expr := by
       rw [Array.getElem_map]
       rfl
     rw [he]
     exact hki ▸ (args[i]'hi).val.wf⟩

/-- Erasing the check of an application applies the name to the erased arguments. -/
theorem expr_appK {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeArg env scope) arity)
    (hk : args.toList.map TypeArg.kind = r.kinds.toList) :
    (appK r args hk).expr = .app r.name (args.toArray.map (·.expr)) := by
  simp [appK]

/-- Apply a declared type constructor, all of whose parameters are types, to checked
arguments: `appK` at the arguments as types.  `rfl` proves `hk` when `r`'s declaration is
visible. -/
public def app {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeExpr env scope) arity)
    (hk : r.kinds = .replicate arity .type := by rfl) : TypeExpr env scope :=
  appK r (args.map .ty) (by simp [hk, Vector.toList_map, Function.comp_def, List.map_const'])

/-- Check a raw type expression against `env` by evaluation. -/
def check? (env : Env α) (scope : Array Kind) (e : TypeExpr.Raw) :
    Option (TypeExpr env scope) :=
  if h : TypeExpr.Raw.checkTypeAt env.raw env.size scope e = true then
    some ⟨e, TypeExpr.Raw.wfType_of_checkTypeAt e h⟩
  else
    none

/-- What `check?` accepts, it returns unchanged. -/
theorem expr_of_check?_eq_some {env : Env α} {scope : Array Kind} {e : TypeExpr.Raw}
    {f : TypeExpr env scope} (h : check? env scope e = some f) : f.expr = e := by
  unfold check? at h
  split at h
  · obtain rfl : f = _ := Option.some.inj h.symm
    rfl
  · exact absurd h (by simp)

/-! ### Reading the raw expression

* `toRaw`: the raw type expression a checked one stands for, which `InsnSig.ext_toRaw`
  compares. -/

/-- The raw type expression `e` stands for. -/
public def toRaw (e : TypeExpr env scope k) : TypeExpr.Raw := e.expr

/-- A type variable stands for the variable. -/
@[simp] public theorem toRaw_var (i : Nat) (h : scope[i]? = some .type) :
    (var (env := env) i h).toRaw = .var i := by
  simp [toRaw, expr_var]

/-- An application stands for its constructor's name applied to what its arguments stand
for. -/
@[simp] public theorem toRaw_app {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeExpr env scope) arity) (hk : r.kinds = .replicate arity .type) :
    (app r args hk).toRaw = .app r.name (args.toArray.map (·.toRaw)) := by
  simp [toRaw, app, expr_appK, Array.map_map, Function.comp_def, TypeArg.expr]

/-- `toRaw` is the erasure. -/
theorem toRaw_eq_expr (e : TypeExpr env scope k) : e.toRaw = e.expr := rfl

/-! ### Equality

Two type expressions are equal when their erasures are, and equality is decidable. -/

/-- Two type expressions are equal exactly when their raw forms are. -/
theorem eq_iff_expr_eq {a b : TypeExpr env scope k} : a = b ↔ a.expr = b.expr := by
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
public def decEq (a b : TypeExpr env scope k) : Decidable (a = b) :=
  decidable_of_iff (a.expr = b.expr) eq_iff_expr_eq.symm

public instance : DecidableEq (TypeExpr env scope k) := decEq

/-- A hash of a type expression: its raw form's. -/
public def hash (a : TypeExpr env scope k) : UInt64 := Hashable.hash a.expr

public instance : Hashable (TypeExpr env scope k) := ⟨hash⟩

/-! ### Instantiation

* `instantiate`: substitute arguments for the variables of a scope. -/

/-- Replace the variables of `e`, whose scope is `scope`, by `args`: a type variable by its
type, and a list variable, which is spliced into a literal, by the list's elements.  It is a
full simultaneous substitution: `args` gives every variable of `scope` an argument, all at
once, so no variable keeps its de Bruijn level.  Substituting some variables only would mean
shifting the others. -/
public def instantiate {scope₁ : Array Kind} (args : TypeArgs env scope scope₁)
    (e : TypeExpr env scope k) : TypeExpr env scope₁ k :=
  ⟨e.expr.instantiate (args.args.map (·.expr)),
   e.wf.instantiate args.wf⟩

/-- Instantiating instantiates the raw form with the arguments' raw forms. -/
theorem expr_instantiate {scope₁ : Array Kind} (args : TypeArgs env scope scope₁)
    (e : TypeExpr env scope k) :
    (e.instantiate args).expr = e.expr.instantiate (args.args.map (·.expr)) := by
  simp [instantiate]

/-- A closed expression instantiates to itself. -/
@[simp] public theorem instantiate_empty (e : TypeExpr env #[] k) :
    e.instantiate ⟨#[], rfl⟩ = e :=
  eq_iff_expr_eq.mpr (by simp [expr_instantiate, Raw.instantiate_empty])

/-! ### Folding

* `fold`: a structural fold over a type expression. -/

/-- Replace every variable by `var` of its level and its kind in the scope, every application
by `app` of the constructor's name and its folded arguments, and every list literal by `list`
of its folded elements. -/
public def fold {β : Type _} (var : Nat → Kind → β) (app : Name → Array β → β)
    (list : Array β → β) (e : TypeExpr env scope k) : β :=
  e.expr.fold (fun i => var i (scope[i]?.getD .type)) app list

/-- Folding a type variable applies `var` to its level and `.type`. -/
@[simp] public theorem fold_var {β : Type _} (v : Nat → Kind → β) (a : Name → Array β → β)
    (l : Array β → β) (i : Nat) (h : scope[i]? = some .type) :
    (var (env := env) i h).fold v a l = v i .type := by
  simp [fold, expr_var, Raw.fold, h]

/-! ### Reading a datatype back

* `ctors?`: the constructors of a datatype, with payload types at its type arguments.
* `ctorPayloads?`: the payload types of every constructor.
* `ctorArgs?`: the payload types of one constructor. -/

private def rawCtors? {env : Env α} :
    (e : TypeExpr.Raw) → WFRel (env.RefBefore env.size) #[] e →
      Option (Array (Name × Array (TypeExpr env)))
  | .app n as, h => do
    let (g, i) ← env.raw.dataOf? n
    let m ← g.member? i
    let args ← (TypeArgs.check? (TyParam.kinds m.params)
      (as.attach.map fun a => TypeArg.ofWF a.1 (h.args a.1 a.2))).toOption
    m.ctors.mapM fun c =>
      (c.args.mapM (fun p => check? env (TyParam.kinds m.params) p.type)).map
        (fun ps => (c.name, ps.map (·.instantiate args)))
  | _, _ => none

/-- The constructors of the datatype `e` is: each name, with its payload types at `e`'s own
type arguments.  `none` for a primitive type, and for a datatype whose group has a member the
environment does not name. -/
public def ctors? {env : Env α} (e : TypeExpr env) :
    Option (Array (Name × Array (TypeExpr env))) :=
  rawCtors? e.expr e.wf.wfRel

/-- The payload types of every constructor, in declaration order. -/
public def ctorPayloads? {env : Env α} (e : TypeExpr env) :
    Option (Array (Array (TypeExpr env))) :=
  e.ctors?.map (·.map (·.2))

/-- The payload types of the constructor named `c`, if `e` is a datatype with one.  A `some`
result means `c` is a constructor of `e`. -/
public def ctorArgs? {env : Env α} (e : TypeExpr env) (c : Name) :
    Option (Array (TypeExpr env)) :=
  e.ctors?.bind fun cs => (cs.find? (·.1 == c)).map (·.2)

end TypeExpr

namespace TypeList

variable {env : Env α} {scope : Array Kind}

/-- The raw form of an element. -/
public def Elem.toRaw (e : Elem env scope) : TypeExpr.Raw := e.expr

/-- A type element's raw form is the type's. -/
@[simp] public theorem Elem.toRaw_ty (t : TypeExpr env scope) :
    (Elem.ty t).toRaw = t.toRaw := by
  simp [Elem.toRaw, Elem.expr, TypeExpr.toRaw]

/-- A splice's raw form is its list variable. -/
@[simp] public theorem Elem.toRaw_splice (j : Nat) (h : scope[j]? = some .list) :
    (Elem.splice (env := env) j h).toRaw = .var j := by
  simp [Elem.toRaw, Elem.expr]

/-- A literal stands for the literal of what its elements stand for. -/
@[simp] public theorem toRaw_lit (es : Array (Elem env scope)) :
    (lit es).toRaw = .list (es.map (·.toRaw)) := by
  simp [TypeExpr.toRaw, lit, Elem.toRaw]

/-- A type is not a list variable. -/
private theorem expr_ne_splice (t : TypeExpr env scope) {j : Nat}
    (hj : scope[j]? = some .list) : t.expr ≠ .var j := by
  intro h
  have ht : TypeExpr.WFType (env.RefBefore env.size) scope t.expr := t.wf
  rw [h, TypeExpr.wfType_var_iff, hj] at ht
  exact absurd (Option.some.inj ht) (by decide)

/-- Elements with equal raw forms are equal. -/
theorem Elem.expr_inj : ∀ {a b : Elem env scope}, a.expr = b.expr → a = b
  | .ty _, .ty _, h => congrArg _ (TypeExpr.eq_iff_expr_eq.mpr h)
  | .splice _ _, .splice _ _, h => by cases h; rfl
  | .ty t, .splice _ hj, h => absurd h (expr_ne_splice t hj)
  | .splice _ hj, .ty t, h => absurd h.symm (expr_ne_splice t hj)

/-- Two literals are equal when their elements are. -/
@[simp] public theorem lit_eq_lit_iff {a b : Array (Elem env scope)} :
    lit a = lit b ↔ a = b := by
  rw [TypeExpr.eq_iff_expr_eq]
  simp only [lit, TypeExpr.Raw.list.injEq]
  exact Array.map_inj_right fun _ _ => Elem.expr_inj

/-- The checked element a well-formed raw element is: a list variable spliced in, or a type. -/
private def Elem.ofWF :
    (a : TypeExpr.Raw) → TypeExpr.WFElem (env.RefBefore env.size) scope a → Elem env scope
  | .var j, h =>
    if hj : scope[j]? = some .list then .splice j hj
    else .ty ⟨.var j, h.wfType (by
      cases hs : scope[j]? with
      | none => simp [TypeExpr.Raw.kind, hs]
      | some k =>
        cases k with
        | type => simp [TypeExpr.Raw.kind, hs]
        | list => exact absurd hs hj)⟩
  | .app n as, h => .ty ⟨.app n as, h.wfType rfl⟩
  | .list _, h => absurd h.isElem (by simp [TypeExpr.Raw.isElem])

/-- `Elem.ofWF` keeps the raw element. -/
private theorem Elem.expr_ofWF : ∀ (a : TypeExpr.Raw)
    (h : TypeExpr.WFElem (env.RefBefore env.size) scope a), (Elem.ofWF a h).expr = a
  | .var j, h => by
    by_cases hj : scope[j]? = some .list <;> simp [Elem.ofWF, hj, Elem.expr]
  | .app _ _, _ => rfl
  | .list _, h => absurd h.isElem (by simp [TypeExpr.Raw.isElem])

/-- The elements of a well-formed literal, checked. -/
private def rawToElems : (e : TypeExpr.Raw) → TypeExpr.WFList (env.RefBefore env.size) scope e →
    Array (Elem env scope)
  | .list es, h => es.attach.map fun a => Elem.ofWF a.1 (h.elems a.1 a.2)
  | _, _ => #[]

/-- The raw elements of `rawToElems` are the literal's. -/
private theorem list_map_expr_rawToElems : ∀ (e : TypeExpr.Raw)
    (h : TypeExpr.WFList (env.RefBefore env.size) scope e),
    TypeExpr.Raw.list ((rawToElems e h).map Elem.expr) = e
  | .list es, h => by
    simp only [rawToElems, Array.map_map, Function.comp_def, Elem.expr_ofWF,
      Array.attach_map_subtype_val]
  | .var _, h => by cases h
  | .app _ _, h => by cases h

end TypeList

namespace TypeExpr

variable {env : Env α} {scope : Array Kind}

/-- Appending two literals is the literal of their elements, one after the other. -/
@[simp] public theorem lit_append_lit (a b : Array (TypeList.Elem env scope)) :
    TypeList.lit a ++ TypeList.lit b = TypeList.lit (a ++ b) :=
  eq_iff_expr_eq.mpr (by
    simp [expr_append, TypeList.lit, rawAppend, Array.map_append])

/-- The elements of a list, each a type or a list variable spliced in: every list is the
literal of its elements (`lit_toElems`). -/
public def toElems (l : TypeExpr env scope .list) : Array (TypeList.Elem env scope) :=
  TypeList.rawToElems l.expr l.wf

/-- A list is the literal of its elements. -/
@[simp] public theorem lit_toElems (l : TypeExpr env scope .list) :
    TypeList.lit l.toElems = l :=
  eq_iff_expr_eq.mpr (TypeList.list_map_expr_rawToElems l.expr l.wf)

/-- A literal's elements are the ones it was built from. -/
@[simp] public theorem toElems_lit (es : Array (TypeList.Elem env scope)) :
    (TypeList.lit es).toElems = es :=
  TypeList.lit_eq_lit_iff.mp (lit_toElems (TypeList.lit es))

/-- A list variable is the one splice. -/
@[simp] public theorem toElems_var (j : Nat) (h : scope[j]? = some .list) :
    (TypeList.var (env := env) j h).toElems = #[.splice j h] :=
  toElems_lit _

/-- The elements of `ofTypes ts` are the types `ts`. -/
@[simp] public theorem toElems_ofTypes (ts : Array (TypeExpr env scope)) :
    (TypeList.ofTypes ts).toElems = ts.map .ty :=
  toElems_lit _

/-- Appending lists appends their elements. -/
@[simp] public theorem toElems_append (l₁ l₂ : TypeExpr env scope .list) :
    (l₁ ++ l₂).toElems = l₁.toElems ++ l₂.toElems := by
  rw [← toElems_lit (l₁.toElems ++ l₂.toElems), ← lit_append_lit, lit_toElems, lit_toElems]

/-- `++` splices a list where `instantiate` splices a list variable, so the two commute, as an
abbreviation's `n.ty`, which appends its list arguments, relies on. -/
@[simp] public theorem instantiate_append {scope₁ : Array Kind}
    (args : TypeArgs env scope scope₁) (l₁ l₂ : TypeExpr env scope .list) :
    (l₁ ++ l₂).instantiate args = l₁.instantiate args ++ l₂.instantiate args := by
  rw [eq_iff_expr_eq]
  obtain ⟨a, ha⟩ := TypeExpr.WF.eq_list l₁.wf
  obtain ⟨b, hb⟩ := TypeExpr.WF.eq_list l₂.wf
  simp [expr_append, expr_instantiate, ha, hb, rawAppend, TypeExpr.Raw.instantiate_list]

end TypeExpr

/-! ### A list's elements, after instantiation

`TypeArgs.listAt` reads a list variable's argument, and `TypeList.Elem.instantiate` instantiates
one element of a literal: a type becomes its instance, and a splice its argument's elements.  A
list instantiates element by element (`toElems_instantiate`), and a closed list's elements are
its types (`toElems_eq_elems`). -/

/-- An argument of kind `list`, as a list. -/
private def TypeArg.asList {env : Env α} {scope : Array Kind} :
    (a : TypeArg env scope) → a.kind = .list → TypeList env scope
  | ⟨.list, l⟩, _ => l
  | ⟨.type, _⟩, h => Kind.noConfusion h

private theorem TypeArg.expr_asList {env : Env α} {scope : Array Kind} :
    ∀ (a : TypeArg env scope) (h : a.kind = .list), (a.asList h).expr = a.expr
  | ⟨.list, _⟩, _ => rfl
  | ⟨.type, _⟩, h => Kind.noConfusion h

/-- The argument for the list variable `j`. -/
public def TypeArgs.listAt {env : Env α} {params scope : Array Kind}
    (a : TypeArgs env params scope) (j : Nat) (h : params[j]? = some .list) :
    TypeList env scope :=
  have hj : j < a.args.size := by
    rw [a.size_args]
    exact (Array.getElem?_eq_some_iff.mp h).1
  (a.args[j]'hj).asList (by
    have hk := congrArg (·[j]?) a.kinds
    simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem hj,
      Option.map_some] at hk
    exact Option.some.inj (hk.trans h))

/-- `listAt` is the `j`th argument. -/
private theorem TypeArgs.expr_listAt {env : Env α} {params scope : Array Kind}
    (a : TypeArgs env params scope) (j : Nat) (h : params[j]? = some .list) :
    (a.args.map (·.expr))[j]? = some (a.listAt j h).expr := by
  have hj : j < a.args.size := by
    rw [a.size_args]
    exact (Array.getElem?_eq_some_iff.mp h).1
  simp [TypeArgs.listAt, TypeArg.expr_asList, Array.getElem?_eq_getElem hj]

namespace TypeList

variable {env : Env α} {scope scope₁ : Array Kind}

/-- What an element of a literal instantiates to: a type its instance, and a list variable
spliced in its argument's elements. -/
public def Elem.instantiate (a : TypeArgs env scope scope₁) :
    Elem env scope → Array (Elem env scope₁)
  | .ty t => #[.ty (t.instantiate a)]
  | .splice j h => (a.listAt j h).toElems

/-- A well-formed literal contributes its checked elements' raw forms. -/
private theorem spliced_eq_rawToElems : ∀ (x : TypeExpr.Raw)
    (hx : TypeExpr.WFList (env.RefBefore env.size) scope x),
    x.spliced = ((rawToElems x hx).map Elem.expr).toList
  | .list ⟨es⟩, h => by
    simp only [rawToElems, Array.map_map, Function.comp_def, Elem.expr_ofWF,
      Array.attach_map_subtype_val, TypeExpr.Raw.spliced]
  | .var _, h => by cases h
  | .app _ _, h => by cases h

/-- A list contributes its elements' raw forms. -/
private theorem spliced_expr (l : TypeExpr env scope .list) :
    l.expr.spliced = (l.toElems.map Elem.expr).toList :=
  spliced_eq_rawToElems l.expr l.wf

/-- A closed literal contributes its types' raw forms. -/
private theorem spliced_eq_rawElems : ∀ (x : TypeExpr.Raw)
    (hx : TypeExpr.WFList (env.RefBefore env.size) #[] x),
    x.spliced = ((rawElems x hx).map (·.expr)).toList
  | .list ⟨es⟩, h => by
    simp only [rawElems, Array.map_map, Function.comp_def, Array.attach_map_subtype_val,
      TypeExpr.Raw.spliced]
  | .var _, h => by cases h
  | .app _ _, h => by cases h

/-- A raw element whose instance is an element of a literal contributes that instance. -/
private theorem instantiateElem_of_isElem (args : Array TypeExpr.Raw) {e : TypeExpr.Raw}
    (h : (e.instantiate args).isElem = true) :
    TypeExpr.Raw.instantiateElem args e = [e.instantiate args] := by
  cases e with
  | var i =>
    simp only [TypeExpr.Raw.instantiate] at h
    simp only [TypeExpr.Raw.instantiateElem, TypeExpr.Raw.instantiate]
    revert h
    generalize args[i]?.getD (.var i) = x
    intro h
    cases x with
    | var => rfl
    | app => rfl
    | list => simp [TypeExpr.Raw.isElem] at h
  | app => rfl
  | list => rfl

/-- The raw elements an element instantiates to. -/
private theorem map_expr_instantiate (a : TypeArgs env scope scope₁) :
    ∀ e : Elem env scope, ((e.instantiate a).map Elem.expr).toList =
      TypeExpr.Raw.instantiateElem (a.args.map (·.expr)) e.expr
  | .ty t => by
    have hk : (t.instantiate a).expr.kind scope₁ = .type := (t.instantiate a).wf.kind_eq
    rw [TypeExpr.expr_instantiate] at hk
    simp only [Elem.instantiate, Elem.expr, List.map_toArray, List.map_cons, List.map_nil,
      TypeExpr.expr_instantiate]
    exact (instantiateElem_of_isElem _ (TypeExpr.Raw.isElem_of_kind hk)).symm
  | .splice j h => by
    simp only [Elem.instantiate, Elem.expr, TypeExpr.Raw.instantiateElem,
      TypeArgs.expr_listAt a j h, Option.getD_some]
    exact (spliced_expr (a.listAt j h)).symm

end TypeList

namespace TypeExpr

variable {env : Env α} {scope scope₁ : Array Kind}

/-- A list instantiates element by element: each type to its instance, and each list variable
spliced in to its argument's elements. -/
public theorem toElems_instantiate (a : TypeArgs env scope scope₁)
    (l : TypeExpr env scope .list) :
    (l.instantiate a).toElems = l.toElems.flatMap (·.instantiate a) := by
  apply Array.map_inj_right (fun _ _ => TypeList.Elem.expr_inj) |>.mp
  apply Array.toList_inj.mp
  rw [← TypeList.spliced_expr, expr_instantiate, ← TypeList.list_map_expr_rawToElems l.expr l.wf,
    TypeExpr.Raw.instantiate_list, TypeExpr.Raw.spliced]
  simp only [Array.toList_map, Array.toList_flatMap, List.map_flatMap, List.flatMap_map]
  exact congrArg (fun f => List.flatMap f _)
    (funext fun e => by rw [← Array.toList_map]; exact (TypeList.map_expr_instantiate a e).symm)

/-- A closed list's elements are its types. -/
public theorem toElems_eq_elems (l : TypeList env) : l.toElems = l.elems.map .ty := by
  apply Array.map_inj_right (fun _ _ => TypeList.Elem.expr_inj) |>.mp
  apply Array.toList_inj.mp
  rw [← TypeList.spliced_expr, TypeList.spliced_eq_rawElems l.expr l.wf, Array.map_map]
  rfl

/-- The closed types an argument stands for at `a`: a type its instance, and a list its
instance's elements.  A successor's payload entry passes one value of each. -/
@[expose] public def _root_.Strata.Mantle.TypeArg.typesAt :
    TypeArg env scope → TypeArgs env scope → Array (TypeExpr env)
  | ⟨.type, t⟩, a => #[t.instantiate a]
  | ⟨.list, l⟩, a => (l.instantiate a).elems

/-- `ofTypes ts`'s types are `ts`. -/
@[simp] public theorem elems_ofTypes (ts : Array (TypeExpr env)) :
    (TypeList.ofTypes ts).elems = ts := by
  have h := toElems_eq_elems (TypeList.ofTypes ts)
  rw [toElems_ofTypes] at h
  exact (Array.map_inj_right fun _ _ h => by cases h; rfl).mp h.symm

end TypeExpr

/-- The raw form of an argument. -/
public def TypeArg.toRaw {env : Env α} {scope : Array Kind} (a : TypeArg env scope) :
    TypeExpr.Raw := a.expr

/-- A type argument's raw form is the type's. -/
@[simp] public theorem TypeArg.toRaw_ty {env : Env α} {scope : Array Kind}
    (t : TypeExpr env scope) : (TypeArg.ty t).toRaw = t.toRaw := by
  simp [TypeArg.toRaw, TypeArg.expr, TypeExpr.toRaw]

/-- A list argument's raw form is the list's. -/
@[simp] public theorem TypeArg.toRaw_list {env : Env α} {scope : Array Kind}
    (l : TypeList env scope) : (TypeArg.list l).toRaw = l.toRaw := by
  simp [TypeArg.toRaw, TypeArg.expr, TypeExpr.toRaw]

/-- `toRaw` is the raw form. -/
theorem TypeArg.toRaw_eq_expr {env : Env α} {scope : Array Kind} (a : TypeArg env scope) :
    a.toRaw = a.expr := rfl

/-- The argument a raw expression stands for, a type or a list by its kind, if it is well
formed in `env` and `scope`.  The builder checks the arguments it infers with it. -/
public def TypeArg.check? (env : Env α) (scope : Array Kind) (e : TypeExpr.Raw) :
    Option (TypeArg env scope) :=
  if h : TypeExpr.Raw.checkAt env.raw env.size scope e = true then
    some (TypeArg.ofWF e (TypeExpr.Raw.wfRel_of_checkAt e h))
  else none

/-- What `check?` accepts, it returns unchanged. -/
public theorem TypeArg.toRaw_of_check? {env : Env α} {scope : Array Kind} {e : TypeExpr.Raw}
    {a : TypeArg env scope} (h : TypeArg.check? env scope e = some a) : a.toRaw = e := by
  unfold TypeArg.check? at h
  split at h
  · cases h
    rfl
  · cases h

/-- Fold over an argument, as `TypeExpr.fold` does. -/
public def TypeArg.fold {env : Env α} {scope : Array Kind} {β : Type _}
    (var : Nat → Kind → β) (app : Name → Array β → β) (list : Array β → β)
    (a : TypeArg env scope) : β :=
  a.val.fold var app list

/-- Arguments with equal raw forms are equal: the raw form determines the kind. -/
theorem TypeArg.expr_inj {env : Env α} {scope : Array Kind} :
    ∀ {a b : TypeArg env scope}, a.expr = b.expr → a = b
  | ⟨_, t₁⟩, ⟨_, t₂⟩, h => by
    have h : t₁.expr = t₂.expr := h
    obtain rfl := t₁.wf.kind_eq.symm.trans ((congrArg (TypeExpr.Raw.kind scope) h).trans
      t₂.wf.kind_eq)
    exact congrArg _ (TypeExpr.eq_iff_expr_eq.mpr h)

/-- Decide equality of type arguments, by their raw forms, which determine the kinds. -/
public def TypeArg.decEq {env : Env α} {scope : Array Kind} (a b : TypeArg env scope) :
    Decidable (a = b) :=
  decidable_of_iff (a.expr = b.expr) ⟨TypeArg.expr_inj, fun h => h ▸ rfl⟩

public instance {env : Env α} {scope : Array Kind} : DecidableEq (TypeArg env scope) :=
  TypeArg.decEq

/-- A hash of a type argument: its raw form's. -/
public def TypeArg.hash {env : Env α} {scope : Array Kind} (a : TypeArg env scope) : UInt64 :=
  Hashable.hash a.expr

public instance {env : Env α} {scope : Array Kind} : Hashable (TypeArg env scope) :=
  ⟨TypeArg.hash⟩

/-- Two applications' type arguments are equal when the arrays of them are. -/
public theorem TypeArgs.eq_iff_args_eq {env : Env α} {params scope : Array Kind}
    {a b : TypeArgs env params scope} : a = b ↔ a.args = b.args := by
  obtain ⟨_, _⟩ := a
  obtain ⟨_, _⟩ := b
  simp

public instance {env : Env α} {params scope : Array Kind} :
    DecidableEq (TypeArgs env params scope) := fun a b =>
  decidable_of_iff (a.args = b.args) TypeArgs.eq_iff_args_eq.symm

public instance {env : Env α} {params scope : Array Kind} :
    Hashable (TypeArgs env params scope) := ⟨fun a => Hashable.hash a.args⟩

/-- Two type arguments are equal when their types are. -/
@[simp] public theorem TypeArg.ty_inj {env : Env α} {scope : Array Kind}
    {t₁ t₂ : TypeExpr env scope} : TypeArg.ty t₁ = TypeArg.ty t₂ ↔ t₁ = t₂ := by
  simp [TypeArg.ty]

/-- Two list arguments are equal when their lists are. -/
@[simp] public theorem TypeArg.list_inj {env : Env α} {scope : Array Kind}
    {l₁ l₂ : TypeList env scope} : TypeArg.list l₁ = TypeArg.list l₂ ↔ l₁ = l₂ := by
  simp [TypeArg.list]

namespace TypeExpr

variable {env : Env α} {scope : Array Kind}

/-- An application stands for its constructor's name applied to what its arguments stand
for. -/
@[simp] public theorem toRaw_appK {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeArg env scope) arity)
    (hk : args.toList.map TypeArg.kind = r.kinds.toList) :
    (appK r args hk).toRaw = .app r.name (args.toArray.map (·.toRaw)) := by
  simp [toRaw, expr_appK, TypeArg.toRaw]

/-- Folding an application applies `app` to the constructor's name and the folded
arguments. -/
@[simp] public theorem fold_appK {β : Type _} (v : Nat → Kind → β) (a : Name → Array β → β)
    (l : Array β → β) {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeArg env scope) arity)
    (hk : args.toList.map TypeArg.kind = r.kinds.toList) :
    (appK r args hk).fold v a l = a r.name (args.toArray.map (·.fold v a l)) := by
  simp [fold, expr_appK, Raw.fold_app, Array.map_map, Function.comp_def, TypeArg.fold,
    TypeArg.expr]

/-- Folding an all-types application applies `app` to the constructor's name and the folded
arguments. -/
@[simp] public theorem fold_app {β : Type _} (v : Nat → Kind → β) (a : Name → Array β → β)
    (l : Array β → β) {arity : Nat} (r : TypeRef env arity)
    (args : Vector (TypeExpr env scope) arity) (hk : r.kinds = .replicate arity .type) :
    (app r args hk).fold v a l = a r.name (args.toArray.map (·.fold v a l)) := by
  simp [app, Array.map_map, Function.comp_def, TypeArg.fold]

end TypeExpr

/-! ### Raw forms, node by node

Each lemma gives a node's raw form from its parts', stated over lists, which reduce on a
literal where `Array.map` does not.  The DSL proves that two spellings of a signature stand
for the same raw data by one of them per node of each type (`InsnSig.carry_eq_of_toRaw`), so
the proof grows with the signature and nothing rewrites a nested term. -/

/-- A list's image, element by element. -/
public theorem map_cons_eq_of {β γ : Type _} {f : β → γ} {a : β} {l : List β} {b : γ}
    {m : List γ} (h₁ : f a = b) (h₂ : l.map f = m) : (a :: l).map f = b :: m := by
  rw [List.map_cons, h₁, h₂]

/-- An option's image. -/
public theorem map_some_eq_of {β γ : Type _} {f : β → γ} {a : β} {b : γ} (h : f a = b) :
    (some a).map f = some b := by
  rw [Option.map_some, h]

/-- Two lists, element by element. -/
public theorem cons_eq_of {β : Type _} {a b : β} {l m : List β} (h₁ : a = b) (h₂ : l = m) :
    a :: l = b :: m := by
  rw [h₁, h₂]

/-- An application, by its arguments. -/
public theorem TypeExpr.Raw.app_eq_of {n : Name} {l m : List TypeExpr.Raw} (h : l = m) :
    TypeExpr.Raw.app n ⟨l⟩ = .app n ⟨m⟩ := by
  rw [h]

/-- A pair, by its second component. -/
public theorem pair_eq_of {β γ : Type _} {a : β} {b c : γ} (h : b = c) : (a, b) = (a, c) := by
  rw [h]

namespace TypeExpr

variable {env : Env α} {scope : Array Kind}

/-- An application's raw form, from its name's and its arguments'. -/
public theorem toRaw_appK_of {arity : Nat} {r : TypeRef env arity}
    {args : Vector (TypeArg env scope) arity}
    {hk : args.toList.map TypeArg.kind = r.kinds.toList} {n : Name} {rs : List TypeExpr.Raw}
    (hn : r.name = n) (ha : args.toList.map TypeArg.toRaw = rs) :
    (appK r args hk).toRaw = .app n ⟨rs⟩ := by
  rw [toRaw_appK, hn, ← ha]
  apply congrArg
  apply Array.toList_inj.mp
  simp [Vector.toList]

/-- An all-types application's raw form, from its name's and its arguments'. -/
public theorem toRaw_app_of {arity : Nat} {r : TypeRef env arity}
    {args : Vector (TypeExpr env scope) arity} {hk : r.kinds = .replicate arity .type}
    {n : Name} {rs : List TypeExpr.Raw} (hn : r.name = n)
    (ha : args.toList.map TypeExpr.toRaw = rs) :
    (app r args hk).toRaw = .app n ⟨rs⟩ := by
  rw [toRaw_app, hn, ← ha]
  apply congrArg
  apply Array.toList_inj.mp
  simp [Vector.toList]

end TypeExpr

/-- A literal's raw form, from its elements'. -/
public theorem TypeList.toRaw_lit_of {env : Env α} {scope : Array Kind}
    {es : Array (TypeList.Elem env scope)} {rs : List TypeExpr.Raw}
    (h : es.toList.map TypeList.Elem.toRaw = rs) : (TypeList.lit es).toRaw = .list ⟨rs⟩ := by
  rw [TypeList.toRaw_lit, ← h]
  apply congrArg
  apply Array.toList_inj.mp
  simp

/-- A type element's raw form is the type's. -/
public theorem TypeList.Elem.toRaw_ty_of {env : Env α} {scope : Array Kind}
    {t : TypeExpr env scope} {r : TypeExpr.Raw} (h : t.toRaw = r) :
    (TypeList.Elem.ty t).toRaw = r := by
  rw [TypeList.Elem.toRaw_ty, h]

/-- A type argument's raw form is the type's. -/
public theorem TypeArg.toRaw_ty_of {env : Env α} {scope : Array Kind}
    {t : TypeExpr env scope} {r : TypeExpr.Raw} (h : t.toRaw = r) :
    (TypeArg.ty t).toRaw = r := by
  rw [TypeArg.toRaw_ty, h]

/-- A list argument's raw form is the list's. -/
public theorem TypeArg.toRaw_list_of {env : Env α} {scope : Array Kind}
    {l : TypeList env scope} {r : TypeExpr.Raw} (h : l.toRaw = r) :
    (TypeArg.list l).toRaw = r := by
  rw [TypeArg.toRaw_list, h]

/-! ## Region signatures, checked

`RegionSig env scope` is a region signature well formed against `env` in `scope`, the kinds of
the variables in scope.  A region binds no variables of its own. -/

/-- The checked signature of a region: the types of its entry block's parameters, and the
type its exit takes.  It is built with `of` and read through `params` and
`returnType`. -/
public structure RegionSig (env : Env α) (scope : Array Kind) where
  private raw : RegionSig.Raw
  private wf : raw.WF (env.RefBefore env.size) scope

namespace RegionSig

variable {env : Env α} {scope : Array Kind}

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

/-- `of`'s raw data, from its parameters' and its return type's.  The distinctness proof is
explicit: unification would not find it. -/
public theorem fields_of {ps : Array (Param (TypeExpr env scope))} {r : TypeExpr env scope}
    (d : (ps.toList.map (·.name)).Nodup) {L : List (String × TypeExpr.Raw)} {R : TypeExpr.Raw}
    (hp : ps.toList.map (fun q => (q.name, q.type.toRaw)) = L) (hr : r.toRaw = R) :
    ((of ps r d).params.toList.map (fun q => (q.name, q.type.toRaw)),
      (of ps r d).returnType.toRaw) = (L, R) := by
  rw [params_of, returnType_of, hp, hr]

/-- The checked form of a well-formed raw region signature. -/
def ofWF (r : RegionSig.Raw) (h : r.WF (env.RefBefore env.size) scope) : RegionSig env scope :=
  ⟨r, h⟩

/-- `ofWF` changes no data. -/
@[simp] theorem raw_ofWF (r : RegionSig.Raw) (h : r.WF (env.RefBefore env.size) scope) :
    (ofWF r h).raw = r := rfl

/-- Region signatures with the same raw data are equal. -/
theorem eq_of_raw_eq {a b : RegionSig env scope} (h : a.raw = b.raw) : a = b := by
  obtain ⟨ra, wa⟩ := a
  obtain ⟨rb, wb⟩ := b
  simp only at h
  subst h
  rfl

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

/-! ## Variadics, checked

`Variadic env scope` is the type of an instruction's trailing operands, in `scope`. -/

/-- The type of an instruction's trailing operands: `each`, a type that each of any number of
operands has, or `spread`, a list whose elements the operands have, one each and in order.  It is
a type argument, a type or a list with its kind; `each` and `spread` match as constructors do. -/
public abbrev Variadic (env : Env α) (scope : Array Kind := #[]) : Type := TypeArg env scope

namespace Variadic

variable {env : Env α} {scope : Array Kind}

/-- `(*xs : τ)`: any number of operands, each of type `τ`. -/
@[match_pattern] public abbrev each (t : TypeExpr env scope) : Variadic env scope := ⟨.type, t⟩

/-- `(*xs : cs)`: exactly one operand per element of `cs`, of that element's type. -/
@[match_pattern] public abbrev spread (cs : TypeList env scope) : Variadic env scope :=
  ⟨.list, cs⟩

/-- An `each` stands for its type. -/
@[simp] public theorem toRaw_each (t : TypeExpr env scope) : (each t).toRaw = t.toRaw := by
  simp [TypeArg.toRaw, TypeArg.expr, TypeExpr.toRaw]

/-- A `spread` stands for its list. -/
@[simp] public theorem toRaw_spread (cs : TypeList env scope) :
    (spread cs).toRaw = cs.toRaw := by
  simp [TypeArg.toRaw, TypeArg.expr, TypeExpr.toRaw]

end Variadic

/-! ## Instruction signatures, checked -/

-- A hand-written signature with no type parameters writes its types in the empty scope, which
-- fixes `typeParams` before its default fires.
/-- Kinds of no type parameters are the empty scope. -/
unif_hint (ps : Array (Param Kind)) where
  ps =?= #[] ⊢ Param.kinds ps =?= #[]

/-- An instruction declaration without its name, with every type expression checked against
`env`. -/
public structure InsnSig (env : Env α) where
  /-- The annotation `addInsn` stores with the declaration.  Nothing else reads it: an `InsnRef`
  resolves its signature up to it, and `carry` keeps it, so it need not be the annotation of the
  declaration in either environment.  `Env.annOf?` reads that annotation. -/
  ann : α
  /-- The variables the signature binds, each a name and a kind, by de Bruijn level: `.var i`
  is `typeParams[i]`.  Their kinds are the scope its type expressions are written in. -/
  typeParams : Array (Param Kind) := #[]
  argTypes : Array (Param (TypeExpr env (Param.kinds typeParams)))
  /-- The trailing variadic operands, if the instruction takes any: their name and their
  type. -/
  variadic : Option (Param (Variadic env (Param.kinds typeParams))) := none
  /-- What the instruction returns, or `none` if it ends its block: a terminal instruction
  never falls through and produces no result. -/
  returnType : Option (TypeExpr env (Param.kinds typeParams))
  /-- The regions the instruction takes, each named and with its own signature under the
  instruction's variables. -/
  regions : Array (Param (RegionSig env (Param.kinds typeParams))) := #[]
  /-- The successors the instruction may transfer to, each named and with the types of the
  values it passes, under the instruction's variables: each entry is a type, one value, or a
  list, one value per element, a spread.  A use site supplies one block per successor, in this
  order. -/
  succs : Array (Param (Array (TypeArg env (Param.kinds typeParams)))) := #[]
  -- Written out, not via `InsnDecl.Raw.paramNames`, so the default `decide` reduces.
  /-- No name is bound twice among the type parameters, arguments, variadic, regions and
  successors. -/
  distinct : (typeParams.toList.map (·.name) ++ argTypes.toList.map (·.name) ++
    (variadic.map (·.name)).toList ++ regions.toList.map (·.name) ++
    succs.toList.map (·.name)).Nodup := by decide

namespace InsnSig

/-- How many type variables the signature binds: one type argument per type parameter.
Reducible, so it computes on a literal signature. -/
@[expose, reducible] public def typeArgc {env : Env α} (s : InsnSig env) : Nat :=
  s.typeParams.size

/-- The kinds of the variables the signature binds: the scope its type expressions are written
in.  Reducible, as `typeArgc` is. -/
@[expose, reducible] public def scope {env : Env α} (s : InsnSig env) : Array Kind :=
  Param.kinds s.typeParams

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
  obtain ⟨ann, typeParams, argTypes, variadic, returnType, regions, succs, distinct⟩ := s
  refine InsnDecl.Raw.wf_mk ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [decl, Array.mem_map] at hp
    obtain ⟨q, -, rfl⟩ := hp
    simpa [decl] using q.type.wf
  · intro v hv
    simp only [decl, Option.mem_def, Option.map_eq_some_iff] at hv
    obtain ⟨q, -, rfl⟩ := hv
    exact q.type.wfRel
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
    exact u.wfRel
  · simpa [decl, InsnDecl.Raw.paramNames, Function.comp_def] using distinct

/-- The checked form of a well-formed raw declaration. -/
def ofWF {env : Env α} (d : InsnDecl.Raw α)
    (h : InsnDecl.Raw.WF (env.RefBefore env.size) d) : InsnSig env where
  ann := d.ann
  typeParams := d.typeParams
  argTypes := d.argTypes.attach.map fun p =>
    ⟨p.val.name, ⟨p.val.type, InsnDecl.Raw.wf_argTypes h p.val p.property⟩⟩
  variadic := d.variadic.attach.map fun v =>
    ⟨v.val.name,
      .ofWF v.val.type (InsnDecl.Raw.wf_variadic h v.val (Option.mem_def.mpr v.property))⟩
  returnType := d.returnType.attach.map fun t =>
    ⟨t.val, InsnDecl.Raw.wf_returnType h t.val (Option.mem_def.mpr t.property)⟩
  regions := d.regions.attach.map fun r =>
    ⟨r.val.name, RegionSig.ofWF r.val.type (InsnDecl.Raw.wf_regions h r.val r.property)⟩
  succs := d.succs.attach.map fun s =>
    ⟨s.val.name, s.val.type.attach.map fun t =>
      .ofWF t.val (InsnDecl.Raw.wf_succs h s.val s.property t.val t.property)⟩
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

/-- A declaration is named by the name it was erased under. -/
theorem name_decl {env : Env α} (i : InsnSig env) (name : Name)
    (kind : InsnKind := .decl) : (i.decl name kind).name = name := by
  simp [decl]

/-- A declaration has the kind it was declared at. -/
theorem kind_decl {env : Env α} (i : InsnSig env) (name : Name)
    (kind : InsnKind := .decl) : (i.decl name kind).kind = kind := by
  simp [decl]

/-- A signature is determined by the declaration it erases to. -/
theorem eq_of_decl_eq {env : Env α} {s₁ s₂ : InsnSig env} {n : Name} {k : InsnKind}
    (h : s₁.decl n k = s₂.decl n k) : s₁ = s₂ := by
  obtain ⟨ann₁, tp₁, args₁, var₁, ret₁, reg₁, succ₁, d₁⟩ := s₁
  obtain ⟨ann₂, tp₂, args₂, var₂, ret₂, reg₂, succ₂, d₂⟩ := s₂
  simp only [decl, InsnDecl.Raw.mk.injEq] at h
  obtain ⟨rfl, -, rfl, hargs, hvar, hret, hreg, hsucc, -⟩ := h
  have hp : ∀ {n : Array Kind} {a b : Param (TypeExpr env n)}, a.name = b.name →
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
    rename_i a b
    obtain ⟨_, _⟩ := a; obtain ⟨_, _⟩ := b
    rw [Param.mk.injEq]
    exact ⟨hvar.1, TypeArg.expr_inj hvar.2⟩
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
    exact TypeArg.expr_inj this
  subst hargs' hvar' hret' hreg' hsucc'
  rfl

/-- Two signatures, in any two environments, declare the same instruction up to its annotation
and kind when everything else they declare stands for the same raw data: the same type
parameters, argument and variadic names and types, return type (or its absence), regions and
successors.  The conclusion is `InsnDecl.Raw.RefinedBy`'s `erase_eq`, so this is how a
refinement's instruction is compared with the original's. -/
theorem erase_decl_eq_of_toRaw {e₁ e₂ : Env α} {s₁ : InsnSig e₁} {s₂ : InsnSig e₂}
    (name : Name) (k₁ k₂ : InsnKind) (htp : s₁.typeParams = s₂.typeParams)
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
      s₂.succs.map (fun p => (p.name, p.type.map (·.toRaw)))) :
    (s₂.decl name k₂).erase =
      { (s₁.decl name k₁).erase with kind := (s₂.decl name k₂).kind } := by
  simp only [TypeExpr.toRaw_eq_expr, TypeArg.toRaw_eq_expr] at hargs hvar hret hregions hsuccs
  -- each field of the erasure is the corresponding hypothesis, re-paired
  have hraw : ∀ {env : Env α} {scope : Array Kind},
      (fun p : Param (RegionSig env scope) => (⟨p.name, p.type.raw⟩ : Param RegionSig.Raw)) =
        fun x => ⟨x.name, ⟨x.type.params.map (fun y => ⟨y.name, y.type.expr⟩),
          x.type.returnType.expr⟩⟩ := by
    intro env scope
    funext p
    rw [RegionSig.map_params]
    rfl
  have hargs₁ := congrArg (Array.map (fun x => (⟨x.1, x.2⟩ : Param TypeExpr.Raw))) hargs
  have hregions₁ := congrArg (Array.map (fun x => (⟨x.1,
    ⟨x.2.1.map (fun y => (⟨y.1, y.2⟩ : Param TypeExpr.Raw)), x.2.2⟩⟩ : Param RegionSig.Raw)))
    hregions
  have hvar₁ := congrArg (Option.map (fun x => (⟨x.1, x.2⟩ : Param TypeExpr.Raw))) hvar
  have hsuccs₁ :=
    congrArg (Array.map (fun x => (⟨x.1, x.2⟩ : Param (Array TypeExpr.Raw)))) hsuccs
  simp only [Array.map_map, Option.map_map, Function.comp_def] at hargs₁ hvar₁ hregions₁ hsuccs₁
  simp only [decl, InsnDecl.Raw.erase, InsnDecl.Raw.mk.injEq, and_true, true_and]
  refine ⟨htp.symm, hargs₁.symm, hvar₁.symm, hret.symm, ?_, hsuccs₁.symm⟩
  rw [hraw, hraw]
  exact hregions₁.symm

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
  simp only [TypeExpr.toRaw_eq_expr, TypeArg.toRaw_eq_expr] at hargs hvar hret hregions hsuccs
  apply eq_of_decl_eq (n := .base) (k := .decl)
  -- each field of the erasure is the corresponding hypothesis, re-paired
  have hraw : ∀ {scope : Array Kind},
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
parameter, then the variadic's.  An `each` variadic gives its type to each trailing operand; a
`spread` one demands exactly its list's elements.  `none` when the operands are too few, or
too many for the variadic. -/
@[expose] public def operandTypes? {env : Env α} (isig : InsnSig env)
    (typeArgs : TypeArgs env isig.scope) (argc : Nat) : Option (Array (TypeExpr env)) :=
  let fixed := isig.argTypes.map (·.type.instantiate typeArgs)
  match isig.variadic with
  | none => if argc = fixed.size then some fixed else none
  | some ⟨_, .each t⟩ =>
    if fixed.size ≤ argc then
      some (fixed ++ Array.replicate (argc - fixed.size) (t.instantiate typeArgs))
    else
      none
  | some ⟨_, .spread cs⟩ =>
    let tail := (cs.instantiate typeArgs).elems
    if argc = fixed.size + tail.size then some (fixed ++ tail) else none

/-- The types `n` variadic operands of `isig` take at `typeArgs`: none without a variadic, `n`
copies of an `each` variadic's type, and a spread's list's types, whatever `n`. -/
@[expose] public def variadicTypes {env : Env α} (isig : InsnSig env)
    (typeArgs : TypeArgs env isig.scope) (n : Nat) : Array (TypeExpr env) :=
  match isig.variadic with
  | none => #[]
  | some ⟨_, .each t⟩ => .replicate n (t.instantiate typeArgs)
  | some ⟨_, .spread cs⟩ => (cs.instantiate typeArgs).elems

/-- What `operandTypes?` gives: the argument types at `typeArgs`, then the variadic's, when
there are `argc` of them in all.  A spread's types are its list's elements, each instantiated
(`TypeExpr.toElems_instantiate`). -/
public theorem operandTypes?_eq_some_iff {env : Env α} (isig : InsnSig env)
    (typeArgs : TypeArgs env isig.scope) (argc : Nat) (ts : Array (TypeExpr env)) :
    isig.operandTypes? typeArgs argc = some ts ↔
      ts = isig.argTypes.map (·.type.instantiate typeArgs) ++
          isig.variadicTypes typeArgs (argc - isig.argTypes.size) ∧ ts.size = argc := by
  unfold operandTypes? variadicTypes
  rcases isig.variadic with _ | ⟨_, ⟨_ | _, t⟩⟩ <;>
    simp only [Array.size_map, Array.append_empty] <;>
    split <;> rename_i h
  · constructor
    · intro he
      obtain rfl := Option.some.inj he
      simp [h]
    · rintro ⟨rfl, -⟩
      rfl
  · simp only [reduceCtorEq, false_iff, not_and]
    rintro rfl hs
    exact h (by simpa using hs.symm)
  · constructor
    · intro he
      obtain rfl := Option.some.inj he
      simp only [Array.size_append, Array.size_map, Array.size_replicate, true_and]
      omega
    · rintro ⟨rfl, -⟩
      rfl
  · simp only [reduceCtorEq, false_iff, not_and]
    rintro rfl hs
    simp only [Array.size_append, Array.size_map, Array.size_replicate] at hs
    omega
  · constructor
    · intro he
      obtain rfl := Option.some.inj he
      simp only [Array.size_append, Array.size_map, true_and, h]
    · rintro ⟨rfl, -⟩
      rfl
  · simp only [reduceCtorEq, false_iff, not_and]
    rintro rfl hs
    simp only [Array.size_append, Array.size_map] at hs
    omega

end InsnSig

/-! ## Declared instructions, and signatures up to annotation -/

/-- `name` is declared in `s` as the instruction with signature `σ` and kind `k`, its
annotation included. -/
public def Env.DeclaresInsn (s : Env α) (name : Name) (σ : InsnSig s) (k : InsnKind) : Prop :=
  s.declOf? name = some (.insn (σ.decl name k))

namespace InsnSig

/-- `σ₁` and `σ₂`, of any two environments, declare the same instruction up to its annotation:
the same type parameters, arguments, variadic, return type, regions and successors. -/
public def EqUpToAnn {s t : Env α} (σ₁ : InsnSig s) (σ₂ : InsnSig t) : Prop :=
  (σ₂.decl .base).erase = (σ₁.decl .base).erase

section
variable {s t u : Env α}

/-- A signature is itself up to annotation. -/
public theorem EqUpToAnn.refl (σ : InsnSig s) : σ.EqUpToAnn σ := by
  unfold EqUpToAnn
  rfl

/-- Equality up to annotation composes. -/
public theorem EqUpToAnn.trans {σ₁ : InsnSig s} {σ₂ : InsnSig t} {σ₃ : InsnSig u}
    (h₁ : σ₁.EqUpToAnn σ₂) (h₂ : σ₂.EqUpToAnn σ₃) : σ₁.EqUpToAnn σ₃ := by
  unfold EqUpToAnn at *
  exact h₂.trans h₁

/-- Two signatures are equal up to annotation when everything they declare stands for the same
raw data.  `simp` proves the hypotheses for a signature written differently, such as one
`addData` derives. -/
public theorem EqUpToAnn.of_toRaw {σ₁ : InsnSig s} {σ₂ : InsnSig t}
    (htp : σ₁.typeParams = σ₂.typeParams)
    (hargs : σ₁.argTypes.map (fun p => (p.name, p.type.toRaw)) =
      σ₂.argTypes.map (fun p => (p.name, p.type.toRaw)))
    (hvar : σ₁.variadic.map (fun p => (p.name, p.type.toRaw)) =
      σ₂.variadic.map (fun p => (p.name, p.type.toRaw)))
    (hret : σ₁.returnType.map (·.toRaw) = σ₂.returnType.map (·.toRaw))
    (hregions : σ₁.regions.map (fun p => (p.name,
        p.type.params.map (fun q => (q.name, q.type.toRaw)), p.type.returnType.toRaw)) =
      σ₂.regions.map (fun p => (p.name,
        p.type.params.map (fun q => (q.name, q.type.toRaw)), p.type.returnType.toRaw)))
    (hsuccs : σ₁.succs.map (fun p => (p.name, p.type.map (·.toRaw))) =
      σ₂.succs.map (fun p => (p.name, p.type.map (·.toRaw)))) :
    σ₁.EqUpToAnn σ₂ := by
  unfold EqUpToAnn
  exact erase_decl_eq_of_toRaw .base .decl .decl htp hargs hvar hret hregions hsuccs

/-- Signatures equal up to annotation declare, under one name, the same instruction up to its
annotation and kind. -/
theorem eqUpToAnn_iff_decl {σ₁ : InsnSig s} {σ₂ : InsnSig t} {n : Name} {k₁ k₂ : InsnKind} :
    σ₁.EqUpToAnn σ₂ ↔ (σ₂.decl n k₂).erase = { (σ₁.decl n k₁).erase with kind := k₂ } := by
  unfold EqUpToAnn
  constructor
  · intro he
    exact congrArg (fun d : InsnDecl.Raw Unit => { d with name := n, kind := k₂ }) he
  · intro he
    exact congrArg (fun d : InsnDecl.Raw Unit => { d with name := .base, kind := .decl }) he

end

end InsnSig

namespace Env

/-- A name declared as an instruction is declared as the signature it stands for. -/
theorem declaresInsn_ofWF {s : Env α} {n : Name} {d : InsnDecl.Raw α}
    (h : s.declOf? n = some (.insn d)) :
    s.DeclaresInsn n (InsnSig.ofWF d (Decl.Raw.wf_insn_iff.mp (declWF_of_declOf? h))) d.kind := by
  have hname : d.name = n := by simpa using name_of_declOf? h
  unfold DeclaresInsn
  rw [InsnSig.decl_ofWF_of_name _ hname]
  exact h

/-- A reference is valid at the end of an environment exactly when the name resolves to a
type of those kinds. -/
theorem refBefore_size_iff {s : Env α} {n : Name} {a : Array Kind} :
    s.RefBefore s.size n a ↔ ∃ d, s.raw.typeOf? n = some d ∧ d.kinds = a := by
  constructor
  · intro hr
    obtain ⟨_, d, _, _, hd, ha⟩ := Raw.refBefore_iff.mp hr
    exact ⟨d, hd, ha⟩
  · rintro ⟨d, hd, rfl⟩
    exact refBefore_of_resolves hd

/-- The annotation `n` is declared with, if `n` is declared: an instruction's own, or the
annotation of the type `n` names, which for a datatype is its member's. -/
public def annOf? (s : Env α) (n : Name) : Option α :=
  match s.declOf? n with
  | some (.insn d) => some d.ann
  | _ => (s.typeOf? n).map (·.ann)

/-- An instruction's annotation is its own. -/
theorem annOf?_of_insn {s : Env α} {n : Name} {d : InsnDecl.Raw α}
    (h : s.declOf? n = some (.insn d)) :
    s.annOf? n = some d.ann := by
  unfold Env.annOf?
  rw [h]

/-- A type's annotation is its declaration's. -/
theorem annOf?_of_type {s : Env α} {n : Name} {d : TypeDecl α} (h : s.declOf? n = some (.type d)) :
    s.annOf? n = some d.ann := by
  unfold Env.annOf?
  rw [h]
  show (s.typeOf? n).map (·.ann) = _
  rw [typeOf?_of_type h]
  rfl

end Env

/-! ## Carrying checked forms

A type expression, a region or instruction signature, or a reference checked against `s` is
checked against every `t` that keeps `s`'s lookups: `KeepsTypes` for types, and `KeepsInsns`
for instructions too.  An extension keeps both; so does a refinement
(`StrataMantle.Env.Refine`).  `ofSubset` carries along an extension. -/

namespace Env

/-- `t` names every type `s` names, up to its annotation. -/
public structure KeepsTypes (s t : Env α) : Prop where
  type : ∀ {n : Name} {d : TypeDecl α}, s.typeOf? n = some d →
    ∃ d', t.typeOf? n = some d' ∧ d'.erase = d.erase

/-- `t` declares every instruction `s` declares, up to its annotation and kind. -/
public structure KeepsInsns (s t : Env α) : Prop where
  insn : ∀ {n : Name} {σ : InsnSig s} {k : InsnKind}, s.DeclaresInsn n σ k →
    ∃ σ' k', t.DeclaresInsn n σ' k' ∧ σ.EqUpToAnn σ'

/-- Keeping types composes. -/
public theorem KeepsTypes.trans {s t u : Env α} (h₁ : s.KeepsTypes t) (h₂ : t.KeepsTypes u) :
    s.KeepsTypes u where
  type hd :=
    let ⟨_, hd₂, he₁⟩ := h₁.type hd
    let ⟨d₃, hd₃, he₂⟩ := h₂.type hd₂
    ⟨d₃, hd₃, he₂.trans he₁⟩

/-- An extension keeps every type. -/
public theorem keepsTypes_of_subset {s t : Env α} (h : s ⊆ t) : s.KeepsTypes t :=
  ⟨fun hd => ⟨_, typeOf?_of_subset h hd, rfl⟩⟩

/-- A name that resolves to a type in `s` resolves to it in every environment that keeps
`s`'s types. -/
public theorem ResolvesType.carry {s t : Env α} (h : s.KeepsTypes t) {n : Name} {d : TypeDecl α}
    (hd : s.ResolvesType n d) : t.ResolvesType n d := by
  obtain ⟨d₁, hd₁, he₁⟩ := hd
  obtain ⟨d₂, hd₂, he₂⟩ := h.type hd₁
  exact ⟨d₂, hd₂, he₂.trans he₁⟩

/-- A reference valid in `s` is valid in every environment that keeps `s`'s types. -/
theorem refBefore_size_of_keepsTypes {s t : Env α} (h : s.KeepsTypes t) {n : Name}
    {a : Array Kind} (hr : s.RefBefore s.size n a) : t.RefBefore t.size n a := by
  obtain ⟨d₁, hd₁, rfl⟩ := refBefore_size_iff.mp hr
  obtain ⟨d₂, hd₂, he⟩ := h.type hd₁
  exact refBefore_size_iff.mpr ⟨d₂, hd₂, TypeDecl.kinds_eq_of_erase_eq he⟩

variable {t s : Env α}

/-- A name's constructor address is that of the instruction it names. -/
theorem ctorAddr?_of_insnOf? {n : Name} {d : InsnDecl.Raw α} (h : s.insnOf? n = some d) :
    s.ctorAddr? n = d.kind.ctor? := by
  unfold ctorAddr? Raw.ctorAddr?
  rw [show s.raw.decls[n]? = some (.insn d) from insnOf?_eq_some_iff.mp h]

/-- A name that is a constructor is declared as an instruction of that kind. -/
public theorem exists_declaresInsn_of_ctorAddr? {n : Name} {a : CtorAddr}
    (h : s.ctorAddr? n = some a) : ∃ σ k, s.DeclaresInsn n σ k ∧ k.ctor? = some a := by
  unfold ctorAddr? Raw.ctorAddr? at h
  split at h
  next d hd => exact ⟨_, _, declaresInsn_ofWF hd, h⟩
  next => exact absurd h (by simp)

end Env

namespace TypeExpr

variable {scope : Array Kind} {k : Kind}

/-- Reinterpret in an environment that keeps the types. -/
public def carry {s t : Env α} (h : s.KeepsTypes t) (e : TypeExpr s scope k) :
    TypeExpr t scope k :=
  ⟨e.expr, e.wf.mono fun _ _ hr => Env.refBefore_size_of_keepsTypes h hr⟩

/-- Reinterpret in an extension. -/
public abbrev ofSubset {s t : Env α} (h : s ⊆ t) (e : TypeExpr s scope k) : TypeExpr t scope k :=
  e.carry (Env.keepsTypes_of_subset h)

/-- Reinterpreting keeps the raw expression. -/
theorem expr_carry {s t : Env α} (h : s.KeepsTypes t) (e : TypeExpr s scope k) :
    (e.carry h).expr = e.expr := rfl

/-- Reinterpreting changes nothing an expression stands for. -/
@[simp] public theorem toRaw_carry {s t : Env α} (h : s.KeepsTypes t) (e : TypeExpr s scope k) :
    (e.carry h).toRaw = e.toRaw := by
  simp [toRaw, expr_carry]

end TypeExpr

namespace TypeList

variable {scope : Array Kind}

/-- Reinterpret an element in an environment that keeps the types. -/
public def Elem.carry {s t : Env α} (h : s.KeepsTypes t) :
    Elem s scope → Elem t scope
  | .ty e => .ty (e.carry h)
  | .splice j hj => .splice j hj

end TypeList

namespace TypeArg

variable {scope : Array Kind}

/-- Reinterpret an argument in an environment that keeps the types. -/
public def carry {s t : Env α} (h : s.KeepsTypes t) (a : TypeArg s scope) : TypeArg t scope :=
  ⟨a.kind, a.val.carry h⟩

/-- Carrying keeps an argument's kind. -/
@[simp] public theorem kind_carry {s t : Env α} (h : s.KeepsTypes t) (a : TypeArg s scope) :
    (a.carry h).kind = a.kind := by
  simp [carry]

/-- Reinterpreting keeps the raw form. -/
theorem expr_carry {s t : Env α} (h : s.KeepsTypes t) (a : TypeArg s scope) :
    (a.carry h).expr = a.expr := rfl

/-- Reinterpreting changes nothing an argument stands for. -/
@[simp] public theorem toRaw_carry {s t : Env α} (h : s.KeepsTypes t) (a : TypeArg s scope) :
    (a.carry h).toRaw = a.toRaw := by
  simp [TypeArg.toRaw, expr_carry]

end TypeArg

/-- Reinterpret an application's type arguments in an environment that keeps the types. -/
public def TypeArgs.carry {s t : Env α} (h : s.KeepsTypes t) {params scope : Array Kind}
    (a : TypeArgs s params scope) : TypeArgs t params scope :=
  ⟨a.args.map (·.carry h), by simpa [Function.comp_def] using a.kinds⟩

/-- Instantiating commutes with reinterpreting: a signature carried into an extension
instantiates at carried arguments to what it instantiated to, carried. -/
public theorem TypeExpr.instantiate_carry {s t : Env α} (h : s.KeepsTypes t)
    {scope scope₁ : Array Kind} {k : Kind} (args : TypeArgs s scope scope₁)
    (e : TypeExpr s scope k) :
    (e.carry h).instantiate (args.carry h) = (e.instantiate args).carry h :=
  TypeExpr.eq_iff_expr_eq.mpr (by
    simp [TypeExpr.expr_instantiate, TypeExpr.expr_carry, TypeArgs.carry, Array.map_map,
      Function.comp_def, TypeArg.expr_carry])

-- Exposed: the DSL's kind proofs (`refKinds`) are `rfl` through it.
/-- Carry a type reference into an environment that keeps the types. -/
@[expose] public def TypeRef.carry {s t : Env α} {arity : Nat} (h : s.KeepsTypes t)
    (r : TypeRef s arity) : TypeRef t arity :=
  ⟨r.name, r.decl, r.matchArity, r.resolves.carry h⟩

/-- Carry a type reference into an extension. -/
public abbrev TypeRef.ofSubset {s t : Env α} {arity : Nat} (h : s ⊆ t)
    (r : TypeRef s arity) : TypeRef t arity :=
  r.carry (Env.keepsTypes_of_subset h)

/-- Carrying a type reference keeps its name. -/
@[simp] public theorem name_TypeRef_carry {s t : Env α} {arity : Nat} (h : s.KeepsTypes t)
    (r : TypeRef s arity) : (r.carry h).name = r.name := by
  simp [TypeRef.carry]

/-- Carrying a type reference keeps its declaration. -/
@[simp] public theorem decl_TypeRef_carry {s t : Env α} {arity : Nat} (h : s.KeepsTypes t)
    (r : TypeRef s arity) : (r.carry h).decl = r.decl := by
  simp [TypeRef.carry]

/-- Carrying a type reference keeps its kinds. -/
@[simp] public theorem kinds_TypeRef_carry {s t : Env α} {arity : Nat} (h : s.KeepsTypes t)
    (r : TypeRef s arity) : (r.carry h).kinds = r.kinds := by
  simp [TypeRef.kinds]

/-! ### Normal forms under reinterpretation

`simp` pushes `carry` (and so `ofSubset`) down to the references and compares applications by
name: it proves two signatures built alike equal (`InsnRef.cast`). -/

/-- Carrying a reference twice is carrying it once. -/
@[simp] public theorem TypeRef.carry_carry {s t u : Env α} {arity : Nat} (h₁ : s.KeepsTypes t)
    (h₂ : t.KeepsTypes u) (r : TypeRef s arity) :
    (r.carry h₁).carry h₂ = r.carry (h₁.trans h₂) := by
  simp [TypeRef.carry]

namespace TypeExpr

/-- Reinterpreting a type variable gives the variable. -/
@[simp] public theorem carry_var {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    (i : Nat) (hi : scope[i]? = some .type) : (var (env := s) i hi).carry h = var i hi :=
  eq_iff_expr_eq.mpr (by simp [expr_carry, expr_var])

/-- Reinterpreting an application reinterprets the reference and the arguments. -/
@[simp] public theorem carry_appK {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    {arity : Nat}
    (r : TypeRef s arity) (args : Vector (TypeArg s scope) arity)
    (hk : args.toList.map TypeArg.kind = r.kinds.toList) :
    (appK r args hk).carry h =
      appK (r.carry h) (args.map (·.carry h))
        (by simpa [Vector.toList_map, Function.comp_def] using hk) :=
  eq_iff_expr_eq.mpr (by
    simp only [expr_carry, expr_appK, name_TypeRef_carry, Vector.toArray_map, Array.map_map,
      TypeExpr.Raw.app.injEq, true_and]
    exact Array.map_congr_left fun x _ => TypeArg.expr_carry h x)

/-- Two applications are equal when they apply the same name to equal arguments. -/
@[simp] public theorem appK_eq_appK_iff {env : Env α} {scope : Array Kind} {arity : Nat}
    {r₁ r₂ : TypeRef env arity} {a₁ a₂ : Vector (TypeArg env scope) arity}
    {h₁ : a₁.toList.map TypeArg.kind = r₁.kinds.toList}
    {h₂ : a₂.toList.map TypeArg.kind = r₂.kinds.toList} :
    appK r₁ a₁ h₁ = appK r₂ a₂ h₂ ↔ r₁.name = r₂.name ∧ a₁ = a₂ := by
  rw [eq_iff_expr_eq, expr_appK, expr_appK, TypeExpr.Raw.app.injEq,
    Array.map_inj_right (fun _ _ h => TypeArg.expr_inj h), Vector.toArray_inj]

/-- Reinterpreting an application reinterprets the reference and the arguments. -/
@[simp] public theorem carry_app {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    {arity : Nat}
    (r : TypeRef s arity) (args : Vector (TypeExpr s scope) arity)
    (hk : r.kinds = .replicate arity .type) :
    (app r args hk).carry h =
      app (r.carry h) (args.map (·.carry h)) ((kinds_TypeRef_carry h r).trans hk) := by
  simp [app, carry_appK, Vector.map_map, Function.comp_def, TypeArg.carry]

/-- Two applications are equal when they apply the same name to equal arguments. -/
@[simp] public theorem app_eq_app_iff {env : Env α} {scope : Array Kind} {arity : Nat}
    {r₁ r₂ : TypeRef env arity} {a₁ a₂ : Vector (TypeExpr env scope) arity}
    {h₁ : r₁.kinds = .replicate arity .type} {h₂ : r₂.kinds = .replicate arity .type} :
    app r₁ a₁ h₁ = app r₂ a₂ h₂ ↔ r₁.name = r₂.name ∧ a₁ = a₂ := by
  rw [app, app, appK_eq_appK_iff, Vector.map_inj_right fun _ _ h => TypeArg.ty_inj.mp h]

end TypeExpr

/-- Reinterpreting a type argument reinterprets the type. -/
@[simp] public theorem TypeArg.carry_ty {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    (e : TypeExpr s scope) : (TypeArg.ty e).carry h = .ty (e.carry h) := by
  simp [TypeArg.carry]

/-- Reinterpreting a list argument reinterprets the list. -/
@[simp] public theorem TypeArg.carry_list {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    (l : TypeList s scope) : (TypeArg.list l).carry h = .list (l.carry h) := by
  simp [TypeArg.carry]

namespace TypeList

/-- Reinterpreting a literal reinterprets its elements. -/
@[simp] public theorem carry_lit {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    (es : Array (Elem s scope)) : (lit es).carry h = lit (es.map (·.carry h)) :=
  TypeExpr.eq_iff_expr_eq.mpr (by
    simp only [TypeExpr.carry, lit, Array.map_map, TypeExpr.Raw.list.injEq]
    apply Array.map_congr_left
    intro e _
    cases e <;> simp [Elem.expr, Elem.carry, TypeExpr.expr_carry])

/-- Reinterpreting a type element reinterprets the type. -/
@[simp] public theorem Elem.carry_ty {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    (e : TypeExpr s scope) : (Elem.ty e).carry h = .ty (e.carry h) := by
  simp [Elem.carry]

/-- Reinterpreting a splice gives the splice. -/
@[simp] public theorem Elem.carry_splice {s t : Env α} (h : s.KeepsTypes t) {scope : Array Kind}
    (j : Nat) (hj : scope[j]? = some .list) : (Elem.splice (env := s) j hj).carry h =
      .splice j hj := by
  simp [Elem.carry]

end TypeList

/-- Reinterpreting a list reinterprets its elements. -/
@[simp] public theorem TypeExpr.toElems_carry {s t : Env α} (h : s.KeepsTypes t)
    {scope : Array Kind} (l : TypeExpr s scope .list) :
    (l.carry h).toElems = l.toElems.map (·.carry h) := by
  have hl : (l.carry h).toElems = ((TypeList.lit l.toElems).carry h).toElems := by
    rw [TypeExpr.lit_toElems]
  rw [hl, TypeList.carry_lit, TypeExpr.toElems_lit]

namespace RegionSig

variable {env : Env α} {scope : Array Kind}

/-- Reinterpret in an environment that keeps the types. -/
public def carry {s t : Env α} (h : s.KeepsTypes t) (r : RegionSig s scope) : RegionSig t scope :=
  ⟨r.raw, r.wf.mono fun _ _ hr => Env.refBefore_size_of_keepsTypes h hr⟩

/-- Reinterpret in an extension. -/
public abbrev ofSubset {s t : Env α} (h : s ⊆ t) (r : RegionSig s scope) :
    RegionSig t scope :=
  r.carry (Env.keepsTypes_of_subset h)

/-- Reinterpreting changes no data. -/
@[simp] theorem raw_carry {s t : Env α} (h : s.KeepsTypes t) (r : RegionSig s scope) :
    (r.carry h).raw = r.raw := rfl

/-- Reinterpreting reinterprets each parameter. -/
@[simp] public theorem params_carry {s t : Env α} (h : s.KeepsTypes t) (r : RegionSig s scope) :
    (r.carry h).params = r.params.map (fun p => ⟨p.name, p.type.carry h⟩) := by
  apply Array.ext
  · simp [RegionSig.params, carry]
  · intro i _ _
    simp [RegionSig.params, carry, TypeExpr.carry]

/-- Reinterpreting reinterprets the return type. -/
@[simp] public theorem returnType_carry {s t : Env α} (h : s.KeepsTypes t) (r : RegionSig s scope) :
    (r.carry h).returnType = r.returnType.carry h := by
  simp only [RegionSig.returnType, carry, TypeExpr.carry]

/-- Reinterpreting `of` reinterprets its parameter types and its return type. -/
@[simp] public theorem carry_of {s t : Env α} (h : s.KeepsTypes t)
    (params : Array (Param (TypeExpr s scope))) (returnType : TypeExpr s scope)
    (distinct : (params.toList.map (·.name)).Nodup) :
    (of params returnType distinct).carry h =
      of (params.map fun p => ⟨p.name, p.type.carry h⟩) (returnType.carry h)
        (by simpa [Function.comp_def] using distinct) :=
  eq_of_raw_eq (by
    simp [of, carry, Array.map_map, Function.comp_def, TypeExpr.expr_carry])

end RegionSig

namespace InsnSig

/-- Reinterpret in an environment that keeps the types. -/
@[expose] public def carry {s t : Env α} (h : s.KeepsTypes t) (i : InsnSig s) : InsnSig t where
  ann := i.ann
  typeParams := i.typeParams
  argTypes := i.argTypes.map (fun p => ⟨p.name, p.type.carry h⟩)
  variadic := i.variadic.map (fun p => ⟨p.name, p.type.carry h⟩)
  returnType := i.returnType.map (·.carry h)
  regions := i.regions.map (fun p => ⟨p.name, p.type.carry h⟩)
  succs := i.succs.map (fun p => ⟨p.name, p.type.map (·.carry h)⟩)
  distinct := by simpa [Function.comp_def] using i.distinct

/-- Reinterpret in an extension. -/
public abbrev ofSubset {s t : Env α} (h : s ⊆ t) (i : InsnSig s) : InsnSig t :=
  i.carry (Env.keepsTypes_of_subset h)

/-- Reinterpreting changes no data. -/
theorem decl_carry {s t : Env α} (h : s.KeepsTypes t) (i : InsnSig s) (name : Name)
    (kind : InsnKind := .decl) :
    (i.carry h).decl name kind = i.decl name kind := by
  simp [decl, carry, Array.map_map, Function.comp_def, TypeExpr.expr_carry,
    TypeArg.expr_carry]

/-- A carried signature is the original, up to annotation. -/
public theorem eqUpToAnn_carry {s t : Env α} (h : s.KeepsTypes t) (σ : InsnSig s) :
    σ.EqUpToAnn (σ.carry h) := by
  unfold EqUpToAnn
  rw [decl_carry]

/-- A carried signature is equal up to annotation to what the original is. -/
@[simp] public theorem eqUpToAnn_carry_left {s t u : Env α} (h : s.KeepsTypes t)
    (σ : InsnSig s) (σ₂ : InsnSig u) : (σ.carry h).EqUpToAnn σ₂ ↔ σ.EqUpToAnn σ₂ := by
  unfold EqUpToAnn
  rw [decl_carry]

/-- Carrying twice is carrying once. -/
public theorem carry_carry {s t u : Env α} (h₁ : s.KeepsTypes t) (h₂ : t.KeepsTypes u)
    (σ : InsnSig s) : (σ.carry h₁).carry h₂ = σ.carry (h₁.trans h₂) := by
  apply ext_toRaw <;>
    simp [carry, Array.map_map, Function.comp_def, Option.map_map]

/-- An array's image, through its list. -/
private theorem toArray_map_toList {β γ : Type _} (f : β → γ) (a : Array β) :
    (a.toList.map f).toArray = a.map f := by
  apply Array.toList_inj.mp
  simp

/-- A signature carried into `t` is `τ` when everything it declares stands for the same raw
data.  The data is compared over lists, which reduce on a literal signature, so each
hypothesis is proved node by node, as the DSL does. -/
public theorem carry_eq_of_toRaw {s t : Env α} (h : s.KeepsTypes t) {σ : InsnSig s}
    {τ : InsnSig t} (hann : σ.ann = τ.ann) (htp : σ.typeParams.toList = τ.typeParams.toList)
    (hargs : σ.argTypes.toList.map (fun p => (p.name, p.type.toRaw)) =
      τ.argTypes.toList.map (fun p => (p.name, p.type.toRaw)))
    (hvar : σ.variadic.map (fun p => (p.name, p.type.toRaw)) =
      τ.variadic.map (fun p => (p.name, p.type.toRaw)))
    (hret : σ.returnType.map (·.toRaw) = τ.returnType.map (·.toRaw))
    (hregions : σ.regions.toList.map (fun p => (p.name,
        p.type.params.toList.map (fun q => (q.name, q.type.toRaw)), p.type.returnType.toRaw)) =
      τ.regions.toList.map (fun p => (p.name,
        p.type.params.toList.map (fun q => (q.name, q.type.toRaw)), p.type.returnType.toRaw)))
    (hsuccs : σ.succs.toList.map (fun p => (p.name, p.type.toList.map (·.toRaw))) =
      τ.succs.toList.map (fun p => (p.name, p.type.toList.map (·.toRaw)))) :
    σ.carry h = τ := by
  apply ext_toRaw
  · exact hann
  · exact Array.toList_inj.mp htp
  · apply Array.toList_inj.mp
    simpa [carry, Function.comp_def] using hargs
  · simpa [carry, Option.map_map, Function.comp_def] using hvar
  · simpa [carry, Option.map_map, Function.comp_def] using hret
  · have h₁ := congrArg (List.map fun (x : String × List (String × TypeExpr.Raw) × TypeExpr.Raw) =>
      (x.1, x.2.1.toArray, x.2.2)) hregions
    apply Array.toList_inj.mp
    simpa [carry, Function.comp_def, toArray_map_toList] using h₁
  · have h₁ := congrArg (List.map fun (x : String × List TypeExpr.Raw) => (x.1, x.2.toArray)) hsuccs
    apply Array.toList_inj.mp
    simpa [carry, Function.comp_def, toArray_map_toList] using h₁

end InsnSig


/-! ## Declarations, checked

* `Env.ResolvesInsn`, `InsnRef`: a reference to an instruction declaration, a datatype's
  constructor included.
* `InsnRef.cast`: the same reference, at an equal signature.
* `InsnRef.ctorAddr?`: which constructor the instruction is, if it is one.
* `Decl`: a declaration of a signature, as a type or instruction reference. -/

/-- `name` is declared in `s` as the instruction with signature `isig`, of whichever kind, up
to its annotation. -/
public def Env.ResolvesInsn (s : Env α) (name : Name) (isig : InsnSig s) : Prop :=
  ∃ d, s.declOf? name = some (.insn d) ∧ d.erase = (isig.decl name d.kind).erase

/-- A name declared as a signature's declaration resolves to it. -/
theorem Env.ResolvesInsn.of_resolves {s : Env α} {name : Name} {isig : InsnSig s}
    {k : InsnKind} (h : s.Resolves name (.insn (isig.decl name k))) :
    s.ResolvesInsn name isig :=
  ⟨_, h, rfl⟩

namespace Env

/-- An extension declares every instruction it extends, at the carried signature. -/
public theorem DeclaresInsn.of_subset {s s' : Env α} (hs : s ⊆ s') {n : Name} {σ : InsnSig s}
    {k : InsnKind} (h : s.DeclaresInsn n σ k) : s'.DeclaresInsn n (σ.ofSubset hs) k := by
  unfold DeclaresInsn at *
  rw [show (σ.ofSubset hs).decl n k = σ.decl n k from InsnSig.decl_carry _ σ n k]
  exact declOf?_of_subset hs h

/-- An extension keeps every instruction. -/
public theorem keepsInsns_of_subset {s t : Env α} (h : s ⊆ t) : s.KeepsInsns t :=
  ⟨fun hσ => ⟨_, _, hσ.of_subset h, InsnSig.eqUpToAnn_carry _ _⟩⟩

/-- A name that resolves to an instruction in `s` resolves to it, carried, in every environment
that keeps `s`'s types and instructions. -/
public theorem ResolvesInsn.carry {s t : Env α} (hT : s.KeepsTypes t) (hI : s.KeepsInsns t)
    {name : Name} {isig : InsnSig s} (hr : s.ResolvesInsn name isig) :
    t.ResolvesInsn name (isig.carry hT) := by
  obtain ⟨d₁, hd₁, he⟩ := hr
  obtain ⟨σ₂, k₂, hσ₂, heq⟩ := hI.insn (declaresInsn_ofWF hd₁)
  refine ⟨σ₂.decl name k₂, hσ₂, ?_⟩
  have e₁ := (InsnSig.eqUpToAnn_iff_decl (n := name) (k₁ := d₁.kind) (k₂ := k₂)).mp heq
  rw [InsnSig.decl_ofWF_of_name _ (by simpa using name_of_declOf? hd₁)] at e₁
  rw [e₁, InsnSig.decl_carry hT isig name (σ₂.decl name k₂).kind, he]
  rfl

end Env

/-- A reference to an instruction of `env` with signature `isig`: the name resolves, and what
it resolves to is that signature's declaration, up to its annotation. -/
public structure InsnRef (env : Env α) (isig : InsnSig env) where
  name : Name
  resolves : env.ResolvesInsn name isig

/-- Carry an instruction reference into an environment that keeps the types and
instructions. -/
public def InsnRef.carry {s t : Env α} (hT : s.KeepsTypes t) (hI : s.KeepsInsns t)
    {isig : InsnSig s} (r : InsnRef s isig) : InsnRef t (isig.carry hT) :=
  ⟨r.name, r.resolves.carry hT hI⟩

/-- Carry an instruction reference into an extension. -/
public abbrev InsnRef.ofSubset {s t : Env α} (h : s ⊆ t) {isig : InsnSig s}
    (r : InsnRef s isig) : InsnRef t (isig.ofSubset h) :=
  r.carry (Env.keepsTypes_of_subset h) (Env.keepsInsns_of_subset h)

/-- Carrying an instruction reference keeps its name. -/
@[simp] public theorem name_InsnRef_carry {s t : Env α} (hT : s.KeepsTypes t)
    (hI : s.KeepsInsns t) {isig : InsnSig s} (r : InsnRef s isig) :
    (r.carry hT hI).name = r.name := by
  simp [InsnRef.carry]

/-- The same reference, at an equal signature.  `simp` proves the equality when both are built
from `TypeExpr.app`, `TypeExpr.var`, `RegionSig.of` and `carry`. -/
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

/-- A reference's constructor address is its name's. -/
public theorem InsnRef.ctorAddr?_eq {env : Env α} {isig : InsnSig env} (r : InsnRef env isig) :
    r.ctorAddr? = env.ctorAddr? r.name := by
  simp only [InsnRef.ctorAddr?]

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
  cases d with
  | type r =>
    obtain ⟨_, hr, -⟩ := r.resolves
    exact Env.mem_of_typeOf? hr
  | insn r =>
    obtain ⟨_, hr, -⟩ := r.resolves
    exact Env.mem_of_resolves hr

/-- Carry a declaration into an environment that keeps the types and instructions. -/
public def carry {s t : Env α} (hT : s.KeepsTypes t) (hI : s.KeepsInsns t) : Decl s → Decl t
  | .type r => .type (r.carry hT)
  | .insn r => .insn (r.carry hT hI)

/-- Carry a declaration into an extension. -/
public abbrev ofSubset {s t : Env α} (h : s ⊆ t) : Decl s → Decl t :=
  carry (Env.keepsTypes_of_subset h) (Env.keepsInsns_of_subset h)

/-- Carrying a declaration keeps its name. -/
@[simp] public theorem name_carry {s t : Env α} (hT : s.KeepsTypes t) (hI : s.KeepsInsns t)
    (d : Decl s) : (d.carry hT hI).name = d.name := by
  cases d <;> rfl

/-- A declaration of `env` is declared in `env`. -/
public theorem mem {env : Env α} (d : Decl env) : d.name ∈ env :=
  mem_of_decl d

end Decl

namespace Env

/-! ### Typesafe lookup

* `get?`, `get`: look a declaration up by name, as a `Decl`. -/

/-- The declaration named `name`, checked. -/
public def get? (s : Env α) (name : Name) : Option (Decl s) :=
  match h : s.declOf? name with
  | none => none
  | some (.type d) =>
    some (.type ⟨name, d, rfl, resolvesType_of_typeOf? (typeOf?_of_type h)⟩)
  -- A datatype head is a type reference, as a primitive is.
  | some (.dataHead g) =>
    some (.type ⟨name, g.first.toTypeDecl, rfl, resolvesType_of_typeOf? (typeOf?_of_dataHead h)⟩)
  -- A member past the head is a type too; `aliasWF` says its group has it.
  | some (.dataRest mn hd i) =>
    have hs : (s.raw.typeOf? name).isSome := isSome_typeOf?_of_dataRest h
    some (.type ⟨name, (s.raw.typeOf? name).get hs, rfl,
      resolvesType_of_typeOf? (Option.some_get hs).symm⟩)
  -- A constructor is an instruction like any other.
  | some (.insn d) =>
    have hwf : InsnDecl.Raw.WF (s.RefBefore s.size) d :=
      Decl.Raw.wf_insn_iff.mp (declWF_of_declOf? h)
    have hname : d.name = name := by simpa using name_of_declOf? h
    some (.insn (isig := InsnSig.ofWF d hwf)
      ⟨name, ResolvesInsn.of_resolves (k := d.kind)
        (by rw [InsnSig.decl_ofWF_of_name hwf hname]; exact h)⟩)

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
    split <;> rename_i h <;> simp_all [← isSome_declOf?]

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

/-- What a name names after `addInsn`. -/
theorem declOf?_addInsn (s : Env α) (name : Name) (isig : InsnSig s) (fresh : name ∉ s)
    (n : Name) :
    (s.addInsn name isig fresh).declOf? n =
      if name == n then some (.insn (isig.decl name)) else s.declOf? n := by
  simp [declOf?_eq_raw, raw_addInsn, Raw.get?_append, InsnSig.name_decl]

theorem resolves_addInsn_self (s : Env α) (name : Name) (isig : InsnSig s)
    (fresh : name ∉ s) : (s.addInsn name isig fresh).Resolves name (.insn (isig.decl name)) := by
  rw [resolves_iff_declOf?, declOf?_addInsn]
  simp

theorem resolves_addInsn_of_ne {s : Env α} {name : Name} {isig : InsnSig s}
    {fresh : name ∉ s} {n : Name} {e : Decl.Raw α} (hne : name ≠ n) :
    (s.addInsn name isig fresh).Resolves n e ↔ s.Resolves n e := by
  rw [resolves_iff_declOf?, resolves_iff_declOf?, declOf?_addInsn, ite_eq_right (by simpa using hne)]

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
  ResolvesInsn.of_resolves (k := .decl)
    (by rw [InsnSig.decl_carry]; exact resolves_addInsn_self s name isig fresh)

/-- What type a name names after `addInsn`. -/
public theorem typeOf?_addInsn (s : Env α) (name : Name) (isig : InsnSig s) (fresh : name ∉ s)
    (n : Name) :
    (s.addInsn name isig fresh).typeOf? n = if name == n then none else s.typeOf? n :=
  typeOf?_of_declOf?_eq (declOf?_addInsn s name isig fresh) fresh rfl n

/-- `addInsn` adds no datatype. -/
public theorem dataOf?_addInsn (s : Env α) (name : Name) (isig : InsnSig s) (fresh : name ∉ s)
    (n : Name) :
    (s.addInsn name isig fresh).dataOf? n = if name == n then none else s.dataOf? n :=
  dataOf?_of_declOf?_eq (declOf?_addInsn s name isig fresh) fresh rfl (fun _ _ _ => nofun) n

/-! ### Declared instructions

`DeclaresInsn` is how a client reads an environment's instructions: as checked signatures,
with their kinds. -/

/-- A declared instruction resolves, as references do. -/
public theorem DeclaresInsn.resolvesInsn {s : Env α} {n : Name} {σ : InsnSig s} {k : InsnKind}
    (h : s.DeclaresInsn n σ k) : s.ResolvesInsn n σ :=
  ⟨_, h, rfl⟩

/-- A declared instruction's annotation is its signature's. -/
public theorem annOf?_of_declaresInsn {s : Env α} {n : Name} {σ : InsnSig s} {k : InsnKind}
    (h : s.DeclaresInsn n σ k) : s.annOf? n = some σ.ann :=
  annOf?_of_insn h

/-- A type's annotation is its declaration's. -/
public theorem annOf?_of_typeOf? {s : Env α} {n : Name} {d : TypeDecl α}
    (h : s.typeOf? n = some d) : s.annOf? n = some d.ann := by
  unfold Env.annOf?
  split
  · next d₀ hd₀ =>
    rw [typeOf?_of_insn hd₀] at h
    cases h
  · rw [h]
    rfl

/-- A name declared as an instruction is declared. -/
public theorem DeclaresInsn.mem {s : Env α} {n : Name} {σ : InsnSig s} {k : InsnKind}
    (h : s.DeclaresInsn n σ k) : n ∈ s :=
  mem_of_resolves h

/-- A declared name names a type or an instruction. -/
public theorem lookup_of_mem {s : Env α} {n : Name} (hn : n ∈ s) :
    (∃ d, s.typeOf? n = some d) ∨ ∃ σ k, s.DeclaresInsn n σ k := by
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp (isSome_declOf?.mpr hn)
  cases e with
  | type _ => exact .inl ⟨_, typeOf?_of_type he⟩
  | dataHead _ => exact .inl ⟨_, typeOf?_of_dataHead he⟩
  | dataRest _ _ _ => exact .inl (Option.isSome_iff_exists.mp (isSome_typeOf?_of_dataRest he))
  | insn _ => exact .inr ⟨_, _, declaresInsn_ofWF he⟩

/-- A name's annotation is that of the instruction or the type it names. -/
public theorem annOf?_eq_some {s : Env α} {n : Name} {a : α} (h : s.annOf? n = some a) :
    (∃ σ k, s.DeclaresInsn n σ k ∧ σ.ann = a) ∨ ∃ d, s.typeOf? n = some d ∧ d.ann = a := by
  unfold annOf? at h
  split at h
  next d hd =>
    obtain rfl := Option.some.inj h
    exact .inl ⟨_, _, declaresInsn_ofWF hd, rfl⟩
  next =>
    obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
    exact .inr ⟨d, hd, rfl⟩

/-- A declared instruction's constructor address is its kind's. -/
public theorem ctorAddr?_of_declaresInsn {s : Env α} {n : Name} {σ : InsnSig s} {k : InsnKind}
    (h : s.DeclaresInsn n σ k) : s.ctorAddr? n = k.ctor? :=
  ctorAddr?_of_insnOf? (insnOf?_eq_some_iff.mpr h)

/-- The empty environment declares no instruction. -/
public theorem not_declaresInsn_empty {n : Name} {σ : InsnSig (Env.empty (α := α))}
    {k : InsnKind} : ¬ (Env.empty (α := α)).DeclaresInsn n σ k := by
  unfold DeclaresInsn
  rw [declOf?_empty]
  nofun

/-- An instruction declared in an extension `s'`, under a name `s` declares, is one of `s`'s,
carried. -/
theorem declaresInsn_of_subset_declOf? {s s' : Env α} (hs : s ⊆ s') {n : Name}
    {σ : InsnSig s'} {k : InsnKind} (h : s.declOf? n = some (.insn (σ.decl n k))) :
    ∃ σ₀ : InsnSig s, s.DeclaresInsn n σ₀ k ∧ σ = σ₀.ofSubset hs := by
  have hwf := Decl.Raw.wf_insn_iff.mp (declWF_of_declOf? h)
  have e : (InsnSig.ofWF _ hwf).decl n k = σ.decl n k :=
    InsnSig.decl_ofWF_of_name hwf (InsnSig.name_decl σ n k)
  refine ⟨InsnSig.ofWF _ hwf, ?_, ?_⟩
  · unfold DeclaresInsn
    rw [e]
    exact h
  · exact InsnSig.eq_of_decl_eq (n := n) (k := k) (by
    rw [show ((InsnSig.ofWF _ hwf).ofSubset hs).decl n k = _ from InsnSig.decl_carry _ _ n k, e])

/-- `addInsn` declares its instruction, as an ordinary one. -/
public theorem declaresInsn_addInsn_self (s : Env α) (name : Name) (isig : InsnSig s)
    (fresh : name ∉ s) :
    (s.addInsn name isig fresh).DeclaresInsn name
      (isig.ofSubset (subset_addInsn s name isig fresh)) .decl := by
  unfold DeclaresInsn
  rw [show (isig.ofSubset _).decl name .decl = isig.decl name from InsnSig.decl_carry _ _ _ _]
  exact resolves_addInsn_self s name isig fresh

/-- An instruction declared after `addInsn` is the added one, or one `s` declares. -/
public theorem declaresInsn_addInsn {s : Env α} {name : Name} {isig : InsnSig s}
    {fresh : name ∉ s} {n : Name} {σ : InsnSig (s.addInsn name isig fresh)} {k : InsnKind}
    (h : (s.addInsn name isig fresh).DeclaresInsn n σ k) :
    (name = n ∧ σ = isig.ofSubset (subset_addInsn s name isig fresh) ∧ k = .decl) ∨
      ∃ σ₀ : InsnSig s, s.DeclaresInsn n σ₀ k ∧
        σ = σ₀.ofSubset (subset_addInsn s name isig fresh) := by
  unfold DeclaresInsn at h
  rw [declOf?_addInsn] at h
  split at h
  · next hn =>
    obtain rfl := beq_iff_eq.mp hn
    have hd := Decl.Raw.insn.inj (Option.some.inj h)
    have hk : k = .decl := (congrArg InsnDecl.Raw.kind hd).symm
    subst hk
    exact .inl ⟨rfl, InsnSig.eq_of_decl_eq (n := name) (k := .decl)
      (by rw [show (isig.ofSubset _).decl name .decl = isig.decl name from
        InsnSig.decl_carry _ _ _ _]; exact hd.symm), rfl⟩
  · exact .inr (declaresInsn_of_subset_declOf? _ h)

/-- An instruction declared after `addType` is one `s` declares. -/
public theorem declaresInsn_addType {s : Env α} {d : TypeDecl α} {fresh : d.name ∉ s}
    {distinct : d.paramNames.Nodup} {n : Name} {σ : InsnSig (s.addType d fresh distinct)}
    {k : InsnKind} (h : (s.addType d fresh distinct).DeclaresInsn n σ k) :
    ∃ σ₀ : InsnSig s, s.DeclaresInsn n σ₀ k ∧ σ = σ₀.ofSubset (subset_addType s d fresh) := by
  unfold DeclaresInsn at h
  rw [declOf?_addType] at h
  split at h
  · cases h
  · exact declaresInsn_of_subset_declOf? _ h

/-! ### Extending by evaluation, and by a batch

* `addType?`: add a type declaration, deciding its obligations.
* `addInsns?`: add a batch of instruction declarations, deciding their obligations. -/

-- One batch, not repeated `add?`: a group's head is well formed only once its aliases follow.
/-- Add the declarations as one batch.  `none` if their names are not distinct and fresh, or
one is not well formed in the environment that has the whole batch. -/
def addAll? (s : Env α) : Array (Decl.Raw α) → Option (Env α)
  | ⟨l⟩ =>
    if fresh : s.raw.FreshList l then
      if h : s.raw.checkAppend l fresh = true then
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
  have hr := resolves_iff_declOf?.mp (resolves_of_add?_eq_some h)
  simp only [Decl.Raw.name_type] at hr
  exact resolvesType_of_typeOf? (typeOf?_of_type hr)

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
  have hr := resolves_iff_declOf?.mp
    (resolves_of_addAll?_eq_some _ h 0 (.dataHead g)
      (by rw [← Array.getElem?_toList]; exact DataGroup.decls_getElem?_zero g))
  simp only [Decl.Raw.name_dataHead] at hr
  exact resolvesType_of_typeOf? (typeOf?_of_dataHead hr)

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
  exact ResolvesInsn.of_resolves (k := .decl) (by rw [InsnSig.decl_carry]; exact this)

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
  exact ResolvesInsn.of_resolves (k := .decl) (by rw [InsnSig.decl_carry]; exact this)

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
theorem declOf?_ctor {i j : Nat} (hi : i < ctors.size) (hj : j < ctors[i].size) :
    (s.addData hdr fresh ctors cfresh adm).declOf? (ctorInsnDecl adm i j hi hj).name =
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
    (Decl.Raw.wf_insn_iff.mp (declWF_of_declOf? (declOf?_ctor hi hj)))

section ctorSig

variable {s : Env α} {hdr : Array (TypeDecl α)} {fresh : s.FreshTypes hdr}
  {ctors : Array (Array (Ctor α (DataTy s (s.addTypes hdr fresh))))}
  {cfresh : (s.addTypes hdr fresh).FreshNames (ctorNames ctors ++ caseNames hdr)}
  {adm : admissible hdr ctors = true} {i j : Nat} {hi : i < ctors.size} {hj : j < ctors[i].size}

/-- A constructor's instruction is annotated as the constructor is. -/
@[simp] public theorem ann_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).ann = ctors[i][j].ann := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, Ctor.mapTy]

/-- Its type parameters are its datatype's, by name and in order, each of its kind. -/
@[simp] public theorem typeParams_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).typeParams =
      (hdr[i]'(size_of_admissible adm ▸ hi)).params.map fun p => ⟨p.name, p.type.kind⟩ := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, memberAt, DatatypeDecl.mapTy]

/-- `typeParams_ctorSig`, over lists. -/
public theorem typeParams_toList_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).typeParams.toList =
      (hdr[i]'(size_of_admissible adm ▸ hi)).params.toList.map fun p => ⟨p.name, p.type.kind⟩ := by
  rw [typeParams_ctorSig, Array.toList_map]

/-- Its arguments are the constructor's payload. -/
@[simp] public theorem argTypes_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).argTypes.map
        (fun p => (p.name, p.type.toRaw)) =
      ctors[i][j].args.map (fun p => (p.name, p.type.toRaw)) := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, Ctor.mapTy, Param.mapTy,
    Array.map_attach_eq_pmap, Array.map_pmap, Function.comp_def, TypeExpr.toRaw_eq_expr]

/-- `argTypes_ctorSig`, over lists. -/
public theorem argTypes_toList_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).argTypes.toList.map
        (fun p => (p.name, p.type.toRaw)) =
      ctors[i][j].args.toList.map (fun p => (p.name, p.type.toRaw)) := by
  rw [← Array.toList_map, argTypes_ctorSig, Array.toList_map]

/-- It takes no variadic arguments. -/
@[simp] public theorem variadic_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).variadic = none := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl]

/-- It returns its datatype, applied to its own parameters. -/
@[simp] public theorem returnType_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).returnType.map TypeExpr.toRaw =
      some (TypeExpr.Raw.app (hdr[i]'(size_of_admissible adm ▸ hi)).name
        (TypeExpr.Raw.vars (TyParam.kinds (hdr[i]'(size_of_admissible adm ▸ hi)).params))) := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl, memberAt, DatatypeDecl.mapTy,
    TypeExpr.toRaw_eq_expr]

/-- It takes no regions. -/
@[simp] public theorem regions_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).regions = #[] := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl]

/-- It has no successors. -/
@[simp] public theorem succs_ctorSig :
    (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).succs = #[] := by
  simp [ctorSig, InsnSig.ofWF, ctorInsnDecl, DataGroup.ctorDecl]

/-- `addData` declares constructor `j` of member `i` as the instruction with the signature it
derives, marked as that constructor. -/
theorem insnOf?_addData_ctor (i j : Nat) (hi : i < ctors.size := by decide)
    (hj : j < ctors[i].size := by decide) :
    (s.addData hdr fresh ctors cfresh adm).insnOf? ctors[i][j].name =
      some ((ctorSig (cfresh := cfresh) (adm := adm) i j hi hj).decl ctors[i][j].name
        (.ctor ⟨(hdr[0]'(pos_of_admissible adm)).name, i, j⟩)) := by
  have hn : (ctorInsnDecl adm i j hi hj).name = ctors[i][j].name := rfl
  have hk : (ctorInsnDecl adm i j hi hj).kind =
      .ctor ⟨(hdr[0]'(pos_of_admissible adm)).name, i, j⟩ := by
    rw [name_first_dataGroup (ctors := ctors) (adm := adm)]
    rfl
  rw [← hn, ← hk, ctorSig, InsnSig.decl_ofWF]
  exact insnOf?_eq_some_iff.mpr (declOf?_ctor hi hj)

/-- `addData` declares constructor `j` of member `i` with the signature it derives, as that
constructor. -/
public theorem declaresInsn_addData_ctor (i j : Nat) (hi : i < ctors.size := by decide)
    (hj : j < ctors[i].size := by decide) :
    (s.addData hdr fresh ctors cfresh adm).DeclaresInsn ctors[i][j].name
      (ctorSig (cfresh := cfresh) (adm := adm) i j hi hj)
      (.ctor ⟨(hdr[0]'(pos_of_admissible adm)).name, i, j⟩) :=
  insnOf?_eq_some_iff.mp (insnOf?_addData_ctor i j hi hj)

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
    exact Env.ResolvesInsn.of_resolves
      (Env.insnOf?_eq_some_iff.mp (Env.insnOf?_addData_ctor i j hi hj))⟩

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
  have h := Env.declOf?_ctor (cfresh := cfresh) (adm := adm) hi hj
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
theorem declOf?_case {i : Nat} (hi : i < ctors.size) :
    (s.addData hdr fresh ctors cfresh adm).declOf? (caseInsnDecl adm i hi).name =
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
    (Decl.Raw.wf_insn_iff.mp (declWF_of_declOf? (declOf?_case hi)))

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

/-- Its type parameters are its datatype's, by name and in order, each of its kind. -/
@[simp] public theorem typeParams_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).typeParams =
      (hdr[i]'(size_of_admissible adm ▸ hi)).params.map fun p => ⟨p.name, p.type.kind⟩ := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl, memberAt, DatatypeDecl.mapTy]

/-- `typeParams_caseSig`, over lists. -/
public theorem typeParams_toList_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).typeParams.toList =
      (hdr[i]'(size_of_admissible adm ▸ hi)).params.toList.map fun p => ⟨p.name, p.type.kind⟩ := by
  rw [typeParams_caseSig, Array.toList_map]

/-- Its one argument is the scrutinee: the datatype, applied to its own parameters. -/
@[simp] public theorem argTypes_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).argTypes.map
        (fun p => (p.name, p.type.toRaw)) =
      #[("scrutinee", .app (hdr[i]'(size_of_admissible adm ▸ hi)).name
        (TypeExpr.Raw.vars (TyParam.kinds (hdr[i]'(size_of_admissible adm ▸ hi)).params)))] := by
  simp [caseSig, InsnSig.ofWF, caseInsnDecl, DataGroup.caseDecl, memberAt, DatatypeDecl.mapTy,
    TypeExpr.toRaw_eq_expr]

/-- `argTypes_caseSig`, over lists. -/
public theorem argTypes_toList_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).argTypes.toList.map
        (fun p => (p.name, p.type.toRaw)) =
      [("scrutinee", .app (hdr[i]'(size_of_admissible adm ▸ hi)).name
        (TypeExpr.Raw.vars (TyParam.kinds (hdr[i]'(size_of_admissible adm ▸ hi)).params)))] := by
  rw [← Array.toList_map, argTypes_caseSig]

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
    TypeArg.toRaw_eq_expr, Array.pmap_map]
  -- `simp` does not rewrite under `pmap`'s binders, so compare the arrays pointwise.
  refine Array.ext (by simp) fun j _ _ => ?_
  simp only [Array.getElem_pmap, Array.getElem_map]
  exact Prod.ext rfl (Array.ext (by simp) fun k _ _ => by
    simp only [Array.getElem_pmap, Array.getElem_map]; rfl)

/-- `succs_caseSig`, over lists. -/
public theorem succs_toList_caseSig :
    (caseSig (cfresh := cfresh) (adm := adm) i hi).succs.toList.map
        (fun p => (p.name, p.type.toList.map (·.toRaw))) =
      ctors[i].toList.map (fun c => (c.name.lastString, c.args.toList.map (·.type.toRaw))) := by
  have h := congrArg (fun (a : Array (String × Array TypeExpr.Raw)) =>
    (a.map fun x => (x.1, x.2.toList)).toList)
    (succs_caseSig (cfresh := cfresh) (adm := adm) (i := i) (hi := hi))
  simp only [Array.toList_map, List.map_map, Function.comp_def] at h
  exact h

/-- `addData` declares member `i`'s case instruction as the instruction with the signature it
derives, marked as that case instruction. -/
theorem insnOf?_addData_case (i : Nat) (hi : i < ctors.size := by decide) :
    (s.addData hdr fresh ctors cfresh adm).insnOf?
        (hdr[i]'(size_of_admissible adm ▸ hi)).name.caseName =
      some ((caseSig (cfresh := cfresh) (adm := adm) i hi).decl
        (hdr[i]'(size_of_admissible adm ▸ hi)).name.caseName
        (.case ⟨(hdr[0]'(pos_of_admissible adm)).name, i⟩)) := by
  have hn : (caseInsnDecl adm i hi).name =
      (hdr[i]'(size_of_admissible adm ▸ hi)).name.caseName := rfl
  have hk : (caseInsnDecl adm i hi).kind = .case ⟨(hdr[0]'(pos_of_admissible adm)).name, i⟩ := by
    rw [name_first_dataGroup (ctors := ctors) (adm := adm)]
    rfl
  rw [← hn, ← hk, caseSig, InsnSig.decl_ofWF]
  exact insnOf?_eq_some_iff.mpr (declOf?_case hi)

/-- `addData` declares member `i`'s case instruction with the signature it derives, as that
case instruction. -/
public theorem declaresInsn_addData_case (i : Nat) (hi : i < ctors.size := by decide) :
    (s.addData hdr fresh ctors cfresh adm).DeclaresInsn
      (hdr[i]'(size_of_admissible adm ▸ hi)).name.caseName
      (caseSig (cfresh := cfresh) (adm := adm) i hi)
      (.case ⟨(hdr[0]'(pos_of_admissible adm)).name, i⟩) :=
  insnOf?_eq_some_iff.mp (insnOf?_addData_case i hi)

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
    exact Env.ResolvesInsn.of_resolves
      (Env.insnOf?_eq_some_iff.mp (Env.insnOf?_addData_case i hi))⟩

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
