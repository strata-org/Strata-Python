module
public import StrataMantle.Util.IndexMap.Raw
import all StrataMantle.Util.IndexMap.Raw

set_option autoImplicit false

/-!
# IndexMap

`IndexMap.Raw` quotiented by "same `keys`, same `vals`". The quotient hides the
`index` cache, so `keys`/`vals` are the only observables and two maps built by
different insertion routes are equal iff they iterate the same way. Every
operation is a `liftOn`/`mapOn` of its `Raw` counterpart, and every lemma below
is the `Raw` lemma transported by `Quotient.ind`.
-/

namespace Strata
namespace IndexMap.Raw

variable {α β} [BEq α] [Hashable α]

protected def eq (x y : IndexMap.Raw α β) : Prop :=
  x.keys = y.keys ∧ x.vals = y.vals

/-- `insert` is a congruence for `IndexMap.Raw.eq`: its observable result (keys and
    vals) is determined by the input's keys and vals. This is the single fact
    `IndexMap.insert` needs to descend to the quotient. -/
theorem insert_eq_congr [EquivBEq α] [LawfulHashable α] {a b : IndexMap.Raw α β}
    (key : α) (val : β) (eq : IndexMap.Raw.eq a b) :
    IndexMap.Raw.eq (a.insert key val) (b.insert key val) :=
  ⟨IndexMap.Raw.keys_insert_eq_of_keys_eq key val eq.left,
   IndexMap.Raw.vals_insert_eq_of_vals_eq key val eq.left eq.right⟩

def isSetoid (α β : Type _) [BEq α] [EquivBEq α] [Hashable α] :
    Setoid (IndexMap.Raw α β) where
  r := IndexMap.Raw.eq
  iseqv := {
    refl := fun _ => .intro (.refl _) (.refl _)
    symm := fun p => .intro p.left.symm p.right.symm
    trans := fun p q => .intro (.trans p.left q.left) (.trans p.right q.right)
  }

end IndexMap.Raw

/-- An insertion-ordered, unique-keyed map; see the module docstring. -/
public def IndexMap (α β : Type _) [BEq α] [EquivBEq α] [Hashable α] :=
  Quotient (IndexMap.Raw.isSetoid α β)

namespace IndexMap

variable {α β : Type _} [BEq α] [EquivBEq α] [Hashable α]

protected def recOn {motive : IndexMap α β → Sort _} (m : IndexMap α β)
    (f : ∀(m : IndexMap.Raw α β), motive (Quotient.mk (IndexMap.Raw.isSetoid α β) m))
    (p : ∀(a b : IndexMap.Raw α β) (p : IndexMap.Raw.eq a b),
      Eq.ndrec (f a) (Quotient.sound p) = f b) : motive m :=
  Quotient.recOn m f p

protected def liftOn {γ} (m : IndexMap α β) (f : IndexMap.Raw α β → γ)
    (p : ∀(a b : IndexMap.Raw α β), IndexMap.Raw.eq a b → f a = f b) : γ :=
  Quotient.liftOn m f p

protected
def mapOn (m : IndexMap α β) (f : IndexMap.Raw α β → IndexMap.Raw α β)
    (p : ∀(a b : IndexMap.Raw α β), IndexMap.Raw.eq a b → IndexMap.Raw.eq (f a) (f b)) :
    IndexMap α β :=
  Quotient.liftOn m (fun x => Quotient.mk _ (f x)) fun a b eq =>
    Quotient.sound (s := IndexMap.Raw.isSetoid α β) (p a b eq)

public protected def keys (m : IndexMap α β) : Array α :=
  m.liftOn (·.keys) fun _ _ ⟨keq, _⟩ => keq

public protected def vals (m : IndexMap α β) : Array β :=
  m.liftOn (·.vals) fun _ _ ⟨_, veq⟩ => veq

abbrev Elt (m : IndexMap α β) := { n : IndexMap.Raw α β // n.keys = m.keys ∧ n.vals = m.vals }

/-- Transport over a constant-codomain Pi reduces to transporting the (proof)
    argument: only the domain `P n` moves, the result type `γ` is fixed. -/
theorem ndrec_pi_const {X : Sort _} {P : X → Prop} {γ : Sort _} {x y : X}
    (h : x = y) (g : P x → γ) (q : P y) :
    (Eq.ndrec (motive := fun n => P n → γ) g h) q
      = g (Eq.ndrec (motive := P) q h.symm) := by
  subst h; rfl

protected def drecOn (m : IndexMap α β) {γ} (f : Elt m → γ)
    (inv : ∀(a b : Elt m), f a = f b) : γ :=
 IndexMap.recOn (motive := fun n => n.keys = m.keys ∧ n.vals = m.vals → γ) m
    (fun n p => f ⟨n, p⟩)
  (p := fun a b ⟨keq, veq⟩ => by
    funext p
    have h := Quotient.sound (s := IndexMap.Raw.isSetoid α β) ⟨keq, veq⟩
    -- the transported branch applies `f` to the same carrier `a`, only with a
    -- different (proof-irrelevant) membership witness; `inv` collapses it.
    exact Eq.trans
      (ndrec_pi_const (P := (fun (q : IndexMap _ _) => q.keys = m.keys ∧ q.vals = m.vals))
        h (fun p => f ⟨a, p⟩) p)
      (inv _ _))
  ⟨rfl, rfl⟩

public section

protected def empty : IndexMap α β := Quotient.mk _ .empty

instance : EmptyCollection (IndexMap α β) := ⟨IndexMap.empty⟩

instance : Inhabited (IndexMap α β) := ⟨IndexMap.empty⟩

/-- The number of entries. -/
protected
def size (m : IndexMap α β) : Nat := m.liftOn (·.size) fun _ _ ⟨keq, _⟩ =>
  congrArg Array.size keq

/-- `keys` has length `size`. Lifts `IndexMap.Raw.keys_size` through the quotient
    (both `keys` and `size` lift the corresponding `Raw` projections). -/
@[simp] theorem keys_size (m : IndexMap α β) : m.keys.size = m.size := by
  induction m using Quotient.ind with
  | _ n => exact n.size_keys

/-- `vals` has length `size`, hence the same length as `keys`. -/
@[simp] theorem vals_size (m : IndexMap α β) : m.vals.size = m.size := by
  induction m using Quotient.ind with
  | _ n => exact n.size_vals

protected
def contains [LawfulHashable α] (m : IndexMap α β) (key : α) : Bool :=
  m.liftOn (·.contains key) fun _ _ ⟨keq, _⟩ =>
    IndexMap.Raw.contains_eq_of_keys_eq keq key

/-- Key membership, delegating to the `index` cache so `k ∈ m` works. -/
instance [LawfulHashable α] : Membership α (IndexMap α β) where
  mem m key := IndexMap.contains m key

instance [LawfulHashable α] (k : α) (m : IndexMap α β) : Decidable (k ∈ m) :=
  inferInstanceAs (Decidable (IndexMap.contains m k = true))

private
theorem mem_elt_of_map [LawfulHashable α] {m : IndexMap α β} {key : α} (e : Elt m)
    (mem : key ∈ m) :
    key ∈ e.val := by
  induction m using Quotient.ind with
  | _ n =>
    have hkeys : e.val.keys = n.keys := e.property.left
    rw [IndexMap.Raw.mem_iff_contains, IndexMap.Raw.contains_eq_of_keys_eq hkeys key]
    exact mem

protected
def toArray (m : IndexMap α β) : Array (α × β) :=
  Array.zip m.keys m.vals

/-- `Repr` shows the entries in insertion order; the `index` cache is not
    printed. -/
instance [Repr α] [Repr β] : Repr (IndexMap α β) where
  reprPrec m :=  Repr.addAppParen s!"IndexMap.ofArray {repr m.toArray}"

section
-- `EquivBEq α` already comes from the namespace `variable`; redeclaring it
-- duplicates the binder.
variable [LawfulHashable α]

protected def insert (m : IndexMap α β) (key : α) (val : β) : IndexMap α β :=
  m.mapOn (·.insert key val) fun _ _ eq =>
    IndexMap.Raw.insert_eq_congr key val eq

protected def get? (m : IndexMap α β) (key : α) : Option β :=
  m.liftOn (·.get? key) fun a b ⟨keq, veq⟩ => by
    unfold IndexMap.Raw.get?
    have r := IndexMap.Raw.idxOf?_eq_of_keys_eq (key := key) keq
    simp [r]
    cases b.idxOf? key <;> grind

/-- The position of `key` in `keys`, or `none`. Positions are observable through
    the quotient because `keys` is. -/
protected def idxOf? (m : IndexMap α β) (key : α) : Option Nat :=
  m.liftOn (fun n => (n.idxOf? key).map Fin.val) fun a b ⟨keq, _⟩ => by
    rw [← IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf? a key,
      ← IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf? b key, keq]

/-- Look up `key`, given a proof it is present. Total (no `Option`): the
    membership proof plus the carried invariants justify the in-bounds access. -/
protected def get (m : IndexMap α β) (key : α) (mem : key ∈ m) : β :=
  m.drecOn (fun n => n.val[key]'(mem_elt_of_map n mem)) fun ⟨a, ae⟩ ⟨b, be⟩ => by
    have amem : key ∈ a := mem_elt_of_map ⟨a, ae⟩ mem
    have bmem : key ∈ b := mem_elt_of_map ⟨b, be⟩ mem
    change a.vals[a.idxOf key amem] = b.vals[b.idxOf key bmem]
    have keq : a.keys = b.keys := by grind
    have p := IndexMap.Raw.idxOf_eq_of_keys_eq keq amem
    simp [p]; grind

protected def getD [Inhabited β] (m : IndexMap α β) (key : α) (d : β) : β :=
  m.liftOn (·.getD key d) fun a b ⟨keq, veq⟩ => by
    unfold IndexMap.Raw.getD
    have r := IndexMap.Raw.idxOf?_eq_of_keys_eq (key := key) keq
    simp [r]
    grind

protected def get! [Inhabited β] (m : IndexMap α β) (key : α) : β :=
  m.getD key default

/-- `m[key]?` is `get?`; `m[key]` is the total `get`. -/
instance : GetElem? (IndexMap α β) α β (fun m key => key ∈ m) where
  getElem := IndexMap.get
  getElem? := IndexMap.get?
  getElem! := IndexMap.get!

/-! ### Lookup lemmas

Every operation here is a `liftOn`/`mapOn` of the corresponding `Raw` operation,
so `Quotient.ind` reduces each statement to its `Raw` counterpart definitionally.
-/

omit [LawfulHashable α] in
/-- Normalise the named constructor to `∅`, so the `_empty` lemmas fire on both. -/
@[simp]
theorem empty_eq : (IndexMap.empty : IndexMap α β) = ∅ := rfl

@[simp]
theorem mem_iff_contains {m : IndexMap α β} {key : α} :
    key ∈ m ↔ IndexMap.contains m key := Iff.rfl

@[simp]
theorem getElem?_empty (key : α) : (∅ : IndexMap α β)[key]? = none :=
  IndexMap.Raw.get?_empty key

@[simp]
theorem contains_empty (key : α) : IndexMap.contains (∅ : IndexMap α β) key = false :=
  IndexMap.Raw.contains_empty key

@[simp]
theorem not_mem_empty {key : α} : ¬ (key ∈ (∅ : IndexMap α β)) := by simp

omit [LawfulHashable α] in
@[simp]
theorem keys_empty : (∅ : IndexMap α β).keys = #[] :=
  IndexMap.Raw.keys_empty

/-- Lookup after `insert`: the inserted key maps to the new value, all other keys
    are unaffected. -/
@[simp]
theorem getElem?_insert (m : IndexMap α β) (key : α) (val : β) (k : α) :
    (m.insert key val)[k]? = if key == k then some val else m[k]? := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.get?_insert n key val k

omit [LawfulHashable α] in
/-- A position found by `idxOf?` holds that key.  Unlike the `iff` below this needs
    no distinctness: it reads off the element the search stopped at. -/
theorem getElem?_keys_of_idxOf?_eq_some [LawfulBEq α] {m : IndexMap α β} {key : α} {i : Nat}
    (h : IndexMap.idxOf? m key = some i) : m.keys[i]? = some key := by
  induction m using Quotient.ind with
  | _ n =>
    have h' : n.keys.idxOf? key = some i := by
      rw [IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf?]
      exact h
    obtain ⟨hlt, hbeq, -⟩ := Array.idxOf?_eq_some_iff_getElem.mp h'
    show n.keys[i]? = some key
    rw [Array.getElem?_eq_getElem hlt, eq_of_beq hbeq]

omit [LawfulHashable α] in
theorem idxOf?_eq_some_iff_getElem?_keys [LawfulBEq α] {m : IndexMap α β} {key : α}
    {i : Nat} (hnd : m.keys.toList.Nodup) :
    IndexMap.idxOf? m key = some i ↔ m.keys[i]? = some key := by
  induction m using Quotient.ind with
  | _ n =>
    show Option.map Fin.val (n.idxOf? key) = some i ↔ _
    rw [← IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf?]
    exact Array.idxOf?_eq_some_iff_getElem?_of_nodup hnd

/-- Inserting a fresh key puts it at the end and leaves other positions alone. -/
theorem idxOf?_insert_of_not_mem {m : IndexMap α β} {key k : α} {val : β} (h : ¬ (key ∈ m)) :
    IndexMap.idxOf? (m.insert key val) k =
      if key == k then some m.keys.size else IndexMap.idxOf? m k := by
  induction m using Quotient.ind with
  | _ n =>
    show Option.map Fin.val ((n.insert key val).idxOf? k) = _
    rw [← IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf?,
      IndexMap.Raw.keys_insert_of_not_mem val h, Array.idxOf?_push]
    show _ = if key == k then some n.keys.size else Option.map Fin.val (n.idxOf? k)
    rw [← IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf?]
    if hb : (key == k) = true then
      -- `key` is absent, so the `BEq`-equal `k` is too, and the search falls
      -- through to the pushed position.
      have hkey : n.keys.idxOf? k = none := by
        rw [← Array.idxOf?_congr hb]
        exact (n.idxOf?_eq_none_iff key).mp (IndexMap.Raw.idxOf?_eq_none_of_not_mem h)
      simp [hb, hkey]
    else
      simp [hb]

@[simp]
theorem isSome_getElem?_eq_contains {m : IndexMap α β} {key : α} :
    (m[key]?).isSome = IndexMap.contains m key := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.isSome_get?_eq_contains

@[simp]
theorem isSome_idxOf?_eq_contains {m : IndexMap α β} {key : α} :
    (IndexMap.idxOf? m key).isSome = IndexMap.contains m key := by
  induction m using Quotient.ind with
  | _ n =>
    show (Option.map Fin.val (n.idxOf? key)).isSome = _
    rw [Option.isSome_map]
    exact IndexMap.Raw.isSome_idxOf?_eq_contains

omit [LawfulHashable α] in
@[simp]
theorem vals_empty : (∅ : IndexMap α β).vals = #[] :=
  IndexMap.Raw.vals_empty

/-- Lookup in terms of the position and `vals`: the bridge between name-indexed
    and position-indexed access. -/
theorem getElem?_eq_bind_idxOf? {m : IndexMap α β} {key : α} :
    m[key]? = (IndexMap.idxOf? m key).bind (fun i => m.vals[i]?) := by
  induction m using Quotient.ind with
  | _ n =>
    show n.get? key = (Option.map Fin.val (n.idxOf? key)).bind _
    rw [← IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf?]
    exact IndexMap.Raw.get?_eq_bind_idxOf? n key

omit [LawfulHashable α] in
/-- `keys` and `vals` determine the map: that pair is exactly what the quotient
    identifies. -/
theorem eq_of_keys_vals_eq {a b : IndexMap α β} (hk : a.keys = b.keys) (hv : a.vals = b.vals) :
    a = b := by
  induction a using Quotient.ind with
  | _ na =>
    induction b using Quotient.ind with
    | _ nb => exact Quotient.sound ⟨hk, hv⟩

omit [LawfulHashable α] in
/-- Keys are `BEq`-distinct. -/
theorem keys_distinct (m : IndexMap α β) :
    m.keys.toList.Pairwise (fun a b => (a == b) = false) := by
  induction m using Quotient.ind with
  | _ n => exact n.keys_distinct

omit [LawfulHashable α] in
/-- Keys are distinct, once `BEq` is equality. -/
theorem keys_nodup [LawfulBEq α] (m : IndexMap α β) : m.keys.toList.Nodup := by
  induction m using Quotient.ind with
  | _ n => exact n.keys_nodup

omit [LawfulHashable α] in
/-- The search for the key at position `i` stops at `i`. -/
theorem idxOf?_getElem_keys (m : IndexMap α β) (i : Nat) (h : i < m.keys.size) :
    IndexMap.idxOf? m (m.keys[i]'h) = some i := by
  induction m using Quotient.ind with
  | _ n =>
    show Option.map Fin.val (n.idxOf? _) = some i
    rw [← IndexMap.Raw.keys_idxOf?_eq_map_val_idxOf?]
    exact n.idxOf?_getElem_keys i h

/-- Every entry is reachable: the key at position `i` looks up to the value at
    position `i`. -/
theorem getElem?_getElem_keys (m : IndexMap α β) (i : Nat) (h : i < m.keys.size) :
    m[m.keys[i]'h]? = m.vals[i]? := by
  rw [getElem?_eq_bind_idxOf?, idxOf?_getElem_keys m i h]
  simp

/-- Inserting a fresh key appends its value. -/
theorem vals_insert_of_not_mem {m : IndexMap α β} {key : α} (val : β) (h : ¬ (key ∈ m)) :
    (m.insert key val).vals = m.vals.push val := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.vals_insert_of_not_mem val h

theorem mem_iff_keys_contains {m : IndexMap α β} {key : α} :
    key ∈ m ↔ m.keys.contains key := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.mem_iff_keys_contains

@[simp]
theorem contains_insert {m : IndexMap α β} {key k : α} {val : β} :
    IndexMap.contains (m.insert key val) k = (key == k || IndexMap.contains m k) := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.contains_insert

/-- The `∈` spelling of `contains_insert`; `contains_insert` is the `simp` form,
    since `mem_iff_contains` normalises `∈` away first. -/
theorem mem_insert {m : IndexMap α β} {key k : α} {val : β} :
    k ∈ m.insert key val ↔ key == k ∨ k ∈ m := by
  simp only [mem_iff_contains, contains_insert, Bool.or_eq_true]

/-- Inserting a fresh key appends it to `keys`. This is what makes a map built by
    folding `insert` over an array iterate in that array's order. -/
theorem keys_insert_of_not_mem {m : IndexMap α β} {key : α} (val : β) (h : ¬ (key ∈ m)) :
    (m.insert key val).keys = m.keys.push key := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.keys_insert_of_not_mem val h

/-- Overwriting an existing key leaves the iteration order unchanged. -/
theorem keys_insert_of_mem {m : IndexMap α β} {key : α} (val : β) (h : key ∈ m) :
    (m.insert key val).keys = m.keys := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.keys_insert_of_mem val h

theorem mem_of_getElem?_eq_some {m : IndexMap α β} {key : α} {v : β} (h : m[key]? = some v) :
    key ∈ m := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.mem_of_get?_eq_some h

/-- `get?` on a member is `some` of the proof-carrying `getElem`. -/
theorem getElem?_eq_some_getElem {m : IndexMap α β} {key : α} (p : key ∈ m) :
    m[key]? = some m[key] := by
  induction m using Quotient.ind with
  | _ n => exact IndexMap.Raw.get?_eq_some_get n key (mem_elt_of_map ⟨n, ⟨rfl, rfl⟩⟩ p)

/-- Read off `getElem` from a known `get?`; the usual way to discharge goals
    stated with `m[key]`. -/
theorem getElem_eq_of_getElem?_eq_some {m : IndexMap α β} {key : α} {v : β} (p : key ∈ m)
    (h : m[key]? = some v) : m[key] = v := by
  rw [getElem?_eq_some_getElem p] at h
  exact Option.some.inj h

theorem mem_insert_self (m : IndexMap α β) (key : α) (val : β) : key ∈ m.insert key val := by
  apply mem_of_getElem?_eq_some (v := val)
  simp

/-- Build from an array of pairs, last value winning on duplicate keys. -/
protected def ofArray (pairs : Array (α × β)) : IndexMap α β :=
  pairs.foldl (init := IndexMap.empty) fun m (key, val) => m.insert key val

/-- Order-insensitive equality: equal sizes, and every key of `a` maps to an
    equal value in `b`. Built from the quotient-respecting `size`/`keys`/`vals`/
    `get?`, so it needs no `Quotient.lift` proof of its own, and iterates `a`'s
    arrays directly rather than allocating via `toArray`.

    NOTE: this is not yet proved to be an equivalence. `keys_distinct` supplies what
    the argument needs — equal sizes and `a ⊆ b`, with no `BEq`-equal duplicate keys,
    give `b ⊆ a` — but that is not yet formalized. -/
protected def beq [BEq β] (a b : IndexMap α β) : Bool :=
  a.size == b.size &&
    a.size.all fun i lt =>
      let k := a.keys[i]'(by have ksz := a.keys_size; decreasing_tactic)
      let v := a.vals[i]'(by have vsz := a.vals_size; decreasing_tactic)
      b[k]?.any (v == .)

instance [BEq β] : BEq (IndexMap α β) where
  beq := IndexMap.beq

end
end
end Strata.IndexMap
