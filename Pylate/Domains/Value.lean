/-
The value domain and its reduced product (LEAN_SPEC.md sections 3 and 5):
tags, allocation-site locations, abstract values, join/order, and the
reduction operator with theorems T2 (reductive) and T3 (monotone).
Representation replaces Finset/Finsupp by Fset (Strata carries no
mathlib).
-/
import Pylate.Fset

namespace Pylate

inductive Tag
  | tnone | tbool | tint | tfloat | tcomplex | tstr | tbytes
  | tlist | tdict | tdictkeys | tdictitems | tdictvalues
  | tset | ttuple | trange | tgen
  | tobj (c : String) | ttype | tunion | tfunc
  | tnotimpl
  | tunbound | tuninit | tmissing | tany
deriving DecidableEq, Repr, Inhabited, Hashable

/-- A literal *as written in the program*.

    One bag for every scalar kind, rather than a domain per type: `strLits` was
    already this for `str`, and the rest of the shopping list in
    `../../PRECISION_AUDIT.md` -- a nonzero divisor, an index against a length,
    a known codec name, an empty separator -- is the same question asked of a
    different tag.

    `lfloat` keeps the source spelling rather than a `Float`: no float
    *arithmetic* is done on it, and `Float` has neither a usable `DecidableEq`
    (NaN) nor a `Hashable`. `lbytes` likewise keeps the pre-encoding string,
    because in the admitted subset every `bytes` arrives through `str.encode`,
    and that string is what decides whether the value is empty. -/
inductive Lit
  | lnone
  | lbool (b : Bool)
  | lint (i : Int)
  | lfloat (spelling : String)
  | lstr (s : String)
  | lbytes (source : String)
deriving DecidableEq, Repr, Inhabited, Hashable

/-- Python spelling, so a literal in the log reads as it does in the source and
    a `str` cannot be confused with a `bytes` of the same characters. -/
def Lit.render : Lit -> String
  | .lnone => "None"
  | .lbool b => if b then "True" else "False"
  | .lint i => toString i
  | .lfloat spelling => spelling
  | .lstr s => s!"'{s}'"
  | .lbytes s => s!"b'{s}'"

def Lit.tag : Lit -> Tag
  | .lnone => .tnone
  | .lbool _ => .tbool
  | .lint _ => .tint
  | .lfloat _ => .tfloat
  | .lstr _ => .tstr
  | .lbytes _ => .tbytes

/-- Tags whose values a literal can name. A tag outside this set never appears
    in `litsOpen`, so a `list` value is not described as "open". -/
def Tag.bearsLiterals : Tag -> Bool
  | .tnone | .tbool | .tint | .tfloat | .tstr | .tbytes => true
  | _ => false

def Tag.render : Tag → String
  | .tnone => "none" | .tbool => "bool" | .tint => "int"
  | .tfloat => "float" | .tcomplex => "complex" | .tstr => "str"
  | .tbytes => "bytes"
  | .tlist => "list" | .tdict => "dict"
  | .tdictkeys => "dict_keys" | .tdictitems => "dict_items"
  | .tdictvalues => "dict_values"
  | .tset => "set"
  | .ttuple => "tuple" | .trange => "range" | .tgen => "gen"
  | .tobj c => s!"obj:{c}" | .ttype => "type"
  | .tunion => "type_union" | .tfunc => "func"
  | .tnotimpl => "NotImplemented"
  | .tunbound => "unbound" | .tuninit => "uninit"
  | .tmissing => "missing" | .tany => "any"

def Tag.isRef : Tag → Bool
  | .tobj _ | .tlist | .tdict | .tdictkeys | .tdictitems
  | .tdictvalues | .tset | .ttuple
  | .trange | .tgen => true
  | _ => false

inductive LocCls
  | list | dict | dictkeys | dictitems | dictvalues | set | tuple | range | gen
  | obj (c : String) | td (n : String)
deriving DecidableEq, Repr, Inhabited, Hashable

def LocCls.tag : LocCls → Tag
  | .list => .tlist | .dict => .tdict | .set => .tset
  | .dictkeys => .tdictkeys | .dictitems => .tdictitems
  | .dictvalues => .tdictvalues
  | .tuple => .ttuple | .range => .trange | .gen => .tgen
  | .obj c => .tobj c | .td _ => .tdict

def LocCls.render : LocCls → String
  | .list => "list" | .dict => "dict"
  | .dictkeys => "dict_keys" | .dictitems => "dict_items"
  | .dictvalues => "dict_values"
  | .set => "set"
  | .tuple => "tuple" | .range => "range" | .gen => "gen"
  | .obj c => s!"obj:{c}" | .td n => s!"td:{n}"

/-- A node's identity: the path of argument indices from the root of the module.

    `[0, 2, 1]` is "command 0, then its argument 2, then that argument's 1". The
    Strata AST indexes its arguments positionally, so the path is canonical: it is
    a property of where the node sits in the tree, not of the order a traversal
    happened to reach it.

    So an id is stable under edits elsewhere in the file: only the subtree that
    moved changes. It is readable -- `Emit` prints `0.2.1` -- and a synthetic site
    can be derived from a real one by extending its path, which no node's path can
    equal.

    Two representation choices matter for performance, because `Loc.site` is a
    `NodeId` and the heap hashes it on **every lookup**:

    * The path is held **innermost-first**, so extending it is a cons rather than
      an append. `parent ++ [i]` would copy the whole path at every node, making
      construction quadratic in depth and the total memory O(nodes x depth);
      `i :: parent` is O(1) and every parent's tail is *shared* by all of its
      descendants, so the whole id set is one tree of cons cells.
    * The hash is folded in as the path is built and cached, so hashing is O(1)
      rather than a walk of the list per lookup. Equality tests the hash first and
      only compares paths when it matches. -/
structure NodeId where
  /-- Folded as the path grows; compared first, so a mismatch rejects in O(1).
      Named `digest` rather than `hash` because a field called `hash` shadows
      `Hashable.hash` inside this namespace. -/
  digest : UInt64
  /-- Argument indices, **innermost first**. -/
  path : List Nat
deriving Repr, Inhabited, DecidableEq

instance : Hashable NodeId where
  hash id := id.digest

/-- The module root: the empty path. -/
def NodeId.root : NodeId := ⟨mixHash 7 11, []⟩

/-- The child at argument index `i`. O(1), and shares the parent's tail. -/
def NodeId.child (parent : NodeId) (i : Nat) : NodeId :=
  ⟨mixHash parent.digest (Hashable.hash i), i :: parent.path⟩

/-- `0.2.1`, outermost first -- the path is stored the other way round. -/
def NodeId.render (id : NodeId) : String :=
  if id.path.isEmpty then "root"
  else ".".intercalate (id.path.reverse.map toString)

instance : ToString NodeId := ⟨NodeId.render⟩

/-- A numeral denotes the one-element path, so a test can name a distinct
    allocation site as `⟨5, .list, true⟩` without spelling out a path. -/
instance : OfNat NodeId n := ⟨NodeId.root.child n⟩

/-- The reserved argument index under which synthetic sites hang. No dialect
    operator has anything like this many arguments -- the widest is `arguments`
    with seven -- so nothing a traversal produces can land here. -/
def NodeId.synthMarker : Nat := 1000000

/-- A site the analysis invents rather than reads off a node: the element of a
    materialized container, a field of a materialized object.

    Synthetic sites hang under a reserved index that no traversal can reach, so
    they are distinct from every real node and from each other by construction. -/
def NodeId.synth (parent : NodeId) (k : Nat) : NodeId :=
  (parent.child NodeId.synthMarker).child k

structure Loc where
  site   : NodeId
  cls    : LocCls
  recent : Bool
deriving DecidableEq, Repr, Inhabited

/-- A cheap hash: the allocation site and its recency, skipping the class.

    `LocCls`'s `obj`/`td` cases carry a class name, so hashing it would hash a
    string on every heap lookup. One site has one class in practice, so dropping it
    costs no spread, and `DecidableEq` still decides equality. -/
instance : Hashable Loc where
  hash l := mixHash (hash l.site) (hash l.recent)

def Loc.render (l : Loc) : String :=
  let c := match l.cls with
    | .obj c => c | .td n => n | k => k.render
  let suffix := if l.recent then "^" else "*"
  s!"{c}@{l.site}{suffix}"

structure AbsVal where
  tags    : Fset Tag     := []
  locs    : Fset Loc     := []
  funcs   : Fset String  := []
  classes : Fset String  := []
  /-- Program literals this value may equal. -/
  lits    : Fset Lit     := []
  /-- Tags whose values `lits` does *not* enumerate -- the `*` marker, kept per
      tag rather than as one flag so that `1 if c else s` can still be exactly
      `1` on the int side while the str side is unknown. -/
  litsOpen : Fset Tag    := []
  witness : Bool         := false
deriving Repr, Inhabited

namespace AbsVal

def bot : AbsVal := {}

def isBot (v : AbsVal) : Bool :=
  v.tags.isEmpty && v.locs.isEmpty && v.funcs.isEmpty && v.classes.isEmpty

def join (v w : AbsVal) : AbsVal where
  tags    := Fset.union v.tags w.tags
  locs    := Fset.union v.locs w.locs
  funcs   := Fset.union v.funcs w.funcs
  classes := Fset.union v.classes w.classes
  lits    := Fset.union v.lits w.lits
  litsOpen := Fset.union v.litsOpen w.litsOpen
  witness := v.witness || w.witness

def le (v w : AbsVal) : Bool :=
  Fset.subset v.tags w.tags && Fset.subset v.locs w.locs &&
  Fset.subset v.funcs w.funcs && Fset.subset v.classes w.classes &&
  Fset.subset v.lits w.lits && Fset.subset v.litsOpen w.litsOpen &&
  (!v.witness || w.witness)

/-- The order at the Prop level; `witness` is ordered by implication. -/
structure Le (v w : AbsVal) : Prop where
  tags    : Fset.Sub v.tags w.tags
  locs    : Fset.Sub v.locs w.locs
  funcs   : Fset.Sub v.funcs w.funcs
  classes : Fset.Sub v.classes w.classes
  lits    : Fset.Sub v.lits w.lits
  litsOpen : Fset.Sub v.litsOpen w.litsOpen
  witness : v.witness = true → w.witness = true

theorem Le.refl (v : AbsVal) : Le v v :=
  ⟨Fset.Sub.refl _, Fset.Sub.refl _, Fset.Sub.refl _, Fset.Sub.refl _,
   Fset.Sub.refl _, Fset.Sub.refl _, id⟩

/-- Reduction (LEAN_SPEC.md 5.2). The `tany` case keeps the location
    filter and suspends only the tag-needs-witness direction, matching
    `core.py:reduce_val` (the spec's `tagLive` resolves to
    `tagOf l.cls ∈ v.tags`). -/
def reduce (v : AbsVal) : AbsVal :=
  let locs := v.locs.filter (fun l => decide (l.cls.tag ∈ v.tags))
  if Tag.tany ∈ v.tags then { v with locs } else
  let locTags := locs.map (·.cls.tag)
  let tags := v.tags.filter (fun t =>
    if t.isRef then decide (t ∈ locTags)
    else match t with
      | .tfunc => !v.funcs.isEmpty
      | .ttype => !v.classes.isEmpty
      | _ => true)
  { tags, locs
    funcs   := if Tag.tfunc ∈ tags then v.funcs else []
    classes := if Tag.ttype ∈ tags then v.classes else []
    -- A literal whose tag is gone is garbage, and so is an open marker for a tag
    -- the value cannot have. `withoutTags` already filtered both; doing it here
    -- too makes tag/literal agreement an invariant of every *reduced* value
    -- rather than a property of the paths that happen to narrow through
    -- `withoutTags`.
    --
    -- It is a no-op today, because `reduce` only drops `isRef` tags, `tfunc` and
    -- `ttype`, and all six `Lit` kinds are non-ref scalars its tag filter always
    -- keeps. That is precisely why it is worth writing down: the guarantee was
    -- true by coincidence, and a `Lit` kind for a ref tag would have broken it
    -- silently.
    lits    := v.lits.filter (fun l => decide (l.tag ∈ tags))
    litsOpen := v.litsOpen.filter (fun t => decide (t ∈ tags))
    witness := v.witness }

/-- T2 (reductive): `reduce v ≤ v`. Every component filters the original. -/
theorem reduce_le (v : AbsVal) : Le (reduce v) v := by
  unfold reduce
  by_cases h : Tag.tany ∈ v.tags <;> simp only [h, if_pos, if_neg, not_false_iff]
  · exact ⟨Fset.Sub.refl _, Fset.filter_sub, Fset.Sub.refl _,
      Fset.Sub.refl _, Fset.Sub.refl _, Fset.Sub.refl _, id⟩
  · refine ⟨Fset.filter_sub, Fset.filter_sub, ?_, ?_,
      Fset.filter_sub, Fset.filter_sub, id⟩
    · dsimp only
      split
      · exact Fset.Sub.refl _
      · intro a ha; cases ha
    · dsimp only
      split
      · exact Fset.Sub.refl _
      · intro a ha; cases ha

/-- T3 (monotone): `v ≤ w → reduce v ≤ reduce w`. -/
theorem reduce_mono {v w : AbsVal} (h : Le v w) : Le (reduce v) (reduce w) := by
  have locsub : Fset.Sub (v.locs.filter (fun l => decide (l.cls.tag ∈ v.tags)))
      (w.locs.filter (fun l => decide (l.cls.tag ∈ w.tags))) := by
    intro l hl
    have ⟨hmem, hdec⟩ := List.mem_filter.mp hl
    exact List.mem_filter.mpr
      ⟨h.locs l hmem, decide_eq_true (h.tags _ (of_decide_eq_true hdec))⟩
  unfold reduce
  by_cases hv : Tag.tany ∈ v.tags
  · have hw : Tag.tany ∈ w.tags := h.tags _ hv
    simp only [hv, hw, if_pos]
    exact ⟨h.tags, locsub, h.funcs, h.classes, h.lits, h.litsOpen, h.witness⟩
  · by_cases hw : Tag.tany ∈ w.tags
    · simp only [hv, hw, if_pos, if_neg, not_false_iff]
      refine ⟨?_, ?_, ?_, ?_,
        (fun l hl => h.lits l (Fset.filter_sub l hl)),
        (fun x hx => h.litsOpen x (Fset.filter_sub x hx)), h.witness⟩
      · exact fun t ht => h.tags t (Fset.filter_sub t ht)
      · exact fun l hl => locsub l hl
      · dsimp only; split
        · exact h.funcs
        · intro a ha; cases ha
      · dsimp only; split
        · exact h.classes
        · intro a ha; cases ha
    · simp only [hv, hw, if_neg, not_false_iff]
      -- a tag kept in reduce v is kept in reduce w
      have tagsub : Fset.Sub
          (v.tags.filter (fun t => if t.isRef then
              decide (t ∈ (v.locs.filter (fun l => decide (l.cls.tag ∈ v.tags))).map (·.cls.tag))
            else match t with
              | .tfunc => !v.funcs.isEmpty
              | .ttype => !v.classes.isEmpty
              | _ => true))
          (w.tags.filter (fun t => if t.isRef then
              decide (t ∈ (w.locs.filter (fun l => decide (l.cls.tag ∈ w.tags))).map (·.cls.tag))
            else match t with
              | .tfunc => !w.funcs.isEmpty
              | .ttype => !w.classes.isEmpty
              | _ => true)) := by
        intro t ht
        have ⟨hmem, hcond⟩ := List.mem_filter.mp ht
        refine List.mem_filter.mpr ⟨h.tags t hmem, ?_⟩
        by_cases href : t.isRef
        · simp only [href, if_pos] at hcond ⊢
          have := of_decide_eq_true hcond
          have ⟨l, hl, hlt⟩ := List.mem_map.mp this
          exact decide_eq_true (List.mem_map.mpr ⟨l, locsub l hl, hlt⟩)
        · simp only [href, if_neg, Bool.false_eq_true, not_false_iff] at hcond ⊢
          cases t with
          | tfunc =>
            simp only at hcond ⊢
            cases hf : v.funcs with
            | nil => rw [hf] at hcond; simp at hcond
            | cons a as =>
              have : a ∈ w.funcs := h.funcs a (by rw [hf]; exact List.mem_cons_self ..)
              cases hg : w.funcs with
              | nil => rw [hg] at this; cases this
              | cons _ _ => simp
          | ttype =>
            simp only at hcond ⊢
            cases hf : v.classes with
            | nil => rw [hf] at hcond; simp at hcond
            | cons a as =>
              have : a ∈ w.classes := h.classes a (by rw [hf]; exact List.mem_cons_self ..)
              cases hg : w.classes with
              | nil => rw [hg] at this; cases this
              | cons _ _ => simp
          | tnone => simp | tbool => simp | tint => simp | tfloat => simp
          | tcomplex => simp | tstr => simp | tbytes => simp
          | tnotimpl => simp | tunbound => simp
          | tuninit => simp | tmissing => simp | tany => simp
          | tobj c => simp [Tag.isRef] at href
          | tlist => simp [Tag.isRef] at href
          | tdict => simp [Tag.isRef] at href
          | tdictkeys => simp [Tag.isRef] at href
          | tdictitems => simp [Tag.isRef] at href
          | tdictvalues => simp [Tag.isRef] at href
          | tset => simp [Tag.isRef] at href
          | ttuple => simp [Tag.isRef] at href
          | trange => simp [Tag.isRef] at href
          | tgen => simp [Tag.isRef] at href
          | tunion => simp
      refine ⟨tagsub, locsub, ?_, ?_, ?_, ?_, h.witness⟩
      · dsimp only
        split
        · rename_i hkept
          have hw' : Tag.tfunc ∈ _ := tagsub _ hkept
          rw [if_pos hw']
          exact h.funcs
        · intro a ha; cases ha
      · dsimp only
        split
        · rename_i hkept
          have hw' : Tag.ttype ∈ _ := tagsub _ hkept
          rw [if_pos hw']
          exact h.classes
        · intro a ha; cases ha
      · -- a literal kept by `reduce v` is kept by `reduce w`: its tag survives
        -- in `v`, and `tagsub` carries that to `w`.
        intro l hl
        have ⟨hmem, hdec⟩ := List.mem_filter.mp hl
        exact List.mem_filter.mpr
          ⟨h.lits l hmem, decide_eq_true (tagsub _ (of_decide_eq_true hdec))⟩
      · intro x hx
        have ⟨hmem, hdec⟩ := List.mem_filter.mp hx
        exact List.mem_filter.mpr
          ⟨h.litsOpen x hmem, decide_eq_true (tagsub _ (of_decide_eq_true hdec))⟩

def withoutTags (v : AbsVal) (bad : Fset Tag) : AbsVal :=
  let tags := Fset.diff v.tags bad
  { tags
    locs := v.locs.filter (fun l => decide (l.cls.tag ∈ tags))
    funcs := if Tag.tfunc ∈ tags then v.funcs else []
    classes := if Tag.ttype ∈ tags then v.classes else []
    lits    := v.lits.filter (fun l => decide (l.tag ∈ tags))
    litsOpen := v.litsOpen.filter (fun t => decide (t ∈ tags))
    witness := v.witness }

def restrictTags (v : AbsVal) (keep : Fset Tag) : AbsVal :=
  v.withoutTags (Fset.diff v.tags keep)

def renameLoc (v : AbsVal) (old new : Loc) : AbsVal :=
  if old ∈ v.locs then
    { v with locs := Fset.insert new (v.locs.filter (· ≠ old)) }
  else v

end AbsVal

/-- Convenience constructor mirroring `core.py:V`. -/
def V (tags : List Tag) (locs : List Loc := []) (funcs : List String := [])
    (classes : List String := []) (witness : Bool := false) : AbsVal :=
  { tags, locs, funcs, classes
    -- No literal is known, so every literal-bearing tag is open. This is the
    -- default for any computed value, which is what keeps `lits` finite: a
    -- transfer that does not deliberately carry a literal through loses it.
    litsOpen := tags.filter Tag.bearsLiterals
    witness }

def litV (l : Lit) : AbsVal :=
  { tags := [l.tag], lits := [l], litsOpen := [] }

def strLitV (s : String) : AbsVal := litV (.lstr s)

/-! ### Reading the bag

`strLits` and `strOpen` are derived rather than stored, so every existing reader
keeps working against the unified representation. -/

namespace AbsVal

def strLits (v : AbsVal) : Fset String :=
  v.lits.filterMap fun l => match l with | .lstr s => some s | _ => none

def strOpen (v : AbsVal) : Bool := Tag.tstr ∈ v.litsOpen

/-- The int literals this value may equal, and whether that set is complete. -/
def intLits (v : AbsVal) : Fset Int :=
  v.lits.filterMap fun l => match l with | .lint i => some i | _ => none

def intOpen (v : AbsVal) : Bool := Tag.tint ∈ v.litsOpen

/-- The pre-encoding source of every `bytes` literal this value may equal. -/
def bytesLits (v : AbsVal) : Fset String :=
  v.lits.filterMap fun l => match l with | .lbytes s => some s | _ => none

def bytesOpen (v : AbsVal) : Bool := Tag.tbytes ∈ v.litsOpen

/-- Numeric tags, for the divisor question. -/
private def numericTag (t : Tag) : Bool :=
  t == .tint || t == .tbool || t == .tfloat || t == .tcomplex

/-- Does this float spelling certainly denote a magnitude of at least one?

    Deliberately weaker than "has a nonzero digit". A mantissa can be nonzero and
    the value still be zero by underflow -- `1e-400` and `0.` followed by four
    hundred zeros and a `1` both evaluate to `0.0` -- so the only spellings
    accepted are those with no exponent and a nonzero digit *before* the point,
    which cannot underflow. `0.5` is therefore treated as possibly zero: sound,
    and it costs nothing that has been measured. -/
private def floatAtLeastOne (spelling : String) : Bool :=
  let s := spelling.replace "_" ""
  if s.any (fun c => c == 'e' || c == 'E') then false
  else
    let intPart := (s.splitOn ".").headD ""
    intPart.any (fun c => '1' ≤ c && c ≤ '9')

/-- Is every value this can denote nonzero?

    A numeric tag whose literals are not enumerated could be zero, so the tag
    must be closed *and* every literal of it nonzero. Non-numeric tags are
    irrelevant here: a non-number divisor is a `TypeError`, which the effect
    table already carries. -/
def definitelyNonzero (v : AbsVal) : Bool :=
  v.tags.all (fun t => !numericTag t || !(v.litsOpen.contains t)) &&
  v.lits.all (fun l => match l with
    | .lint i => i != 0
    | .lbool b => b
    | .lfloat spelling => floatAtLeastOne spelling
    | _ => true) &&
  v.tags.any numericTag

end AbsVal

def unboundV : AbsVal := V [.tunbound]
def anyV : AbsVal := V [.tany]

-- ---------------------------------------------------------------- states

end Pylate
