/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
-- For `String.compare`'s body.
import all Init.Data.Ord.String

set_option autoImplicit false

/-!
# Hierarchical names
-/

namespace Strata.Mantle

public section

-- Expose these definitions for other modules.
@[expose] section

inductive Name where
| base
| num (n : Name) (i : Nat) -- A counter suffix used for generating fresh names.
| str (n : Name) (s : String)
deriving DecidableEq, Hashable, Repr

namespace Name

/-- Number of segments in the name. -/
def depth : Name → Nat
| .base => 0
| .num b _ => depth b + 1
| .str b _ => depth b + 1

/-- Drop the `k` outermost segments, keeping the root-side prefix. -/
def dropOuter : Name → Nat → Name
| n, 0 => n
| .str b _, k+1 => dropOuter b k
| .num b _, k+1 => dropOuter b k
| .base, _+1 => .base          -- unreachable when `k ≤ depth n`

/-- `String.compare`, computed on UTF-8 bytes. The kernel reduces this much faster than
`String.compare`, which decodes to characters first. Compiled code runs `String.compare`
(`cmpStr_eq_compare`). -/
def cmpStr (a b : String) : Ordering :=
  List.compareLex compare a.toByteArray.data.toList b.toByteArray.data.toList

end Name

end

end

/-! ### `cmpStr` is `String.compare` -/

namespace Name

/-- `x` is below `y` at a position both have. -/
def LexLt : List UInt8 → List UInt8 → Prop
  | a :: as, b :: bs => a < b ∨ (a = b ∧ LexLt as bs)
  | _, _ => False

/-- If `x` is below `y` at a shared position, anything appended after them leaves `x` first. -/
private theorem compareLex_append_of_lexLt : ∀ {x y : List UInt8} (r s : List UInt8),
    LexLt x y → List.compareLex compare (x ++ r) (y ++ s) = .lt ∧
      List.compareLex compare (y ++ s) (x ++ r) = .gt
  | a :: as, b :: bs, r, s, h => by
    rcases h with h | ⟨rfl, h⟩
    · simp [List.compareLex_cons_cons, Std.compare_eq_lt.mpr h, Std.compare_eq_gt.mpr h]
    · simp [List.compareLex_cons_cons, compareLex_append_of_lexLt r s h]

/-- A common prefix does not change a byte comparison. -/
private theorem compareLex_append_self : ∀ (x : List UInt8) (r s : List UInt8),
    List.compareLex compare (x ++ r) (x ++ s) = List.compareLex compare r s
  | [], _, _ => rfl
  | a :: as, r, s => by simp [List.compareLex_cons_cons, compareLex_append_self as r s]

/-- UTF-8 encoding preserves character order, deciding within the shorter encoding. -/
private theorem lexLt_utf8EncodeChar {c d : Char} (h : c < d) :
    LexLt (String.utf8EncodeChar c) (String.utf8EncodeChar d) := by
  have hv : c.val.toNat < d.val.toNat := UInt32.lt_iff_toNat_lt.mp h
  have hd : d.val.toNat < 0x110000 := by
    have := d.valid
    revert this
    simp only [UInt32.isValidChar, Nat.isValidChar]
    omega
  -- `omega` needs each division as one step from the previous one.
  have hc₁ : c.val.toNat / 4096 = c.val.toNat / 64 / 64 := by rw [Nat.div_div_eq_div_mul]
  have hc₂ : c.val.toNat / 262144 = c.val.toNat / 4096 / 64 := by rw [Nat.div_div_eq_div_mul]
  have hd₁ : d.val.toNat / 4096 = d.val.toNat / 64 / 64 := by rw [Nat.div_div_eq_div_mul]
  have hd₂ : d.val.toNat / 262144 = d.val.toNat / 4096 / 64 := by rw [Nat.div_div_eq_div_mul]
  simp only [String.utf8EncodeChar]
  repeat' split
  all_goals
    simp only [LexLt, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, UInt8.toNat_ofNat',
      Nat.reducePow, hc₂, hd₂, hc₁, hd₁]
    clear hc₁ hc₂ hd₁ hd₂
    omega

/-- Every character encodes to at least one byte. -/
private theorem utf8EncodeChar_ne_nil (c : Char) : String.utf8EncodeChar c ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  have hpos := c.utf8Size_pos
  simp_all

/-- Comparing UTF-8 encodings byte-wise is lexicographic order on the characters. -/
private theorem compareLex_flatMap : ∀ (l m : List Char),
    List.compareLex compare (l.flatMap String.utf8EncodeChar) (m.flatMap String.utf8EncodeChar) =
      if l < m then .lt else if l = m then .eq else .gt
  | [], [] => by simp [List.compareLex_nil_nil]
  | [], d :: ds => by
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil (utf8EncodeChar_ne_nil d)
    simp [hb, List.compareLex_nil_cons, List.nil_lt_cons]
  | c :: cs, [] => by
    obtain ⟨b, bs, hb⟩ := List.exists_cons_of_ne_nil (utf8EncodeChar_ne_nil c)
    simp [hb, List.compareLex_cons_nil]
  | c :: cs, d :: ds => by
    simp only [List.flatMap_cons, List.cons_lt_cons_iff, List.cons.injEq]
    by_cases h : c < d
    · simp [(compareLex_append_of_lexLt _ _ (lexLt_utf8EncodeChar h)).1, h]
    by_cases e : c = d
    · subst e; simp [compareLex_append_self, compareLex_flatMap cs ds]
    have h' : d < c := Char.lt_def.mpr <| UInt32.lt_of_le_of_ne
      (Char.not_lt.mp h) (fun v => e (Char.val_inj.mp v).symm)
    simp [(compareLex_append_of_lexLt _ _ (lexLt_utf8EncodeChar h')).2, h, e]

-- Before `cmpAligned`, so that its compiled code uses `String.compare`.
public section

/-- `cmpStr` agrees with `String.compare`. -/
@[csimp] theorem cmpStr_eq_compare : @cmpStr = @String.compare := by
  funext a b
  simp only [cmpStr, ← String.utf8Encode_toList, List.utf8Encode, List.toList_data_toByteArray,
    compareLex_flatMap, String.compare, compareOfLessAndEq, String.toList_inj]
  rfl

end

end Name

public section
@[expose] section

namespace Name

/-- Compare two names of equal depth, using `cmpStr` for kernel performance. -/
def cmpAligned : Name → Name → Ordering
| .base, _ => .eq
| _, .base => .eq
| .num a _, .str b _ =>
  match cmpAligned a b with
  | .eq => .lt
  | o => o
| .str a _, .num b _ =>
  match cmpAligned a b with
  | .eq => .gt
  | o => o
| .str a s, .str b t =>
  match cmpAligned a b with
  | .eq => cmpStr s t
  | o => o
| .num a i, .num b j =>
  match cmpAligned a b with
  | .eq => compare i j
  | o => o

/-- Compare names lexicographically by segment, from the root outwards; a name
    that is a proper prefix of the other compares `.lt`. -/
protected def compare (x y : Name) : Ordering :=
  let dx := x.depth
  let dy := y.depth
  match compare dx dy with
  | .eq => cmpAligned x y
  | .lt =>
    match cmpAligned x (y.dropOuter (dy - dx)) with
    | .lt | .eq => .lt          -- `x` is a proper prefix of `y`
    | .gt => .gt
  | .gt =>
    match cmpAligned (x.dropOuter (dx - dy)) y with
    | .lt => .lt
    | .eq | .gt => .gt          -- `y` is a proper prefix of `x`

instance : Ord Name := ⟨Name.compare⟩

instance : LT Name where
  lt x y := compare x y = .lt

end Name

end

end

end Strata.Mantle
