/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Value

set_option autoImplicit false

/-!
# Properties of values

`Value.beq`, the structural equality, is lawful: it holds exactly of equal values
(`Value.eq_of_beq`, `Value.beq_of_eq`), so a table can index entries by a whole `Value`.

The encoding of hashes determines them (`Hash.encode_inj`, `encodeHashes_inj`).  Each kind of
source other than `reduced` is injective (`HashSrc.buffer_inj` and its siblings) and starts with
its own tag (`HashSrc.tag_buffer` and its siblings), so that two sources are equal only when the
same kind is applied to equal arguments.  Reducing a reduced source gives it back
(`HashSrc.reduced_reduced`).

The definitions are in `Value.lean`: `Value` and `Value.beq`, and `Hash` and `HashSrc`, with the
encodings (`Hash.encode`, `encodeHashes`, `encodeParts`) and the kinds of source.
-/

namespace StrataPython.Dyn.Sem

@[expose] public section

/-- Two arrays of one size whose members are pairwise `beq`, for a `beq` that gives equality on
the members of the first, are equal. -/
private theorem tupleAll {xs ys : Array Value} (ih : ∀ x ∈ xs, ∀ y, Value.beq x y = true → x = y)
    (hs : xs.size = ys.size)
    (ha : (xs.attach.zip ys).all (fun (p : {x // x ∈ xs} × Value) => Value.beq p.1.1 p.2) = true) :
    xs = ys := by
  apply Array.ext hs
  intro i h1 h2
  have hz : i < (xs.attach.zip ys).size := by simp [Array.size_zip]; omega
  have := (Array.all_eq_true.mp ha) i hz
  simp only [Array.getElem_zip, Array.getElem_attach] at this
  exact ih _ (Array.getElem_mem h1) _ this

/-- `Value.beq` gives only equal values. -/
theorem Value.eq_of_beq : ∀ {a b : Value}, Value.beq a b = true → a = b := by
  intro a b h
  fun_induction Value.beq a b
  case case10 xs ys ih =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact congrArg Value.tuple (tupleAll ih h.1 h.2)
  all_goals simp_all

/-- `Value.beq` holds of equal values. -/
theorem Value.beq_of_eq : ∀ {a b : Value}, a = b → Value.beq a b = true := by
  intro a b h
  fun_induction Value.beq a b
  case case10 xs ys ih =>
    cases h
    simp only [Bool.and_eq_true, beq_iff_eq, true_and, Array.all_eq_true]
    intro i hi
    simp only [Array.getElem_zip, Array.getElem_attach]
    exact ih _ (Array.getElem_mem _) _ rfl
  case case20 x y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    subst h
    cases x <;> simp_all
    all_goals (rename_i hx; apply hx <;> rfl)
  all_goals (cases h <;> simp_all)

/-- `Value`'s `==` holds of a value and itself. -/
instance : ReflBEq Value := ⟨Value.beq_of_eq rfl⟩

/-- `Value`'s `==` is equality. -/
instance : LawfulBEq Value where
  eq_of_beq := Value.eq_of_beq

/-- `encodeInt` is injective. -/
public theorem encodeInt_inj {a b : Int} (h : encodeInt a = encodeInt b) : a = b := by
  simp only [encodeInt, List.cons.injEq, and_true] at h
  obtain ⟨hs, hn⟩ := h
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp [ha, hb] at hs <;> omega

/-- A hash's encoding determines it. -/
public theorem Hash.encode_inj {a b : Hash} (h : a.encode = b.encode) : a = b := by
  cases a <;> cases b <;> simp [Hash.encode] at h
  · rw [encodeInt_inj h]
  · rename_i s t; rw [HashSrc.ext h.2]

/-- The parts of two lists of hashes of one length, followed by anything, determine the lists. -/
public theorem encodeParts_append_inj : ∀ {hs hs' : List Hash} {r r' : List Nat},
    hs.length = hs'.length → encodeParts hs ++ r = encodeParts hs' ++ r' → hs = hs' ∧ r = r'
  | [], [], _, _, _, h => by simpa [encodeParts] using h
  | a :: as, b :: bs, r, r', hl, h => by
    simp only [encodeParts, List.flatMap_cons, List.cons_append, List.append_assoc,
      List.cons.injEq] at h
    obtain ⟨hlen, h⟩ := h
    obtain ⟨hab, hrest⟩ := List.append_inj h hlen
    have hab' := Hash.encode_inj hab
    obtain ⟨h1, h2⟩ := encodeParts_append_inj (by simpa using hl) hrest
    exact ⟨by rw [hab', h1], h2⟩

/-- `encodeHashes` is injective. -/
public theorem encodeHashes_inj {hs hs' : List Hash} (h : encodeHashes hs = encodeHashes hs') : hs = hs' := by
  simp only [encodeHashes, List.cons.injEq] at h
  have hparts := encodeParts_append_inj (r := []) (r' := []) h.1 (by simpa [encodeParts] using h.2)
  exact hparts.1

end

namespace HashSrc

@[expose] section

/-- A buffer source starts with its own tag. -/
public theorem tag_buffer (b : List UInt8) : (buffer b).tag = some 0 := by
  unfold tag buffer; rfl
/-- A address source starts with its own tag. -/
public theorem tag_addr (id : ObjId) : (addr id).tag = some 1 := by
  unfold tag addr; rfl
/-- A constant source starts with its own tag. -/
public theorem tag_const (b : Builtin) : (const b).tag = some 2 := by
  unfold tag const; rfl
/-- A tuple source starts with its own tag. -/
public theorem tag_tuple (ps : List Hash) : (tuple ps).tag = some 3 := by
  unfold tag tuple; rfl
/-- A frozenset source starts with its own tag. -/
public theorem tag_frozenset (ps : List Hash) : (frozenset ps).tag = some 4 := by
  unfold tag frozenset; rfl
/-- A combined source starts with its own tag. -/
public theorem tag_combine (t : String) (ps : List Hash) : (combine t ps).tag = some 5 := by
  unfold tag combine; rfl
/-- A singleton source starts with its own tag. -/
public theorem tag_singleton (e : Bool) : (singleton e).tag = some 7 := by
  unfold tag singleton; rfl
/-- A built-in function source starts with its own tag. -/
public theorem tag_builtinFn (b : Builtin) : (builtinFn b).tag = some 8 := by
  unfold tag builtinFn; rfl
/-- A descriptor source starts with its own tag. -/
public theorem tag_descr (t : Builtin) (n : String) : (descr t n).tag = some 9 := by
  unfold tag descr; rfl

/-- A source that `reduced` makes starts with the tag `6`. -/
public theorem tag_reduced (src : HashSrc) : src.reduced.tag = some 6 := by
  unfold tag reduced
  split
  · rename_i hc; simp [hc]
  · rfl

/-- `reduced` is injective on the sources it doesn't give back: those not reduced already. -/
public theorem reduced_inj {a b : HashSrc} (ha : a.tag ≠ some 6) (hb : b.tag ≠ some 6)
    (h : a.reduced = b.reduced) : a = b := by
  rcases a with ⟨ca⟩
  rcases b with ⟨cb⟩
  have hca : ∀ t, ca ≠ 6 :: t := fun t e => ha (by simp [tag, e])
  have hcb : ∀ t, cb ≠ 6 :: t := fun t e => hb (by simp [tag, e])
  have hra : reduced ⟨ca⟩ = ⟨6 :: ca⟩ := by
    unfold reduced; split
    · rename_i t e; exact absurd e (hca t)
    · rfl
  have hrb : reduced ⟨cb⟩ = ⟨6 :: cb⟩ := by
    unfold reduced; split
    · rename_i t e; exact absurd e (hcb t)
    · rfl
  rw [hra, hrb] at h
  have hc := congrArg code h
  simp only [List.cons.injEq, true_and] at hc
  rw [hc]

/-- Equal buffer sources have equal bytes. -/
public theorem buffer_inj {a b : List UInt8} (h : buffer a = buffer b) : a = b := by
  have hc := congrArg code h
  simp only [buffer, List.cons.injEq, true_and] at hc
  exact (List.map_inj_right (fun x y hxy => UInt8.toNat_inj.mp hxy)).mp hc

/-- Equal address sources are of one object. -/
public theorem addr_inj {a b : ObjId} (h : addr a = addr b) : a = b := by
  have hc := congrArg code h
  simpa [addr] using hc

/-- `ctorIdx` is injective on built-in constants. -/
public theorem _root_.StrataPython.Dyn.Sem.Builtin.ctorIdx_inj {a b : Builtin}
    (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← Builtin.ofNat_ctorIdx a, h, Builtin.ofNat_ctorIdx]

/-- Equal constant sources are of one constant. -/
public theorem const_inj {a b : Builtin} (h : const a = const b) : a = b := by
  have hc := congrArg code h
  simp only [const, List.cons.injEq, and_true, true_and] at hc
  exact Builtin.ctorIdx_inj hc

/-- Equal built-in function sources are of one function. -/
public theorem builtinFn_inj {a b : Builtin} (h : builtinFn a = builtinFn b) : a = b := by
  have hc := congrArg code h
  simp only [builtinFn, List.cons.injEq, and_true, true_and] at hc
  exact Builtin.ctorIdx_inj hc

/-- Equal tuple sources have equal parts. -/
public theorem tuple_inj {a b : List Hash} (h : tuple a = tuple b) : a = b := by
  have hc := congrArg code h
  simp only [tuple, List.cons.injEq, true_and] at hc
  exact encodeHashes_inj hc

/-- Equal frozenset sources have equal parts. -/
public theorem frozenset_inj {a b : List Hash} (h : frozenset a = frozenset b) : a = b := by
  have hc := congrArg code h
  simp only [frozenset, List.cons.injEq, true_and] at hc
  exact encodeHashes_inj hc

/-- Equal singleton sources are of one singleton. -/
public theorem singleton_inj {a b : Bool} (h : singleton a = singleton b) : a = b := by
  have hc := congrArg code h
  cases a <;> cases b <;> simp_all [singleton]

/-- A string's characters as numbers determine it. -/
private theorem chars_inj {a b : String}
    (h : a.toList.map (·.toNat) = b.toList.map (·.toNat)) : a = b := by
  have hl : a.toList = b.toList := (List.map_inj_right (fun x y hxy => Char.toNat_inj.mp hxy)).mp h
  exact String.toList_inj.mp hl

/-- Equal combined sources have equal tags and parts. -/
public theorem combine_inj {t t' : String} {a b : List Hash} (h : combine t a = combine t' b) :
    t = t' ∧ a = b := by
  have hc := congrArg code h
  simp only [combine, List.cons.injEq] at hc
  have hl := hc.2.1
  have hrest := hc.2.2
  have hlen : (t.toList.map (·.toNat)).length = (t'.toList.map (·.toNat)).length := by
    simp only [List.length_map, String.length_toList, hl]
  obtain ⟨hchars, hparts⟩ := List.append_inj hrest hlen
  exact ⟨chars_inj hchars, encodeHashes_inj hparts⟩

/-- Equal descriptor sources are of one descriptor. -/
public theorem descr_inj {t t' : Builtin} {n n' : String} (h : descr t n = descr t' n') :
    t = t' ∧ n = n' := by
  have hc := congrArg code h
  simp only [descr, List.cons.injEq] at hc
  obtain ⟨-, hi, -, hchars⟩ := hc
  exact ⟨Builtin.ctorIdx_inj hi, chars_inj hchars⟩

/-- Reducing a reduced source gives it back. -/
public theorem reduced_reduced (s : HashSrc) : s.reduced.reduced = s.reduced := by
  rcases s with ⟨c⟩
  cases c with
  | nil => rfl
  | cons x xs =>
    by_cases hx : x = 6
    · subst hx; rfl
    · simp [reduced, hx]

end

end HashSrc

end StrataPython.Dyn.Sem
