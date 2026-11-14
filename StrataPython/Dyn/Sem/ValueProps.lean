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

A source's code determines it (`HashSrc.code_inj`).  Each kind of source other
than `reduced` is injective (`HashSrc.buffer_inj` and its siblings) and starts with its own tag
(`HashSrc.tag_buffer` and its siblings), so that two sources are equal only when the same kind is
applied to equal arguments.  Reducing a reduced source gives it back (`HashSrc.reduced_reduced`).

The definitions are in `Value.lean`: `Value` and `Value.beq`, and `Hash` and `HashSrc`, with its
code and the kinds of source.
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

/-- `Hash.toPart` is injective. -/
private theorem Hash.toPart_inj {a b : Hash} (h : a.toPart = b.toPart) : a = b := by
  cases a <;> cases b <;> simp_all [Hash.toPart]

/-- Mapping hashes to parts is injective. -/
private theorem Hash.map_toPart_inj {a b : List Hash} (h : a.map Hash.toPart = b.map Hash.toPart) :
    a = b :=
  (List.map_inj_right fun _ _ => Hash.toPart_inj).mp h

end

namespace HashSrc

/-- `encodeInt` is injective. -/
private theorem encodeInt_inj {a b : Int} (h : encodeInt a = encodeInt b) : a = b := by
  simp only [encodeInt, List.cons.injEq, and_true] at h
  obtain ⟨hs, hn⟩ := h
  by_cases ha : a < 0 <;> by_cases hb : b < 0 <;> simp [ha, hb] at hs <;> omega

/-- A string's characters as numbers determine it. -/
private theorem chars_inj {a b : String}
    (h : a.toList.map (·.toNat) = b.toList.map (·.toNat)) : a = b := by
  have hl : a.toList = b.toList := (List.map_inj_right (fun x y hxy => Char.toNat_inj.mp hxy)).mp h
  exact String.toList_inj.mp hl

/-- `ctorIdx` is injective on built-in constants. -/
public theorem _root_.StrataPython.Dyn.Sem.Builtin.ctorIdx_inj {a b : Builtin}
    (h : a.ctorIdx = b.ctorIdx) : a = b := by
  rw [← Builtin.ofNat_ctorIdx a, h, Builtin.ofNat_ctorIdx]

mutual
/-- **A source's code determines it**, by structural recursion on the source, its parts and its
lists of parts. Like `decEqSrc`, it is written case by case, because `HashSrc` is a nested
inductive (through `List (Int ⊕ HashSrc)`). -/
public theorem code_inj : ∀ (a b : HashSrc), a.code = b.code → a = b
  | buffer x, buffer y, h => by
    simp only [code, List.cons.injEq, true_and] at h
    have hl := (List.map_inj_right (fun x y hxy => UInt8.toNat_inj.mp hxy)).mp h
    rw [ByteArray.ext (Array.toList_inj.mp hl)]
  | addr x, addr y, h => by simp_all [code]
  | const x, const y, h => by
    simp only [code, List.cons.injEq, and_true, true_and] at h; rw [Builtin.ctorIdx_inj h]
  | tuple' ps, tuple' qs, h => by
    simp only [code, List.cons.injEq, true_and] at h
    rw [(partsCode_inj ps qs [] [] h.1 (by simpa using h.2)).1]
  | frozenset' ps, frozenset' qs, h => by
    simp only [code, List.cons.injEq, true_and] at h
    rw [(partsCode_inj ps qs [] [] h.1 (by simpa using h.2)).1]
  | combine' t ps, combine' u qs, h => by
    simp only [code, List.cons.injEq, true_and] at h
    obtain ⟨hl, hrest⟩ := h
    have hlen : (t.toList.map (·.toNat)).length = (u.toList.map (·.toNat)).length := by
      simp only [List.length_map, String.length_toList, hl]
    obtain ⟨hchars, hparts⟩ := List.append_inj hrest hlen
    simp only [List.cons.injEq] at hparts
    rw [chars_inj hchars, (partsCode_inj ps qs [] [] hparts.1 (by simpa using hparts.2)).1]
  | reduced' s, reduced' t, h => by
    simp only [code, List.cons.injEq, true_and] at h
    rw [code_inj s t h]
  | singleton x, singleton y, h => by cases x <;> cases y <;> simp_all [code]
  | builtinFn x, builtinFn y, h => by
    simp only [code, List.cons.injEq, and_true, true_and] at h; rw [Builtin.ctorIdx_inj h]
  | descr t n, descr u k, h => by
    simp only [code, List.cons.injEq, true_and] at h
    obtain ⟨hi, -, hchars⟩ := h
    rw [Builtin.ctorIdx_inj hi, chars_inj hchars]
  -- Different constructors start with different tags.
  | buffer .., addr .., h | buffer .., const .., h | buffer .., tuple' .., h
  | buffer .., frozenset' .., h | buffer .., combine' .., h | buffer .., reduced' .., h
  | buffer .., singleton .., h | buffer .., builtinFn .., h | buffer .., descr .., h
  | addr .., buffer .., h | addr .., const .., h | addr .., tuple' .., h
  | addr .., frozenset' .., h | addr .., combine' .., h | addr .., reduced' .., h
  | addr .., singleton .., h | addr .., builtinFn .., h | addr .., descr .., h
  | const .., buffer .., h | const .., addr .., h | const .., tuple' .., h
  | const .., frozenset' .., h | const .., combine' .., h | const .., reduced' .., h
  | const .., singleton .., h | const .., builtinFn .., h | const .., descr .., h
  | tuple' .., buffer .., h | tuple' .., addr .., h | tuple' .., const .., h
  | tuple' .., frozenset' .., h | tuple' .., combine' .., h | tuple' .., reduced' .., h
  | tuple' .., singleton .., h | tuple' .., builtinFn .., h | tuple' .., descr .., h
  | frozenset' .., buffer .., h | frozenset' .., addr .., h | frozenset' .., const .., h
  | frozenset' .., tuple' .., h | frozenset' .., combine' .., h | frozenset' .., reduced' .., h
  | frozenset' .., singleton .., h | frozenset' .., builtinFn .., h | frozenset' .., descr .., h
  | combine' .., buffer .., h | combine' .., addr .., h | combine' .., const .., h
  | combine' .., tuple' .., h | combine' .., frozenset' .., h | combine' .., reduced' .., h
  | combine' .., singleton .., h | combine' .., builtinFn .., h | combine' .., descr .., h
  | reduced' .., buffer .., h | reduced' .., addr .., h | reduced' .., const .., h
  | reduced' .., tuple' .., h | reduced' .., frozenset' .., h | reduced' .., combine' .., h
  | reduced' .., singleton .., h | reduced' .., builtinFn .., h | reduced' .., descr .., h
  | singleton .., buffer .., h | singleton .., addr .., h | singleton .., const .., h
  | singleton .., tuple' .., h | singleton .., frozenset' .., h | singleton .., combine' .., h
  | singleton .., reduced' .., h | singleton .., builtinFn .., h | singleton .., descr .., h
  | builtinFn .., buffer .., h | builtinFn .., addr .., h | builtinFn .., const .., h
  | builtinFn .., tuple' .., h | builtinFn .., frozenset' .., h | builtinFn .., combine' .., h
  | builtinFn .., reduced' .., h | builtinFn .., singleton .., h | builtinFn .., descr .., h
  | descr .., buffer .., h | descr .., addr .., h | descr .., const .., h
  | descr .., tuple' .., h | descr .., frozenset' .., h | descr .., combine' .., h
  | descr .., reduced' .., h | descr .., singleton .., h | descr .., builtinFn .., h =>
    by simp [code] at h

/-- A part's code determines it. -/
private theorem partCode_inj : ∀ (p q : Int ⊕ HashSrc), partCode p = partCode q → p = q
  | .inl x, .inl y, h => by
    simp only [partCode, List.cons.injEq, true_and] at h; rw [encodeInt_inj h]
  | .inr x, .inr y, h => by
    simp only [partCode, List.cons.injEq, true_and] at h; rw [code_inj x y h.2]
  | .inl _, .inr _, h | .inr _, .inl _, h => by simp [partCode] at h

/-- The codes of two lists of parts of one length, followed by anything, determine the lists. -/
private theorem partsCode_inj : ∀ (ps qs : List (Int ⊕ HashSrc)) (r r' : List Nat),
    ps.length = qs.length → partsCode ps ++ r = partsCode qs ++ r' → ps = qs ∧ r = r'
  | [], [], _, _, _, h => by simpa [partsCode] using h
  | p :: ps, q :: qs, r, r', hl, h => by
    simp only [partsCode, List.cons_append, List.append_assoc, List.cons.injEq] at h
    obtain ⟨hlen, h⟩ := h
    obtain ⟨hpq, hrest⟩ := List.append_inj h hlen
    obtain ⟨h1, h2⟩ := partsCode_inj ps qs r r' (by simpa using hl) hrest
    exact ⟨by rw [partCode_inj p q hpq, h1], h2⟩
  | [], _ :: _, _, _, hl, _ | _ :: _, [], _, _, hl, _ => by simp at hl
end


@[expose] section

/-- A buffer source starts with its own tag. -/
public theorem tag_buffer (b : ByteArray) : (buffer b).tag = some 0 := rfl
/-- An address source starts with its own tag. -/
public theorem tag_addr (id : ObjId) : (addr id).tag = some 1 := rfl
/-- A constant source starts with its own tag. -/
public theorem tag_const (b : Builtin) : (const b).tag = some 2 := rfl
/-- A tuple source starts with its own tag. -/
public theorem tag_tuple (ps : List Hash) : (tuple ps).tag = some 3 := rfl
/-- A frozenset source starts with its own tag. -/
public theorem tag_frozenset (ps : List Hash) : (frozenset ps).tag = some 4 := rfl
/-- A combined source starts with its own tag. -/
public theorem tag_combine (t : String) (ps : List Hash) : (combine t ps).tag = some 5 := rfl
/-- A singleton source starts with its own tag. -/
public theorem tag_singleton (e : Bool) : (singleton e).tag = some 7 := rfl
/-- A built-in function source starts with its own tag. -/
public theorem tag_builtinFn (b : Builtin) : (builtinFn b).tag = some 8 := rfl
/-- A descriptor source starts with its own tag. -/
public theorem tag_descr (t : Builtin) (n : String) : (descr t n).tag = some 9 := rfl

/-- A source that `reduced` makes starts with the tag `6`. -/
public theorem tag_reduced (src : HashSrc) : src.reduced.tag = some 6 := by
  cases src <;> rfl

/-- `reduced` is injective on the sources it doesn't give back: those not reduced already. -/
public theorem reduced_inj {a b : HashSrc} (ha : a.tag ≠ some 6) (hb : b.tag ≠ some 6)
    (h : a.reduced = b.reduced) : a = b := by
  cases a <;> cases b <;> simp_all [reduced, tag]

/-- Equal buffer sources have equal bytes. -/
public theorem buffer_inj {a b : ByteArray} (h : buffer a = buffer b) : a = b := by
  cases h; rfl

/-- Equal address sources are of one object. -/
public theorem addr_inj {a b : ObjId} (h : addr a = addr b) : a = b := by
  cases h; rfl

/-- Equal constant sources are of one constant. -/
public theorem const_inj {a b : Builtin} (h : const a = const b) : a = b := by
  cases h; rfl

/-- Equal built-in function sources are of one function. -/
public theorem builtinFn_inj {a b : Builtin} (h : builtinFn a = builtinFn b) : a = b := by
  cases h; rfl

/-- Equal tuple sources have equal parts. -/
public theorem tuple_inj {a b : List Hash} (h : tuple a = tuple b) : a = b := by
  simp only [tuple, tuple'.injEq] at h
  exact Hash.map_toPart_inj h

/-- Equal frozenset sources have equal parts. -/
public theorem frozenset_inj {a b : List Hash} (h : frozenset a = frozenset b) : a = b := by
  simp only [frozenset, frozenset'.injEq] at h
  exact Hash.map_toPart_inj h

/-- Equal singleton sources are of one singleton. -/
public theorem singleton_inj {a b : Bool} (h : singleton a = singleton b) : a = b := by
  cases h; rfl

/-- Equal combined sources have equal tags and parts. -/
public theorem combine_inj {t t' : String} {a b : List Hash} (h : combine t a = combine t' b) :
    t = t' ∧ a = b := by
  simp only [combine, combine'.injEq] at h
  exact ⟨h.1, Hash.map_toPart_inj h.2⟩

/-- Equal descriptor sources are of one descriptor. -/
public theorem descr_inj {t t' : Builtin} {n n' : String} (h : descr t n = descr t' n') :
    t = t' ∧ n = n' := by
  cases h; exact ⟨rfl, rfl⟩

/-- Reducing a reduced source gives it back. -/
public theorem reduced_reduced (s : HashSrc) : s.reduced.reduced = s.reduced := by
  cases s <;> rfl

end

end HashSrc

end StrataPython.Dyn.Sem
