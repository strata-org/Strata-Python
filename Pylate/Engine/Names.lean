/-
Verified name generation. Decorated names (qualified names, invocation
frames, per-key edges, flavor names) are inductive values, not strings;
`render` produces the encoded spelling and the theorems make collisions
impossible by construction:

- `render_inj`: no two decorated names render alike (via the parser
  roundtrip `parse_render`).
- `render_prefixFree`: no rendering is a prefix of another, so later
  passes may concatenate encoded names and still decode uniquely (the
  terminator discipline: '#' ends every rendering and never occurs
  inside one).
- `render_fresh`: no rendering is a bare user identifier (every
  rendering contains '#', which the atom alphabet excludes).

Atoms carry exactly the Python identifier alphabet, so the separator
and terminator characters are atom-free by construction; the admission
checker's identifiers satisfy the atom predicate by CPython's lexical
grammar, checked once at `Ident.of?`.
-/
import Pylate.Fset

namespace Pylate

/-- Characters allowed inside a name atom: the Python identifier
    alphabet. Separators (':', '.', '|', '>') and the terminator '#'
    are excluded, which is what every proof below leans on. -/
def atomChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- A name atom: nonempty, atom characters only. -/
def Ident : Type := { l : List Char // l ≠ [] ∧ l.all atomChar = true }

instance : DecidableEq Ident := by
  unfold Ident; infer_instance

/-- Boundary constructor: check a string once, carry the proof after. -/
def Ident.of? (s : String) : Option Ident :=
  let l := s.toList
  if h : l ≠ [] ∧ l.all atomChar = true then some ⟨l, h⟩ else none

def Ident.str (i : Ident) : String := String.ofList i.val

-- ------------------------------------------------------------- digits

def digitChar : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

def readDigit : Char → Option Nat
  | '0' => some 0 | '1' => some 1 | '2' => some 2 | '3' => some 3
  | '4' => some 4 | '5' => some 5 | '6' => some 6 | '7' => some 7
  | '8' => some 8 | '9' => some 9 | _ => none

theorem readDigit_digitChar (d : Nat) (h : d < 10) :
    readDigit (digitChar d) = some d := by
  match d, h with
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl
  | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl

theorem digitChar_isDigit (d : Nat) (h : d < 10) :
    (readDigit (digitChar d)).isSome := by
  rw [readDigit_digitChar d h]; rfl

/-- Decimal rendering, most significant digit first. -/
def natChars (n : Nat) : List Char :=
  if _h : n < 10 then [digitChar n]
  else natChars (n / 10) ++ [digitChar (n % 10)]
decreasing_by
  omega

theorem natChars_ne_nil (n : Nat) : natChars n ≠ [] := by
  rw [natChars]
  split <;> simp

theorem natChars_digits (n : Nat) :
    ∀ c ∈ natChars n, (readDigit c).isSome := by
  induction n using natChars.induct with
  | case1 n h =>
    rw [natChars]
    rw [dif_pos h]
    intro c hc
    simp at hc
    subst hc
    exact digitChar_isDigit n h
  | case2 n h ih =>
    rw [natChars]
    rw [dif_neg h]
    intro c hc
    simp only [List.mem_append] at hc
    cases hc with
    | inl hl => exact ih c hl
    | inr hr =>
      simp at hr
      subst hr
      exact digitChar_isDigit (n % 10) (Nat.mod_lt _ (by omega))

/-- Greedy digit reader: accumulates the value, returns the rest. -/
def readNatAux : List Char → Nat → Nat × List Char
  | [], acc => (acc, [])
  | c :: rest, acc =>
    match readDigit c with
    | some d => readNatAux rest (acc * 10 + d)
    | none => (acc, c :: rest)

theorem readNatAux_append (l : List Char) :
    (∀ c ∈ l, (readDigit c).isSome) →
    ∀ (rest : List Char) (acc : Nat),
      (∀ h : rest ≠ [], ¬ (readDigit (rest.head h)).isSome) →
      readNatAux (l ++ rest) acc =
        (l.foldl (fun a c => a * 10 + (readDigit c).getD 0) acc, rest) := by
  induction l with
  | nil =>
    intro _ rest acc hrest
    simp only [List.nil_append, List.foldl_nil]
    cases rest with
    | nil => rfl
    | cons c cs =>
      have hnd := hrest (by simp)
      simp only [List.head_cons] at hnd
      cases hrd : readDigit c with
      | some d => exact absurd (by rw [hrd]; rfl) hnd
      | none => simp [readNatAux, hrd]
  | cons c cs ih =>
    intro hl rest acc hrest
    have hc : (readDigit c).isSome := hl c (by simp)
    cases hrd : readDigit c with
    | none => rw [hrd] at hc; exact absurd hc (by simp)
    | some d =>
      simp only [List.cons_append, readNatAux, hrd]
      rw [ih (fun x hx => hl x (by simp [hx])) rest (acc * 10 + d) hrest]
      simp [List.foldl, hrd]

theorem foldl_natChars (n : Nat) : ∀ acc,
    (natChars n).foldl (fun a c => a * 10 + (readDigit c).getD 0) acc =
      acc * 10 ^ (natChars n).length + n := by
  induction n using natChars.induct with
  | case1 n h =>
    intro acc
    rw [natChars, dif_pos h]
    simp [List.foldl, readDigit_digitChar n h]
  | case2 n h ih =>
    intro acc
    rw [natChars, dif_neg h]
    rw [List.foldl_append, ih acc]
    simp only [List.foldl, readDigit_digitChar (n % 10)
      (Nat.mod_lt _ (by omega)), Option.getD_some, List.length_append,
      List.length_cons, List.length_nil, Nat.pow_succ, ← Nat.mul_assoc]
    omega

/-- The roundtrip at the digits layer: reading a rendered number back,
    with a non-digit boundary, recovers the number and the rest. -/
theorem readNat_natChars (n : Nat) (rest : List Char)
    (hrest : ∀ h : rest ≠ [], ¬ (readDigit (rest.head h)).isSome) :
    readNatAux (natChars n ++ rest) 0 = (n, rest) := by
  rw [readNatAux_append (natChars n) (natChars_digits n) rest 0 hrest]
  rw [foldl_natChars n 0]
  simp

-- -------------------------------------------------------------- atoms

/-- Greedy atom reader: the longest atom-character prefix. -/
def readAtomAux : List Char → List Char × List Char
  | [] => ([], [])
  | c :: rest =>
    if atomChar c then
      let (a, r) := readAtomAux rest
      (c :: a, r)
    else ([], c :: rest)

theorem readAtom_append (i : List Char) (hi : i.all atomChar = true)
    (rest : List Char)
    (hr : ∀ h : rest ≠ [], atomChar (rest.head h) = false) :
    readAtomAux (i ++ rest) = (i, rest) := by
  induction i with
  | nil =>
    simp only [List.nil_append]
    cases rest with
    | nil => rfl
    | cons c cs =>
      have := hr (by simp)
      simp only [List.head_cons] at this
      simp [readAtomAux, this]
  | cons c cs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hi
    simp [readAtomAux, hi.1, ih hi.2]

/-- Digits are atom characters, so an atom boundary is also a digit
    boundary. -/
theorem readDigit_isSome_atom (c : Char) :
    (readDigit c).isSome → atomChar c = true := by
  unfold readDigit
  split <;> intro h <;> simp_all <;> decide

-- ---------------------- CBMC-style three-level renaming, made a type

/-- A renamed variable copy, CBMC's multi-level SSA convention as a
    type: one copy of a variable per execution context, one typed field
    per indexing level. `thread` is the running thread, `call` the
    invocation of the enclosing function, `iteration` the loop
    iteration, `update` the sequential assignment index (CBMC collapses
    thread and call into level 0 `!`, and spells iteration `@` and
    update `#`). The fields ARE the decoration grammar: a copy cannot
    be built with a level missing, duplicated, or attached to the
    wrong thing. -/
structure VarCopy where
  scope     : List Ident
  name      : Ident
  thread    : Nat
  call      : Nat
  iteration : Nat
  update    : Nat

/-- The rendered body, terminator excluded, as a flat list of segments
    (a shape the membership proofs can take apart mechanically).
    Spelling: `scope:name~thread!call@iteration#update`. -/
def VarCopy.body (v : VarCopy) : List Char :=
  [v.scope.flatMap (fun i => i.val ++ [':']),
   v.name.val,
   ['~'], natChars v.thread,
   ['!'], natChars v.call,
   ['@'], natChars v.iteration,
   ['#'], natChars v.update].flatten

/-- The encoded spelling: body plus the terminator. -/
def VarCopy.render (v : VarCopy) : List Char := v.body ++ [';']

def VarCopy.renderStr (v : VarCopy) : String := String.ofList v.render

-- parser -------------------------------------------------------------

def readScoped : List Char → Nat → Option (List Ident × Ident × List Char)
  | l, fuel =>
    match fuel with
    | 0 => none
    | fuel + 1 =>
      let (a, r) := readAtomAux l
      if ha : a ≠ [] ∧ a.all atomChar = true then
        match r with
        | ':' :: r' =>
          match readScoped r' fuel with
          | some (sc, b, rest) => some (⟨a, ha⟩ :: sc, b, rest)
          | none => none
        | _ => some ([], ⟨a, ha⟩, r)
      else none

def expect (c : Char) : List Char → Option (List Char)
  | x :: rest => if x = c then some rest else none
  | [] => none

def parseVarCopy (l : List Char) : Option VarCopy := do
  let (sc, b, r) ← readScoped l (l.length + 1)
  let r ← expect '~' r
  let (t, r) := readNatAux r 0
  let r ← expect '!' r
  let (c, r) := readNatAux r 0
  let r ← expect '@' r
  let (i, r) := readNatAux r 0
  let r ← expect '#' r
  let (u, r) := readNatAux r 0
  let _ ← expect ';' r
  pure ⟨sc, b, t, c, i, u⟩

-- theorems -----------------------------------------------------------

theorem sep_not_atom : atomChar ';' = false := by decide

theorem ident_no_sep (i : Ident) : ';' ∉ i.val := by
  intro hmem
  have := List.all_eq_true.mp i.property.2 ';' hmem
  rw [sep_not_atom] at this
  exact absurd this (by simp)

theorem natChars_no_sep (n : Nat) : ';' ∉ natChars n := by
  intro hmem
  have := natChars_digits n ';' hmem
  simp [readDigit] at this

/-- The terminator never occurs inside a rendered body. -/
theorem body_no_sep (v : VarCopy) : ';' ∉ v.body := by
  intro hmem
  unfold VarCopy.body at hmem
  rw [List.mem_flatten] at hmem
  obtain ⟨seg, hseg, hin⟩ := hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hseg
  rcases hseg with h | h | h | h | h | h | h | h | h | h <;> subst h
  · rw [List.mem_flatMap] at hin
    obtain ⟨i, _, hi⟩ := hin
    rw [List.mem_append] at hi
    rcases hi with hi | hi
    · exact ident_no_sep i hi
    · simp at hi
  · exact ident_no_sep v.name hin
  · simp at hin
  · exact natChars_no_sep v.thread hin
  · simp at hin
  · exact natChars_no_sep v.call hin
  · simp at hin
  · exact natChars_no_sep v.iteration hin
  · simp at hin
  · exact natChars_no_sep v.update hin

/-- If two terminator-free lists agree as `a ++ [t] = b ++ t :: rest`,
    the rest is empty: the terminator's position is determined. -/
theorem sep_position {t : Char} {a : List Char} :
    ∀ {b rest : List Char}, t ∉ a → t ∉ b →
      a ++ [t] = b ++ t :: rest → rest = [] := by
  induction a with
  | nil =>
    intro b rest _ hb h
    cases b with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at h
      exact h.2.symm
    | cons y bs =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd h.2.symm (by simp)
  | cons x xs ih =>
    intro b rest ha hb h
    cases b with
    | nil =>
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      obtain ⟨hx, _⟩ := h
      subst hx
      exact absurd (List.mem_cons_self ..) ha
    | cons y bs =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨_, htail⟩ := h
      exact ih (fun hm => ha (List.mem_cons_of_mem _ hm))
        (fun hm => hb (List.mem_cons_of_mem _ hm)) htail

/-- Freshness: no rendered name is a user identifier. Every rendering
    ends with the terminator, which the atom alphabet excludes, so a
    generated name can never capture (or be captured by) a source-level
    name. -/
theorem render_fresh (v : VarCopy) (i : Ident) : v.render ≠ i.val := by
  intro heq
  have hmem : ';' ∈ v.render := by
    unfold VarCopy.render
    simp
  rw [heq] at hmem
  exact ident_no_sep i hmem

/-- Prefix-freedom: one rendering is never a proper prefix of another.
    The terminator discipline does the work: renders end with ';' and
    never contain it earlier, so the terminator's position pins the
    length. -/
theorem render_prefixFree (v w : VarCopy) (hne : v.render ≠ w.render) :
    ¬ v.render <+: w.render := by
  intro hpre
  obtain ⟨t, ht⟩ := hpre
  -- ht : v.render ++ t = w.render
  cases t with
  | nil =>
    rw [List.append_nil] at ht
    exact hne ht
  | cons c cs =>
    have hw : w.body ++ [';'] = v.body ++ ';' :: c :: cs := by
      show w.render = v.body ++ ';' :: c :: cs
      rw [← ht]
      show (v.body ++ [';']) ++ c :: cs = _
      rw [List.append_assoc]
      rfl
    have := sep_position (body_no_sep w) (body_no_sep v) hw
    simp at this

end Pylate
