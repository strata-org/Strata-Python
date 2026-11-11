/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Format

set_option autoImplicit false

/-!
# The format strings of `str.format` and `str.format_map`

CPython 3.12's reading of a format string (`Objects/stringlib/unicode_format.h`), as pure
functions: `pieces` splits it into literal text and replacement fields (`MarkupIterator_next`
and `parse_field`), `splitName` splits a field's name into its first part and its accessors
(`field_name_split` and `FieldNameIterator_next`), and `autoNumber` numbers the fields whose name
is empty and rejects a mix of automatic and manual numbering. `conversionError` is the error of an
unknown conversion. These functions run no user code. The caller does the lookups, the
conversions, the nested specs and the calls of `__format__`, in the order of the pieces.

Each error is a `ValueError` with CPython's message. CPython raises it only when it reaches it:
after the pieces before it have been formatted, and, for an accessor, after the lookups before
it. So `pieces` ends with the error where CPython's iteration stops, and `splitName` keeps an
accessor's error in the list of accessors.
-/

namespace StrataPython.Dyn.Sem.Library.FormatString

open StrataPython.Dyn.Sem.Format (decimalValue ssizeMax)

@[expose] public section

/-- One step after a field's first part: `.name` or `[key]`; a key of decimal digits is an
index. -/
inductive Accessor where
  | attr (name : String)
  | index (i : Nat)
  | key (k : String)
  deriving Repr, BEq

/-- A replacement field `{name!conversion:spec}`. -/
structure Field where
  /-- The raw field name. -/
  name : String
  /-- The conversion character after `!`, if any; never NUL. -/
  conversion : Option Char
  /-- The raw format spec after `:`. -/
  spec : String
  /-- Whether the spec holds a `{`, so that it must be formatted itself first. -/
  specNeedsExpanding : Bool
  deriving Repr, BEq

/-- A piece of a format string. -/
inductive Piece where
  | literal (s : String)
  | field (f : Field)
  /-- The `ValueError` where CPython's reading stops, with its message. -/
  | error (msg : String)
  deriving Repr, BEq

/-- `parse_field`, on the characters after a `{`: the field and the characters after its `}`, or
the error. -/
def parseField (cs : List Char) : Except String (Field × List Char) :=
  -- The name ends at `}`, `:` or `!`; a `[` skips to the next `]`.
  match nameEnd cs [] with
  | .error e => .error e
  | .ok (name, stop, rest) =>
    let name := String.ofList name
    match stop with
    | some '}' => .ok ({ name, conversion := none, spec := "", specNeedsExpanding := false }, rest)
    | some '!' =>
      match rest with
      | [] => .error "end of string while looking for conversion specifier"
      | [c] => specOf name (conversionOf c) []
      | c :: '}' :: rest' =>
        .ok ({ name, conversion := conversionOf c, spec := "", specNeedsExpanding := false }, rest')
      | c :: ':' :: rest' => specOf name (conversionOf c) rest'
      | _ :: _ :: _ => .error "expected ':' after conversion specifier"
    | some _ => specOf name none rest
    | none => .error "expected '}' before end of string"
where
  /-- CPython reads the conversion character NUL as no conversion. -/
  conversionOf (c : Char) : Option Char := if c == '\x00' then none else some c
  /-- The name: its characters, the character that ends it, and the rest. -/
  nameEnd : List Char → List Char → Except String (List Char × Option Char × List Char)
    | [], acc => .ok (acc.reverse, none, [])
    | c :: cs, acc =>
      if c == '{' then .error "unexpected '{' in field name"
      else if c == '[' then
        let inside := cs.takeWhile (· != ']')
        nameEnd (cs.drop inside.length) ((inside.reverse ++ [c]) ++ acc)
      else if c == '}' || c == ':' || c == '!' then .ok (acc.reverse, some c, cs)
      else nameEnd cs (c :: acc)
  termination_by cs => cs.length
  /-- The spec, up to the `}` that matches the field's `{`. -/
  specOf (name : String) (conversion : Option Char) (cs : List Char) :
      Except String (Field × List Char) :=
    match specEnd cs 1 [] false with
    | some (spec, expand, rest) =>
      .ok ({ name, conversion, spec := String.ofList spec, specNeedsExpanding := expand }, rest)
    | none => .error "unmatched '{' in format spec"
  specEnd : List Char → Nat → List Char → Bool → Option (List Char × Bool × List Char)
    | [], _, _, _ => none
    | c :: cs, depth, acc, expand =>
      if c == '{' then specEnd cs (depth + 1) (c :: acc) true
      else if c == '}' then
        if depth == 1 then some (acc.reverse, expand, cs) else specEnd cs (depth - 1) (c :: acc) expand
      else specEnd cs depth (c :: acc) expand

/-- The rest that `parseField.nameEnd` returns is no longer than its input, and shorter when a
character ended the name. -/
private theorem nameEnd_suffix : ∀ (cs acc : List Char) {n : List Char} {stop : Option Char}
    {rest : List Char}, parseField.nameEnd cs acc = .ok (n, stop, rest) →
    rest.length ≤ cs.length ∧ (stop.isSome → rest.length < cs.length)
  | [], acc, n, stop, rest, h => by
    rw [parseField.nameEnd] at h
    simp at h
    obtain ⟨-, rfl, rfl⟩ := h
    simp
  | c :: cs, acc, n, stop, rest, h => by
    rw [parseField.nameEnd] at h
    split at h
    · simp at h
    · split at h
      · have hrec := nameEnd_suffix _ _ h
        have hdrop : (List.drop (List.takeWhile (fun x => x != ']') cs).length cs).length ≤
            cs.length := by simp
        simp; omega
      · split at h
        · simp at h; obtain ⟨-, rfl, rfl⟩ := h; simp
        · have hrec := nameEnd_suffix _ _ h; simp; omega
termination_by cs => cs.length
decreasing_by all_goals (simp_wf; try omega)

/-- The rest that `parseField.specEnd` returns is shorter than its input: at least the closing `}`
is read. -/
private theorem specEnd_suffix : ∀ (cs : List Char) (d : Nat) (acc : List Char) (e : Bool)
    {spec : List Char} {ex : Bool} {rest : List Char},
    parseField.specEnd cs d acc e = some (spec, ex, rest) → rest.length < cs.length
  | [], _, _, _, _, _, _, h => by simp [parseField.specEnd] at h
  | c :: cs, d, acc, e, spec, ex, rest, h => by
    unfold parseField.specEnd at h
    split at h
    · have hrec := specEnd_suffix cs _ _ _ h; simp; omega
    · split at h
      · split at h
        · simp at h; obtain ⟨-, -, rfl⟩ := h; simp
        · have hrec := specEnd_suffix cs _ _ _ h; simp; omega
      · have hrec := specEnd_suffix cs _ _ _ h; simp; omega

/-- The rest that `parseField` returns after a field is shorter than its input: at least the
field's `}` is read. -/
theorem parseField_suffix (cs : List Char) {f : Field} {rest : List Char}
    (h : parseField cs = .ok (f, rest)) : rest.length < cs.length := by
  unfold parseField at h
  split at h
  · simp at h
  · rename_i name stop r hn
    have hn' := nameEnd_suffix _ _ hn
    split at h
    · simp at h; obtain ⟨-, rfl⟩ := h; exact hn'.2 rfl
    · have hlt := hn'.2 rfl
      split at h
      · simp at h
      · simp [parseField.specOf, parseField.specEnd] at h
      · simp at h; obtain ⟨-, rfl⟩ := h; simp at hlt ⊢; omega
      · unfold parseField.specOf at h
        split at h
        · rename_i heq; simp at h; obtain ⟨-, rfl⟩ := h
          have hspec := specEnd_suffix _ _ _ _ heq; simp at hlt ⊢; omega
        · simp at h
      · simp at h
    · have hlt := hn'.2 (by simp_all)
      unfold parseField.specOf at h
      split at h
      · rename_i heq; simp at h; obtain ⟨-, rfl⟩ := h
        have hspec := specEnd_suffix _ _ _ _ heq; omega
      · simp at h
    · simp at h

/-- `MarkupIterator_next`, repeated: the pieces of the format string `s`, in order; the last one
is an error if CPython's reading stops with one. As in CPython, the literal text just before an
error is dropped. -/
def pieces (s : String) : List Piece := go s.toList []
where
  go (cs : List Char) (acc : List Piece) : List Piece :=
    if cs.isEmpty then acc.reverse else
    -- The literal text, up to a brace.
    let lit := cs.takeWhile fun c => c != '{' && c != '}'
    let push (acc : List Piece) := if lit.isEmpty then acc else .literal (String.ofList lit) :: acc
    match hr : cs.drop lit.length with
    | [] => (push acc).reverse
    | '}' :: '}' :: rest' =>
      have : rest'.length < cs.length := by
        have := congrArg List.length hr; simp at this; omega
      go rest' (.literal "}" :: push acc)
    | '}' :: _ => (.error "Single '}' encountered in format string" :: acc).reverse
    | ['{'] => (.error "Single '{' encountered in format string" :: acc).reverse
    | '{' :: '{' :: rest' =>
      have : rest'.length < cs.length := by
        have := congrArg List.length hr; simp at this; omega
      go rest' (.literal "{" :: push acc)
    | _ :: rest' =>
      have : rest'.length < cs.length := by
        have := congrArg List.length hr; simp at this; omega
      match hp : parseField rest' with
      | .ok (f, rest'') =>
        have := parseField_suffix rest' hp
        go rest'' (.field f :: push acc)
      | .error e => (.error e :: acc).reverse
  termination_by cs.length

/-- CPython's `get_integer` in `unicode_format.h`: the value of a non-empty string of decimal
digits (Unicode digits too), or `none` for any other string. Its leading digits must not exceed
`PY_SSIZE_T_MAX`, so `"99999999999999999999x"` is the error, not `none`. -/
def getInteger (s : String) : Except String (Option Nat) :=
  if s.isEmpty then .ok none else go s.toList 0
where
  -- The digits are read one at a time; CPython checks before each that the value stays within
  -- `PY_SSIZE_T_MAX`, and stops at the first character that is not a digit.
  go : List Char → Nat → Except String (Option Nat)
    | [], acc => .ok (some acc)
    | c :: cs, acc =>
      match decimalValue c with
      | none => .ok none
      | some d =>
        if acc > (ssizeMax - d) / 10 then .error "Too many decimal digits in format string"
        else go cs (acc * 10 + d)

/-- `field_name_split` and `FieldNameIterator_next`: a field's name as its first part, its value
as an index (or the error of too many digits), and its accessors. An accessor that CPython can't
read is an error, which ends the list. -/
def splitName (name : String) : String × Except String (Option Nat) × List (Except String Accessor) :=
  let cs := name.toList
  let first := cs.takeWhile fun c => c != '[' && c != '.'
  let firstStr := String.ofList first
  (firstStr, getInteger firstStr, rest (cs.drop first.length))
where
  rest : List Char → List (Except String Accessor)
    | [] => []
    | '.' :: cs =>
      let n := cs.takeWhile fun c => c != '[' && c != '.'
      if n.isEmpty then [.error "Empty attribute in format string"]
      else .ok (.attr (String.ofList n)) :: rest (cs.drop n.length)
    | '[' :: cs =>
      let k := cs.takeWhile (· != ']')
      match hk : cs.drop k.length with
      | [] => [.error "Missing ']' in format string"]
      | _ :: after =>
        have : after.length < cs.length + 1 := by
          have := congrArg List.length hk; simp at this; omega
        if k.isEmpty then [.error "Empty attribute in format string"]
        else
          let ks := String.ofList k
          match getInteger ks with
          | .error e => [.error e]
          | .ok (some i) => .ok (.index i) :: rest after
          | .ok none => .ok (.key ks) :: rest after
    | _ => [.error "Only '.' or '[' may follow ']' in format field specifier"]
  termination_by cs => cs.length
  decreasing_by all_goals (simp_wf; omega)

/-- The state of CPython's automatic field numbering: nothing seen yet, automatic (with the next
number), or manual. -/
inductive AutoState where
  | init
  | auto (next : Nat)
  | manual
  deriving Repr, BEq

/-- CPython's numbering of a field whose first part is `first`, with `index` its value as an
index: the index that the field uses (none for a keyword) and the new state, or the error when the
fields mix automatic and manual numbering. -/
def autoNumber (state : AutoState) (first : String) (index : Option Nat) :
    Except String (Option Nat × AutoState) :=
  let empty := first.isEmpty
  if !(empty || index.isSome) then .ok (none, state) else
  let state := match state with
    | .init => if empty then AutoState.auto 0 else .manual
    | s => s
  match state, empty with
  | .manual, true =>
    .error "cannot switch from manual field specification to automatic field numbering"
  | .auto _, false =>
    .error "cannot switch from automatic field numbering to manual field specification"
  | .auto n, true => .ok (some n, .auto (n + 1))
  | s, _ => .ok (index, s)

/-- The error of an unknown conversion character, as `do_conversion` writes it. -/
def conversionError (c : Char) : String :=
  if 32 < c.toNat && c.toNat < 127 then s!"Unknown conversion specifier {c}"
  else s!"Unknown conversion specifier \\x{String.ofList (Nat.toDigits 16 c.toNat)}"

end

end StrataPython.Dyn.Sem.Library.FormatString
