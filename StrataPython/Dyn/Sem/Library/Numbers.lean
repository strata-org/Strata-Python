/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.FloatText
public import StrataPython.Dyn.Sem.Format
public import StrataPython.Dyn.Sem.Library.Unicode

set_option autoImplicit false

/-!
# Numbers from strings

`int(s, base)` and `float(s)` of a `str`, as CPython 3.12 reads it: `intFromStr` follows
`PyLong_FromUnicodeObject` and `PyLong_FromString`, and `floatFromStr` follows
`PyFloat_FromString`, `_Py_string_to_number_with_underscores` and `_Py_dg_strtod`. Both first map
Unicode whitespace to a space and Unicode decimal digits to ASCII digits
(`_PyUnicode_TransformDecimalAndSpaceToASCII`). The nearest binary64 value of a decimal comes
from `StrataDyn/FloatText.lean`'s `ofDigits`. The model assumes CPython's default limit on
the digits of a str-to-int conversion, that is, that neither `sys.set_int_max_str_digits`, nor
the environment variable `PYTHONINTMAXSTRDIGITS`, nor the option `-X int_max_str_digits` changes
it.
-/

namespace StrataPython.Dyn.Sem.Library.Numbers

open StrataPython.Dyn.Sem
open StrataPython.Dyn.Sem.Format (Failure valueError decimalValue)

@[expose] public section

/-! ## The ASCII form of a string -/

/-- CPython's `_PyUnicode_TransformDecimalAndSpaceToASCII`. A string of ASCII characters stays
as it is. In any other string, a character below `0x7f` stays, a whitespace character becomes a
space, a decimal digit becomes its ASCII digit, and any other character becomes `?` and ends
the string. -/
def toAscii (cs : List Char) : List Char :=
  if cs.all (·.toNat < 0x80) then cs else go cs #[]
where
  go : List Char → Array Char → List Char
    | [], acc => acc.toList
    | c :: cs, acc =>
      if c.toNat < 0x7f then go cs (acc.push c)
      else if Library.Unicode.isSpace c then go cs (acc.push ' ')
      else match decimalValue c with
        | some d => go cs (acc.push (Char.ofNat ('0'.toNat + d)))
        | none => (acc.push '?').toList

/-- CPython's `Py_ISSPACE`: the ASCII whitespace characters. -/
def isAsciiSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\x0b' || c == '\x0c' || c == '\r'

/-- `cs` without its leading ASCII whitespace. -/
def dropSpace (cs : List Char) : List Char := cs.dropWhile isAsciiSpace

/-- `cs` without its trailing ASCII whitespace. -/
def dropSpaceRight (cs : List Char) : List Char := (dropSpace cs.reverse).reverse

/-! ## `int` -/

/-- CPython's `_PyLong_DigitValue`: the value of a digit in the bases up to 36, and 37 for any
other character. -/
def digitValue (c : Char) : Nat :=
  if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'z' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'Z' then c.toNat - 'A'.toNat + 10
  else 37

/-- The number of digits from which CPython checks its limit on the digits of a str-to-int
conversion (`_PY_LONG_MAX_STR_DIGITS_THRESHOLD`). The limit is `Format.intMaxStrDigits`, and it
counts the digits in any base that is not a power of two. -/
def maxStrDigitsThreshold : Nat := 640

/-- How `PyLong_FromString` ended on an ASCII string. -/
inductive IntRead where
  | ok (n : Int)
  /-- A syntax error: `ValueError: invalid literal for int() …`. -/
  | invalid
  /-- More digits than the limit allows (in a base that is not a power of two), with their
  number. -/
  | tooManyDigits (digits : Nat)
  deriving Repr, BEq

/-- CPython's `long_from_string_base`. `cs` must hold digits of `base` and single underscores
between them, and then only whitespace. It returns the digits' values, or `none` for a syntax
error. -/
def digitsOf (base : Nat) (cs : List Char) : Option (Array Nat) :=
  match cs with
  | '_' :: _ => none
  | _ => go cs #[] false
where
  go : List Char → Array Nat → Bool → Option (Array Nat)
    | c :: rest, ds, prevUnderscore =>
      if c == '_' then
        if prevUnderscore then none else go rest ds true
      else if digitValue c < base then go rest (ds.push (digitValue c)) false
      else if prevUnderscore || ds.isEmpty then none
      else if (dropSpace (c :: rest)).isEmpty then some ds else none
    | [], ds, prevUnderscore => if prevUnderscore || ds.isEmpty then none else some ds

/-- CPython's `PyLong_FromString` on the ASCII characters `cs`, for a base of 0 or 2 to 36. -/
def readInt (cs : List Char) (base : Nat) : IntRead :=
  let cs := dropSpace cs
  let (neg, cs) := match cs with
    | '+' :: rest => (false, rest)
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  -- Base 0 reads the base from the prefix; a leading zero without one allows only zeros.
  let (base, onlyZero) : Nat × Bool := if base != 0 then (base, false) else match cs with
    | '0' :: c :: _ =>
      if c == 'x' || c == 'X' then (16, false) else if c == 'o' || c == 'O' then (8, false)
      else if c == 'b' || c == 'B' then (2, false) else (10, true)
    | '0' :: _ => (10, true)
    | _ => (10, false)
  let cs := match cs with
    | '0' :: c :: rest =>
      if (base == 16 && (c == 'x' || c == 'X')) || (base == 8 && (c == 'o' || c == 'O'))
          || (base == 2 && (c == 'b' || c == 'B')) then
        -- One underscore may follow the prefix.
        match rest with | '_' :: rest' => rest' | _ => rest
      else cs
    | _ => cs
  match digitsOf base cs with
  | none => .invalid
  | some ds =>
    let binary := base &&& (base - 1) == 0
    if !binary && ds.size > maxStrDigitsThreshold && ds.size > Format.intMaxStrDigits then
      .tooManyDigits ds.size
    else
      let n := Strata.Dyn.FloatText.digitsValue base ds
      if onlyZero && n != 0 then .invalid else .ok (if neg then -(n : Int) else n)

/-- `repr(s)` as `%.200R` writes it into a message: at most 200 characters. -/
def repr200 (s : String) : String := String.ofList ((Format.strRepr s).toList.take 200)

/-- `int(s, base)` for a `str` `s` and a base of 0 or 2 to 36 (`PyLong_FromUnicodeObject`). -/
def intFromStr (s : String) (base : Nat) : Except Failure Int :=
  -- `PyLong_FromString` reads up to a NUL. With one in the string, the reading is a syntax error
  -- unless it stopped at the limit on digits first.
  let ascii := toAscii s.toList
  let read := readInt (ascii.takeWhile (· != '\x00')) base
  let read := if ascii.contains '\x00' && !(read matches .tooManyDigits _) then .invalid else read
  match read with
  | .ok n => .ok n
  | .invalid => .error (valueError s!"invalid literal for int() with base {base}: {repr200 s}")
  | .tooManyDigits d =>
    .error (valueError s!"Exceeds the limit ({Format.intMaxStrDigits} digits) for integer string \
      conversion: value has {d} digits; use sys.set_int_max_str_digits() to increase the limit")

/-! ## `float` -/

/-- The bits of CPython's NaN (`Py_NAN`, a quiet NaN with the sign bit clear). -/
def nanBits : UInt64 := 0x7FF8000000000000

/-- The bits of positive infinity. -/
def infBits : UInt64 := 0x7FF0000000000000

/-- `_Py_string_to_number_with_underscores`'s rule: every underscore of `cs` comes after a digit
and before a digit; then `cs` without them, or `none`. -/
def dropUnderscores (cs : List Char) : Option (List Char) := go cs '\x00' #[]
where
  go : List Char → Char → Array Char → Option (List Char)
    | [], prev, acc => if prev == '_' then none else some acc.toList
    | c :: rest, prev, acc =>
      if c == '_' then
        if prev.isDigit then go rest c acc else none
      else if prev == '_' && !c.isDigit then none
      else go rest c (acc.push c)

/-- Whether `cs` starts with `word`, ignoring the case of ASCII letters. -/
def startsWithCi (cs : List Char) (word : String) : Bool :=
  word.length ≤ cs.length && (cs.take word.length).map Char.toLower == word.toList

/-- `_Py_parse_inf_or_nan`: `inf`, `infinity` or `nan` in any case, after an optional sign; the
bits and the rest of `cs`. -/
def readInfOrNan (cs : List Char) : Option (UInt64 × List Char) :=
  let (neg, rest) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _ => (false, cs)
  let sign : UInt64 := if neg then 0x8000000000000000 else 0
  if startsWithCi rest "infinity" then some (infBits ||| sign, rest.drop 8)
  else if startsWithCi rest "inf" then some (infBits ||| sign, rest.drop 3)
  else if startsWithCi rest "nan" then some (nanBits ||| sign, rest.drop 3)
  else none

/-- `_Py_dg_strtod`'s `MAX_ABS_EXP`: a larger exponent reads as this one. Since a number has at
most `maxDigits` digits, the result (zero or infinity) stays the same. -/
def maxAbsExp : Nat := 1100000000

/-- `_Py_dg_strtod`'s `MAX_DIGITS`: a number with more significant digits, or more digits after
the point, is a syntax error. -/
def maxDigits : Nat := 1000000000

/-- `_Py_dg_strtod`'s reading of `cs`: an optional sign, digits with at most one point (at least
one digit), and an optional exponent; the bits of the nearest binary64 value and the rest of
`cs`, or `none` if no number starts `cs`. -/
def readDecimal (cs : List Char) (limit : Nat := maxDigits) : Option (UInt64 × List Char) :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _ => (false, cs)
  let intDigits := cs.takeWhile Char.isDigit
  let cs := cs.drop intDigits.length
  let (fracDigits, cs) := match cs with
    | '.' :: r => (r.takeWhile Char.isDigit, r.drop (r.takeWhile Char.isDigit).length)
    | _ => ([], cs)
  if intDigits.isEmpty && fracDigits.isEmpty then none else
  -- The exponent is read only if at least one digit follows `e` and its sign.
  let (exp, cs) : Int × List Char := match cs with
    | e :: r =>
      if e == 'e' || e == 'E' then
        let (eneg, r') := match r with
          | '-' :: r'' => (true, r'')
          | '+' :: r'' => (false, r'')
          | _ => (false, r)
        let eds := r'.takeWhile Char.isDigit
        if eds.isEmpty then (0, cs) else
          let mag := ((eds.dropWhile (· == '0')).take 10).foldl
            (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0
          let mag : Nat := if (eds.dropWhile (· == '0')).length > 9 then maxAbsExp
            else min mag maxAbsExp
          ((if eneg then -(mag : Int) else mag), r'.drop eds.length)
      else (0, cs)
    | [] => (0, cs)
  let digits := (intDigits ++ fracDigits).map (fun d => d.toNat - '0'.toNat)
  if (digits.dropWhile (· == 0)).length > limit || fracDigits.length > limit then none
  else
  let bits := (Strata.Dyn.FloatText.ofDigits neg digits (exp - fracDigits.length)).toBits
  some (bits, cs)

/-- `float(s)` for a `str` `s` (`PyFloat_FromString`): the bits of the result. -/
def floatFromStr (s : String) : Except Failure UInt64 :=
  let error := valueError s!"could not convert string to float: {Format.strRepr s}"
  let cs := s.toList
  -- The ASCII form ends at a NUL for CPython's C functions, so a string with one is an error.
  if cs.contains '\x00' then .error error else
  let ascii := toAscii cs
  match (if ascii.contains '_' then dropUnderscores ascii else some ascii) with
  | none => .error error
  | some ascii =>
    let body := dropSpaceRight (dropSpace ascii)
    if body.isEmpty then .error error else
    match (readDecimal body).orElse fun _ => readInfOrNan body with
    | some (bits, []) => .ok bits
    | _ => .error error

end

end StrataPython.Dyn.Sem.Library.Numbers
