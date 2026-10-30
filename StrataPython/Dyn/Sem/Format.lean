/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDyn.FloatText
public import StrataPython.Dyn.Sem.Unicode

set_option autoImplicit false

/-!
# The formatting of ints, floats and strs

CPython 3.12's `repr` of an `int`, a `float` and a `str`, and the `__format__` methods of `int`,
`float` and `str` (`Objects/longobject.c`, `Objects/floatobject.c`, `Python/pystrtod.c` and
`Python/formatter_unicode.c`).  Each function gives the string, or the exception that CPython
raises, or says that the case is not modelled.

The digits of a float come from exact arithmetic on its mantissa and exponent: the shortest digits
that read back as the float for `repr` (`FloatText.shortest`), and otherwise the digits rounded
correctly, ties to even, as the modes 2 and 3 of `_Py_dg_dtoa` give them.

Widths count code points, as CPython's do.  Two settings are CPython's defaults:
* the limit on the digits of an int-to-str conversion is 4300 (`sys.set_int_max_str_digits`);
* the presentation type `'n'` uses the C locale: the point is `'.'` and digits are not grouped.
  CPython keeps that locale for `LC_NUMERIC` unless the program calls `locale.setlocale`.

Key theorem: `digitsPad_eq_digitsPadFast`, which swaps a fast conversion to a power-of-two base
in for the simple one.  It is here, not in a Props file, because a `@[csimp]` lemma must come
before the code that uses it.

Two kinds of results are not modelled:
* a `str` that holds a lone surrogate, which a Lean `String` can't hold: the format code `'c'` on a
  code point from `0xD800` to `0xDFFF`;
* a result of the format functions longer than `2 ^ 24` characters, for which CPython raises
  `MemoryError` if the machine doesn't have the memory.
-/

namespace StrataPython.Dyn.Sem.Format

open Strata.Dyn

@[expose] public section

/-- Why a function of the semantics gives no result. -/
inductive Failure where
  /-- CPython raises the exception class `cls` with the message `msg`. -/
  | raise (cls msg : String)
  /-- A case that this port doesn't model; `what` says which. -/
  | notModelled (what : String)
deriving Repr, BEq, DecidableEq, Inhabited

/-- A `ValueError` with the message `msg`. -/
def valueError (msg : String) : Failure := .raise "ValueError" msg

/-! ## Long results -/

/-- The longest result that this port builds.  CPython raises `MemoryError` for a result too long
for the machine's memory, so a longer result is not modelled. -/
def maxLength : Nat := 2 ^ 24

/-- The result of a case whose string would be longer than `maxLength`. -/
def tooLong : Failure := .notModelled "a result longer than 2 ^ 24 characters"

/-! ## `repr` of an int -/

/-- CPython's default limit on the decimal digits of an int-to-str conversion
(`sys.get_int_max_str_digits()`). -/
def intMaxStrDigits : Nat := 4300

/-- The `ValueError` of an int-to-str conversion over the limit on digits. -/
def maxStrDigitsError : Failure :=
  valueError s!"Exceeds the limit ({intMaxStrDigits} digits) for integer string conversion; \
    use sys.set_int_max_str_digits() to increase the limit"

/-- `repr(n)` and `str(n)` for an int `n`: its decimal digits, or the `ValueError` when it has
more than 4300 of them. -/
def intRepr (n : Int) : Except Failure String :=
  if n.natAbs < 10 ^ intMaxStrDigits then .ok (toString n) else .error maxStrDigitsError

/-! ## Binary64 values -/

/-- A binary64 value, by its parts. -/
inductive Parts where
  /-- A NaN, of any sign and payload. -/
  | nan
  /-- An infinity, negative if `neg`. -/
  | inf (neg : Bool)
  /-- `±mantissa * 2 ^ exponent`, negative if `neg`; the mantissa is `0` for a zero. -/
  | finite (neg : Bool) (mantissa : Nat) (exponent : Int)

/-- The parts of the binary64 value with the bits `bits`. -/
def parts (bits : UInt64) : Parts :=
  let b := bits.toNat
  let neg := b >>> 63 == 1
  let biased := (b >>> 52) % 2048
  let frac := b % 2 ^ 52
  if biased == 2047 then (if frac == 0 then .inf neg else .nan)
  else if biased == 0 then .finite neg frac (-1074)
  else .finite neg (frac + 2 ^ 52) ((biased : Int) - 1075)

/-- The bits of the binary64 value nearest `n * 2 ^ x`, ties to even, negative if `neg`; an
infinity if the magnitude rounds to `2 ^ 1024` or more.  A magnitude of at least `2 ^ 1024`, or
one below `2 ^ -1075`, is decided from the bit length of `n` first, without a power.  Otherwise
it computes a power `2 ^ k` with `k ≤ 52`, or with `k` at most the bit length of `n`.  Lean's
runtime aborts on `2 ^ k` for `k ≥ 2 ^ 32`, so a caller passes an `n` with fewer than `2 ^ 32`
bits, or `x = 0`. -/
def roundToBits (neg : Bool) (n : Nat) (x : Int) : UInt64 :=
  let mag : Nat :=
    if n == 0 then 0
    else if (n.log2 : Int) + x ≥ 1024 then 0x7FF0000000000000
    else if (n.log2 : Int) + x ≤ -1076 then 0
    else
      -- `e` is the exponent of the last bit that the result keeps.
      let e := max ((n.log2 : Int) + x - 52) (-1074)
      let s := x - e
      let q := if 0 ≤ s then n * 2 ^ s.toNat else FloatText.roundDiv n (2 ^ s.natAbs)
      -- Rounding up may carry into the next binade.
      let (q, e) := if q == 2 ^ 53 then (2 ^ 52, e + 1) else (q, e)
      if q < 2 ^ 52 then q
      else if e + 1075 ≥ 2047 then 0x7FF0000000000000
      else (e + 1075).toNat * 2 ^ 52 + (q - 2 ^ 52)
  (if neg then mag + 2 ^ 63 else mag).toUInt64

/-- `float(n)` for an int `n` (`PyLong_AsDouble`): the nearest binary64 value, ties to even, or the
`OverflowError` when that is infinite. -/
def intToFloat (n : Int) : Except Failure UInt64 :=
  let bits := roundToBits (n < 0) n.natAbs 0
  if bits &&& 0x7FFFFFFFFFFFFFFF == 0x7FF0000000000000 then
    .error (.raise "OverflowError" "int too large to convert to float")
  else .ok bits

/-- `x * 100` for the binary64 value `x` with the bits `bits`, rounded as binary64 arithmetic
rounds it: the nearest value, ties to even.  An infinity or a NaN stays as it is. -/
def mul100 (bits : UInt64) : UInt64 :=
  match parts bits with
  | .finite neg m x => roundToBits neg (m * 100) x
  | _ => bits

/-! ## Decimal digits of a float -/

/-- The decimal digits of `n`, at least one. -/
def decDigits (n : Nat) : List Char := Nat.toDigits 10 n

/-- `ds` without its trailing zeros. -/
def dropTrailingZeros (ds : List Char) : List Char :=
  (ds.reverse.dropWhile (· == '0')).reverse

/-- The `k` with `10 ^ k ≤ n / d < 10 ^ (k + 1)`, for positive `n` and `d`. -/
def floorLog10 (n d : Nat) : Int :=
  -- `n / d` is above `10 ^ (p - 1)` and below `10 ^ (p + 1)`.
  let p : Int := (FloatText.digits n : Int) - FloatText.digits d
  let atLeast : Bool := if 0 ≤ p then n ≥ d * 10 ^ p.toNat else n * 10 ^ p.natAbs ≥ d
  if atLeast then p else p - 1

/-- The digits of `_Py_dg_dtoa` for a finite value: the significant digits, without trailing
zeros, and the position `decpt` of the decimal point, so that the value is
`0.d₁d₂… * 10 ^ decpt`. -/
structure Digits where
  /-- The significant digits. -/
  digits : List Char
  /-- The position of the decimal point. -/
  decpt : Int

/-- The modes of `_Py_dg_dtoa` that CPython uses. -/
inductive Mode where
  /-- Mode 0: the shortest digits that read back as the value. -/
  | shortest
  /-- Mode 2: `n` significant digits, at least one. -/
  | significant (n : Nat)
  /-- Mode 3: `n` digits past the decimal point. -/
  | fixed (n : Nat)

/-- `_Py_dg_dtoa`'s digits of the finite value `±m * 2 ^ x` whose bits are `bits`.  A zero gives
the digit `0` with `decpt = 1`; mode 3 gives no digits, with `decpt = -n`, for a value that rounds
to zero. -/
def dtoa (bits : UInt64) (m : Nat) (x : Int) (mode : Mode) : Digits :=
  if m == 0 then ⟨['0'], 1⟩
  else
    -- The magnitude is `n / d`.
    let (n, d) : Nat × Nat := if 0 ≤ x then (m * 2 ^ x.toNat, 1) else (m, 2 ^ x.natAbs)
    -- A binary64 value has at most 767 significant digits and at most 1074 digits past the
    -- point, so a precision over 1100 gives the same digits as 1100: the exact ones.
    match mode with
    | .shortest =>
      match FloatText.shortest (Float.ofBits bits) with
      | some dec =>
        let ds := decDigits dec.mantissa
        ⟨ds, ds.length + dec.exponent⟩
      | none => ⟨['0'], 1⟩
    | .significant p =>
      let p := min (max p 1) 1100
      let k := floorLog10 n d
      let s : Int := (p : Int) - 1 - k
      let q := if 0 ≤ s then FloatText.roundDiv (n * 10 ^ s.toNat) d
        else FloatText.roundDiv n (d * 10 ^ s.natAbs)
      let (q, k) := if q == 10 ^ p then (10 ^ (p - 1), k + 1) else (q, k)
      ⟨dropTrailingZeros (decDigits q), k + 1⟩
    | .fixed p =>
      let p := min p 1100
      let q := FloatText.roundDiv (n * 10 ^ p) d
      if q == 0 then ⟨[], -(p : Int)⟩
      else
        let ds := decDigits q
        ⟨dropTrailingZeros ds, (ds.length : Int) - p⟩

/-- `n` zeros, none if `n` is negative. -/
def zeros (n : Int) : List Char := List.replicate n.toNat '0'

/-- The exponent `e` as `sprintf("%+.02d")` writes it: its sign and at least two digits. -/
def expDigits (e : Int) : List Char :=
  let ds := decDigits e.natAbs
  (if e < 0 then '-' else '+') :: (if ds.length < 2 then '0' :: ds else ds)

/-- CPython's `format_float_short`: the binary64 value with the bits `bits` in the format `code`,
one of `'e'` (`precision` significant digits), `'f'` (`precision` digits past the point), `'g'`
(`precision` significant digits, at least one, without trailing zeros) and `'r'` (`repr`).
`addDot0` adds `.0` to an integer without an exponent, `alt` keeps trailing zeros and the
point, `noNegZero` drops the sign of a value that shows as zero, and `upper` writes `E`, `INF`
and `NAN`. -/
def formatFloatShort (bits : UInt64) (code : Char) (precision : Nat)
    (addDot0 alt noNegZero upper : Bool) : String :=
  match parts bits with
  | .nan => if upper then "NAN" else "nan"
  | .inf neg => (if neg then "-" else "") ++ (if upper then "INF" else "inf")
  | .finite neg m x =>
    let mode := match code with
      | 'e' | 'g' => Mode.significant precision
      | 'f' => .fixed precision
      | _ => .shortest
    let ⟨ds, decpt⟩ := dtoa bits m x mode
    let len : Int := ds.length
    let neg := neg && !(noNegZero && (ds.isEmpty || ds == ['0']))
    -- The output is the slice `[vstart, vend)` of the digits padded with zeros on both sides,
    -- with the point after the first `decpt` digits.
    let (useExp, vend) : Bool × Int := match code with
      | 'e' => (true, precision)
      | 'f' => (false, decpt + precision)
      | 'g' =>
        (decpt ≤ -4 || decpt > (if addDot0 then (precision : Int) - 1 else precision),
          if alt then precision else len)
      | _ => (decpt ≤ -4 || decpt > 16, len)
    let exp := decpt - 1
    let decpt := if useExp then 1 else decpt
    let vstart : Int := if decpt ≤ 0 then decpt - 1 else 0
    let vend := if !useExp && addDot0 then max vend (decpt + 1) else max vend decpt
    let body : List Char :=
      (if decpt ≤ 0 then zeros (decpt - vstart) ++ ['.'] ++ zeros (-decpt) else zeros (-vstart)) ++
      (if 0 < decpt && decpt ≤ len then ds.take decpt.toNat ++ ['.'] ++ ds.drop decpt.toNat
        else ds) ++
      (if len < decpt then zeros (decpt - len) ++ ['.'] ++ zeros (vend - decpt)
        else zeros (vend - len))
    let body := if body.getLast? == some '.' && !alt then body.dropLast else body
    let expPart := if useExp then (if upper then 'E' else 'e') :: expDigits exp else []
    String.ofList ((if neg then ['-'] else []) ++ body ++ expPart)

/-- CPython's `PyOS_double_to_string` for the format codes `e E f F g G r`: the `ValueError` for a
precision over `INT_MAX - 1024`, or `format_float_short`'s string, where `'e'` counts the digits
past the point and `'g'` reads a precision of `0` as `1`.  A `'g'` without `alt` drops trailing
zeros, and for a precision over 309 it uses an exponent only for a value below `1e-4`, whatever
the precision.  So it reads a precision over 1100 as 1100, which gives the same string.  This
assumes that the process has the memory that CPython reserves for the precision (one byte per
digit, before it writes any): with a limited address space, a huge precision makes CPython raise
`MemoryError`.  Any other precision of at least `maxLength` gives a result longer than
`maxLength`, which is not modelled. -/
def doubleToString (bits : UInt64) (code : Char) (precision : Nat) (addDot0 alt noNegZero : Bool) :
    Except Failure String :=
  if precision > 2147483647 - 1024 then .error (valueError "precision too big")
  else
    let upper := code == 'E' || code == 'F' || code == 'G'
    let code := code.toLower
    let precision := if code == 'g' && !alt then min precision 1100 else precision
    if precision ≥ maxLength then .error tooLong
    else
      let precision := match code with
        | 'e' => precision + 1
        | 'g' => max precision 1
        | _ => precision
      .ok (formatFloatShort bits code precision addDot0 alt noNegZero upper)

/-- `repr(x)` and `str(x)` for the float `x` with the bits `bits` (`float_repr`): the shortest
digits that read back as `x`, with an exponent below `1e-4` and from `1e16` on, and `.0` added to
an integer. -/
def floatRepr (bits : UInt64) : String := formatFloatShort bits 'r' 0 true false false false

/-- The `width` lowest hexadecimal digits of `n`, the highest first, in lower case. -/
def hexDigits (n width : Nat) : List Char :=
  (List.range width).reverse.map fun i => Nat.digitChar (n / 16 ^ i % 16)

/-- `repr(s)` for the str `s` (`unicode_repr`).  The quote is `'`, or `"` when `s` holds a `'`
and no `"`.  A backslash, the quote, `\t`, `\n` and `\r` are escaped; any other character that
is not printable (`Unicode.isPrintable`) becomes `\xhh`, `\uhhhh` or `\Uhhhhhhhh`.  `strRepr` has no
length limit: its result is at most ten times as long as `s`, plus the two quotes, and it assumes
that CPython has the memory for it. -/
def strRepr (s : String) : String :=
  let cs := s.toList
  let quote := if cs.contains '\'' && !cs.contains '"' then '"' else '\''
  let escape (c : Char) : List Char :=
    if c == quote || c == '\\' then ['\\', c]
    else if c == '\t' then ['\\', 't']
    else if c == '\n' then ['\\', 'n']
    else if c == '\r' then ['\\', 'r']
    else if Unicode.isPrintable c then [c]
    else if c.toNat < 0x100 then '\\' :: 'x' :: hexDigits c.toNat 2
    else if c.toNat < 0x10000 then '\\' :: 'u' :: hexDigits c.toNat 4
    else '\\' :: 'U' :: hexDigits c.toNat 8
  String.ofList (quote :: cs.flatMap escape ++ [quote])

/-! ## Format specs -/

/-- The thousands separators of a format spec (CPython's `LocaleType`, without the current
locale). -/
inductive Separators where
  /-- No separators. -/
  | none
  /-- `','` between groups of 3 digits. -/
  | comma
  /-- `'_'` between groups of 3 digits. -/
  | underscore
  /-- `'_'` between groups of 4 digits, for the types `b o x X`. -/
  | underscoreFour
deriving Repr, BEq, DecidableEq, Inhabited

/-- A parsed format spec, `[[fill]align][sign][z][#][0][width][grouping][.precision][type]`
(CPython's `InternalFormatSpec`). -/
structure Spec where
  /-- The fill character. -/
  fill : Char
  /-- The alignment: `'<'`, `'>'`, `'='` or `'^'`. -/
  align : Char
  /-- `#`: the alternate form. -/
  alternate : Bool
  /-- `z`: a negative zero shows as a zero. -/
  noNegZero : Bool
  /-- `'+'`, `'-'` or `' '`, if the spec gives a sign. -/
  sign : Option Char
  /-- The minimum width, if the spec gives one. -/
  width : Option Nat
  /-- The thousands separators. -/
  separators : Separators
  /-- The precision, if the spec gives one. -/
  precision : Option Nat
  /-- The presentation type; `'\x00'` when there is none (the default type of a float). -/
  type : Char
deriving Repr, BEq, DecidableEq, Inhabited

/-- The value of `c` as a decimal digit, if it is one (`Py_UNICODE_TODECIMAL`). -/
def decimalValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else (Unicode.decimalZeros.find? fun z => z ≤ c.toNat && c.toNat < z + 10).map (c.toNat - ·)

/-- CPython's `PY_SSIZE_T_MAX` on a 64-bit build. -/
def ssizeMax : Nat := 2 ^ 63 - 1

/-- CPython's `get_integer`: reads the decimal digits at the start of `cs`, going on from `count`
digits already read, whose value is `acc`.  It gives the value of all the digits, or `ssizeMax + 1` if that is larger, the number
of digits, and the characters after them. -/
def readInteger : List Char → Nat → Nat → Nat × Nat × List Char
  | [], acc, count => (acc, count, [])
  | c :: cs, acc, count =>
    match decimalValue c with
    | some v => readInteger cs (min (acc * 10 + v) (ssizeMax + 1)) (count + 1)
    | none => (acc, count, c :: cs)

/-- Whether `c` is an alignment. -/
def isAlign (c : Char) : Bool := c == '<' || c == '>' || c == '=' || c == '^'

/-- Whether `c` is a sign option. -/
def isSign (c : Char) : Bool := c == ' ' || c == '+' || c == '-'

/-- A character as CPython's messages show a presentation type: itself from `'!'` to `'\x7f'`,
otherwise `\x` and its code in hexadecimal. -/
def showType (c : Char) : String :=
  if 32 < c.toNat && c.toNat < 128 then c.toString
  else "\\x" ++ String.ofList (Nat.toDigits 16 c.toNat)

/-- The characters of `cs` that fit in `budget` bytes of UTF-8, and whether the budget ends inside
a character. -/
def takeBytes : List Char → Nat → List Char × Bool
  | [], _ => ([], false)
  | c :: cs, budget =>
    if c.utf8Size ≤ budget then
      let (kept, cut) := takeBytes cs (budget - c.utf8Size)
      (c :: kept, cut)
    else ([], budget > 0)

/-- A type name as `%.200s` writes it into a message: at most 200 bytes of its UTF-8, and a
replacement character for a character that the limit cuts. -/
def cTypeName (name : String) : String :=
  let (kept, cut) := takeBytes name.toList 200
  String.ofList (kept ++ (if cut then ['\uFFFD'] else []))

/-- The `ValueError` for both `','` and `'_'`. -/
def commaAndUnderscore : Failure := valueError "Cannot specify both ',' and '_'."

/-- The `ValueError` for a width or a precision over `PY_SSIZE_T_MAX`. -/
def tooManyDigits : Failure := valueError "Too many decimal digits in format string"

/-- The `ValueError` for the separators `seps` with the presentation type `t`. -/
def separatorError (seps : Separators) (t : Char) : Failure :=
  let s := if seps == .comma then ',' else '_'
  valueError s!"Cannot specify '{s}' with '{showType t}'."

/-- CPython's `parse_internal_render_format_spec`: the format spec `spec` of an object of the type
`typeName`, whose default type is `defaultType` and default alignment `defaultAlign`, or CPython's
`ValueError`.  It checks the separators against the type, but not the type against the object. -/
def parseSpec (spec : String) (typeName : String) (defaultType defaultAlign : Char) :
    Except Failure Spec := do
  let cs := spec.toList
  let (fill, align, fillGiven, alignGiven, cs) : Char × Char × Bool × Bool × List Char :=
    match cs with
    | f :: a :: rest =>
      if isAlign a then (f, a, true, true, rest)
      else if isAlign f then (' ', f, false, true, a :: rest)
      else (' ', defaultAlign, false, false, cs)
    | [a] => if isAlign a then (' ', a, false, true, []) else (' ', defaultAlign, false, false, cs)
    | [] => (' ', defaultAlign, false, false, [])
  let (sign, cs) := match cs with
    | c :: rest => if isSign c then (some c, rest) else (none, cs)
    | [] => (none, [])
  let (noNegZero, cs) := match cs with
    | 'z' :: rest => (true, rest)
    | _ => (false, cs)
  let (alternate, cs) := match cs with
    | '#' :: rest => (true, rest)
    | _ => (false, cs)
  -- A `0` before the width, without a fill, pads with zeros, after the sign for a number.
  let (fill, align, cs) := match cs with
    | '0' :: rest =>
      if fillGiven then (fill, align, cs)
      else ('0', if !alignGiven && defaultAlign == '>' then '=' else align, rest)
    | _ => (fill, align, cs)
  let (width, count, cs) := readInteger cs 0 0
  if width > ssizeMax then throw tooManyDigits
  let width := if count == 0 then none else some width
  let (seps, cs) := match cs with
    | ',' :: rest => (Separators.comma, rest)
    | _ => (.none, cs)
  let (seps, cs) ← match cs with
    | '_' :: rest => if seps != .none then throw commaAndUnderscore else pure (.underscore, rest)
    | _ => pure (seps, cs)
  if seps == .underscore && cs.head? == some ',' then throw commaAndUnderscore
  let (precision, cs) ← match cs with
    | '.' :: rest =>
      let (p, count, rest) := readInteger rest 0 0
      if p > ssizeMax then throw tooManyDigits
      if count == 0 then throw (valueError "Format specifier missing precision")
      pure (some p, rest)
    | _ => pure (none, cs)
  let type ← match cs with
    | [] => pure defaultType
    | [t] => pure t
    | _ => throw (valueError
        s!"Invalid format specifier '{spec}' for object of type '{cTypeName typeName}'")
  let seps ← if seps == .none then pure seps
    else match type with
      | 'd' | 'e' | 'f' | 'g' | 'E' | 'G' | '%' | 'F' | '\x00' => pure seps
      | 'b' | 'o' | 'x' | 'X' =>
        if seps == .underscore then pure .underscoreFour else throw (separatorError seps type)
      | _ => throw (separatorError seps type)
  pure { fill, align, alternate, noNegZero, sign, width, separators := seps, precision, type }

/-- The `ValueError` for the presentation type `t` on an object of the type `typeName`. -/
def unknownType (t : Char) (typeName : String) : Failure :=
  valueError s!"Unknown format code '{showType t}' for object of type '{cTypeName typeName}'"

/-! ## Laying out a number -/

/-- How the digits before the point are grouped. -/
inductive Grouping where
  /-- Not grouped. -/
  | none
  /-- In groups of `size` digits, from the right, with `sep` between them. -/
  | every (size : Nat) (sep : Char)

/-- The grouping that the separators `seps` ask for. -/
def Separators.grouping : Separators → Grouping
  | .none => .none
  | .comma => .every 3 ','
  | .underscore => .every 3 '_'
  | .underscoreFour => .every 4 '_'

/-- The length of the next group of `_PyUnicode_InsertThousandsGrouping`, with groups of `size`,
`n` digits still to place and the width `w` still to fill: at least one if `size` is not zero. -/
def groupLen (size n w : Nat) : Nat := min size (max (max n w) 1)

/-- A group is at least one character long when the group size `size` is not zero. -/
private theorem one_le_groupLen (size n w : Nat) (h : ¬size = 0) : 1 ≤ groupLen size n w := by
  simp only [groupLen]
  omega

/-- The groups of `_PyUnicode_InsertThousandsGrouping`, right to left and each reversed: `rd`
holds the `n` digits still to place, the last one first, and `minWidth` the width still to fill.
A group takes up to `size` digits, then zeros once the digits run out; every group but the first
one (the rightmost) has `sep` on its right. -/
def groupRev (size : Nat) (sep : Char) (rd : List Char) (n minWidth : Nat) (first : Bool) :
    List Char :=
  if h : size = 0 then []
  else
    let len := groupLen size n minWidth
    let group := (if first then [] else [sep]) ++ rd.take len ++ List.replicate (len - n) '0'
    if _ : n ≤ len ∧ minWidth ≤ len then group
    else
      have hlen : 1 ≤ groupLen size n minWidth := by exact one_le_groupLen size n minWidth h
      group ++ groupRev size sep (rd.drop len) (n - len) (minWidth - len - 1) false
termination_by n + minWidth

/-- `_PyUnicode_InsertThousandsGrouping`: the digits `ds` with the separators of `g`, and zeros on
their left, grouped too, until they are at least `minWidth` long. -/
def insertGrouping (g : Grouping) (ds : List Char) (minWidth : Nat) : List Char :=
  match g with
  | .every (size + 1) sep => (groupRev (size + 1) sep ds.reverse ds.length minWidth true).reverse
  | _ => List.replicate (minWidth - ds.length) '0' ++ ds

/-- CPython's `calc_number_widths` and `fill_number`: a number laid out for the spec `spec` as
`<padding><sign><prefix><padding><digits><point><remainder><padding>`, where only one padding is
not empty.  `neg` says whether the number is negative, `pfx` is its prefix (`0x`), `digits` are its
digits before the point, grouped by `g` and zero-padded for the alignment `=` with the fill `0`,
`point` says whether a point follows them, and `remainder` is the rest.  `upper` makes the prefix
and the digits upper case.  A width or a result longer than `maxLength` is not modelled. -/
def layoutNumber (spec : Spec) (neg : Bool) (pfx digits : List Char) (point : Bool)
    (remainder : List Char) (g : Grouping) (upper : Bool) : Except Failure String := do
  if spec.width.getD 0 > maxLength then throw tooLong
  let signChars : List Char := match spec.sign with
    | some '+' => [if neg then '-' else '+']
    | some ' ' => [if neg then '-' else ' ']
    | _ => if neg then ['-'] else []
  let nonDigits : Int :=
    signChars.length + pfx.length + (if point then 1 else 0) + remainder.length
  let width : Int := match spec.width with
    | some w => w
    | none => -1
  let minWidth : Int := if spec.fill == '0' && spec.align == '=' then width - nonDigits else 0
  let grouped := if digits.isEmpty then [] else insertGrouping g digits minWidth.toNat
  let padding : Int := width - (nonDigits + grouped.length)
  let pad := padding.toNat
  let (left, middle, right) : Nat × Nat × Nat := match spec.align with
    | '<' => (0, 0, pad)
    | '^' => (pad / 2, 0, pad - pad / 2)
    | '=' => (0, pad, 0)
    | _ => (pad, 0, 0)
  let up (cs : List Char) : List Char := if upper then cs.map Char.toUpper else cs
  let out := List.replicate left spec.fill ++ signChars ++ up pfx ++
    List.replicate middle spec.fill ++ up grouped ++ (if point then ['.'] else []) ++ remainder ++
    List.replicate right spec.fill
  if out.length > maxLength then throw tooLong
  return String.ofList out

/-! ## `int.__format__` -/

/-- The lowest `m` digits of `n` in base `b`, the lowest first. -/
def digitsPad (b : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | m + 1, n => n % b :: digitsPad b m (n / b)

/-- The lowest `m₁ + m₂` digits of `n` are the lowest `m₁` digits of `n % b ^ m₁`, then the lowest
`m₂` digits of `n / b ^ m₁`. -/
private theorem digitsPad_add (b : Nat) (m₁ m₂ n : Nat) :
    digitsPad b (m₁ + m₂) n = digitsPad b m₁ (n % b ^ m₁) ++ digitsPad b m₂ (n / b ^ m₁) := by
  induction m₁ generalizing n with
  | zero => simp [digitsPad]
  | succ m ih =>
    rw [Nat.add_right_comm, digitsPad, digitsPad, ih, List.cons_append, Nat.pow_succ',
      Nat.mod_mod_of_dvd n (Nat.dvd_mul_right b (b ^ m)), Nat.mod_mul_right_div_self,
      Nat.div_div_eq_div_mul]

/-- `digitsPad`, splitting the count in halves, so that the conversion costs about
O(size · log m) instead of O(size · m). -/
def digitsPadFast (b : Nat) (m n : Nat) : List Nat :=
  if m ≤ 32 then digitsPad b m n
  else
    let half := m / 2
    digitsPadFast b half (n % b ^ half) ++ digitsPadFast b (m - half) (n / b ^ half)
termination_by m

/-- `digitsPadFast` gives `digitsPad`'s digits. -/
private theorem digitsPadFast_eq (b m n : Nat) : digitsPadFast b m n = digitsPad b m n := by
  induction m using Nat.strongRecOn generalizing n with
  | ind m ih =>
    unfold digitsPadFast
    split
    · rfl
    · rename_i h
      simp only
      rw [ih (m / 2) (by omega), ih (m - m / 2) (by omega)]
      have hm : m = m / 2 + (m - m / 2) := by omega
      conv => rhs; rw [hm]
      rw [digitsPad_add]

/-- `digitsPad` and `digitsPadFast` are the same function, so the compiled code runs the fast
one. -/
@[csimp] theorem digitsPad_eq_digitsPadFast : @digitsPad = @digitsPadFast := by
  funext b m n
  exact (digitsPadFast_eq b m n).symm

/-- The digits of `n` in base `2 ^ k` (`k` is 1, 3 or 4), the highest first, as `bin`, `oct` and
`hex` write them. -/
def pow2Digits (k n : Nat) : List Char :=
  ((digitsPad (2 ^ k) (n.log2 / k + 1) n).reverse.map Nat.digitChar)

/-- CPython's `format_long_internal`: the int `n` for the parsed spec `spec`, whose type is one of
`b c d n o x X`. -/
def formatLong (n : Int) (spec : Spec) : Except Failure String := do
  if spec.precision.isSome then
    throw (valueError "Precision not allowed in integer format specifier")
  if spec.noNegZero then
    throw (valueError "Negative zero coercion (z) not allowed in integer format specifier")
  if spec.type == 'c' then
    if spec.sign.isSome then
      throw (valueError "Sign not allowed with integer format specifier 'c'")
    if spec.alternate then
      throw (valueError "Alternate form (#) not allowed with integer format specifier 'c'")
    if n < -2 ^ 63 || n ≥ 2 ^ 63 then
      throw (.raise "OverflowError" "Python int too large to convert to C long")
    if n < 0 || n > 0x10FFFF then
      throw (.raise "OverflowError" "%c arg not in range(0x110000)")
    if 0xD800 ≤ n && n ≤ 0xDFFF then
      throw (.notModelled "a str that holds a lone surrogate")
    return ← layoutNumber spec false [] [] false [Char.ofNat n.toNat] .none false
  let (bits, pfx) : Nat × List Char := match spec.type with
    | 'b' => (1, ['0', 'b'])
    | 'o' => (3, ['0', 'o'])
    | 'x' | 'X' => (4, ['0', 'x'])
    | _ => (0, [])
  -- Decimal digits are limited to `intMaxStrDigits`, so `Nat.toDigits` stays fast enough.
  if bits == 0 && n.natAbs ≥ 10 ^ intMaxStrDigits then throw maxStrDigitsError
  let digits := if bits == 0 then Nat.toDigits 10 n.natAbs else pow2Digits bits n.natAbs
  let g := if spec.type == 'n' then .none else spec.separators.grouping
  layoutNumber spec (n < 0) (if spec.alternate then pfx else []) digits false [] g
    (spec.type == 'X')

/-! ## `float.__format__` -/

/-- CPython's `format_float_internal`: the float with the bits `bits` for the parsed spec `spec`,
whose type is one of `e E f F g G n %` or none (`'\x00'`).  Without a type, the float formats as
`repr` when the spec has no precision, and otherwise as `'g'`, with `.0` added to an integer.
`'%'` is `'f'` of the value times 100, with a `%` after it. -/
def formatFloatWith (bits : UInt64) (spec : Spec) : Except Failure String := do
  if spec.precision.any (· > 2147483647) then throw (valueError "precision too big")
  let (type, defaultPrecision, addDot0) : Char × Nat × Bool :=
    if spec.type == '\x00' then ('r', 0, true) else (spec.type, 6, false)
  let type := if type == 'n' then 'g' else type
  let (type, bits, percent) := if type == '%' then ('f', mul100 bits, true) else (type, bits, false)
  let type := if spec.precision.isSome && type == 'r' then 'g' else type
  let buf ← doubleToString bits type (spec.precision.getD defaultPrecision) addDot0
    spec.alternate spec.noNegZero
  let buf := buf.toList ++ (if percent then ['%'] else [])
  let (neg, body) := match buf with
    | '-' :: rest => (true, rest)
    | _ => (false, buf)
  let digits := body.takeWhile Char.isDigit
  let (point, remainder) := match body.drop digits.length with
    | '.' :: rest => (true, rest)
    | rest => (false, rest)
  let g := if spec.type == 'n' then .none else spec.separators.grouping
  layoutNumber spec neg [] digits point remainder g false

/-! ## `str.__format__` -/

/-- CPython's `format_string_internal`: the str `s` for the parsed spec `spec`, whose type is
`'s'`.  The precision is the most characters of `s` to keep.  A new string longer than `maxLength`
is not modelled. -/
def formatStringWith (s : String) (spec : Spec) : Except Failure String := do
  if spec.sign == some ' ' then throw (valueError "Space not allowed in string format specifier")
  if spec.sign.isSome then throw (valueError "Sign not allowed in string format specifier")
  if spec.noNegZero then
    throw (valueError "Negative zero coercion (z) not allowed in string format specifier")
  if spec.alternate then
    throw (valueError "Alternate form (#) not allowed in string format specifier")
  if spec.align == '=' then
    throw (valueError "'=' alignment not allowed in string format specifier")
  -- Without padding or truncation, CPython returns `s` itself.
  if spec.width.all (· ≤ s.length) && spec.precision.all (· ≥ s.length) then return s
  let cs := match spec.precision with
    | some p => s.toList.take p
    | none => s.toList
  let total := max cs.length (spec.width.getD 0)
  if total > maxLength then throw tooLong
  let left := match spec.align with
    | '>' => total - cs.length
    | '^' => (total - cs.length) / 2
    | _ => 0
  let right := total - cs.length - left
  return String.ofList (List.replicate left spec.fill ++ cs ++ List.replicate right spec.fill)

/-! ## The `__format__` methods -/

/-- `int.__format__` for the parsed spec `spec` (`_PyLong_FormatAdvancedWriter` after parsing),
for an object of the type `typeName`.  The types `e E f F g G %` format `float(n)`.  A `bool`
`b` formats as `int(b)` with the type name `"bool"`, except that its empty spec gives `str(b)`. -/
def formatIntSpec (n : Int) (spec : Spec) (typeName : String) : Except Failure String :=
  match spec.type with
  | 'b' | 'c' | 'd' | 'o' | 'x' | 'X' | 'n' => formatLong n spec
  | 'e' | 'E' | 'f' | 'F' | 'g' | 'G' | '%' => do formatFloatWith (← intToFloat n) spec
  | t => .error (unknownType t typeName)

/-- `format(n, spec)` for an `int` `n` (`int.__format__`). -/
def formatInt (n : Int) (spec : String) : Except Failure String :=
  if spec.isEmpty then intRepr n
  else do formatIntSpec n (← parseSpec spec "int" 'd' '>') "int"

/-- `format(x, spec)` for the `float` `x` with the bits `bits` (`float.__format__`). -/
def formatFloat (bits : UInt64) (spec : String) : Except Failure String :=
  if spec.isEmpty then .ok (floatRepr bits)
  else do
    let s ← parseSpec spec "float" '\x00' '>'
    match s.type with
    | '\x00' | 'e' | 'E' | 'f' | 'F' | 'g' | 'G' | 'n' | '%' => formatFloatWith bits s
    | t => throw (unknownType t "float")

/-- `format(s, spec)` for a `str` `s` (`str.__format__`). -/
def formatStr (s : String) (spec : String) : Except Failure String :=
  if spec.isEmpty then .ok s
  else do
    let p ← parseSpec spec "str" 's' '<'
    match p.type with
    | 's' => formatStringWith s p
    | t => throw (unknownType t "str")

end

end StrataPython.Dyn.Sem.Format
