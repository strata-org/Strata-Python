/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Proto.Repr

set_option autoImplicit false

/-!
# printf-style `%` formatting

Generic over the record of primitives, ports of CPython 3.12's `PyUnicode_Format` (`str % args`)
and `_PyBytes_FormatEx` (`bytes % args`): the arguments (a tuple's items, one argument, or a
mapping's values by `%(key)`), the parse of a unit (flags, width and precision, `*` included), its
conversion, and its padding (`unicode_format_arg_output`).  The conversions:

* `s`, `r`, `a`: `str`, `repr` and `ascii` (`bytes`: `s` and `b` take a `bytes` or `__bytes__`,
  `r` and `a` give `ascii`);
* `d`, `i`, `u`: an `int` as it is, else `PyNumber_Long` (`__int__`, then `__index__`; a `float`
  truncated); `o`, `x`, `X`: an `int`, else `__index__`; a `TypeError` of the conversion becomes the
  format's own;
* `e`, `E`, `f`, `F`, `g`, `G`: a `float`, else `__float__`, then `__index__`;
* `c`: an `int` code or a one-character `str` (`bytes`: a byte value or a one-byte `bytes`).

Where CPython 3.12 warns (an `__int__` or `__index__` that returns an instance of a strict subclass
of `int`, a `__float__` that returns one of `float`), the format stops with a gap.  A width, or a
number's precision, beyond `Format.maxLength`, and a result that grows beyond it, stop with a gap.
-/

namespace StrataPython.Dyn.Sem.Proto

@[expose] public section

/-- The flags, width and precision of a unit, and its conversion character; `sign` marks a
number's text, whose sign the padding handles. -/
structure PfArg where
  ljust : Bool := false
  plus : Bool := false
  blank : Bool := false
  alt : Bool := false
  zero : Bool := false
  width : Int := -1
  prec : Int := -1
  sign : Bool := false
  ch : Char := '\x00'

/-- `unicode_format_arg_output` (and the padding of `_PyBytes_FormatEx`): the text `str` of a unit
with its sign, its `0x` or `0o` prefix, and its padding.  A string conversion's precision has
already truncated `str`. -/
def pfPad (a : PfArg) (str : List Char) : List Char := Id.run do
  let fill := if a.sign && a.zero then '0' else ' '
  let mut len : Int := str.length
  let mut width := a.width
  let mut body := str
  let mut sign := a.sign
  let mut signchar := ' '
  if sign then
    match str with
    | c :: rest =>
      if c == '-' || c == '+' then
        signchar := c
        len := len - 1
        body := rest
      else if a.plus then signchar := '+'
      else if a.blank then signchar := ' '
      else sign := false
    | [] => sign := false
  if width < len then width := len
  let mut out : List Char := []
  if sign then
    if fill != ' ' then out := out ++ [signchar]
    if width > len then width := width - 1
  let hasPrefix := a.alt && (a.ch == 'x' || a.ch == 'X' || a.ch == 'o')
  let mut pfx : List Char := []
  if hasPrefix then
    pfx := body.take 2
    body := body.drop 2
    if fill != ' ' then out := out ++ pfx
    width := max 0 (width - 2)
    len := len - 2
  if width > len && !a.ljust then
    out := out ++ List.replicate (width - len).toNat fill
    width := len
  if fill == ' ' then
    if sign then out := out ++ [signchar]
    if hasPrefix then out := out ++ pfx
  out := out ++ body.take len.toNat
  if width > len then out := out ++ List.replicate (width - len).toNat ' '
  return out

/-- `_PyUnicode_FormatLong`'s text of the `int` `n` for the conversion `type` (`d`, `i`, `u`, `o`,
`x` or `X`): at least `prec` digits, the `0o` or `0x` prefix with `alt`, upper case for `X`. -/
def pfLongText (n : Int) (alt : Bool) (prec : Int) (type : Char) : Except Format.Failure (List Char) := do
  if prec > 2147483647 - 3 then throw (.raise "OverflowError" "precision too large")
  let neg := n < 0
  let (pfx, digits) ← match type with
    | 'o' => pure (['0', 'o'], Nat.toDigits 8 n.natAbs)
    | 'x' | 'X' => pure (['0', 'x'], Nat.toDigits 16 n.natAbs)
    | _ => do
      let s ← Format.intRepr n.natAbs
      pure ([], s.toList)
  let pfx := if alt then pfx else []
  let digits := if prec > digits.length then List.replicate (prec.toNat - digits.length) '0' ++ digits else digits
  let s := (if neg then ['-'] else []) ++ pfx ++ digits
  return if type == 'X' then s.map fun c => if 'a' ≤ c && c ≤ 'x' then Char.ofNat (c.toNat - 32) else c else s

section
variable {m : Type → Type 1} {V : Type}

/-- The state of the arguments: the current ones (`ctx.args`), a tuple's items, the count
(`arglen`, `-1` for one argument) and the next index (`argidx`). -/
structure PfArgs (V : Type) where
  args : V
  items : Array V
  arglen : Int
  argidx : Int

/-- `getnextarg`: the next argument, or CPython's `TypeError`. -/
def pfNext [PyCalls m V] (st : PfArgs V) : m (V × PfArgs V) := do
  if st.argidx < st.arglen then
    let st' := { st with argidx := st.argidx + 1 }
    if st.arglen < 0 then return (st.args, st')
    let some v := st.items[st.argidx.toNat]? | PyPure.modelInvariant "printf: an argument past the tuple"
    return (v, st')
  raiseBuiltin "TypeError" "not enough arguments for format string"

/-- A `*` width or precision, which must be an `int`: its number. -/
def pfStarInt [PyCalls m V] (v : V) : m Int := do
  let some i ← intPart? v | raiseBuiltin "TypeError" "* wants int"
  pure i

/-- Whether `v` passes `PyNumber_Check`: a number, or a value whose type has `__index__`,
`__int__` or `__float__`. -/
def pfNumberCheck [PyCalls m V] (v : V) : m Bool := do
  if (← numOf? v).isSome then return true
  let t ← PyReads.classOf v
  for n in ["__index__", "__int__", "__float__"] do
    if (← lookupType t n).isSome then return true
  return false

/-- `PyNumber_Long(v)` for a value that is not an `int`: a `float` truncated, the type's `__int__`,
else its `__index__`; a gap where CPython 3.12 warns, or reads a `str`, a `bytes` or a buffer. -/
def pfNumberLong [PyCalls m V] (v : V) : m Int := do
  let t ← PyReads.classOf v
  match ← lookupType t "__int__" with
  | some f =>
    if let some (.descr .float "__int__" _) ← PyPure.immView f then
      let some (.float x) ← numOf? v | PyPure.modelInvariant "float.__int__ of a value that is not a float"
      match Arith.floatToInt x with
      | .ok i => return i
      | .error e => ofFailure e
    if let some (.descr _ _ _) ← PyPure.immView f then
      PyPure.gap "this built-in type's __int__ is not modelled yet"
    let r ← callFound "__int__" f v t #[] (← PyPure.allocDict)
    match ← PyPure.immView r with
    | some (.int i) => return i
    | some (.bool _) => PyPure.gap "an __int__ that returns a bool, where CPython warns, is not modelled yet"
    | _ =>
      if (← intPart? r).isSome then
        PyPure.gap "an __int__ that returns an instance of a subclass of int, where CPython warns, is not modelled yet"
      raiseBuiltin "TypeError" s!"__int__ returned non-int (type {← typeName r})"
  | none =>
    if let some i ← indexValue? v then return i
    if (← lookupType t "__trunc__").isSome then
      PyPure.gap "an int conversion through __trunc__, where CPython warns, is not modelled yet"
    if (← strText? v).isSome || (← bytesPart? v).isSome || (← lookupType t "__buffer__").isSome then
      PyPure.gap "an int conversion of a str, a bytes or a buffer is not modelled yet"
    raiseBuiltin "TypeError"
      s!"int() argument must be a string, a bytes-like object or a real number, not '{← typeName v}'"

/-- `PyFloat_AsDouble(v)`: a `float` as it is, else the type's `__float__`, whose result must be a
`float`, else its `__index__`; a gap where CPython 3.12 warns. -/
def pfFloat [PyCalls m V] (v : V) : m UInt64 := do
  if let some (.float x) ← numOf? v then return x
  let t ← PyReads.classOf v
  match ← lookupType t "__float__" with
  | some f =>
    if let some (.descr .int "__float__" _) ← PyPure.immView f then
      let some i ← intPart? v | PyPure.modelInvariant "int.__float__ of a value that is not an int"
      match Format.intToFloat i with
      | .ok x => return x
      | .error e => ofFailure e
    if let some (.descr _ _ _) ← PyPure.immView f then
      PyPure.gap "this built-in type's __float__ is not modelled yet"
    let r ← callFound "__float__" f v t #[] (← PyPure.allocDict)
    match ← PyPure.immView r with
    | some (.float x) => return x
    | _ =>
      if (← numOf? r) matches some (.float _) then
        PyPure.gap "a __float__ that returns an instance of a subclass of float, where CPython warns, is not modelled yet"
      raiseBuiltin "TypeError" s!"{← typeName v}.__float__ returned non-float (type {← typeName r})"
  | none =>
    match ← indexValue? v with
    | some i =>
      match Format.intToFloat i with
      | .ok x => return x
      | .error e => ofFailure e
    | none => raiseBuiltin "TypeError" s!"must be real number, not {← typeName v}"

/-- The `int` of a `%c`, `PyLong_AsLongAndOverflow`: an `int` as it is, else its `__index__`;
`none` for a `TypeError`. -/
def pfCharCode? [PyCalls m V] (v : V) : m (Option Int) := do
  if let some i ← intPart? v then return some i
  tryCatch (do
      let some i ← indexValue? v |
        raiseBuiltin "TypeError" s!"'{← typeName v}' object cannot be interpreted as an integer"
      return some i)
    fun x => do if ← isTypeErrorExc x then pure none else throw x

/-- One unit's text: its conversion of `v`, whether it is padded (`pad`; a fast path writes the
text as it is), and the object that `str`, `repr` or `ascii` gave, if any. -/
structure PfConv (V : Type) where
  text : List Char
  obj : Option V := none
  pad : Bool := true

/-- **The conversion of one unit** of a `str` format (`unicode_format_arg_format`), or of a
`bytes` format when `isBytes`; `unsignedCh` says how a `bytes` format read the conversion's byte. -/
def pfConvert [PyCalls m V] (isBytes : Bool) (a : PfArg) (v : V) (index : Nat) (unsignedCh : Bool) :
    m (PfArg × PfConv V) := do
  let numType := if a.ch == 'i' && isBytes then 'd' else a.ch
  let wrongType : m (PfArg × PfConv V) := do
    let what := if a.ch == 'o' || a.ch == 'x' || a.ch == 'X' then "an integer" else "a real number"
    raiseBuiltin "TypeError" s!"%{numType} format: {what} is required, not {Format.cTypeName (← typeName v)}"
  match a.ch with
  | 's' | 'r' | 'a' | 'b' =>
    if isBytes then
      if a.ch == 'b' || a.ch == 's' then
        -- `format_obj`: a `bytes` as it is, else `__bytes__`, else the buffer protocol.
        let bs ← match ← bytesPart? v with
          | some bs => pure bs
          | none =>
            let t ← PyReads.classOf v
            match ← lookupType t "__bytes__" with
            | some f =>
              let r ← callFound "__bytes__" f v t #[] (← PyPure.allocDict)
              let some bs ← bytesPart? r |
                raiseBuiltin "TypeError" s!"__bytes__ returned non-bytes (type {Format.cTypeName (← typeName r)})"
              pure bs
            | none =>
              if (← lookupType t "__buffer__").isSome then
                PyPure.gap "a %b of an object with the buffer protocol is not modelled yet"
              raiseBuiltin "TypeError"
                s!"%b requires a bytes-like object, or an object that implements __bytes__, not '{← typeName v}'"
        let cs := bs.toList.map (Char.ofNat ·.toNat)
        return (a, { text := if a.prec ≥ 0 then cs.take a.prec.toNat else cs })
      let cs := (← textOf (← asciiOf v)).toList
      return (a, { text := if a.prec ≥ 0 then cs.take a.prec.toNat else cs })
    if a.ch == 'b' then
      raiseBuiltin "ValueError" s!"unsupported format character 'b' (0x62) at index {index}"
    -- The fast path of an exact `int` with no width and no precision: its decimal digits.
    if let some (.int i) ← PyPure.immView v then
      if a.width == -1 && a.prec == -1 then
        return (a, { text := (← intText i).toList, pad := false })
    let r ← match a.ch with
      | 's' => if (← PyPure.immView v) matches some (.str _) then pure v else strOf v
      | 'r' => reprOf v
      | _ => asciiOf v
    let cs := (← textOf r).toList
    -- A precision that cuts the text makes a new `str`.
    let cut := a.prec ≥ 0 && cs.length > a.prec.toNat
    return (a, { text := if cut then cs.take a.prec.toNat else cs, obj := if cut then none else some r })
  | 'i' | 'd' | 'u' | 'o' | 'x' | 'X' =>
    if a.prec > Format.maxLength then ofFailure Format.tooLong
    let n ← match ← intPart? v with
      | some n => pure n
      | none =>
        if !(← pfNumberCheck v) then return ← wrongType
        let r? ← tryCatch (some <$> (if a.ch == 'o' || a.ch == 'x' || a.ch == 'X' then do
              let some i ← indexValue? v |
                raiseBuiltin "TypeError" s!"'{← typeName v}' object cannot be interpreted as an integer"
              pure i
            else pfNumberLong v))
          fun x => do if ← isTypeErrorExc x then pure none else throw x
        match r? with
        | some n => pure n
        | none => return ← wrongType
    match pfLongText n a.alt a.prec numType with
    | .ok cs => return ({ a with sign := true }, { text := cs })
    | .error e => ofFailure e
  | 'e' | 'E' | 'f' | 'F' | 'g' | 'G' =>
    let x ← if isBytes then
        tryCatch (pfFloat v) fun _ => do
          raiseBuiltin "TypeError" s!"float argument required, not {Format.cTypeName (← typeName v)}"
      else pfFloat v
    let prec := if a.prec < 0 then 6 else a.prec.toNat
    match Format.doubleToString x a.ch prec false a.alt false with
    | .ok s => return ({ a with sign := true }, { text := s.toList })
    | .error e => ofFailure e
  | 'c' =>
    if isBytes then
      let b ← match ← bytesPart? v with
        | some #[b] => pure b.toNat
        | _ =>
          let some i ← pfCharCode? v |
            raiseBuiltin "TypeError" "%c requires an integer in range(256) or a single byte"
          if i < 0 || i > 255 then raiseBuiltin "OverflowError" "%c arg not in range(256)"
          pure i.toNat
      return (a, { text := [Char.ofNat b] })
    let c ← match ← strText? v with
      | some s =>
        match s.toList with
        | [c] => pure c
        | _ => raiseBuiltin "TypeError" "%c requires int or char"
      | none =>
        let some i ← pfCharCode? v | raiseBuiltin "TypeError" "%c requires int or char"
        if i < 0 || i > 0x10FFFF then raiseBuiltin "OverflowError" "%c arg not in range(0x110000)"
        if 0xD800 ≤ i && i ≤ 0xDFFF then PyPure.gap "a %c of a surrogate code point is not modelled yet"
        pure (Char.ofNat i.toNat)
    return (a, { text := [c] })
  | c =>
    -- `_PyBytes_FormatEx` reads the character as a signed C `char`, except after a run of digits:
    -- a negative one fails in the message's `%c`.
    if isBytes && c.toNat ≥ 0x80 && !unsignedCh then
      raiseBuiltin "OverflowError" "character argument not in range(0x110000)"
    let shown := if isBytes || (31 ≤ c.toNat && c.toNat ≤ 126) then c else '?'
    raiseBuiltin "ValueError"
      s!"unsupported format character '{shown}' (0x{String.ofList (Nat.toDigits 16 c.toNat)}) at index {index}"

/-- The steps that a format takes at most, past which it stops with a gap. -/
def pfFuel : Nat := 2 ^ 24

/-- **`PyUnicode_Format`**, or **`_PyBytes_FormatEx`** when `isBytes`, of the format `cs` with the
arguments `args`: the text, and the object of the one unit that the result is when CPython gives
that object itself (a `str`, `repr` or `ascii` result written alone, unpadded, at the end). -/
def pfFormat [PyCalls m V] (isBytes : Bool) (cs : Array Char) (args : V) : m (List Char × Option V) := do
  let size := cs.size
  let items? ← match ← PyPure.immView args with
    | some (.tuple xs) => pure (some xs)
    | some _ => pure none
    | none => PyReads.tupleView args
  let isTuple := items?.isSome
  let excluded ← if isTuple then pure true
    else if (← strText? args).isSome then pure true
    else if isBytes then pure (← bytesPart? args).isSome
    else pure false
  let dict? ← if excluded then pure none
    else do pure (if (← lookupType (← PyReads.classOf args) "__getitem__").isSome then some args else none)
  let mut st : PfArgs V :=
    { args, items := items?.getD #[], arglen := if isTuple then (items?.getD #[]).size else -1,
      argidx := if isTuple then 0 else -2 }
  let notAll := s!"not all arguments converted during {if isBytes then "bytes" else "string"} formatting"
  -- The text so far, as its chunks in reverse order, and its length.
  let mut out : List (List Char) := []
  let mut outLen := 0
  let mut sole : Option V := none
  let mut pos := 0
  for _ in [0:pfFuel] do
    if pos ≥ size then
      if st.argidx < st.arglen && dict?.isNone then raiseBuiltin "TypeError" notAll
      return (out.reverse.flatten, sole)
    if cs[pos]! != '%' then
      -- A run of text up to the next `%`.
      let mut q := pos + 1
      for _ in [0:size + 1] do
        if !(q < size && cs[q]! != '%') then break
        q := q + 1
      out := (cs.extract pos q).toList :: out
      outLen := outLen + (q - pos)
      pos := q
      continue
    pos := pos + 1
    -- `%%` directly after the `%`.
    if cs.getD pos '\x00' == '%' then
      out := ['%'] :: out
      outLen := outLen + 1
      pos := pos + 1
      continue
    let wasEmpty := outLen == 0 && sole.isNone
    let mut a : PfArg := {}
    let mut ch := cs.getD pos '\x00'
    -- Whether `ch` ended a run of width or precision digits, the one read of a `bytes` format that
    -- takes a byte as unsigned.
    let mut unsignedCh := false
    let mut done := false
    -- `%(key)`: the argument from the mapping.
    if ch == '(' then
      let some d := dict? | raiseBuiltin "TypeError" "format requires a mapping"
      pos := pos + 1
      let keyStart := pos
      let mut depth := 1
      for _ in [0:size + 1] do
        if !(depth > 0 && pos < size) then break
        if cs[pos]! == ')' then depth := depth - 1
        else if cs[pos]! == '(' then depth := depth + 1
        pos := pos + 1
      if depth > 0 then raiseBuiltin "ValueError" "incomplete format key"
      let key := (cs.extract keyStart (pos - 1)).toList
      let keyV := if isBytes then PyPure.imm (m := m) (.bytes (key.map (·.toNat.toUInt8)).toArray)
        else strValue (m := m) (String.ofList key)
      let v ← getItem d keyV
      st := { st with args := v, arglen := -1, argidx := -2 }
    -- The flags; `ch` is the first character after them.
    for _ in [0:size + 1] do
      if !(pos < size) then break
      ch := cs[pos]!
      unsignedCh := false
      pos := pos + 1
      if ch == '-' then a := { a with ljust := true }
      else if ch == '+' then a := { a with plus := true }
      else if ch == ' ' then a := { a with blank := true }
      else if ch == '#' then a := { a with alt := true }
      else if ch == '0' then a := { a with zero := true }
      else
        done := true
        break
    let mut exhausted := !done
    -- The width.
    if ch == '*' && done then
      let (v, st') ← pfNext st
      st := st'
      let w ← pfStarInt v
      if w < Arith.ssizeMin || w > (Format.ssizeMax : Int) then
        raiseBuiltin "OverflowError" "Python int too large to convert to C ssize_t"
      a := if w < 0 then { a with ljust := true, width := -w } else { a with width := w }
      if pos < size then
        ch := cs[pos]!
        unsignedCh := false
        pos := pos + 1
      else exhausted := true
    else if '0' ≤ ch && ch ≤ '9' && done then
      let mut w : Int := ch.toNat - '0'.toNat
      exhausted := true
      for _ in [0:size + 1] do
        if !(pos < size) then break
        ch := cs[pos]!
        unsignedCh := false
        pos := pos + 1
        if ch < '0' || ch > '9' then
          unsignedCh := true
          exhausted := false
          break
        if w > ((Format.ssizeMax : Int) - (ch.toNat - '0'.toNat)) / 10 then
          raiseBuiltin "ValueError" "width too big"
        w := w * 10 + (ch.toNat - '0'.toNat)
      a := { a with width := w }
    -- The precision.
    if ch == '.' && !exhausted then
      a := { a with prec := 0 }
      if pos < size then
        ch := cs[pos]!
        unsignedCh := false
        pos := pos + 1
      else exhausted := true
      if ch == '*' && !exhausted then
        let (v, st') ← pfNext st
        st := st'
        let p ← pfStarInt v
        if p < -2147483648 || p > 2147483647 then
          raiseBuiltin "OverflowError" "Python int too large to convert to C int"
        a := { a with prec := max p 0 }
        if pos < size then
          ch := cs[pos]!
          unsignedCh := false
          pos := pos + 1
        else exhausted := true
      else if '0' ≤ ch && ch ≤ '9' && !exhausted then
        let mut p : Int := ch.toNat - '0'.toNat
        exhausted := true
        for _ in [0:size + 1] do
          if !(pos < size) then break
          ch := cs[pos]!
          unsignedCh := false
          pos := pos + 1
          if ch < '0' || ch > '9' then
            unsignedCh := true
            exhausted := false
            break
          if p > (2147483647 - (ch.toNat - '0'.toNat)) / 10 then
            raiseBuiltin "ValueError" (if isBytes then "prec too big" else "precision too big")
          p := p * 10 + (ch.toNat - '0'.toNat)
        a := { a with prec := p }
    -- One length modifier `h`, `l` or `L` is skipped.
    if !exhausted && (ch == 'h' || ch == 'l' || ch == 'L') then
      if pos < size then
        ch := cs[pos]!
        unsignedCh := false
        pos := pos + 1
      else exhausted := true
    if exhausted then raiseBuiltin "ValueError" "incomplete format"
    a := { a with ch }
    if a.width > Format.maxLength then ofFailure Format.tooLong
    let (v, st') ← pfNext st
    st := st'
    let (a', conv) ← pfConvert isBytes a v (pos - 1) unsignedCh
    let text := if conv.pad then pfPad a' conv.text else conv.text
    -- The object itself is the result when it is written alone, unpadded, at the end.
    if wasEmpty && pos == size && !text.isEmpty && text == conv.text && !a'.plus && !a'.blank then
      sole := conv.obj
    out := text :: out
    outLen := outLen + text.length
    if outLen > Format.maxLength then ofFailure Format.tooLong
    if dict?.isSome && st.argidx < st.arglen then raiseBuiltin "TypeError" notAll
  PyPure.gap "a format longer than the model walks"

/-- **`fmt % args` for a `str` format** (`unicode_mod`): `PyUnicode_Format`. -/
def printfStr [PyCalls m V] (fmt : String) (args : V) : m V := do
  let (out, sole) ← pfFormat false fmt.toList.toArray args
  if let some r := sole then return r
  return strValue (m := m) (String.ofList out)

/-- **`fmt % args` for a `bytes` format** (`bytes_mod`): `_PyBytes_FormatEx`. -/
def printfBytes [PyCalls m V] (fmt : Array UInt8) (args : V) : m V := do
  let (out, _) ← pfFormat true (fmt.map (Char.ofNat ·.toNat)) args
  return PyPure.imm (m := m) (.bytes (out.map (·.toNat.toUInt8)).toArray)

end

end

end StrataPython.Dyn.Sem.Proto
