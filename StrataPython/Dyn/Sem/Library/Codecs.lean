/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Format

set_option autoImplicit false

/-!
# The built-in codecs of `str.encode` and `str(b, encoding, errors)`

The five codecs that CPython 3.12 runs without the `encodings` package (the fast paths of
`PyUnicode_AsEncodedString` and `PyUnicode_Decode`): UTF-8, UTF-16 and UTF-32 (native order,
little-endian here, with a byte order mark), ASCII and Latin-1. Their error handlers are
`strict`, `ignore`, `replace`, `backslashreplace`, `xmlcharrefreplace`, `surrogateescape` and
`surrogatepass`.

Three cases are not modelled. Every other codec, or another spelling of one of these, is found
through the codec registry in a module of the `encodings` package; `namereplace` on encoding
reads the Unicode name database of the `unicodedata` module; and a decoding that would give a
lone surrogate (by `surrogateescape` or `surrogatepass`) gives a string that a Lean `String` can't
hold. A Lean `String` holds no surrogate, so no encoding of these codecs meets one.
-/

namespace StrataPython.Dyn.Sem.Library.Codecs

@[expose] public section

/-- The five built-in codecs. -/
inductive Codec where
  | utf8 | utf16 | utf32 | ascii | latin1
  deriving Repr, BEq, DecidableEq

/-- The name of a codec in its error messages. UTF-16 and UTF-32 decoders name the byte order
that they read. -/
def Codec.name : Codec → String
  | .utf8 => "utf-8"
  | .utf16 => "utf-16"
  | .utf32 => "utf-32"
  | .ascii => "ascii"
  | .latin1 => "latin-1"

/-- CPython's `_Py_normalize_encoding` into its 11-byte buffer: the runs of ASCII letters, digits
and dots, lowercased and joined by `_`; `none` when the result needs more than 10 characters, so
that the fast paths don't apply. -/
def normalize (name : String) : Option String :=
  let keep (c : Char) : Bool := c.isAlphanum || c == '.'
  let (out, _) := name.toList.foldl (fun (out, punct) c =>
    if keep c then
      ((if punct && !out.isEmpty then out.push '_' else out).push c.toLower, false)
    else (out, true)) ((#[] : Array Char), false)
  if out.size > 10 then none else some (String.ofList out.toList)

/-- The codec of `name` if one of the fast paths of `PyUnicode_AsEncodedString` and
`PyUnicode_Decode` matches it. -/
def fastCodec (name : String) : Option Codec :=
  match normalize name with
  | some "utf8" | some "utf_8" => some .utf8
  | some "utf16" | some "utf_16" => some .utf16
  | some "utf32" | some "utf_32" => some .utf32
  | some "ascii" | some "us_ascii" => some .ascii
  | some "latin1" | some "latin_1" | some "iso_8859_1" | some "iso8859_1" => some .latin1
  | _ => none

/-- An error handler, by its name. -/
inductive Handler where
  | strict | ignore | replace | backslashreplace | xmlcharrefreplace | surrogateescape
  | surrogatepass | namereplace
  | unknown (name : String)
  deriving Repr, BEq

/-- The handler with the name `name`. -/
def Handler.ofName : String → Handler
  | "strict" => .strict
  | "ignore" => .ignore
  | "replace" => .replace
  | "backslashreplace" => .backslashreplace
  | "xmlcharrefreplace" => .xmlcharrefreplace
  | "surrogateescape" => .surrogateescape
  | "surrogatepass" => .surrogatepass
  | "namereplace" => .namereplace
  | n => .unknown n

/-- How a codec call fails. -/
inductive Error where
  /-- `UnicodeEncodeError(encoding, object, start, end, reason)`. -/
  | encode (encoding : String) (obj : String) (start stop : Nat) (reason : String)
  /-- `UnicodeDecodeError(encoding, object, start, end, reason)`. -/
  | decode (encoding : String) (obj : Array UInt8) (start stop : Nat) (reason : String)
  /-- Another exception, by its class and message (`LookupError`, `TypeError`). -/
  | raise (cls msg : String)
  /-- A case that is not modelled, and which. -/
  | notModelled (what : String)
  deriving Repr, BEq

/-- `n` in hexadecimal, with at least `width` digits. -/
def hex (n width : Nat) : String :=
  let ds := Nat.toDigits 16 n
  String.ofList (List.replicate (width - ds.length) '0' ++ ds)

/-- How `UnicodeEncodeError.__str__` writes the character with the code point `cp`. -/
def escapeChar (cp : Nat) : String :=
  if cp ≤ 0xff then "\\x" ++ hex cp 2
  else if cp ≤ 0xffff then "\\u" ++ hex cp 4
  else "\\U" ++ hex cp 8

/-- `str(e)` of a `UnicodeEncodeError` or `UnicodeDecodeError` that these codecs raise (CPython's
`UnicodeEncodeError_str` and `UnicodeDecodeError_str`), and the message of another exception.
These codecs always give `start < end ≤ len(object)`; an exception that a program builds itself
can have other positions, which this function doesn't cover. -/
def Error.message : Error → String
  | .encode enc obj start stop reason =>
    match obj.toList[start]? with
    | some c =>
      if stop == start + 1 then
        s!"'{enc}' codec can't encode character '{escapeChar c.toNat}' in position {start}: {reason}"
      else s!"'{enc}' codec can't encode characters in position {start}-{stop - 1}: {reason}"
    | none => s!"'{enc}' codec can't encode characters in position {start}-{stop - 1}: {reason}"
  | .decode enc obj start stop reason =>
    match obj[start]? with
    | some b =>
      if stop == start + 1 then
        s!"'{enc}' codec can't decode byte 0x{hex b.toNat 2} in position {start}: {reason}"
      else s!"'{enc}' codec can't decode bytes in position {start}-{stop - 1}: {reason}"
    | none => s!"'{enc}' codec can't decode bytes in position {start}-{stop - 1}: {reason}"
  | .raise _ msg => msg
  | .notModelled what => what

/-- A name as `%.400s` writes it into a message: at most 400 bytes of its UTF-8, and a replacement
character for a character that the limit cuts. -/
def cName400 (name : String) : String :=
  let (kept, cut) := Format.takeBytes name.toList 400
  String.ofList (kept ++ (if cut then ['\uFFFD'] else []))

/-- The `LookupError` of a handler that doesn't exist. -/
def unknownHandler (name : String) : Error :=
  .raise "LookupError" s!"unknown error handler name '{cName400 name}'"

/-- The `TypeError` of a handler that only encodes, called on a decoding error. -/
def encodeOnly : Error :=
  .raise "TypeError" "don't know how to handle UnicodeDecodeError in error callback"

/-- The case of `namereplace` on encoding. -/
def nameNotModelled : Error :=
  .notModelled "the namereplace error handler is not modelled"

/-- A decoder whose step would not move forward. It can't happen: `utf8At` always gives a length
of at least 1, and `onDecodeError` always goes on after `start`. The termination guards detect
it, and this error makes a change that broke it show, instead of returning a shorter result. -/
def noProgress : Error := .notModelled "a decoder made no progress"

/-- The case of a decoding that gives a lone surrogate. -/
def surrogateNotModelled : Error :=
  .notModelled "a lone surrogate from decoding is not modelled"

/-! ## Encoding -/

/-- The bytes of the ASCII string `s`. -/
def asciiBytes (s : String) : Array UInt8 := s.toList.toArray.map fun c => c.toNat.toUInt8

/-- The two little-endian bytes of `u`. -/
def le16 (u : Nat) : Array UInt8 := #[(u % 256).toUInt8, (u / 256 % 256).toUInt8]

/-- The UTF-16 code units of `cp`, little-endian. -/
def utf16Of (cp : Nat) : Array UInt8 :=
  if cp < 0x10000 then le16 cp
  else le16 (0xD800 + (cp - 0x10000) / 1024) ++ le16 (0xDC00 + (cp - 0x10000) % 1024)

/-- The four little-endian bytes of `cp`. -/
def utf32Of (cp : Nat) : Array UInt8 := le16 (cp % 65536) ++ le16 (cp / 65536)

/-- The end of the run of characters of `a` from `i` on whose code points are `limit` or more. -/
def runEnd (limit : Nat) (a : Array Char) (i : Nat) : Nat :=
  if i < a.size ∧ (a.getD i ' ').toNat ≥ limit then runEnd limit a (i + 1) else i
termination_by a.size - i

/-- `runEnd` never goes back. -/
private theorem le_runEnd (limit : Nat) (a : Array Char) (i : Nat) : i ≤ runEnd limit a i := by
  unfold runEnd; split
  · have := le_runEnd limit a (i + 1); omega
  · omega
termination_by a.size - i

/-- `s.encode(codec, errors)` for ASCII (`limit` 128) and Latin-1 (`limit` 256): CPython's
`unicode_encode_ucs1`. A run of characters that the codec can't encode is one error; a handler
replaces the whole run. -/
def encodeUcs1 (codec : Codec) (limit : Nat) (h : Handler) (s : String) :
    Except Error (Array UInt8) :=
  let a := s.toList.toArray
  go a s!"ordinal not in range({limit})" 0 #[]
where
  go (a : Array Char) (reason : String) (i : Nat) (out : Array UInt8) :
      Except Error (Array UInt8) :=
    if _hi : i < a.size then
      let c := a.getD i ' '
      if _hc : c.toNat < limit then go a reason (i + 1) (out.push c.toNat.toUInt8)
      else
        -- The run of characters that the codec can't encode; it holds at least `a[i]`.
        let j := runEnd limit a (i + 1)
        let run := (a.extract i j).toList
        let err := Error.encode codec.name (String.ofList a.toList) i j reason
        match h with
        | .strict | .surrogateescape | .surrogatepass => .error err
        | .ignore => go a reason j out
        | .replace => go a reason j (out ++ Array.replicate (j - i) (63 : UInt8))
        | .backslashreplace =>
          go a reason j (out ++ asciiBytes (String.join (run.map fun c => escapeChar c.toNat)))
        | .xmlcharrefreplace =>
          go a reason j (out ++ asciiBytes (String.join (run.map fun c => s!"&#{c.toNat};")))
        | .namereplace => .error nameNotModelled
        | .unknown n => .error (unknownHandler n)
    else .ok out
  termination_by a.size - i
  decreasing_by all_goals (have := le_runEnd limit a (i + 1); omega)

/-- `s.encode(codec, errors)`. -/
def encode (codec : Codec) (h : Handler) (s : String) : Except Error (Array UInt8) :=
  match codec with
  | .utf8 => .ok s.toUTF8.data
  | .utf16 => .ok (s.toList.foldl (fun out c => out ++ utf16Of c.toNat) #[0xFF, 0xFE])
  | .utf32 => .ok (s.toList.foldl (fun out c => out ++ utf32Of c.toNat) #[0xFF, 0xFE, 0x00, 0x00])
  | .ascii => encodeUcs1 .ascii 128 h s
  | .latin1 => encodeUcs1 .latin1 256 h s

/-! ## Decoding -/

/-- How a decoder goes on after a malformed range `b[start, stop)` with the reason `reason`, by the
handler `h`: the characters to add, where to go on, and whether the handler gave a lone surrogate
(which the result can't hold), or the error. `surrogate` is the number of bytes from `start` that
encode a surrogate in this codec, if they do; `surrogatepass` gives that surrogate back and goes
on after those bytes. As in CPython, `surrogateescape` escapes the bytes from 128 on at the start
of the range and goes on after them, and raises the error if the range starts below 128. -/
def onDecodeError (enc : String) (b : Array UInt8) (h : Handler) (start stop : Nat)
    (reason : String) (surrogate : Option Nat) : Except Error (List Char × Nat × Bool) :=
  let err := Error.decode enc b start stop reason
  match h with
  | .strict => .error err
  | .ignore => .ok ([], stop, false)
  | .replace => .ok (['\uFFFD'], stop, false)
  | .backslashreplace =>
    .ok ((List.range (stop - start)).flatMap
      (fun k => ("\\x" ++ hex (b.getD (start + k) 0).toNat 2).toList), stop, false)
  | .surrogateescape =>
    let consumed := ((List.range (stop - start)).takeWhile fun k => b.getD (start + k) 0 ≥ 128).length
    if consumed == 0 then .error err else .ok ([], start + consumed, true)
  | .surrogatepass =>
    match surrogate with
    | some w => .ok ([], start + w, true)
    | none => .error err
  | .xmlcharrefreplace | .namereplace => .error encodeOnly
  | .unknown n => .error (unknownHandler n)

/-- The end of a decoding: the characters, or the case that is not modelled if a handler gave a
lone surrogate. -/
def finish (out : Array Char) (lone : Bool) : Except Error (List Char) :=
  if lone then .error surrogateNotModelled else .ok out.toList

/-- An error that a decoding meets after a handler gave a lone surrogate: CPython raises it on
the exception object of the first error, whose `args` stay those of the first error, so the
model stops with the gap of the lone surrogate instead. -/
def laterError (lone : Bool) (e : Error) : Error := if lone then surrogateNotModelled else e

/-- Whether `x` is a UTF-8 continuation byte between `lo` and `hi`. -/
def inRange (x : Option UInt8) (lo hi : UInt8) : Bool :=
  match x with
  | some x => lo ≤ x && x ≤ hi
  | none => false

/-- The UTF-8 sequence that starts at `b[i]`: its length and its code point, or the length of its
maximal valid prefix and whether the data ends inside it. The ranges of the second byte follow
the Unicode standard (Table 3-7). -/
def utf8At (b : Array UInt8) (i : Nat) : Except (Nat × Bool) (Nat × Nat) :=
  let x0 := (b.getD i 0).toNat
  let at_ (k : Nat) : Option UInt8 := b[i + k]?
  -- The length, and the range of the second byte.
  let shape : Option (Nat × UInt8 × UInt8) :=
    if x0 < 0x80 then some (1, 0, 0)
    else if x0 < 0xC2 then none
    else if x0 < 0xE0 then some (2, 0x80, 0xBF)
    else if x0 == 0xE0 then some (3, 0xA0, 0xBF)
    else if x0 == 0xED then some (3, 0x80, 0x9F)
    else if x0 < 0xF0 then some (3, 0x80, 0xBF)
    else if x0 == 0xF0 then some (4, 0x90, 0xBF)
    else if x0 < 0xF4 then some (4, 0x80, 0xBF)
    else if x0 == 0xF4 then some (4, 0x80, 0x8F)
    else none
  match shape with
  | none => .error (1, false)
  | some (1, _, _) => .ok (1, x0)
  | some (n, lo, hi) =>
    -- The number of bytes of the valid prefix.
    let k :=
      if !inRange (at_ 1) lo hi then 1
      else if n == 2 || !inRange (at_ 2) 0x80 0xBF then 2
      else if n == 3 || !inRange (at_ 3) 0x80 0xBF then 3
      else 4
    if k < n then .error (k, i + k ≥ b.size && (at_ k).isNone)
    else
      let cont (j : Nat) : Nat := (b.getD (i + j) 0).toNat % 64
      let cp := match n with
        | 2 => (x0 % 32) * 64 + cont 1
        | 3 => (x0 % 16) * 4096 + cont 1 * 64 + cont 2
        | _ => (x0 % 8) * 262144 + cont 1 * 4096 + cont 2 * 64 + cont 3
      .ok (n, cp)

/-- The number of bytes from `b[i]` that encode a surrogate in UTF-8 (`ED A0..BF 80..BF`), if
they do. -/
def utf8Surrogate (b : Array UInt8) (i : Nat) : Option Nat :=
  if b[i]? == some 0xED && inRange b[i + 1]? 0xA0 0xBF && inRange b[i + 2]? 0x80 0xBF then some 3
  else none

/-- `b.decode("utf-8", errors)`: CPython's loop. -/
def decodeUtf8 (h : Handler) (b : Array UInt8) : Except Error (List Char) := go 0 #[] false
where
  go (i : Nat) (out : Array Char) (lone : Bool) : Except Error (List Char) :=
    if _hi : i < b.size then
      match utf8At b i with
      | .ok (n, cp) =>
        if _hn : 0 < n then go (i + n) (out.push (Char.ofNat cp)) lone else .error noProgress
      | .error (k, atEnd) =>
        -- At the end of the data, `i + k` is the end.
        let stop := i + k
        let x0 := b.getD i 0
        let reason := if atEnd then "unexpected end of data"
          else if x0 < 0xC2 || x0 > 0xF4 then "invalid start byte"
          else "invalid continuation byte"
        match onDecodeError "utf-8" b h i stop reason (utf8Surrogate b i) with
        | .ok (cs, next, l) =>
          if _hs : b.size - next < b.size - i then go next (out ++ cs.toArray) (lone || l)
          else .error noProgress
        | .error e => .error (laterError lone e)
    else finish out lone
  termination_by b.size - i

/-- A decoder of fixed-size code units (UTF-16 and UTF-32) reads a byte order mark at the start of
`b`; this gives the mark's length and whether the order is big-endian. -/
def bomOrder (b : Array UInt8) (bom : List UInt8) (bomBE : List UInt8) : Nat × Bool :=
  if (b.extract 0 bom.length).toList == bom then (bom.length, false)
  else if (b.extract 0 bomBE.length).toList == bomBE then (bomBE.length, true)
  else (0, false)

/-- The value of the unit of `w` bytes at `b[i]`, in the order `be`. -/
def unitAt (b : Array UInt8) (i w : Nat) (be : Bool) : Nat :=
  (List.range w).foldl (fun acc k =>
    let byte := (b.getD (i + (if be then k else w - 1 - k)) 0).toNat
    acc * 256 + byte) 0

/-- The number of bytes from `b[i]` that encode a surrogate in units of `w` bytes in the order
`be`, if they do. -/
def unitSurrogate (b : Array UInt8) (i w : Nat) (be : Bool) : Option Nat :=
  let u := unitAt b i w be
  if i + w ≤ b.size && 0xD800 ≤ u && u ≤ 0xDFFF then some w else none

/-- `b.decode("utf-16", errors)`: the byte order mark, if any, chooses the order; without one, the
order is little-endian. -/
def decodeUtf16 (h : Handler) (b : Array UInt8) : Except Error (List Char) :=
  let (start, be) := bomOrder b [0xFF, 0xFE] [0xFE, 0xFF]
  let enc := if be then "utf-16-be" else "utf-16-le"
  go enc be start #[] false
where
  go (enc : String) (be : Bool) (i : Nat) (out : Array Char) (lone : Bool) :
      Except Error (List Char) :=
    if _hi : i < b.size then
      let err (stop : Nat) (reason : String) : Except Error (List Char) :=
        match onDecodeError enc b h i stop reason (unitSurrogate b i 2 be) with
        | .ok (cs, next, l) =>
          if _hn : b.size - next < b.size - i then go enc be next (out ++ cs.toArray) (lone || l)
          else .error noProgress
        | .error e => .error (laterError lone e)
      if i + 2 > b.size then err b.size "truncated data"
      else
        let u := unitAt b i 2 be
        if u < 0xD800 || u > 0xDFFF then go enc be (i + 2) (out.push (Char.ofNat u)) lone
        else if u ≥ 0xDC00 then err (i + 2) "illegal encoding"
        else if i + 4 > b.size then err b.size "unexpected end of data"
        else
          let v := unitAt b (i + 2) 2 be
          if 0xDC00 ≤ v && v ≤ 0xDFFF then
            go enc be (i + 4) (out.push (Char.ofNat (0x10000 + (u - 0xD800) * 1024 + (v - 0xDC00))))
              lone
          else err (i + 2) "illegal UTF-16 surrogate"
    else finish out lone
  termination_by b.size - i

/-- `b.decode("utf-32", errors)`, as `decodeUtf16` with units of four bytes. -/
def decodeUtf32 (h : Handler) (b : Array UInt8) : Except Error (List Char) :=
  let (start, be) := bomOrder b [0xFF, 0xFE, 0x00, 0x00] [0x00, 0x00, 0xFE, 0xFF]
  let enc := if be then "utf-32-be" else "utf-32-le"
  go enc be start #[] false
where
  go (enc : String) (be : Bool) (i : Nat) (out : Array Char) (lone : Bool) :
      Except Error (List Char) :=
    if _hi : i < b.size then
      let err (stop : Nat) (reason : String) : Except Error (List Char) :=
        match onDecodeError enc b h i stop reason (unitSurrogate b i 4 be) with
        | .ok (cs, next, l) =>
          if _hn : b.size - next < b.size - i then go enc be next (out ++ cs.toArray) (lone || l)
          else .error noProgress
        | .error e => .error (laterError lone e)
      if i + 4 > b.size then err b.size "truncated data"
      else
        let u := unitAt b i 4 be
        if u > 0x10FFFF then err (i + 4) "code point not in range(0x110000)"
        else if 0xD800 ≤ u && u ≤ 0xDFFF then
          err (i + 4) "code point in surrogate code point range(0xd800, 0xe000)"
        else go enc be (i + 4) (out.push (Char.ofNat u)) lone
    else finish out lone
  termination_by b.size - i

/-- `b.decode("ascii", errors)`: each byte from 128 on is an error of its own. -/
def decodeAscii (h : Handler) (b : Array UInt8) : Except Error (List Char) := go 0 #[] false
where
  go (i : Nat) (out : Array Char) (lone : Bool) : Except Error (List Char) :=
    if _hi : i < b.size then
      let x := b.getD i 0
      if x < 128 then go (i + 1) (out.push (Char.ofNat x.toNat)) lone
      else match onDecodeError "ascii" b h i (i + 1) "ordinal not in range(128)" none with
        | .ok (cs, _, l) => go (i + 1) (out ++ cs.toArray) (lone || l)
        | .error e => .error (laterError lone e)
    else finish out lone
  termination_by b.size - i

/-- `b.decode(codec, errors)`. -/
def decode (codec : Codec) (h : Handler) (b : Array UInt8) : Except Error String :=
  match codec, String.fromUTF8? ⟨b⟩ with
  -- Valid UTF-8 takes Lean's decoder, which rejects the same sequences as CPython (overlong forms,
  -- surrogates, code points above U+10FFFF).
  | .utf8, some s => .ok s
  | _, _ => String.ofList <$> match codec with
    | .utf8 => decodeUtf8 h b
    | .utf16 => decodeUtf16 h b
    | .utf32 => decodeUtf32 h b
    | .ascii => if b.all (· < 128) then .ok (b.toList.map fun x => Char.ofNat x.toNat)
      else decodeAscii h b
    | .latin1 => .ok (b.toList.map fun x => Char.ofNat x.toNat)

/-! ## From the names -/

/-- The `ValueError` of a codec name or handler name that holds a NUL, which CPython's argument
parsing (format `s`) raises before anything else. -/
def embeddedNul : Error := .raise "ValueError" "embedded null character"

/-- Whether a codec or handler name holds a NUL, which CPython rejects as an embedded null
character. -/
def holdsNul (encoding errors : Option String) : Bool :=
  (encoding.getD "").toList.contains '\x00' || (errors.getD "").toList.contains '\x00'

/-- The codec of the name `encoding` (`utf-8` if none is given) and the handler of the name
`errors` (`strict` if none is given), as `str.encode` and `str(b, encoding, errors)` read them:
the `ValueError` of a NUL in a name, or the case that is not modelled for a name that no fast
path matches. -/
def lookup (encoding errors : Option String) : Except Error (Codec × Handler) :=
  if holdsNul encoding errors then .error embeddedNul
  else
    let h := Handler.ofName (errors.getD "strict")
    match encoding with
    | none => .ok (.utf8, h)
    | some name => match fastCodec name with
      | some c => .ok (c, h)
      | none => .error (.notModelled s!"the codec {name} is not modelled")

/-- `s.encode(encoding, errors)`. -/
def encodeWith (encoding errors : Option String) (s : String) : Except Error (Array UInt8) := do
  let (c, h) ← lookup encoding errors
  encode c h s

/-- `str(b, encoding, errors)` and `b.decode(encoding, errors)`, with at least one of the names
given for `str` (`str(b)` with neither is `repr(b)`, not a decoding). As in CPython, empty bytes
decode to the empty string before the codec is looked up, once the names are known to hold no
NUL. -/
def decodeWith (encoding errors : Option String) (b : Array UInt8) : Except Error String :=
  if holdsNul encoding errors then .error embeddedNul
  else if b.isEmpty then .ok ""
  else do
    let (c, h) ← lookup encoding errors
    decode c h b

end

end StrataPython.Dyn.Sem.Library.Codecs
