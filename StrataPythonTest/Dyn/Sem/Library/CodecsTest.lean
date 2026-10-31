/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Library.Codecs
public import StrataPythonTest.Dyn.Sem.Library.CodecCases
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Library.Codecs
meta import StrataPythonTest.Dyn.Sem.Library.CodecCases

set_option autoImplicit false

/-!
# The built-in codecs

`CodecCases.cases` holds CPython 3.12's results of `str.encode` and `bytes.decode` with the five
built-in codecs and every error handler; the functions must give the same.
-/

namespace StrataPython.Dyn.Sem.Library.CodecsTest

open StrataPython.Dyn.Sem.Library.Codecs

/-- A result, written as the cases write CPython's. -/
private def enc (r : Except Error String) : String :=
  match r with
  | .ok s => s
  | .error e@(.encode encName _ start stop reason) =>
    s!"e UnicodeEncodeError|{encName}|{start}|{stop}|{reason}|{e.message}"
  | .error e@(.decode encName _ start stop reason) =>
    s!"e UnicodeDecodeError|{encName}|{start}|{stop}|{reason}|{e.message}"
  | .error (.raise cls msg) => s!"x {cls}|{msg}"
  | .error (.notModelled what) =>
    if what == nameNotModelled.message then "n name"
    else if what == surrogateNotModelled.message then "n surrogate"
    else s!"n other: {what}"

private def codecOf : String → Codec
  | "utf-8" => .utf8
  | "utf-16" => .utf16
  | "utf-32" => .utf32
  | "ascii" => .ascii
  | _ => .latin1

private def run (kind codec handler input : String) : String :=
  let c := codecOf codec
  let h := Handler.ofName handler
  if kind == "encode" then
    enc ((encode c h input).map fun b => "b " ++ " ".intercalate (b.toList.map (toString ·.toNat)))
  else
    let bytes := input.toList.toArray.map fun ch => ch.toNat.toUInt8
    enc ((decode c h bytes).map fun s => "s " ++ " ".intercalate (s.toList.map (toString ·.toNat)))

private def mismatches : List (String × String × String × String) :=
  CodecCases.cases.toList.filterMap fun (k, c, h, x, r) =>
    if run k c h x == r then none else some (k, c, h, x)

#guard CodecCases.cases.size == 3500
#guard mismatches == []

/-! ## The fast paths of the codec names

The spellings that `PyUnicode_AsEncodedString` and `PyUnicode_Decode` match after
`_Py_normalize_encoding`; any other spelling goes through the codec registry. -/

-- The twelve names that the fast paths compare with, after normalizing.
#guard ["utf8", "utf_8"].all (fastCodec · == some .utf8)
#guard ["utf16", "utf_16"].all (fastCodec · == some .utf16)
#guard ["utf32", "utf_32"].all (fastCodec · == some .utf32)
#guard ["ascii", "us_ascii"].all (fastCodec · == some .ascii)
#guard ["latin1", "latin_1", "iso_8859_1", "iso8859_1"].all (fastCodec · == some .latin1)
-- Other spellings that normalize to them.
#guard fastCodec "UTF-8" == some .utf8 && fastCodec " UTF--8 " == some .utf8
#guard fastCodec "ISO-8859-1" == some .latin1 && fastCodec "Latin_1" == some .latin1
-- Names that no fast path matches: other codecs, other spellings, and a dot, which normalizing
-- keeps.
#guard ["u8", "utf-16-le", "latin", "cp1252", "iso_8859_1_x", "utf.8", "mbcs"].all
  (fastCodec · == none)

/-! ## The names -/

/-- Results compared by their contents, for the guards below. -/
private instance {α : Type} [BEq α] : BEq (Except Error α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

#guard (encodeWith (some "utf\x008") none "a") == .error embeddedNul
#guard (encodeWith (some "ascii") (some "x\x00") "a") == .error embeddedNul
#guard (decodeWith (some "utf\x008") none #[97]) == .error embeddedNul
#guard (decodeWith (some "utf\x008") none #[]) == .error embeddedNul
-- Without `errors`, the handler is `strict`.
#guard (encodeWith (some "ascii") none "é") ==
  .error (.encode "ascii" "é" 0 1 "ordinal not in range(128)")
#guard (decodeWith none none #[0x80]) == .error (.decode "utf-8" #[0x80] 0 1 "invalid start byte")
-- Empty bytes decode before the codec is looked up.
#guard (decodeWith (some "bogus") (some "bogus") #[]) == .ok ""
#guard (decodeWith (some "bogus") none #[97]) == .error (.notModelled "the codec bogus is not modelled")
#guard (encodeWith none none "é") == .ok #[0xC3, 0xA9]
-- A handler's name in its LookupError keeps at most 400 bytes of UTF-8, as `%.400s` does; a
-- character that the limit cuts becomes U+FFFD.
#guard (match decode .ascii (.unknown (String.ofList (List.replicate 500 'x'))) #[0x80] with
  | .error (.raise _ m) => m.length
  | _ => 0) == 429
#guard (match decode .ascii (.unknown (String.ofList ('x' :: List.replicate 200 'é'))) #[0x80] with
  | .error (.raise _ m) => m.endsWith "\uFFFD'"
  | _ => false)

-- A NUL in the handler name alone, with empty octets, is the embedded null character too
-- (`str(b"", errors="x\x00")`).
#guard match decodeWith none (some "x\x00") #[] with | .error e => e == embeddedNul | _ => false

end StrataPython.Dyn.Sem.Library.CodecsTest
