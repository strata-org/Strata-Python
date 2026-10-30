#!/usr/bin/env python3
"""Write the tests of the formatting of ints, floats and strs, as CPython 3.12 formats them.

Writes `StrataPythonTest/Dyn/Sem/FormatTest.lean`: one `#guard` per case, each with what
CPython gives for it: the string, or the exception class and its message, or "not modelled" for
what the port doesn't model (a string that holds a lone surrogate, a MemoryError, a string longer
than 2^24 characters).  The cases are long type names in messages, the corner cases of `CORNERS`
and `TOO_LONG` below, and a sample of random cases: random values (ints up to 10^50, floats from
random bits, subnormals, zeros, infinities, NaNs, ties, strs with non-ASCII characters) with random
specs from the grammar `[[fill]align][sign][z][#][0][width][grouping][.precision][type]`, and
invalid specs.

Run it with CPython 3.12, from the package root:

    python3.12 StrataPythonTest/Dyn/Sem/gen_format_cases.py

With `--jsonl FILE --count N`, it writes the cases of `CORNERS` and N random cases to FILE
instead, one JSON object per line, for a differential run of the Lean functions against CPython:

    {"k": "int" | "float" | "str", "v": value, "s": spec, "r": result}

where the value of an int is its decimal digits, the value of a float is its IEEE 754 bits as 16
hexadecimal digits, and the result is `["ok", string]`, `["raise", class, message]` or `["nm"]`.

Any other version than 3.12.15 is refused: the strings and the messages are 3.12.15's (its
`INT_MAX - 1024` bound on float precisions is new in 3.12.15).
"""

import argparse
import json
import random
import struct
import sys
import unicodedata
from pathlib import Path

if sys.version_info[:3] != (3, 12, 15):
    sys.exit(f"gen_format_cases.py needs CPython 3.12.15, not {sys.version.split()[0]}")

OUT = Path(__file__).resolve().parent / "FormatTest.lean"

# The number of random cases in FormatTest.lean, and the longest expected string among them.
LEAN_RANDOM_CASES = 400
LEAN_MAX_OUTPUT = 80


def bits_of(x):
    """The IEEE 754 bits of the float `x`."""
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def float_of(b):
    """The float with the IEEE 754 bits `b`."""
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def decimal(n):
    """The decimal digits of the int `n`, however many: the limit on digits stays 4300 for the
    calls of `format`."""
    sys.set_int_max_str_digits(0)
    try:
        return str(n)
    finally:
        sys.set_int_max_str_digits(4300)


def has_lone_surrogate(s):
    """Whether the str `s` holds a code point from 0xD800 to 0xDFFF."""
    return any(0xD800 <= ord(c) <= 0xDFFF for c in s)


def result_of(f):
    """What CPython gives for the call `f()`."""
    try:
        out = f()
    except MemoryError:
        return ["nm"]  # the port doesn't model running out of memory
    except Exception as e:  # noqa: BLE001 -- every exception is a result to record
        return ["raise", type(e).__name__, str(e)]
    if has_lone_surrogate(out):
        return ["nm"]
    return ["ok", out]


def run(kind, value, spec):
    """What CPython gives for `format(value, spec)`, where `value` is an int, a float's bits, or a
    str."""
    v = float_of(value) if kind == "float" else value
    return result_of(lambda: format(v, spec))


# ---------------------------------------------------------------------------------------------
# Random values and specs

FILLS = [" ", "*", "0", "x", "_", ",", ".", "<", "=", "{", "é", "中", "😀"]
STR_CHARS = list("abcXYZ019 .,_-") + ["é", "ß", "中", "😀", "\t", "𐒠"]
INT_TYPES = list("bcdoxXn") + list("eEfFgG%")
FLOAT_TYPES = list("eEfFgGn%")
BAD_TYPES = list("sqrSaiu ") + ["é", "😀", "\x00", "\x01"]
GARBAGE = list("0123456789<>=^+- z#,._xsfdg%éQ")


def random_int(rng):
    """A random int: small, around a bound of CPython's, or up to 10^50, of either sign."""
    pick = rng.random()
    if pick < 0.3:
        n = rng.randint(-1000, 1000)
    elif pick < 0.4:
        n = rng.choice([0, 1, -1, 0x10FFFF, 0x110000, 0xD7FF, 0xE000, 2**63 - 1, 2**63,
                        -(2**63), -(2**63) - 1, 2**53 + 1, 2**1024 - 2**970 - 1, 2**1024,
                        10**16, 10**17 + 1, 255, 4095, 65535])
    else:
        n = rng.randint(0, 10 ** rng.randint(1, 50))
        if rng.random() < 0.4:
            n = -n
    return n


def random_float_bits(rng):
    """The bits of a random float: random bits, a subnormal, a special value, a tie, a value
    with few digits, or random bits with a moderate exponent."""
    pick = rng.random()
    if pick < 0.3:
        return rng.getrandbits(64)
    if pick < 0.4:
        return (rng.getrandbits(1) << 63) | rng.getrandbits(52)  # subnormal or zero
    if pick < 0.5:
        return bits_of(rng.choice([0.0, -0.0, float("inf"), float("-inf"), 0.125, 2.5, 0.5,
                                   1.5, 1e16, 1e-5, 1e-4, 0.0001, 123.0, 0.1, 1 / 3, 9.995,
                                   0.0005, 1e22, 1e23, 5e-324, 1.7976931348623157e308,
                                   2.2250738585072014e-308, 1e300, 100.0, 999999.5]))
    if pick < 0.53:
        return rng.choice([0x7FF8000000000000, 0xFFF8000000000000, 0x7FF0000000000001])
    if pick < 0.65:
        # A tie at some digit: an integer and a half, or a short binary fraction.
        if rng.random() < 0.5:
            x = rng.randint(0, 10**6) + 0.5
        else:
            x = rng.randint(0, 2**10) / 2 ** rng.randint(1, 10)
        return bits_of(-x if rng.random() < 0.3 else x)
    if pick < 0.85:
        # A value with a few decimal digits, as a program writes it.
        x = float(f"{rng.randint(0, 10**rng.randint(1, 8))}e{rng.randint(-12, 12)}")
        return bits_of(-x if rng.random() < 0.3 else x)
    # A float with a moderate exponent, so that 'f' stays short.
    biased = rng.randint(1023 - 40, 1023 + 60)
    return (rng.getrandbits(1) << 63) | (biased << 52) | rng.getrandbits(52)


def random_str(rng):
    """A random str of up to 8 characters."""
    return "".join(rng.choice(STR_CHARS) for _ in range(rng.randint(0, 8)))


def random_spec(rng, kind, types):
    """A random spec from the grammar for a value of the kind `kind`, with a type from `types` or
    none.  The options that the type doesn't allow are rare, so that most specs are valid."""
    t = rng.choice(types) if rng.random() < 0.85 else ""
    numeric = kind != "str"
    precise = kind != "int" or (t != "" and t in "eEfFgG%")
    rare = 0.03
    spec = ""
    if rng.random() < 0.5:
        if rng.random() < 0.4:
            spec += rng.choice(FILLS)
        spec += rng.choice("<>=^" if numeric or rng.random() < rare else "<>^")
    if rng.random() < (0.3 if numeric else rare):
        spec += rng.choice("+- ")
    if rng.random() < (0.1 if numeric else rare):
        spec += "z"
    if rng.random() < (0.2 if numeric else rare):
        spec += "#"
    if rng.random() < 0.2:
        spec += "0"
    if rng.random() < 0.6:
        spec += str(rng.choice([rng.randint(0, 30), rng.randint(0, 30), rng.randint(30, 120)]))
    if rng.random() < (0.25 if numeric else rare):
        spec += rng.choice(",_")
    if rng.random() < (0.4 if precise else rare):
        p = rng.choice([rng.randint(0, 20), rng.randint(0, 20), rng.randint(20, 60), 1100, 1200])
        spec += "." + str(p)
    return spec + t


def random_bad_spec(rng, kind):
    """A random spec that is mostly not valid: garbage, or a bad type."""
    if rng.random() < 0.5:
        return "".join(rng.choice(GARBAGE) for _ in range(rng.randint(1, 4)))
    return random_spec(rng, kind, BAD_TYPES)


def random_case(rng):
    """A random case: its kind, value and spec."""
    pick = rng.random()
    if pick < 0.35:
        kind, value, types = "int", random_int(rng), INT_TYPES
    elif pick < 0.8:
        kind, value, types = "float", random_float_bits(rng), FLOAT_TYPES
    else:
        kind, value, types = "str", random_str(rng), ["s"]
    if rng.random() < 0.1:
        spec = random_bad_spec(rng, kind)
    elif rng.random() < 0.05:
        spec = ""
    else:
        spec = random_spec(rng, kind, types)
    return kind, value, spec


# ---------------------------------------------------------------------------------------------
# Corner cases: groups of cases, each with what its cases show.
CORNERS = [
    ("repr of an int", [
        ("int", 0, ""), ("int", -(10**30), "")]),
    ("an int with more than 4300 digits has no repr: ValueError; the sign doesn't count", [
        ("int", 10**4300, ""), ("int", 10**4300 - 1, ""), ("int", -(10**4300 - 1), ""),
        ("int", 2**14400, "")]),
    ("the limit on digits is for decimal digits only", [
        ("int", 2**14400, "x"), ("int", 10**4300, "d"), ("int", 10**4300, ",")]),
    ("repr of a float; a NaN has no sign", [
        ("float", bits_of(0.0), ""), ("float", bits_of(-0.0), ""),
        ("float", bits_of(float("inf")), ""), ("float", bits_of(float("-inf")), ""),
        ("float", 0xFFF8000000000000, "")]),
    ("repr has an exponent from 1e16 on and below 1e-4", [
        ("float", bits_of(1e16), ""), ("float", bits_of(9999999999999998.0), ""),
        ("float", bits_of(1e-5), ""), ("float", bits_of(0.0001), ""),
        ("float", bits_of(123.0), "")]),
    ("repr has the shortest digits that read back as the float", [
        ("float", bits_of(0.1), ""), ("float", bits_of(1 / 3), ""), ("float", 1, ""),
        ("float", bits_of(1.7976931348623157e308), ""), ("float", bits_of(2e16 + 8), "")]),
    ("specs that don't parse", [
        ("int", 1, "xx"), ("int", 1, "1."), ("int", 1, ",_"), ("int", 1, "_,"),
        ("int", 1, "9223372036854775808"), ("float", bits_of(1.0), ".9223372036854775808")]),
    ("the second ',' is the type", [
        ("int", 1, ",,")]),
    ("a width at PY_SSIZE_T_MAX is read, and CPython raises MemoryError", [
        ("int", 1, "9223372036854775807x")]),
    ("widths in other decimal digits: Arabic-Indic and mathematical", [
        ("int", 5, "١٠"), ("int", 5, "𝟙𝟚")]),
    ("a NUL type: no type for a float, an unknown type otherwise", [
        ("int", 5, "\x00"), ("float", bits_of(1.5), "\x00"), ("str", "abc", "\x00")]),
    ("a type outside '!' to '~' shows in hexadecimal", [
        ("int", 1, ".2 "), ("int", 1, "é"), ("int", 1, "😀")]),
    ("separators go with the types d e f g E G % F and none; '_' also with b o x X", [
        ("int", 1, ",c"), ("int", 1, ",x"), ("int", 0xABCDEF, "_x"), ("int", 1, "_n"),
        ("float", bits_of(1.0), ",n"), ("str", "abc", ","), ("str", "abc", "_")]),
    ("fills and alignments; a '0' after a fill is part of the width", [
        ("int", 1, "<<5"), ("int", 1, "0<5"), ("int", -1, "x=05"), ("int", -1, "=05"),
        ("int", -1, "<05"), ("str", "ab", "05")]),
    ("zero padding is grouped too, without a separator in front", [
        ("int", 1234, "08,"), ("int", 1234, "09,"), ("int", 1234, "010,"),
        ("int", -1234, "010_"), ("int", 0xFFFFF, "#012_x")]),
    ("prefixes and signs; 'X' makes the prefix upper case, and '#' adds none to decimals", [
        ("int", 255, "#_X"), ("int", -255, "#o"), ("int", 5, "#b"), ("int", -5, "+d"),
        ("int", 5, " d"), ("int", 5, "#d")]),
    ("'n' in the C locale: no grouping", [
        ("int", 1234567, "n"), ("float", bits_of(1234.5), "n")]),
    ("no precision and no 'z' for the int types; an unknown type", [
        ("int", 1, ".2"), ("int", 1, "z"), ("int", 1, "Q")]),
    ("'c' is laid out like a number, without a sign or '#'", [
        ("int", 65, "05c"), ("int", 65, "^5c"), ("int", 0, "c"), ("int", 0x10FFFF, "c"),
        ("int", 1, "+c"), ("int", 1, "#c")]),
    ("'c' first converts to a C long", [
        ("int", 2**63, "c"), ("int", -(2**63), "c"), ("int", -1, "c"), ("int", 0x110000, "c")]),
    ("'c' on a lone surrogate: not modelled", [
        ("int", 0xD800, "c")]),
    ("an int converts to a float, rounding ties to even, for e E f F g G %", [
        ("int", 2**53 + 1, "f"), ("int", 2**53 + 3, "f"), ("int", 7, "%"),
        ("int", 2**1024 - 2**970 - 1, "e")]),
    ("the conversion overflows from 2^1024 - 2^970 on", [
        ("int", 2**1024, "e"), ("int", 2**1024 - 2**970, "f")]),
    ("'z' is allowed once an int formats as a float", [
        ("int", 0, "z.1f")]),
    ("'e' has 6 digits past the point by default", [
        ("float", bits_of(1.5), "e"), ("float", bits_of(0.0), "e"), ("float", 1, "e")]),
    ("ties round to even; 2.675 and 9.995 are below the tie", [
        ("float", bits_of(0.125), ".2f"), ("float", bits_of(0.375), ".2f"),
        ("float", bits_of(2.5), ".0f"), ("float", bits_of(3.5), ".0f"),
        ("float", bits_of(0.5), ".0f"), ("float", bits_of(2.675), ".2f"),
        ("float", bits_of(9.995), ".2f")]),
    ("digits of the exact binary value", [
        ("float", bits_of(0.1), ".30f"), ("float", bits_of(1e300), ".3e"),
        ("float", bits_of(1e22), "f")]),
    ("more digits than any float has", [
        ("float", bits_of(0.5), ".1100e")]),
    ("'g' without '#' drops trailing zeros, so a precision over 2 ^ 24 gives a short string", [
        ("float", bits_of(1.0), ".16777217g"), ("float", bits_of(0.1), ".2000g"),
        ("float", bits_of(0.1), ".16777217")]),
    ("the digits of a large number in a power-of-two base, grouped", [
        ("int", 2**3001 - 12345, "x"), ("int", -(2**2000 + 1), "_b"),
        ("int", 3**2000, "#_o"), ("int", 2**4096, "X")]),
    ("a negative value that shows as zero keeps its sign, unless 'z'", [
        ("float", bits_of(-0.001), ".1f"), ("float", bits_of(-0.001), "z.1f"),
        ("float", bits_of(-0.0), "z"), ("float", bits_of(-0.0), "z.3e"),
        ("float", bits_of(-1e-300), "z.2e")]),
    ("'g' has an exponent below 1e-4 and from 10 ^ precision on; rounding may add a digit", [
        ("float", bits_of(9.9999), ".3g"), ("float", bits_of(0.0001), "g"),
        ("float", bits_of(0.00001), "g"), ("float", bits_of(123456.0), "g"),
        ("float", bits_of(1234567.0), "g"), ("float", bits_of(1.0), ".0g")]),
    ("'#' keeps the point and the trailing zeros", [
        ("float", bits_of(0.3), "#.0f"), ("float", bits_of(1.0), "#g"),
        ("float", bits_of(1.5), ".0e"), ("float", bits_of(1.5), "#.0e")]),
    ("no type with a precision is 'g' with '.0' on integers, and an exponent one digit earlier", [
        ("float", bits_of(100.0), ".3"), ("float", bits_of(10.0), ".3"),
        ("float", bits_of(1.0), "#.3"), ("float", bits_of(1.0), ".0")]),
    ("'#' with no type keeps the point of repr", [
        ("float", bits_of(1e16), "#")]),
    ("grouping and zero padding of a float", [
        ("float", bits_of(1234567.891), ",.2f"), ("float", bits_of(1234567.891), "_"),
        ("float", bits_of(-1234.5), "015,.1f"), ("float", bits_of(-1.5), "010"),
        ("float", bits_of(1.5), "^+10.3e")]),
    ("'%' formats the value times 100 with 'f'; 1e307 times 100 overflows to inf", [
        ("float", bits_of(0.5), "%"), ("float", bits_of(0.5), ".0%"),
        ("float", bits_of(1e307), "%"), ("float", bits_of(float("inf")), "%")]),
    ("inf and nan: zero padding, upper case, signs and separators", [
        ("float", bits_of(float("inf")), "010"), ("float", bits_of(float("-inf")), "F"),
        ("float", bits_of(float("inf")), "E"), ("float", 0x7FF8000000000000, "G"),
        ("float", 0xFFF8000000000000, "+"), ("float", bits_of(float("inf")), ",")]),
    ("a precision over INT_MAX, then over INT_MAX - 1024", [
        ("float", bits_of(1.0), ".2147483648f"), ("float", bits_of(1.0), ".2147482624f")]),
    ("int types on a float", [
        ("float", bits_of(1.0), "d"), ("float", bits_of(1.0), "x")]),
    ("alignments of a str; centering puts the extra fill on the right", [
        ("str", "abc", ""), ("str", "abc", "^7"), ("str", "abc", "*^8"), ("str", "abc", ">5")]),
    ("a precision truncates a str", [
        ("str", "abcdef", ".2"), ("str", "abcdef", "5.2")]),
    ("widths count code points", [
        ("str", "中😀é", "x^8")]),
    ("what a str spec can't have", [
        ("str", "abc", "+"), ("str", "abc", " "), ("str", "abc", "z"), ("str", "abc", "#"),
        ("str", "abc", "="), ("str", "abc", "d")]),
]

# Cases that the port leaves unmodelled although CPython gives a string: a result longer than
# 2^24 characters (`Format.maxLength`).  CPython raises MemoryError for one too long for the memory.
TOO_LONG = [
    ("int", 1, str(2**24 + 1), "a width over 2^24"),
    ("float", bits_of(1.0), "." + str(2**24 + 1) + "f", "a precision over 2^24"),
    ("str", "a", str(2**24 + 1), None),
]

# Values whose Lean expression is not their literal.
LEAN_INT_EXPRS = {
    10**4300: "10 ^ 4300",
    10**4300 - 1: "10 ^ 4300 - 1",
    -(10**4300 - 1): "-(10 ^ 4300 - 1)",
    2**1024: "2 ^ 1024",
    2**1024 - 2**970: "2 ^ 1024 - 2 ^ 970",
    2**1024 - 2**970 - 1: "2 ^ 1024 - 2 ^ 970 - 1",
    2**14400: "2 ^ 14400",
}

# ---------------------------------------------------------------------------------------------
# Lean output

def lean_char_ok(c):
    """Whether `c` can stand for itself in a Lean string literal."""
    o = ord(c)
    if c in '"\\':
        return False
    if 0x20 <= o < 0x7F:
        return True
    return o >= 0x80 and c != "\ufffd" and unicodedata.category(c)[0] in "LNPS"


def lean_escape(c, quote='"'):
    """The character `c` inside a Lean literal between the quotes `quote`, or None if a literal
    can't write it (outside the BMP, and not a letter, digit, punctuation or symbol)."""
    o = ord(c)
    if c in quote + "\\":
        return "\\" + c
    if c in "\"'":
        return c
    if lean_char_ok(c):
        return c
    if c == "\n":
        return "\\n"
    if c == "\t":
        return "\\t"
    if o < 0x80:
        return f"\\x{o:02x}"
    if o <= 0xFFFF:
        return f"\\u{o:04x}"
    return None


def lean_char(c):
    """The character `c` as a Lean term."""
    e = lean_escape(c, "'")
    return f"'{e}'" if e is not None else f"(Char.ofNat 0x{ord(c):X})"


# A run of one character at least this long is written with `List.replicate`.
LEAN_RUN = 32


def lean_str(s):
    """`s` as a Lean term: a string literal, or literals, runs of one character (`List.replicate`)
    and the characters that a literal can't write, joined by `++`."""
    parts, lit = [], []

    def flush():
        if lit:
            parts.append('"' + "".join(lit) + '"')
            lit.clear()

    i = 0
    while i < len(s):
        c = s[i]
        j = i
        while j < len(s) and s[j] == c:
            j += 1
        e = lean_escape(c)
        if j - i >= LEAN_RUN:
            flush()
            parts.append(f"String.ofList (List.replicate {j - i} {lean_char(c)})")
        elif e is None:
            flush()
            parts += [f"(Char.ofNat 0x{ord(c):X}).toString"] * (j - i)
        else:
            lit += [e] * (j - i)
        i = j
    flush()
    if not parts:
        return '""'
    if len(parts) == 1 and parts[0].startswith('"'):
        return parts[0]
    return "(" + " ++ ".join(parts) + ")"


def lean_call(kind, value, spec):
    """The Lean call for `format(value, spec)`."""
    if kind == "int":
        v = LEAN_INT_EXPRS.get(value) or decimal(value)
        if v.startswith("-") or " " in v:
            v = f"({v})"
        return f"formatInt {v} {lean_str(spec)}"
    if kind == "float":
        return f"formatFloat 0x{value:016X} {lean_str(spec)}"
    return f"formatStr {lean_str(value)} {lean_str(spec)}"


def lean_guard(kind, value, spec, result):
    """The `#guard` of a case, with the float's repr in a comment; the expectation goes on its own
    line if the line would be longer than 100 characters."""
    call = lean_call(kind, value, spec)
    comment = f"  -- {float_of(value)!r}" if kind == "float" else ""
    if result[0] == "nm":
        return f"#guard unmodelled ({call}){comment}"
    if result[0] == "ok":
        head, expected = f"#guard gives ({call})", lean_str(result[1])
    else:
        head, expected = f'#guard raises ({call}) "{result[1]}"', lean_str(result[2])
    line = f"{head} {expected}{comment}"
    return line if len(line) <= 100 else f"{head}{comment}\n  {expected}"


HEADER = '''/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Format
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Format

set_option autoImplicit false

/-!
# The formatting of ints, floats and strs

Generated by `gen_format_cases.py`; do not edit.  Each expected string or exception is what
CPython 3.12.15 gives for the same `format(value, spec)`.  "Not modelled" stands for CPython's
`MemoryError`, for a str that holds a lone surrogate, and for a str longer than `2 ^ 24`
characters.  First come long type names in messages, then the corner cases, each group with what
it shows, then random cases.  A float is given by its bits, with its `repr` in a comment.
-/

namespace StrataPython.Dyn.Sem.FormatTest

open StrataPython.Dyn.Sem.Format

/-- `r` is the string `s`. -/
def gives (r : Except Failure String) (s : String) : Bool := r.toOption == some s

/-- `r` is CPython raising the exception class `cls` with the message `msg`. -/
def raises (r : Except Failure String) (cls msg : String) : Bool :=
  match r with
  | .error e => e == .raise cls msg
  | .ok _ => false

/-- `r` is a case that the port doesn't model. -/
def unmodelled (r : Except Failure String) : Bool :=
  match r with
  | .error (.notModelled _) => true
  | _ => false

-- The type name in a message is cut at 200 bytes of UTF-8, as `%.200s` cuts it.
'''

FOOTER = '''
end StrataPython.Dyn.Sem.FormatTest
'''


def named_type_guards():
    """Cases for a type name in a message: an int subclass with a long name, cut by `%.200s`."""
    lines = []
    for name in ["a" * 210, "é" * 150, "a" + "é" * 150, "中" * 70]:
        cls = type(name, (int,), {})
        result = result_of(lambda: format(cls(5), "Q"))
        assert result[0] == "raise", result
        lines.append("#guard")
        lines.append(f"  let name := {lean_str(name)}")
        lines.append(f"  raises (do formatIntSpec 5 (← parseSpec \"Q\" name 'd' '>') name)"
                     f' "{result[1]}"')
        lines.append(f"    {lean_str(result[2])}")
    return lines


STR_REPRS = [
    "", "a", "'", '"', "'\"", "it's", 'say "x"', "\\", "a\\'b", "\t\n\r", "\x00\x1f\x7f",
    "\x80\x9f\xa0\xad\xff", "é中😀", "\u0378\u2028\u3000\ufeff\uffff", "\U000e0001\U0010ffff",
    "\U0001f600\U000e0100", " ~", "\u0300a", "a\x0bb\x0cc",
]


def random_repr_str(rng):
    """A random str, with characters from every plane, and no lone surrogate."""
    out = []
    for _ in range(rng.randrange(1, 12)):
        r = rng.random()
        if r < 0.3:
            cp = rng.randrange(0x00, 0x100)
        elif r < 0.7:
            cp = rng.randrange(0x100, 0x10000)
        else:
            cp = rng.randrange(0x10000, 0x110000)
        if 0xD800 <= cp <= 0xDFFF:
            cp = 0x41
        out.append(chr(cp))
    return "".join(out)


def str_repr_guards():
    """Cases of `repr` of a str: the corner cases, then random strs."""
    lines = []
    rng = random.Random(3_12_15)
    for s in STR_REPRS + [random_repr_str(rng) for _ in range(150)]:
        line = f"#guard strRepr {lean_str(s)} == {lean_str(repr(s))}"
        lines.append(line if len(line) <= 100 else
                     f"#guard strRepr {lean_str(s)} ==\n  {lean_str(repr(s))}")
    return lines


def write_lean():
    """Write FormatTest.lean."""
    lines = [HEADER.rstrip("\n")]
    lines += named_type_guards()
    lines.append("")
    lines.append("/-! ## repr of a str -/")
    lines.append("")
    lines += str_repr_guards()
    lines.append("")
    lines.append("/-! ## Corner cases -/")
    for note, cases in CORNERS:
        lines.append("")
        lines.append(f"-- {note[0].upper()}{note[1:]}.")
        for kind, value, spec in cases:
            lines.append(lean_guard(kind, value, spec, run(kind, value, spec)))
    lines.append("")
    lines.append("/-! ## Results over 2^24 characters, which are not modelled -/")
    for kind, value, spec, note in TOO_LONG:
        result = run(kind, value, spec)
        assert result[0] == "ok" and len(result[1]) > 2**24, result[:1]
        if note:
            lines.append("")
            lines.append(f"-- {note[0].upper()}{note[1:]}.")
        lines.append(f"#guard unmodelled ({lean_call(kind, value, spec)})")
    lines.append("")
    lines.append("/-! ## Random cases -/")
    lines.append("")
    rng = random.Random(3_12_15)
    seen = set()
    picked = []
    while len(picked) < LEAN_RANDOM_CASES:
        kind, value, spec = random_case(rng)
        result = run(kind, value, spec)
        if result[0] == "ok" and len(result[1]) > LEAN_MAX_OUTPUT:
            continue
        if (kind, value, spec) in seen:
            continue
        seen.add((kind, value, spec))
        picked.append(lean_guard(kind, value, spec, result))
    lines += picked
    lines.append(FOOTER.rstrip("\n"))
    OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_jsonl(path, count, seed):
    """Write `count` random cases, and the corner cases, to `path` as JSON lines."""
    rng = random.Random(seed)
    cases = [case for _, group in CORNERS for case in group]
    cases += [random_case(rng) for _ in range(count)]
    with open(path, "w", encoding="utf-8") as f:
        for kind, value, spec in cases:
            v = f"{value:016X}" if kind == "float" else decimal(value) if kind == "int" else value
            obj = {"k": kind, "v": v, "s": spec, "r": run(kind, value, spec)}
            f.write(json.dumps(obj, ensure_ascii=False) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--jsonl", help="write random cases to this file instead")
    parser.add_argument("--count", type=int, default=20000, help="the number of random cases")
    parser.add_argument("--seed", type=int, default=0, help="the seed of the random cases")
    args = parser.parse_args()
    if args.jsonl:
        write_jsonl(args.jsonl, args.count, args.seed)
    else:
        write_lean()


if __name__ == "__main__":
    main()
