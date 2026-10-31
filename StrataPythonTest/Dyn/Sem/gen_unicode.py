#!/usr/bin/env python3
"""Write the Unicode tables of the Python semantics, as CPython 3.12 has them.

Writes `StrataPython/Dyn/Sem/Generated/Unicode.lean`, from CPython 3.12's Unicode database
(Unicode 15.0):
* the ranges of code points for which `str.isprintable()` is true (CPython's
  `Py_UNICODE_ISPRINTABLE`, which `repr` of a `str` uses to decide what to escape);
* the zero digits of the runs of decimal digits (`Py_UNICODE_TODECIMAL`, which reads the widths
  and precisions of format specs).

It also writes `StrataPython/Dyn/Sem/Generated/LibraryUnicode.lean`, the tables of the
methods of `str` (`StrataPython/Dyn/Sem/Library/`):
* the ranges of the character classes of `str.isalpha`, `isdecimal`, `isdigit`, `isnumeric`,
  `isspace`, `isupper`, `islower`, `isidentifier` (its first character and the others), of
  titlecase letters (category Lt), of cased and case-ignorable characters (the two properties
  of the final-sigma rule of `lower`), and of line boundaries (`splitlines`);
* the case mappings of one character: `upper` and `lower` where they change it, `title` where it
  differs from `upper`, and `casefold` where it differs from `lower`, each as a list of code
  points.

Run it with CPython 3.12, from the package root:

    python3.12 StrataPythonTest/Dyn/Sem/gen_unicode.py [DIR]

With `DIR`, it writes the two files there instead (a test compares them with the checked-in
ones).

Any other version is refused: the tables are 3.12's.
"""

import sys
import unicodedata
from pathlib import Path

if sys.version_info[:2] != (3, 12):
    sys.exit(f"gen_unicode.py needs CPython 3.12, not {sys.version.split()[0]}")

GENERATED = Path(__file__).resolve().parents[3] / "StrataPython/Dyn/Sem/Generated"
OUT_DIR = Path(sys.argv[1]) if len(sys.argv) > 1 else GENERATED
OUT = OUT_DIR / "Unicode.lean"
LIB_OUT = OUT_DIR / "LibraryUnicode.lean"


def ranges(pred):
    """The maximal ranges `[lo, hi]` of code points that satisfy `pred`."""
    out = []
    start = None
    for cp in range(0x110000):
        ok = pred(cp)
        if ok and start is None:
            start = cp
        elif not ok and start is not None:
            out.append((start, cp - 1))
            start = None
    if start is not None:
        out.append((start, 0x10FFFF))
    return out


def chars():
    """Every code point that a Lean `Char` can hold: all but the surrogates."""
    return (cp for cp in range(0x110000) if not 0xD800 <= cp <= 0xDFFF)


def char_ranges(pred):
    """The maximal ranges of non-surrogate code points `cp` with `pred(chr(cp))`."""
    return ranges(lambda cp: not 0xD800 <= cp <= 0xDFFF and pred(chr(cp)))


def is_cased(c):
    """CPython's `_PyUnicode_IsCased`: the Unicode property Cased, which is Lowercase, Uppercase
    or category Lt; `str.islower` and `str.isupper` of one character are the first two."""
    return c.islower() or c.isupper() or unicodedata.category(c) == "Lt"


def is_case_ignorable(c):
    """CPython's `_PyUnicode_IsCaseIgnorable`, read from the final-sigma rule of `lower`: a capital
    sigma at the end of a word becomes a final sigma. Looking back from the sigma, `lower` skips
    case-ignorable characters and then needs a cased one; looking forward, it skips
    case-ignorable characters and then needs the end or a character that is not cased."""
    if is_cased(c):
        # Forward: the sigma is final only if `c` is skipped.
        return ("\u0391\u03a3" + c).lower()[1] == "\u03c2"
    # Backward: the sigma is final only if `c` is skipped, since the alpha before it is cased.
    return ("\u0391" + c + "\u03a3").lower()[-1] == "\u03c2"


def mapping(f, base=None):
    """`(cp, f(chr(cp)))` for every code point where `f` changes it, or differs from `base`."""
    out = []
    for cp in chars():
        c = chr(cp)
        m = f(c)
        if m != (base(c) if base else c):
            # `chars` in Library/Unicode.lean relies on this: a Lean `Char` holds no surrogate.
            assert not any(0xD800 <= ord(x) <= 0xDFFF for x in m), hex(cp)
            out.append((cp, [ord(x) for x in m]))
    return out


def check_against_c():
    """Check `is_cased` and `is_case_ignorable` against CPython's own C functions, which ctypes
    can call in CPython 3.12."""
    import ctypes

    def cfun(name):
        f = getattr(ctypes.pythonapi, name)
        f.restype, f.argtypes = ctypes.c_int, [ctypes.c_uint32]
        return f

    cased, ignorable = cfun("_PyUnicode_IsCased"), cfun("_PyUnicode_IsCaseIgnorable")
    for cp in chars():
        assert is_cased(chr(cp)) == bool(cased(cp)), hex(cp)
        assert is_case_ignorable(chr(cp)) == bool(ignorable(cp)), hex(cp)


def lean_ranges(name, doc, rs):
    lines = [f"/-- {doc} -/", f"def {name} : Array (Nat × Nat) := #["]
    for i, (lo, hi) in enumerate(rs):
        sep = "," if i + 1 < len(rs) else ""
        lines.append(f"  ({lo:#x}, {hi:#x}){sep}")
    return lines + ["]", ""]


def lean_map(name, doc, m, chunk=400):
    """A map as the concatenation of parts of `chunk` entries: one long array literal exceeds the
    elaborator's recursion depth."""
    parts = [m[i:i + chunk] for i in range(0, len(m), chunk)] or [[]]
    lines = []
    for k, part in enumerate(parts):
        lines.append(f"/-- Part {k} of `{name}`. -/")
        lines.append(f"def {name}{k} : Array (Nat × List Nat) := #[")
        for i, (cp, xs) in enumerate(part):
            sep = "," if i + 1 < len(part) else ""
            lines.append(f"  ({cp:#x}, [{', '.join(f'{x:#x}' for x in xs)}]){sep}")
        lines += ["]", ""]
    lines.append(f"/-- {doc} -/")
    # Joined as lists: the kernel's check that the keys increase unfolds an array join into
    # pushes, which would cost the square of the map's size.
    lines.append(f"def {name} : Array (Nat × List Nat) := ("
                 + " ++ ".join(f"{name}{k}.toList" for k in range(len(parts))) + ").toArray")
    return lines + [""]


def library_tables():
    """The tables of `LIB_OUT`."""
    check_against_c()
    # `isalnum` of one character is one of these four classes, so it needs no table.
    assert all(chr(cp).isalnum() == (chr(cp).isalpha() or chr(cp).isdecimal()
               or chr(cp).isdigit() or chr(cp).isnumeric()) for cp in chars())
    classes = [
        ("alphaRanges", "`str.isalpha()` of one character.", str.isalpha),
        ("decimalRanges", "`str.isdecimal()` of one character.", str.isdecimal),
        ("digitRanges", "`str.isdigit()` of one character.", str.isdigit),
        ("numericRanges", "`str.isnumeric()` of one character.", str.isnumeric),
        ("spaceRanges", "`str.isspace()` of one character.", str.isspace),
        ("upperRanges", "`str.isupper()` of one character: the property Uppercase.", str.isupper),
        ("lowerRanges", "`str.islower()` of one character: the property Lowercase.", str.islower),
        ("titleRanges", "The titlecase letters: category Lt.",
         lambda c: unicodedata.category(c) == "Lt"),
        ("casedRanges", "The cased characters (`_PyUnicode_IsCased`).", is_cased),
        ("caseIgnorableRanges", "The case-ignorable characters (`_PyUnicode_IsCaseIgnorable`).",
         is_case_ignorable),
        ("identStartRanges", "The characters that may start an identifier: `c.isidentifier()`.",
         str.isidentifier),
        ("identContinueRanges",
         "The characters that may continue an identifier: `('a' + c).isidentifier()`.",
         lambda c: ("a" + c).isidentifier()),
        ("lineBreakRanges", "The line boundaries of `str.splitlines`.",
         lambda c: len(("a" + c + "b").splitlines()) == 2),
    ]
    maps = [
        ("upperMap", "`str.upper()` of one character, where it changes it.",
         mapping(str.upper)),
        ("lowerMap", "`str.lower()` of one character, where it changes it. (For one character, the "
         "final-sigma rule never applies.)", mapping(str.lower)),
        ("titleMap", "`str.title()` of one character, where it differs from `str.upper()`.",
         mapping(str.title, str.upper)),
        ("casefoldMap", "`str.casefold()` of one character, where it differs from `str.lower()`.",
         mapping(str.casefold, str.lower)),
    ]
    lines = [
        "/-",
        "  Copyright Strata Contributors",
        "",
        "  SPDX-License-Identifier: Apache-2.0 OR MIT",
        "-/",
        "module",
        "",
        "set_option autoImplicit false",
        "",
        "/-!",
        "# Unicode tables of the methods of `str` (generated)",
        "",
        "Generated by `StrataPythonTest/Dyn/Sem/gen_unicode.py` from CPython 3.12",
        f"(Unicode {unicodedata.unidata_version}).  Do not edit: run the script again.  The ranges",
        "`(lo, hi)` are in order; the maps are sorted by their code point.",
        "-/",
        "",
        "namespace StrataPython.Dyn.Sem.Library.Unicode",
        "",
        "@[expose] public section",
        "",
    ]
    for name, doc, pred in classes:
        lines += lean_ranges(name, doc, char_ranges(pred))
    for name, doc, m in maps:
        lines += lean_map(name, doc, m)
    lines += ["end", "", "end StrataPython.Dyn.Sem.Library.Unicode", ""]
    return lines


def main():
    printable = ranges(lambda cp: chr(cp).isprintable())
    zeros = [cp for cp in range(0x110000) if unicodedata.decimal(chr(cp), None) == 0]
    # Each zero starts a run of the digits 0 to 9, and the runs hold every decimal digit.
    digits = {cp for cp in range(0x110000) if unicodedata.decimal(chr(cp), None) is not None}
    assert digits == {z + d for z in zeros for d in range(10)}
    assert all(unicodedata.decimal(chr(z + d)) == d for z in zeros for d in range(10))
    lines = [
        "/-",
        "  Copyright Strata Contributors",
        "",
        "  SPDX-License-Identifier: Apache-2.0 OR MIT",
        "-/",
        "module",
        "",
        "set_option autoImplicit false",
        "",
        "/-!",
        "# Unicode tables (generated)",
        "",
        "Generated by `StrataPythonTest/Dyn/Sem/gen_unicode.py` from CPython 3.12",
        f"(Unicode {unicodedata.unidata_version}).  Do not edit: run the script again.",
        "-/",
        "",
        "namespace StrataPython.Dyn.Sem.Unicode",
        "",
        "@[expose] public section",
        "",
        "/-- The ranges `(lo, hi)` of code points for which `str.isprintable()` is true, in order. -/",
        "def printableRanges : Array (Nat × Nat) := #[",
    ]
    for i, (lo, hi) in enumerate(printable):
        sep = "," if i + 1 < len(printable) else ""
        lines.append(f"  ({lo:#x}, {hi:#x}){sep}")
    lines += [
        "]",
        "",
        "/-- The code points of the zero digits: each one starts a run of the ten decimal digits 0 to 9,",
        "and these runs hold all the decimal digits. -/",
        "def decimalZeros : Array Nat := #[",
    ]
    for i in range(0, len(zeros), 10):
        chunk = ", ".join(f"{z:#x}" for z in zeros[i:i + 10])
        sep = "," if i + 10 < len(zeros) else ""
        lines.append(f"  {chunk}{sep}")
    lines += [
        "]",
        "",
        "end",
        "",
        "end StrataPython.Dyn.Sem.Unicode",
        "",
    ]
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text("\n".join(lines))
    print(f"wrote {OUT} ({len(printable)} ranges, {len(zeros)} zero digits)")
    LIB_OUT.write_text("\n".join(library_tables()))
    print(f"wrote {LIB_OUT}")


if __name__ == "__main__":
    main()
