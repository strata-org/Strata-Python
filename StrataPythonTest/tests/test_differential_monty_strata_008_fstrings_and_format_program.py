# Feature: f-strings (JoinedStr / FormattedValue) and format specs / conversions.
#
# Monty (pydantic-monty 0.0.18): f-strings are FULLY and faithfully supported —
#   simple interpolation, conversions !s/!r/!a, every format spec (width, align,
#   fill, precision, sign, bases b/o/x/X, :c/:d/:e/:f/:g/:%), nested specs, debug
#   `=`. Crucially Monty TYPE-CHECKS the spec against the value: f"{s:d}" on a str
#   raises ValueError, exactly like CPython (see crates/monty/test_cases/fstring__*).
#
# Strata front end: TRANSLATES f-strings but loses information:
#   - JoinedStr  (PythonToLaurel.lean:756): concat parts via Any..as_string! + StrConcat.
#   - FormattedValue (line 740): `to_string_any` of the value; the CONVERSION flag
#     (3rd field) and the FORMAT_SPEC (4th field) are matched as `_` and DROPPED.
#   Consequence: the result is modeled as an abstract str (sound at the TYPE level
#   for plain interpolation) but the format-spec/value type compatibility that
#   Monty/CPython enforce at runtime is NOT modeled — so a spec type error like
#   f"{s:d}" on a str is silently accepted.
#
# Frontend documented stance (frontend-subset.md): "f-string format specs with
#   expressions ... is OUT" (line 424) and listed under "may grow" (line 522).
#   So specs are *supposed* to be rejected, but the front end drops them instead.
#
# Result: basic interpolation is soundly verifiable (A-flavored); format
#   specs/conversions are silently unsound today (B). Classified (B) — the
#   dangerous case dominates. See analysis.md.


def good(x: int, name: str) -> list:
    # All of these run identically on Monty and CPython.
    return [
        f"{name} = {x}",     # basic interpolation     -> "hi = 7"
        f"{x:04d}",          # zero-padded width       -> "0007"
        f"{x:+d}",           # explicit sign           -> "+7"
        f"{name:>6}",        # right align width       -> "    hi"
        f"{name!r}",         # repr conversion         -> "'hi'"
        f"{3.14159:.2f}",    # float precision         -> "3.14"
    ]


def bad_spec(s: str) -> str:
    # Monty/CPython: ValueError("Unknown format code 'd' for object of type 'str'").
    # Strata encoding: spec dropped -> abstract str, NO error -> silently unsound.
    return f"{s:d}"          # NOT called from main(); exercised by the harness


def main() -> list:
    r = good(7, "hi")
    assert r == ["hi = 7", "0007", "+7", "    hi", "'hi'", "3.14"], "faithful formatting"
    return r


main()
