"""Write `NumberCases.lean`: CPython 3.12's `int(s, base)` and `float(s)` on test strings.

    python3.12 StrataPythonTest/Dyn/Sem/Library/gen_number_cases.py \
        > StrataPythonTest/Dyn/Sem/Library/NumberCases.lean

The strings are fixed examples (prefixes, underscores, signs, whitespace, Unicode digits and
spaces, the digit limit, inf and nan, rounding), decimals at and next to the exact midpoints
between adjacent doubles, and random strings over a pool of the characters that the readers
handle differently.
"""
import decimal
import math
import random
import struct
import sys

assert sys.version_info[:2] == (3, 12), "run with CPython 3.12"

INT_FIXED = [
    ("0", 10), ("-0", 10), ("+12", 10), (" 12 ", 10), ("\t\n12\x0b\x0c\r", 10), ("1_000", 10),
    ("1__0", 10), ("_1", 10), ("1_", 10), ("", 10), (" ", 10), ("-", 10), ("- 1", 10),
    ("12a", 10), ("ff", 16), ("FF", 16), ("0xff", 16), ("0x_ff", 16), ("0x", 16), ("0x_", 16),
    ("0xff", 0), ("0o17", 0), ("0b101", 0), ("0B1_0", 0), ("010", 0), ("00", 0), ("0_0", 0),
    ("0", 0), ("12", 0), ("-0x1f", 0), ("0x1f", 10), ("z", 36), ("Z", 36), ("10", 2), ("12", 2),
    ("١٢", 10), ("١_٢", 10), ("　 12 ", 10), ("12 ", 10), ("1\x00", 10),
    ("é", 10), ("1é", 10), ("𝟏𝟐", 10), ("٣", 0), ("1" * 4300, 10), ("1" * 4301, 10),
    ("1" * 5000, 16), ("1" * 641, 10), ("-" + "9" * 4301, 10), ("1" * 4301 + "\x00", 10),
    ("1" * 300 + "x", 10), ("x" * 300, 10), ("'", 10), ("\\", 10), ("\x7f", 10),
    ("1" * 3000, 2), ("0b" + "1" * 70, 0),
]

FLOAT_FIXED = [
    "0", "-0", "1.5", " 1.5 ", "1.", ".5", ".", "1e5", "1E+5", "1e-5", "1e", "1e+", "1ee5",
    "inf", "-inf", "+INF", "Infinity", "-infinity", "infinit", "nan", "-nan", "NaN", "nan1",
    "1_0.5", "1__0", "_1", "1_", "1_.5", "1._5", "1e1_0", "1_e5", "0x10", "1e1000000000",
    "1e-1000000000", "1e99999999999999999999", "0." + "0" * 400 + "1e400", "1" * 900 + "e-900",
    "22.22177891178025", "2.2250738585072011e-308", "4.9406564584124654e-324",
    "2.4703282292062327e-324", "2.4703282292062328e-324", "1.7976931348623157e308",
    "1.7976931348623159e308", "9007199254740993", "١.٥", "　 1.5 ", "1.5\x00", "",
    " ", "-", "+.e5", "1 2", "1.5é", "e5", "0e0", "-0.0", "00.00", "1_000_000.000_1",
    "0." + "5" * 1000, "1" + "0" * 2000, "\t-1.5e3\n", "1e0000000005", "1e-000000000000000000001",
    "0.0000e0005", "0." + "0" * 1000 + "1e1001",
]


def midpoint_cases():
    """Decimals at the exact midpoint between a double and the next one, and next to it: one
    above it by a 1 at the 801st and at the 1200th significant digit, and one below it by a unit
    of its last digit followed by 9s."""
    decimal.getcontext().prec = 2000
    out = []
    for x in (5e-324, 1e-310, 2.2250738585072014e-308, 0.1, 1.0, 9007199254740993.0,
              1e22, 1.7976931348623157e308):
        y = math.nextafter(x, math.inf)
        if math.isinf(y):
            # The midpoint above the largest double: half a unit above it.
            y_dec = decimal.Decimal(x) + (decimal.Decimal(x) - decimal.Decimal(
                math.nextafter(x, 0)))
        else:
            y_dec = decimal.Decimal(y)
        m = (decimal.Decimal(x) + y_dec) / 2
        digits, exp = m.as_tuple().digits, m.as_tuple().exponent
        ds = "".join(map(str, digits))
        def sci(ds, exp):
            return f"{ds[0]}.{ds[1:]}e{exp + len(ds) - 1}" if len(ds) > 1 else f"{ds}e{exp}"
        out.append(sci(ds, exp))
        for at in (801, 1200):
            pad = ds + "0" * max(0, at - 1 - len(ds))
            out.append(sci(pad + "1", exp - (len(pad) + 1 - len(ds))))
        below = str(int(ds) - 1) + "9" * 30
        out.append(sci(below, exp - 30))
    return out

INT_POOL = "0123456789abfxXoOb_+- \t ١"
FLOAT_POOL = "0123456789._eE+- infatyIN ٥"


def lean_str(s):
    out = []
    for c in s:
        if c == '"' or c == "\\":
            out.append("\\" + c)
        elif 0x20 <= ord(c) < 0x7f:
            out.append(c)
        elif ord(c) <= 0xFFFF:
            out.append(f"\\u{ord(c):04x}")
        else:
            out.append(c)
    return '"' + "".join(out) + '"'


def int_result(s, base):
    try:
        n = int(s, base)
    except ValueError as e:
        return f".error {lean_str(str(e))}"
    # Writing a long result needs no limit; reading `s` above had CPython's default limit.
    sys.set_int_max_str_digits(0)
    text = str(n)
    sys.set_int_max_str_digits(4300)
    return f".ok ({text})"


def float_result(s):
    try:
        bits = struct.unpack("<Q", struct.pack("<d", float(s)))[0]
        return f".ok {bits:#x}"
    except ValueError as e:
        return f".error {lean_str(str(e))}"


def cases():
    rng = random.Random(20261028)
    ints = list(INT_FIXED)
    for _ in range(300):
        s = "".join(rng.choice(INT_POOL) for _ in range(rng.randrange(1, 8)))
        ints.append((s, rng.choice([0, 2, 8, 10, 16, 36])))
    floats = list(FLOAT_FIXED) + midpoint_cases()
    for _ in range(300):
        floats.append("".join(rng.choice(FLOAT_POOL) for _ in range(rng.randrange(1, 9))))
    for _ in range(200):
        # Random decimals with 15 to 24 digits.
        digits = "".join(rng.choice("0123456789") for _ in range(rng.randrange(15, 25)))
        floats.append(f"{digits[0]}.{digits[1:]}e{rng.randrange(-330, 310)}")
    return ints, floats


ints, floats = cases()
print("""/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! Generated by `gen_number_cases.py` from CPython 3.12; do not edit. The results of `int(s,
base)` (the int, or the message of its `ValueError`) and of `float(s)` (the bits of the float, or
the message of its `ValueError`). -/

namespace StrataPython.Dyn.Sem.Library.NumberCases

public section
""")


def chunks(name, typ, items, size=150):
    parts = [items[i:i + size] for i in range(0, len(items), size)]
    for k, part in enumerate(parts):
        print(f"def {name}{k} : Array {typ} := #[")
        print(",\n".join(part))
        print("]\n")
    print(f"def {name} : Array {typ} := " + " ++ ".join(f"{name}{k}" for k in range(len(parts))))
    print()


chunks("intCases", "(String × Nat × Except String Int)",
       [f"  ({lean_str(s)}, {b}, {int_result(s, b)})" for s, b in ints])
chunks("floatCases", "(String × Except String UInt64)",
       [f"  ({lean_str(s)}, {float_result(s)})" for s in floats])
print("""end

end StrataPython.Dyn.Sem.Library.NumberCases""")
