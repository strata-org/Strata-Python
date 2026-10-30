#!/usr/bin/env python3
"""Write the tests of the arithmetic on ints, bools and floats, as CPython 3.12 computes it.

Writes `StrataPythonTest/Dyn/Sem/ArithTest.lean`: one `#guard` per case, each with what
CPython gives for it: the result, or the exception class and its message, or "not modelled" for
what the port doesn't model (a MemoryError, an int with more than 2^32 bits, a complex power, or
the OverflowError of a complex power).  The cases are the binary operators, the unary operators
and `abs`, `divmod`, the comparisons, `int()` of a float, `float()` of an int, and the indices of
slices.  First come the corner cases of `CORNERS` and `TOO_LARGE` below, then a sample of random
cases.

Run it with CPython 3.12, from the package root:

    python3.12 StrataPythonTest/Dyn/Sem/gen_arith_cases.py

With `--jsonl FILE --count N`, it writes the corner cases and N random cases to FILE instead, one
JSON object per line, for a differential run of the Lean functions against CPython:

    {"k": "bin" | "un" | "divmod" | "cmp", "op": name, "a": num, "b": num, "r": result}
    {"k": "int", "a": num, "r": result}       -- int(a) for a float a
    {"k": "float", "a": num, "r": result}     -- float(a) for an int or a bool a
    {"k": "slice", "start": i, "stop": i, "step": i, "len": n, "r": result}

where a number is `["bool", b]`, `["int", decimal digits]` or `["float", 16 hexadecimal digits of
its IEEE 754 bits]`, a slice bound is `null` or its decimal digits, and the result is `["ok",
num]`, `["ok2", num, num]` (divmod), `["bool", b]` (a comparison), `["slice", start, stop, step,
length]`, `["raise", class, message]` or `["nm", reason]`.

The indices of a slice come from CPython's own `PySlice_Unpack` and `PySlice_AdjustIndices`,
called through `ctypes`.

Any other version than 3.12.15 is refused: the results and the messages are 3.12.15's.
"""

import argparse
import ast
import ctypes
import json
import math
import operator
import random
import struct
import sys
import textwrap
import warnings
from pathlib import Path

if sys.version_info[:3] != (3, 12, 15):
    sys.exit(f"gen_arith_cases.py needs CPython 3.12.15, not {sys.version.split()[0]}")

# `~True` warns with a DeprecationWarning, which the port doesn't model (`run_un`).
warnings.simplefilter("ignore", DeprecationWarning)
sys.set_int_max_str_digits(0)

OUT = Path(__file__).resolve().parent / "ArithTest.lean"

# The number of random cases in ArithTest.lean, and the most digits of an int in them.
LEAN_RANDOM_CASES = 700
LEAN_MAX_DIGITS = 60

# The bounds of the port (`Arith.maxBits`, `Arith.maxLongDigits`, `Format.ssizeMax`).
MAX_BITS = 2**32
SSIZE_MAX = 2**63 - 1
SSIZE_MIN = -(2**63)
MAX_LONG_DIGITS = (SSIZE_MAX - 24) // 4


def bits_of(x):
    """The IEEE 754 bits of the float `x`."""
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def float_of(b):
    """The float with the IEEE 754 bits `b`."""
    return struct.unpack("<d", struct.pack("<Q", b))[0]


class F:
    """A float given by its bits, so that a NaN keeps its payload and -0.0 its sign."""

    def __init__(self, bits):
        self.bits = bits

    def value(self):
        return float_of(self.bits)


def fl(x):
    """The float `x` as an `F`."""
    return F(bits_of(x))


def val(x):
    """The Python value of an operand: a bool, an int, or the float of an `F`."""
    return x.value() if isinstance(x, F) else x


def enc(v):
    """A Python number as JSON: `["bool", b]`, `["int", digits]` or `["float", hex bits]`."""
    if isinstance(v, bool):
        return ["bool", v]
    if isinstance(v, int):
        return ["int", str(v)]
    if isinstance(v, F):
        return ["float", f"{v.bits:016X}"]
    assert isinstance(v, float), v
    return ["float", f"{bits_of(v):016X}"]


# ---------------------------------------------------------------------------------------------
# The cases, run in CPython

BINOPS = {
    "add": (operator.add, "+"), "sub": (operator.sub, "-"), "mul": (operator.mul, "*"),
    "trueDiv": (operator.truediv, "/"), "floorDiv": (operator.floordiv, "//"),
    "mod": (operator.mod, "%"), "pow": (operator.pow, "**"), "lshift": (operator.lshift, "<<"),
    "rshift": (operator.rshift, ">>"), "and": (operator.and_, "&"), "or": (operator.or_, "|"),
    "xor": (operator.xor, "^"),
}
UNOPS = {"neg": (operator.neg, "-"), "pos": (operator.pos, "+"),
         "invert": (operator.invert, "~"), "abs": (abs, "abs")}
CMPOPS = {"eq": (operator.eq, "=="), "ne": (operator.ne, "!="), "lt": (operator.lt, "<"),
          "le": (operator.le, "<="), "gt": (operator.gt, ">"), "ge": (operator.ge, ">=")}


def int_bits(n):
    """The bits of the magnitude of the int `n`."""
    return abs(int(n)).bit_length()


def too_large(op, a, b):
    """Whether the port leaves `a op b` unmodelled for its size: an int result with more than
    2^32 bits (`Arith.intPowNat`, `Arith.intLshift`)."""
    if isinstance(a, F) or isinstance(b, F):
        return False
    a, b = int(a), int(b)
    if op == "pow" and b >= 0 and abs(a) >= 2:
        return abs(a).bit_length() * b > MAX_BITS
    if op == "lshift" and b >= 0 and a != 0:
        clipped = b // 30 >= SSIZE_MAX // 4
        word, rem = (SSIZE_MAX // 4, 0) if clipped else (b // 30, b % 30)
        size = (abs(a).bit_length() - 1) // 30 + 1 + word + (1 if rem else 0)
        return size <= MAX_LONG_DIGITS and int_bits(a) + b > MAX_BITS
    return False


def safe_memory_error(op, a, b):
    """Whether CPython raises MemoryError for `a op b` at once, before using any memory: a shift
    whose result needs more bytes than any machine has."""
    return op == "lshift" and int_bits(a) + int(b) > 2**45


# The reasons that `Arith` gives for the cases it doesn't model.
TOO_LARGE_REASON = "an int with more than 2 ^ 32 bits"
COMPLEX_REASON = "a complex power"
ERRNO_REASON = "the OverflowError of a float power, which has an errno"
INVERT_BOOL_REASON = "~ on a bool, which warns"


def result_of(f, pair=False):
    """What CPython gives for the call `f()`."""
    try:
        out = f()
    except MemoryError:
        return ["nm", TOO_LARGE_REASON]
    except OverflowError as e:
        if str(e) == "complex exponentiation":
            # The complex power of a negative float overflowed: the port models no complex power.
            return ["nm", COMPLEX_REASON]
        if len(e.args) == 2:
            # A float power's OverflowError carries an errno, which the port doesn't model.
            return ["nm", ERRNO_REASON]
        return ["raise", "OverflowError", str(e)]
    except Exception as e:  # noqa: BLE001 -- every exception is a result to record
        return ["raise", type(e).__name__, str(e)]
    if pair:
        return ["ok2", enc(out[0]), enc(out[1])]
    if isinstance(out, complex):
        return ["nm", COMPLEX_REASON]
    return ["ok", enc(out)]


def run_bin(op, a, b):
    """What CPython gives for `a op b`."""
    if too_large(op, a, b):
        if safe_memory_error(op, a, b):
            assert result_of(lambda: BINOPS[op][0](val(a), val(b)))[0] == "nm"
        return ["nm", TOO_LARGE_REASON]
    return result_of(lambda: BINOPS[op][0](val(a), val(b)))


def run_un(op, a):
    """What CPython gives for `op a`.  `~` on a bool is not modelled: it also warns, and the
    warning writes the module's `__warningregistry__`."""
    if op == "invert" and isinstance(val(a), bool):
        return ["nm", INVERT_BOOL_REASON]
    return result_of(lambda: UNOPS[op][0](val(a)))


def run_divmod(a, b):
    """What CPython gives for `divmod(a, b)`."""
    return result_of(lambda: divmod(val(a), val(b)), pair=True)


def run_cmp(op, a, b):
    """What CPython gives for `a op b`, a comparison."""
    out = CMPOPS[op][0](val(a), val(b))
    assert isinstance(out, bool)
    return ["bool", out]


def run_int(a):
    """What CPython gives for `int(a)`, for a float `a`."""
    return result_of(lambda: int(val(a)))


def run_float(a):
    """What CPython gives for `float(a)`, for an int or a bool `a`."""
    return result_of(lambda: float(a))


Py_ssize_t = ctypes.c_ssize_t
_unpack = ctypes.pythonapi.PySlice_Unpack
_unpack.argtypes = [ctypes.py_object] + [ctypes.POINTER(Py_ssize_t)] * 3
_unpack.restype = ctypes.c_int
_adjust = ctypes.pythonapi.PySlice_AdjustIndices
_adjust.argtypes = [Py_ssize_t, ctypes.POINTER(Py_ssize_t), ctypes.POINTER(Py_ssize_t), Py_ssize_t]
_adjust.restype = Py_ssize_t


def run_slice(start, stop, step, length):
    """What CPython's `PySlice_Unpack` and `PySlice_AdjustIndices` give for the slice
    `start:stop:step` of a sequence of `length` items.  For a short sequence, the indices are
    checked against what slicing a list gives."""
    a, o, s = Py_ssize_t(), Py_ssize_t(), Py_ssize_t()
    try:
        _unpack(slice(start, stop, step), ctypes.byref(a), ctypes.byref(o), ctypes.byref(s))
    except Exception as e:  # noqa: BLE001 -- every exception is a result to record
        if length <= 100:
            try:
                list(range(length))[start:stop:step]
                raise AssertionError("slicing a list doesn't raise")
            except ValueError as e2:
                assert str(e2) == str(e)
        return ["raise", type(e).__name__, str(e)]
    n = _adjust(length, ctypes.byref(a), ctypes.byref(o), s.value)
    if length <= 100:
        assert list(range(length))[start:stop:step] == [a.value + i * s.value for i in range(n)]
    return ["slice", a.value, o.value, s.value, n]


def run(case):
    """What CPython gives for a case."""
    kind = case[0]
    if kind == "bin":
        return run_bin(*case[1:])
    if kind == "un":
        return run_un(*case[1:])
    if kind == "divmod":
        return run_divmod(*case[1:])
    if kind == "cmp":
        return run_cmp(*case[1:])
    if kind == "int":
        return run_int(case[1])
    if kind == "float":
        return run_float(case[1])
    return run_slice(*case[1:])


# ---------------------------------------------------------------------------------------------
# Values whose Lean expression is not their literal: E("2**1000") registers one.

EXPRS = {}


# The precedences of Lean's operators, and of an atom.
LEAN_PREC = {ast.Add: 65, ast.Sub: 65, ast.Mult: 70, ast.Pow: 75}
LEAN_OPS = {ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.Pow: "^"}


def lean_of_ast(node):
    """The Lean expression of a Python expression made of ints, `+`, `-`, `*` and `**`, and its
    precedence.  `^` groups to the right, the others to the left; a negation is `-(...)`."""
    if isinstance(node, ast.Constant) and type(node.value) is int:
        return str(node.value), 100
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        inner, prec = lean_of_ast(node.operand)
        return (f"-{inner}" if prec == 100 else f"-({inner})"), 60
    if isinstance(node, ast.BinOp):
        prec = LEAN_PREC[type(node.op)]
        left, lp = lean_of_ast(node.left)
        right, rp = lean_of_ast(node.right)
        right_assoc = isinstance(node.op, ast.Pow)
        if lp < prec or (right_assoc and lp == prec):
            left = f"({left})"
        if rp < prec or (not right_assoc and rp == prec):
            right = f"({right})"
        return f"{left} {LEAN_OPS[type(node.op)]} {right}", prec
    raise ValueError(ast.dump(node))


def E(src):
    """The int that the Python expression `src` gives, registered with its Lean expression."""
    v = eval(src, {})  # noqa: S307 -- the sources are the constants below
    assert type(v) is int
    EXPRS[v] = (lean_of_ast(ast.parse(src, mode="eval").body)[0], src)
    return v


# ---------------------------------------------------------------------------------------------
# Random cases

SPECIAL_INTS = [0, 1, -1, 2, -2, 3, 7, -7, 10, 2**30, 2**30 - 1, 2**31, 2**52, 2**53 - 1, 2**53,
                2**53 + 1, 2**53 + 2, 2**53 + 3, 2**54 + 1, 2**62, 2**63 - 1, 2**63, -(2**63),
                2**64, 10**15, 10**16, 10**22, 10**23, 2**1023, 2**1024 - 2**970 - 1,
                2**1024 - 2**970, 2**1024, -(2**1024)]
SPECIAL_FLOATS = [0.0, -0.0, math.inf, -math.inf, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 1.5, 3.0,
                  0.1, 0.3, 1e16, 1e-300, 1e300, 5e-324, -5e-324, 2.2250738585072014e-308,
                  1.7976931348623157e308, -1.7976931348623157e308, 2.0**53, 2.0**53 + 2,
                  2.0**63, 2.0**64, 1e22, 0.7, 7.5, -7.5, 1 / 3, 2.0**-1074]
NANS = [0x7FF8000000000000, 0xFFF8000000000000, 0x7FF0000000000001, 0x7FF8000000000123]


def random_int(rng):
    """A random int: small, special, of up to 200 bits, or of up to 1100 bits."""
    pick = rng.random()
    if pick < 0.3:
        return rng.randint(-1000, 1000)
    if pick < 0.45:
        n = rng.choice(SPECIAL_INTS) + rng.choice([0, 0, 0, 1, -1])
    elif pick < 0.7:
        n = rng.getrandbits(rng.randint(1, 64))
    elif pick < 0.9:
        n = rng.getrandbits(rng.randint(1, 200))
    else:
        n = rng.getrandbits(rng.randint(900, 1100))
    return -n if rng.random() < 0.4 else n


def random_float(rng):
    """The bits of a random float: random bits, a special value, a NaN, a small integer, a value
    with a moderate exponent, a subnormal, or a value with few decimal digits."""
    pick = rng.random()
    if pick < 0.2:
        return F(rng.getrandbits(64))
    if pick < 0.35:
        return fl(rng.choice(SPECIAL_FLOATS))
    if pick < 0.38:
        return F(rng.choice(NANS))
    if pick < 0.5:
        return fl(float(rng.randint(-20, 20)))
    if pick < 0.7:
        biased = rng.randint(1023 - 60, 1023 + 60)
        return F((rng.getrandbits(1) << 63) | (biased << 52) | rng.getrandbits(52))
    if pick < 0.78:
        return F((rng.getrandbits(1) << 63) | rng.getrandbits(52))
    x = float(f"{rng.randint(0, 10**rng.randint(1, 8))}e{rng.randint(-12, 12)}")
    return fl(-x if rng.random() < 0.3 else x)


def random_num(rng):
    """A random bool, int or float."""
    pick = rng.random()
    if pick < 0.1:
        return rng.random() < 0.5
    if pick < 0.55:
        return random_int(rng)
    return random_float(rng)


def is_intlike(x):
    """Whether the operand is an int or a bool."""
    return not isinstance(x, F)


def random_bin(rng):
    """A random binary case, with exponents and shift counts that keep the results small."""
    op = rng.choice(list(BINOPS))
    a, b = random_num(rng), random_num(rng)
    if op == "pow" and is_intlike(a) and is_intlike(b) and b >= 0:
        if rng.random() < 0.1:
            a, b = rng.choice([0, 1, -1, True, False]), rng.getrandbits(rng.randint(1, 100))
        else:
            a = a if int_bits(a) <= 64 else rng.randint(-100, 100)
            b = rng.randint(0, 64)
    if op == "pow" and is_intlike(a) and isinstance(b, F) and rng.random() < 0.5:
        b = fl(float(rng.randint(-30, 30)) / rng.choice([1, 2, 4]))
    if op in ("lshift", "rshift") and is_intlike(a) and is_intlike(b):
        if rng.random() < 0.8:
            b = rng.randint(-3, 200)
        else:
            # A huge count: >> gives 0 or -1, and << raises OverflowError or MemoryError at once.
            b = rng.choice([2**45 + rng.getrandbits(40), 2**63 + rng.getrandbits(70)])
    if op in ("and", "or", "xor") and rng.random() < 0.3:
        a, b = rng.random() < 0.5, rng.random() < 0.5
    if op == "trueDiv" and is_intlike(a) and is_intlike(b) and rng.random() < 0.5:
        a, b = random_quotient(rng)
    return ("bin", op, a, b)


def random_quotient(rng):
    """Two ints whose quotient is near a rounding boundary: a tie, a subnormal, an overflow."""
    pick = rng.random()
    if pick < 0.3:
        # An exact tie or a near-tie: (2m + 1) * 2^j + d over 2^(j + 1).
        m = rng.getrandbits(53) | (1 << 52)
        j = rng.randint(0, 80)
        return ((2 * m + 1) << j) + rng.choice([0, 0, 1, -1]), 1 << (j + 1)
    if pick < 0.6:
        # A quotient with a random exponent, down to the subnormals and up to overflow.
        a = rng.getrandbits(rng.randint(1, 1200)) | 1
        b = rng.getrandbits(rng.randint(1, 1200)) | 1
        if rng.random() < 0.5:
            b <<= rng.randint(0, 1100)
        return a * rng.choice([1, -1]), b * rng.choice([1, 1, -1])
    if pick < 0.8:
        a = (2**1024 - 2**970) * rng.getrandbits(30) + rng.randint(-5, 5)
        return a, rng.getrandbits(30) or 1
    b = rng.getrandbits(rng.randint(1, 64)) or 1
    return rng.getrandbits(rng.randint(1, 1100)) * b + rng.randint(-1, 1), b


def random_cmp(rng):
    """A random comparison, often of an int near a float."""
    op = rng.choice(list(CMPOPS))
    if rng.random() < 0.6:
        f = random_float(rng)
        x = f.value()
        if math.isfinite(x) and rng.random() < 0.8:
            i = int(x) + rng.choice([-2, -1, 0, 0, 0, 1, 2])
        else:
            i = random_int(rng)
        a, b = (f, i) if rng.random() < 0.5 else (i, f)
    else:
        a, b = random_num(rng), random_num(rng)
    return ("cmp", op, a, b)


def random_bound(rng):
    """A random slice bound: none, small, or huge."""
    pick = rng.random()
    if pick < 0.25:
        return None
    if pick < 0.85:
        return rng.randint(-15, 15)
    return rng.choice([10**20, -(10**20), SSIZE_MAX, SSIZE_MIN, SSIZE_MAX + 1, SSIZE_MIN - 1,
                       SSIZE_MIN + 1, -SSIZE_MAX, 2**62, -(2**62)])


def random_slice(rng):
    """A random slice of a sequence of a random length."""
    step = random_bound(rng)
    if step is not None and rng.random() < 0.5:
        step = rng.choice([1, -1, 2, -2, 3, -3])
    if rng.random() < 0.03:
        step = 0
    length = rng.randint(0, 12) if rng.random() < 0.9 else rng.choice([0, 1, 2**40, SSIZE_MAX])
    return ("slice", random_bound(rng), random_bound(rng), step, length)


def random_case(rng):
    """A random case of any kind."""
    pick = rng.random()
    if pick < 0.5:
        return random_bin(rng)
    if pick < 0.6:
        op = rng.choice(list(UNOPS))
        return ("un", op, random_num(rng))
    if pick < 0.7:
        return ("divmod", random_num(rng), random_num(rng))
    if pick < 0.85:
        return random_cmp(rng)
    if pick < 0.9:
        return ("int", random_float(rng))
    if pick < 0.94:
        return ("float", random_int(rng) if rng.random() < 0.9 else rng.random() < 0.5)
    return random_slice(rng)


# ---------------------------------------------------------------------------------------------
# Corner cases: groups of cases, each with what its cases show.

NAN = 0x7FF8000000000000
NEG_NAN = 0xFFF8000000000000
# NaNs with payloads, and a signaling NaN.
NAN_A = 0x7FF8000000000123
NAN_B = 0xFFF8000000000456
SNAN = 0x7FF0000000000001
INF = math.inf


def B(op, a, b):
    """The binary case `a op b`; a Python float operand stands for its bits."""
    return ("bin", op, fl(a) if type(a) is float else a, fl(b) if type(b) is float else b)


def U(op, a):
    """The unary case `op a`."""
    return ("un", op, fl(a) if type(a) is float else a)


def D(a, b):
    """The case `divmod(a, b)`."""
    return ("divmod", fl(a) if type(a) is float else a, fl(b) if type(b) is float else b)


def C(op, a, b):
    """The comparison `a op b`."""
    return ("cmp", op, fl(a) if type(a) is float else a, fl(b) if type(b) is float else b)


def S(start, stop, step, length):
    """The indices of the slice `start:stop:step` of a sequence of `length` items."""
    return ("slice", start, stop, step, length)


# The ints of the corner cases that are too long for a Lean literal.
for _src in ["10**400", "-10**400", "10**100", "10**100 + 1", "10**90", "3**200", "3**400",
             "2**1000000", "2**1024", "-2**1024", "2**1024 - 2**970", "2**1024 - 2**970 - 1",
             "2**1074", "2**1075", "2**1075 - 1", "2**1075 + 1", "2**1076", "2**1127", "-2**2000",
             "2**976", "-2**1000", "2**1023", "(2**53 - 1) * 2**971"]:
    E(_src)

CORNERS = [
    ("int true division decides a huge or a tiny quotient from the bit lengths first", [
        B("trueDiv", E("2**3000"), 3), B("trueDiv", E("2**1100"), E("2**75")),
        B("trueDiv", E("2**1100"), E("2**76")),
        B("trueDiv", 1, E("2**3000")), B("trueDiv", -1, E("2**3000")), B("trueDiv", 3, E("2**1077")),
        B("trueDiv", 3, E("2**1076")), B("trueDiv", E("2**3000"), E("2**2990")), B("trueDiv", 0, E("-(2**3000)"))]),
    ("an int far beyond a float's range overflows when it converts", [
        B("add", E("2**5000"), 0.5), B("mul", E("-(2**5000)"), 1.0), B("trueDiv", E("2**5000"), 3.0),
        C("lt", E("2**5000"), float("inf"))]),
    ("+, - and * of ints are exact, at any size", [
        B("add", 2**64, 2**64), B("sub", -(2**100), 1), B("mul", 2**64 + 1, -(2**64 - 1)),
        B("mul", 3**200, 3**200)]),
    ("// takes the floor, and % the sign of the divisor", [
        B("floorDiv", 7, 2), B("floorDiv", -7, 2), B("floorDiv", 7, -2), B("floorDiv", -7, -2),
        B("mod", 7, 2), B("mod", -7, 2), B("mod", 7, -2), B("mod", -7, -2),
        B("floorDiv", 0, -5), B("mod", 0, -5), B("mod", -(10**30), 7),
        B("floorDiv", 10**40 + 1, -(10**20)), D(-7, 2), D(10**30, -(2**61 - 1))]),
    ("the zero divisions of ints, each with its message", [
        B("floorDiv", 1, 0), B("mod", 1, 0), D(1, 0), B("trueDiv", 1, 0), B("trueDiv", 0, 0),
        B("mod", True, False), B("trueDiv", 10**400, 0)]),
    ("int true division rounds correctly, ties to even, with the sign of the product", [
        B("trueDiv", 1, 3), B("trueDiv", -2, 3), B("trueDiv", 2**53 + 1, 1),
        B("trueDiv", 2**53 + 3, 1), B("trueDiv", 2**54 + 1, 2), B("trueDiv", 2**54 + 3, 2),
        B("trueDiv", 2**54 + 3, -2), B("trueDiv", 10**30, 7), B("trueDiv", 10**400, 10**100),
        B("trueDiv", 0, -5), B("trueDiv", -1, 10**400)]),
    ("int true division down to the subnormals: 2^-1075 is a tie, which rounds to 0", [
        B("trueDiv", 1, 2**1074), B("trueDiv", 1, 2**1075), B("trueDiv", 3, 2**1076),
        B("trueDiv", 1, 2**1075 - 1), B("trueDiv", -1, 2**1075 + 1),
        B("trueDiv", 2**52 + 1, 2**1074 * 2**53)]),
    ("int true division overflows when the result rounds to 2^1024", [
        B("trueDiv", 2**1024, 1), B("trueDiv", 2**1024 - 2**970, 1),
        B("trueDiv", 2**1024 - 2**970 - 1, 1), B("trueDiv", -(2**2000), 2**976),
        B("trueDiv", 10**400, 10**90)]),
    ("** of ints is exact for an exponent that is not negative", [
        B("pow", 2, 10), B("pow", -2, 3), B("pow", 0, 0), B("pow", -3, 0), B("pow", 0, 5),
        B("pow", 3, 200), B("pow", -7, 41), B("pow", 2, 10**6)]),
    ("0, 1 and -1 to a huge power", [
        B("pow", 1, 10**100), B("pow", -1, 10**100), B("pow", -1, 10**100 + 1),
        B("pow", 0, 10**100)]),
    ("a negative exponent makes ** a pow of floats; 0 to a negative power is an error", [
        B("pow", 2, -1), B("pow", -8, -1), B("pow", 10, -5), B("pow", 0, -1), B("pow", 7, -400),
        B("pow", -2, -1075), B("pow", 2, -(2**1000)), B("pow", 10**400, -1),
        B("pow", 2, -(10**400))]),
    ("shifts by a negative count are a ValueError, even for 0", [
        B("lshift", 1, -1), B("lshift", 0, -1), B("rshift", 1, -1), B("rshift", 0, -(10**30))]),
    ("<< and >> are a multiplication and a floor division by a power of 2", [
        B("lshift", 1, 100), B("lshift", -3, 70), B("rshift", -5, 1), B("rshift", 5, 1),
        B("rshift", -(2**100), 99), B("rshift", -(2**100) - 1, 100), B("lshift", 0, 10**30),
        B("lshift", 1, 10**6)]),
    (">> by a huge count gives 0 or -1", [
        B("rshift", 5, 10**30), B("rshift", -5, 10**30), B("rshift", -1, 2**63),
        B("rshift", 2**100, 2**64)]),
    ("<< by a huge count: OverflowError past the most digits of an int, else MemoryError", [
        B("lshift", 1, 2**66), B("lshift", 1, 30 * (2**61 - 8)),
        B("lshift", 2**30, 30 * (2**61 - 8)), B("lshift", -1, 2**63), B("lshift", 1, 2**62)]),
    ("&, | and ^ treat negative ints as two's complement", [
        B("and", -6, 5), B("or", -6, 5), B("xor", -6, 5), B("and", 5, -6), B("or", 5, -6),
        B("xor", 5, -6), B("and", -6, -5), B("or", -6, -5), B("xor", -6, -5),
        B("and", 2**100 + 7, -1), B("or", -(2**100), 2**100 - 1), B("xor", -1, 2**70)]),
    ("~, - and abs of ints", [
        U("invert", 0), U("invert", -1), U("invert", 2**100), U("neg", -(2**100)),
        U("abs", -(2**100)), U("pos", -5)]),
    ("bools act as ints, but &, | and ^ of two bools give a bool", [
        B("add", True, True), B("and", True, True), B("and", True, False), B("or", False, False),
        B("xor", True, True), B("xor", True, False), B("and", True, 1), B("and", 1, True),
        B("or", False, 0), B("sub", False, True), B("mul", True, -5)]),
    ("other operators on bools give ints or floats; ~ on a bool is not modelled", [
        U("invert", True), U("invert", False), U("neg", True), U("pos", True), U("abs", False),
        B("trueDiv", True, True), B("floorDiv", True, True), B("mod", True, True),
        B("pow", True, -1), B("pow", False, 0), B("lshift", True, 3), D(True, True)]),
    ("+, -, * and / of floats round to nearest, ties to even, and overflow to inf", [
        B("add", 0.1, 0.2), B("mul", 1e308, 10.0), B("sub", -1e308, 1e308),
        B("trueDiv", 1.0, 3.0), B("trueDiv", 5e-324, 2.0), B("trueDiv", 1.5 * 5e-324, 2.0),
        B("mul", 1e-200, 1e-200), B("add", 2.0**53, 1.0), B("add", 2.0**53, 3.0)]),
    ("signed zeros", [
        B("add", -0.0, 0.0), B("add", -0.0, -0.0), B("sub", 0.0, 0.0), B("sub", -0.0, 0.0),
        B("mul", -1.0, 0.0), B("trueDiv", -1.0, INF), B("trueDiv", 0.0, -3.0)]),
    ("inf and nan in +, -, * and /", [
        B("sub", INF, INF), B("mul", INF, 0.0), B("add", INF, -1e308), B("trueDiv", INF, INF),
        ("bin", "add", F(NAN), 1.0), ("bin", "mul", F(NEG_NAN), F(NEG_NAN)),
        B("trueDiv", 1.0, INF)]),
    ("a NaN operand gives itself, quieted; of two NaN operands, + gives the second one and -, * "
     "and / the first one; ** and unary + keep a NaN operand as it is, even a signaling one", [
        ("bin", "add", F(NAN_A), F(NAN_B)), ("bin", "add", F(NAN_B), F(NAN_A)),
        ("bin", "sub", F(NAN_A), F(NAN_B)), ("bin", "mul", F(NAN_B), F(NAN_A)),
        ("bin", "trueDiv", F(NAN_A), F(NAN_B)), ("bin", "add", F(SNAN), 1.0),
        ("bin", "mul", 2.0, F(SNAN)), ("bin", "add", 1, F(NAN_A)),
        ("bin", "mod", F(SNAN), F(NAN_B)), ("bin", "floorDiv", F(NAN_B), F(NAN_A)),
        ("divmod", F(NAN_A), 1.0), ("bin", "pow", F(SNAN), 2.0), ("un", "pos", F(SNAN)),
        ("un", "neg", F(SNAN))]),
    ("the zero divisions of floats, each with its message; a NaN or inf numerator too", [
        B("trueDiv", 1.0, 0.0), B("trueDiv", 1.0, -0.0), B("trueDiv", 0.0, 0.0),
        ("bin", "trueDiv", F(NAN), 0.0), B("trueDiv", INF, 0.0), B("floorDiv", 1.0, 0.0),
        B("mod", 1.0, -0.0), D(1.0, 0.0), B("trueDiv", 1, 0.0), B("mod", 1.0, False),
        B("floorDiv", 5, -0.0)]),
    ("float // takes the floor, and float % the sign of the divisor", [
        B("floorDiv", 7.5, 2.0), B("floorDiv", -7.5, 2.0), B("floorDiv", 7.5, -2.0),
        B("mod", 7.5, 2.0), B("mod", -7.5, 2.0), B("mod", 7.5, -2.0), B("mod", -7.5, -2.0),
        D(-7.5, 2.0), D(7.5, -2.0)]),
    ("a zero remainder takes the sign of the divisor, and a zero quotient the sign of v / w", [
        B("mod", 6.0, 3.0), B("mod", -6.0, 3.0), B("mod", 6.0, -3.0), B("mod", 0.0, -1.0),
        B("mod", -0.0, 1.0), B("floorDiv", -0.0, 1.0), B("floorDiv", 0.0, -1.0),
        B("floorDiv", 0.5, -2.0), D(-0.0, 1.0), D(0.0, -1.0), D(-0.0, -1.0)]),
    ("adding the divisor to a tiny remainder rounds", [
        B("mod", -1e-300, 1e300), B("mod", 1e-300, -1e300), D(-1e-300, 1e300),
        B("mod", -5e-324, 1.0)]),
    ("divmod snaps the quotient to the nearest integer", [
        D(1.0, 0.1), D(-1.0, 0.1), B("floorDiv", 0.5, 0.1), B("mod", 0.5, 0.1), D(2.0**53, 3.0),
        D(1e16 + 2.0, 3.0), B("floorDiv", 1e300, 1e-300), D(1e308, 1e-308)]),
    ("inf and nan in // and %", [
        B("floorDiv", INF, 1.0), B("mod", INF, 1.0), B("floorDiv", 1.0, INF),
        B("floorDiv", -1.0, INF), B("mod", 1.0, INF), B("mod", -1.0, INF), B("mod", 1.0, -INF),
        B("mod", 0.0, INF), B("mod", -0.0, INF), ("bin", "mod", F(NAN), 1.0),
        ("bin", "floorDiv", 1.0, F(NAN)), D(INF, 1.0), D(-1.0, INF), D(5, -INF)]),
    ("float **: an exponent 0 gives 1.0, even for a NaN; NaNs stay, but 1.0 ** nan is 1.0", [
        ("bin", "pow", F(NAN), 0.0), B("pow", 0.0, 0.0), B("pow", INF, -0.0),
        ("bin", "pow", F(NAN), 1.0), ("bin", "pow", 1.0, F(NAN)), ("bin", "pow", 1, F(NAN)),
        ("bin", "pow", 2.0, F(NAN)), ("bin", "pow", -1.0, F(NEG_NAN))]),
    ("float ** with an infinite exponent", [
        B("pow", -1.0, INF), B("pow", 1.0, -INF), B("pow", 0.5, INF), B("pow", 0.5, -INF),
        B("pow", -0.5, -INF), B("pow", 2.0, INF), B("pow", -2.0, -INF), B("pow", INF, INF),
        B("pow", -INF, -INF), B("pow", 0.0, INF), B("pow", -0.0, -INF)]),
    ("float ** with an infinite base: the sign stays for an odd integer exponent", [
        B("pow", INF, 2.0), B("pow", INF, -2.0), B("pow", -INF, 3.0), B("pow", -INF, 2.0),
        B("pow", -INF, -3.0), B("pow", -INF, -2.0), B("pow", -INF, 0.5), B("pow", -INF, -0.5),
        B("pow", -INF, 2.0**53 + 2)]),
    ("float ** with a zero base: the sign stays for an odd integer, and a negative power fails", [
        B("pow", 0.0, 3.0), B("pow", -0.0, 3.0), B("pow", -0.0, 2.0), B("pow", -0.0, 0.5),
        B("pow", -0.0, 1e300), B("pow", 0.0, -1.0), B("pow", -0.0, -3.0), B("pow", 0.0, -0.5),
        B("pow", 0, -INF), B("pow", 0.0, -INF)]),
    ("float ** with a negative base: an integer exponent, or a complex power, which is not "
     "modelled", [
        B("pow", -2.0, 3.0), B("pow", -2.0, 2.0), B("pow", -2.0, -3.0), B("pow", -1.0, 1e300),
        B("pow", -1.0, 3.0), B("pow", -1.0, 2.0**53 + 2), B("pow", -2.0, 0.5),
        B("pow", -8, 1 / 3), B("pow", -0.5, 2.5), B("pow", -1.5, 10001.0)]),
    ("float ** overflows with OverflowError, and underflows to zero or a subnormal", [
        B("pow", 1.5, 10000.0), B("pow", 10.0, 308.0), B("pow", 10.0, 309.0),
        B("pow", 2.0, 1023.0), B("pow", 2.0, 1024.0), B("pow", 0.5, -1024.0),
        B("pow", 2.0, -1074.0), B("pow", 2.0, -1075.0), B("pow", 1.5, -1800.0),
        B("pow", 10.0, -400.0), B("pow", 2.0, 1e10)]),
    ("float ** in the C library", [
        B("pow", 2.0, 0.5), B("pow", 1.1, 2.5), B("pow", 10.0, -5.0), B("pow", 3.0, 1 / 3),
        B("pow", 1e-300, 0.5), B("pow", 0.999, 1e5)]),
    ("an int operand of a float converts first, ties to even, and can overflow", [
        B("add", 2**53 + 1, 0.0), B("mul", 2**53 + 3, 1.0), B("add", 1.0, 10**400),
        B("add", 10**400, 1.0), B("sub", 2**1024 - 2**970 - 1, 0.0),
        B("mul", 2**1024 - 2**970, 1.0), B("add", True, 0.5), B("floorDiv", 10**400, 1.0),
        D(10**400, 1.0), B("pow", 1.0, 10**400), B("pow", 10**400, 0.0),
        B("trueDiv", 0.0, 10**400)]),
    ("floats have no <<, >>, &, | or ^, and an int operand doesn't convert then", [
        B("and", 1.0, 1), B("and", 1, 1.0), B("lshift", 1.0, 1), B("rshift", 1, 1.0),
        B("or", 1.0, True), B("xor", True, 1.0), B("and", 1.0, 10**400), B("xor", 0.5, 0.5),
        U("invert", 1.0)]),
    ("- flips the sign bit of a float, abs clears it, and + keeps it", [
        U("neg", 0.0), U("neg", -0.0), U("abs", -0.0), U("abs", -INF), U("pos", -0.0),
        U("neg", 1.5), ("un", "neg", F(NAN)), ("un", "abs", F(NEG_NAN)),
        ("un", "pos", F(NEG_NAN))]),
    ("ints and floats compare exactly, even past 2^53 and 2^1024", [
        C("eq", 2**53 + 1, 2.0**53), C("eq", 2**53, 2.0**53), C("gt", 2**53 + 1, 2.0**53),
        C("lt", 2**53 + 1, 2.0**53 + 2), C("le", 2.0**53, 2**53), C("ne", 2**60 + 1, 2.0**60),
        C("gt", 10**400, 1.7976931348623157e308), C("lt", -(10**400), -1.7976931348623157e308),
        C("gt", 2**1024 - 2**970, 1.7976931348623157e308), C("eq", 1, 1.0000000000000002),
        C("lt", 1, 1.5), C("gt", 2, 1.5), C("lt", -2, -1.5), C("ge", 0, 5e-324),
        C("gt", 0, -5e-324)]),
    ("inf is above every int, and -inf below", [
        C("gt", INF, 10**400), C("lt", -INF, -(10**400)), C("lt", 10**400, INF), C("eq", INF, INF),
        C("lt", -INF, INF), C("ge", -INF, -INF), C("eq", INF, 10**400)]),
    ("a NaN is unequal to everything, itself included, and unordered", [
        ("cmp", "eq", F(NAN), F(NAN)), ("cmp", "ne", F(NAN), F(NAN)), ("cmp", "lt", F(NAN), 1),
        ("cmp", "ge", F(NAN), 1), ("cmp", "le", 1, F(NAN)), ("cmp", "eq", F(NAN), 0),
        ("cmp", "ne", 10**400, F(NEG_NAN)), ("cmp", "gt", F(NAN), -INF)]),
    ("-0.0 equals 0, and bools compare as ints", [
        C("eq", -0.0, 0), C("eq", -0.0, 0.0), C("lt", -0.0, 0.0), C("eq", True, 1.0),
        C("gt", True, 0.5), C("eq", False, 0), C("eq", True, 1), C("lt", True, 2),
        C("eq", True, False), C("le", False, -0.0)]),
    ("int() of a float rounds toward zero", [
        ("int", fl(1.9)), ("int", fl(-1.9)), ("int", fl(-0.0)), ("int", fl(0.5)),
        ("int", fl(-5e-324)), ("int", fl(2.0**53 + 2)), ("int", fl(1e20)),
        ("int", fl(2.0**1023)), ("int", fl(1.7976931348623157e308)),
        ("int", fl(-(2.0**63)))]),
    ("int() of inf and nan", [
        ("int", fl(INF)), ("int", fl(-INF)), ("int", F(NAN)), ("int", F(NEG_NAN))]),
    ("float() of an int rounds to nearest, ties to even, and overflows from 2^1024 - 2^970", [
        ("float", 2**53 + 1), ("float", 2**53 + 3), ("float", -(2**63) - 1),
        ("float", 2**1024 - 2**970 - 1), ("float", 2**1024 - 2**970), ("float", -(10**400)),
        ("float", True), ("float", False), ("float", 0)]),
    ("a missing bound of a slice is an end of the sequence, by the sign of the step", [
        S(None, None, None, 10), S(None, None, -1, 10), S(None, None, 2, 10),
        S(None, None, -3, 10), S(2, None, -1, 10), S(None, 2, -1, 10)]),
    ("negative indices count from the end, and then are clamped to the sequence", [
        S(-3, None, None, 10), S(-20, 5, None, 10), S(None, -20, -1, 10), S(-20, None, -1, 10),
        S(5, -20, -1, 10), S(-1, -11, -1, 10), S(-2, -1, None, 10)]),
    ("indices past the end are clamped to the length, or to the last index for a negative step", [
        S(20, None, None, 10), S(20, None, -1, 10), S(3, 100, 2, 10), S(100, 3, -2, 10),
        S(10, 10, 1, 10), S(9, 9, -1, 10)]),
    ("a zero step is a ValueError, whatever the bounds", [
        S(None, None, 0, 10), S(10**30, None, 0, 10), S(None, None, 0, 0)]),
    ("huge values are clamped to PY_SSIZE_T_MIN and PY_SSIZE_T_MAX, and a step of "
     "PY_SSIZE_T_MIN becomes -PY_SSIZE_T_MAX", [
        S(10**30, -(10**30), -1, 10), S(-(10**30), 10**30, None, 10), S(None, None, 10**30, 10),
        S(None, None, -(10**30), 10), S(None, None, SSIZE_MIN, 10), S(None, None, -SSIZE_MAX, 10),
        S(None, None, SSIZE_MAX, SSIZE_MAX), S(-1, None, -1, SSIZE_MAX),
        S(SSIZE_MIN, SSIZE_MAX, 1, SSIZE_MAX)]),
    ("an empty sequence", [
        S(None, None, None, 0), S(None, None, -1, 0), S(-1, None, None, 0), S(5, -5, -2, 0)]),
    ("the length of a slice with a step", [
        S(0, 10, 3, 10), S(9, None, -4, 10), S(1, 2, SSIZE_MAX, 10), S(0, 9, 3, 10),
        S(0, 10, 9, 10), S(8, 0, -3, 10)]),
]

# Cases that the port leaves unmodelled although CPython computes them while the machine has
# the memory: an int with more than 2^32 bits (`Arith.maxBits`).  CPython runs the first one only:
# the powers would take it hours.
TOO_LARGE = [
    (B("lshift", 1, 2**32), True, "a shift whose result has 2^32 + 1 bits"),
    (B("lshift", -(2**40), 2**32 - 40), False, None),
    (B("pow", 2, 2**32), False, "a power whose result has 2^32 + 1 bits"),
    (B("pow", 4, 2**31), False, None),
    (B("pow", 3, 2**32), False,
     "a power with e * floor(log2 |a|) = 2^32, whose result has more than 2^32 bits"),
    (B("pow", -2, 10**30), False, None),
]

# ---------------------------------------------------------------------------------------------
# Lean output


def short_int(n):
    """Whether the int `n` is written as a literal in Lean."""
    return len(str(abs(n))) <= LEAN_MAX_DIGITS


def lean_int(n):
    """The int `n` as a Lean term."""
    if not short_int(n):
        return f"({EXPRS[n][0]})"
    return f"({n})" if n < 0 else str(n)


def py_int(n):
    """The int `n` as the comments show it."""
    return str(n) if short_int(n) else EXPRS[n][1]


def lean_num(v):
    """A number as a Lean `Num`."""
    if isinstance(v, bool):
        return f"(.bool {str(v).lower()})"
    if isinstance(v, int):
        return f"(.int {lean_int(v)})"
    bits = v.bits if isinstance(v, F) else bits_of(v)
    return f"(.float 0x{bits:016X})"


def py_num(v):
    """A number as the comments show it."""
    if isinstance(v, bool) or not isinstance(v, (int, F)):
        return repr(v)
    if isinstance(v, int):
        return py_int(v)
    x = v.value()
    if math.isnan(x):
        return "nan" if v.bits >> 63 == 0 else "-nan"
    return repr(x)


def py_operand(v):
    """An operand as the comments show it, in parentheses if it is negative or an expression."""
    s = py_num(v)
    return f"({s})" if s.startswith("-") or " " in s else s


def bare(term):
    """A Lean term without its outer parentheses."""
    return term[1:-1] if term.startswith("(") and term.endswith(")") else term


def enc_lean(e):
    """A JSON number as a Lean `Num`."""
    kind, x = e
    if kind == "bool":
        return lean_num(x)
    if kind == "int":
        return lean_num(int(x))
    return lean_num(F(int(x, 16)))


def enc_py(e):
    """A JSON number as the comments show it."""
    kind, x = e
    if kind == "bool":
        return repr(x)
    if kind == "int":
        return py_int(int(x))
    return py_num(F(int(x, 16)))


def fits(case, result):
    """Whether every int of the case and its result is short enough for a Lean literal."""
    nums = [x for x in case[1:] if isinstance(x, int) and not isinstance(x, bool)]
    for e in result[1:]:
        if isinstance(e, list) and e[0] == "int":
            nums.append(int(e[1]))
    return all(short_int(n) or n in EXPRS for n in nums)


def lean_call(case):
    """The Lean call of a case, as its function and its arguments, and the case as Python writes
    it."""
    kind = case[0]
    if kind == "bin":
        _, op, a, b = case
        return (["bin", f".{op}", lean_num(a), lean_num(b)],
                f"{py_operand(a)} {BINOPS[op][1]} {py_operand(b)}")
    if kind == "un":
        _, op, a = case
        sym = UNOPS[op][1]
        return (["un", f".{op}", lean_num(a)],
                f"abs({py_num(a)})" if op == "abs" else f"{sym}{py_operand(a)}")
    if kind == "divmod":
        _, a, b = case
        return ["divmod", lean_num(a), lean_num(b)], f"divmod({py_num(a)}, {py_num(b)})"
    if kind == "cmp":
        _, op, a, b = case
        return (["compare", f".{op}", lean_num(a), lean_num(b)],
                f"{py_operand(a)} {CMPOPS[op][1]} {py_operand(b)}")
    if kind == "int":
        return ["floatToInt", f"0x{case[1].bits:016X}"], f"int({py_num(case[1])})"
    if kind == "float":
        return ["Num.toFloat", lean_num(case[1])], f"float({py_num(case[1])})"
    _, start, stop, step, length = case

    def bound(x):
        return "none" if x is None else f"(some {lean_int(x)})"

    def pyb(x):
        return "" if x is None else py_int(x)
    return (["sliceIndices", bound(start), bound(stop), bound(step), str(length)],
            f"[{pyb(start)}:{pyb(stop)}:{pyb(step)}] of {length}")


def fill(words):
    """The words joined into lines of at most 100 characters, where they fit; the lines after the
    first one are indented."""
    lines = [words[0]]
    for w in words[1:]:
        if len(lines[-1]) + 1 + len(w) <= 100:
            lines[-1] += " " + w
        else:
            lines.append("  " + w)
    return "\n".join(lines)


def lean_guard(case, result):
    """The `#guard` of a case, with the case and its result as Python writes them in a comment,
    on the line before it if they don't fit after it in 100 characters."""
    call, py = lean_call(case)
    words = [f"({call[0]}"] + call[1:-1] + [call[-1] + ")"] if len(call) > 1 else [f"({call[0]})"]
    tag = result[0]
    if tag == "nm":
        words, shown = ["#guard", "unmodelled"] + words + [json.dumps(result[1])], "not modelled"
    elif tag == "raise":
        words = ["#guard", "raises"] + words + [f'"{result[1]}"', json.dumps(result[2])]
        shown = result[1]
    elif tag == "bool":
        words, shown = ["#guard"] + call + ["==", str(result[1]).lower()], str(result[1])
    elif tag == "ok":
        expected, shown = enc_lean(result[1]), enc_py(result[1])
        if case[0] == "int":
            expected = lean_int(int(result[1][1]))
        elif case[0] == "float":
            expected = f"0x{int(result[1][1], 16):016X}"
        words = ["#guard", "gives"] + words + [expected]
    elif tag == "ok2":
        words = ["#guard", "gives"] + words + [
            f"({bare(enc_lean(result[1]))}, {bare(enc_lean(result[2]))})"]
        shown = f"({enc_py(result[1])}, {enc_py(result[2])})"
    else:
        _, start, stop, step, n = result
        words = ["#guard", "gives"] + words + [f"⟨{start}, {stop}, {step}, {n}⟩"]
        shown = f"{start}, {stop}, {step}, length {n}"
    comment = f"-- {py}: {shown}"
    text = fill(words)
    if "\n" not in text and len(text) + 2 + len(comment) <= 100:
        return f"{text}  {comment}"
    comment = "\n".join(textwrap.wrap(comment[3:], 97, initial_indent="-- ",
                                      subsequent_indent="--   ", break_long_words=False))
    return f"{comment}\n{text}"


HEADER = '''/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataPython.Dyn.Sem.Arith
-- The `#guard`s below run as compiled code.
meta import StrataPython.Dyn.Sem.Arith

set_option autoImplicit false

/-!
# Arithmetic on ints, bools and floats

Generated by `gen_arith_cases.py`; do not edit.  Each expected result or exception is what CPython
3.12.15 gives for the same case: a binary operator, a unary operator or `abs`, `divmod`, a
comparison, `int()` of a float, `float()` of an int, or the indices of a slice, which come from
CPython's `PySlice_Unpack` and `PySlice_AdjustIndices`.  "Not modelled" stands for CPython's
`MemoryError`, for an int with more than `2 ^ 32` bits, and for a complex power, which CPython
computes or finds too large ("complex exponentiation").  A float is given by its bits, a NaN too,
as CPython's `float_add` and the other slots of `float` give them on x86-64; the comment of each
case shows it as Python writes it.  First come the corner cases, each group with what it shows,
then the results that are too large, then random cases.
-/

namespace StrataPython.Dyn.Sem.ArithTest

open StrataPython.Dyn.Sem.Format
open StrataPython.Dyn.Sem.Arith

/-- `r` is the result `x`. -/
def gives {α : Type} [BEq α] (r : Except Failure α) (x : α) : Bool := r.toOption == some x

/-- `r` is CPython raising the exception class `cls` with the message `msg`. -/
def raises {α : Type} (r : Except Failure α) (cls msg : String) : Bool :=
  match r with
  | .error e => e == .raise cls msg
  | .ok _ => false

/-- `r` is a case that the port doesn't model, for the reason `why`. -/
def unmodelled {α : Type} (r : Except Failure α) (why : String) : Bool :=
  match r with
  | .error (.notModelled w) => w == why
  | _ => false

/-- The name of the type of the number `x`. -/
def typeName : Num → String
  | .bool _ => "bool"
  | .int _ => "int"
  | .float _ => "float"

/-- The symbol of the binary operator `op`. -/
def symbol : BinOp → String
  | .add => "+" | .sub => "-" | .mul => "*" | .trueDiv => "/" | .floorDiv => "//" | .mod => "%"
  | .pow => "** or pow()" | .lshift => "<<" | .rshift => ">>" | .and => "&" | .or => "|"
  | .xor => "^"

/-- `a op b`, with CPython's `TypeError` when no slot implements `op` for the operands. -/
def bin (op : BinOp) (a b : Num) : Except Failure Num :=
  (binary op a b).getD (.error (.raise "TypeError"
    s!"unsupported operand type(s) for {symbol op}: '{typeName a}' and '{typeName b}'"))

/-- `op a`, with CPython's `TypeError` for `~` on a float. -/
def un (op : UnaryOp) (a : Num) : Except Failure Num :=
  match unary op a with
  | some r => r
  | none => .error (.raise "TypeError" s!"bad operand type for unary ~: '{typeName a}'")
'''

FOOTER = '''
end StrataPython.Dyn.Sem.ArithTest
'''


def write_lean():
    """Write ArithTest.lean."""
    lines = [HEADER.rstrip("\n"), "", "/-! ## Corner cases -/"]
    for note, cases in CORNERS:
        lines.append("")
        lines += textwrap.wrap(f"{note[0].upper()}{note[1:]}.", 97, initial_indent="-- ",
                               subsequent_indent="-- ")
        for case in cases:
            result = run(case)
            assert fits(case, result), (case, result)
            lines.append(lean_guard(case, result))
    lines.append("")
    lines.append("/-! ## Ints with more than 2 ^ 32 bits, which are not modelled -/")
    for case, run_it, note in TOO_LARGE:
        if run_it:
            _, op, a, b = case
            out = BINOPS[op][0](a, b)
            assert out.bit_length() > MAX_BITS
            del out
        if note:
            lines.append("")
            lines.append(f"-- {note[0].upper()}{note[1:]}.")
        assert too_large(*case[1:]), case
        lines.append(lean_guard(case, ["nm", TOO_LARGE_REASON]))
    lines.append("")
    lines.append("/-! ## Random cases -/")
    lines.append("")
    rng = random.Random(3_12_15)
    seen = set()
    picked = []
    while len(picked) < LEAN_RANDOM_CASES:
        case = random_case(rng)
        result = run(case)
        if not fits(case, result):
            continue
        key = json.dumps([case[0]] + [enc(x) if isinstance(x, (int, F)) else x for x in case[1:]])
        if key in seen:
            continue
        seen.add(key)
        picked.append(lean_guard(case, result))
    lines += picked
    lines.append(FOOTER.rstrip("\n"))
    OUT.write_text("\n".join(lines) + "\n", encoding="utf-8")


def case_json(case):
    """A case and its result as a JSON object."""
    kind = case[0]
    obj = {"k": kind}
    if kind in ("bin", "cmp"):
        obj.update(op=case[1], a=enc(case[2]), b=enc(case[3]))
    elif kind == "un":
        obj.update(op=case[1], a=enc(case[2]))
    elif kind == "divmod":
        obj.update(a=enc(case[1]), b=enc(case[2]))
    elif kind in ("int", "float"):
        obj.update(a=enc(case[1]))
    else:
        _, start, stop, step, length = case
        obj.update(start=None if start is None else str(start),
                   stop=None if stop is None else str(stop),
                   step=None if step is None else str(step), len=str(length))
    result = run(case)
    if result[0] == "slice":
        result = ["slice"] + [str(x) for x in result[1:]]
    obj["r"] = result
    return obj


def write_jsonl(path, count, seed):
    """Write the corner cases and `count` random cases to `path` as JSON lines."""
    rng = random.Random(seed)
    with open(path, "w", encoding="utf-8") as f:
        for _, group in CORNERS:
            for case in group:
                f.write(json.dumps(case_json(case)) + "\n")
        for _ in range(count):
            f.write(json.dumps(case_json(random_case(rng))) + "\n")


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
