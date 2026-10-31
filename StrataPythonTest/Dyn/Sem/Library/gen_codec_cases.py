"""Write `CodecCases.lean`: CPython 3.12's `str.encode` and `bytes.decode` with the five built-in
codecs and every error handler.

    python3.12 StrataPythonTest/Dyn/Sem/Library/gen_codec_cases.py \
        > StrataPythonTest/Dyn/Sem/Library/CodecCases.lean

The strings are random over characters of every width; the byte strings are random, biased
toward UTF-8, UTF-16 and UTF-32 sequences, valid or broken. A result is written as text that
the test writes in the same way: `b` and the bytes (encoding) or `s` and the code points
(decoding); `e`, the exception class, its encoding, start, end and reason, and its message, for a
`UnicodeEncodeError` or `UnicodeDecodeError`; `x`, the class and message of another exception;
`n surrogate` for a decoding that gives a lone surrogate, or that raises an error after its
handler gave one (CPython raises it with the first error's `args`), and `n name` for `namereplace`
on an encoding error, which the semantics doesn't model.
"""
import codecs
import random
import sys

assert sys.version_info[:2] == (3, 12), "run with CPython 3.12"

CODECS = ["utf-8", "utf-16", "utf-32", "ascii", "latin-1"]
HANDLERS = ["strict", "ignore", "replace", "backslashreplace", "xmlcharrefreplace",
            "surrogateescape", "surrogatepass", "foo"]
POOL = "aZ09 \x00\x7f\x80éÿĀ€￿\U0001f600\U0010ffff"


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


def enc_result(f, namereplace=False):
    if namereplace:
        return "n name"
    try:
        r = f()
    except (UnicodeEncodeError, UnicodeDecodeError) as e:
        return f"e {type(e).__name__}|{e.encoding}|{e.start}|{e.end}|{e.reason}|{e}"
    except (LookupError, TypeError) as e:
        return f"x {type(e).__name__}|{e}"
    if isinstance(r, bytes):
        return "b " + " ".join(str(x) for x in r)
    if any(0xD800 <= ord(c) <= 0xDFFF for c in r):
        return "n surrogate"
    return "s " + " ".join(str(ord(c)) for c in r)


def surrogate_then_error(b, c, h):
    """Whether decoding `b` with `c` and the handler `h` raises an error after the handler gave a
    lone surrogate, found with a handler that wraps `h`."""
    if h not in ("surrogateescape", "surrogatepass"):
        return False
    gave = []

    def track(exc):
        r = codecs.lookup_error(h)(exc)
        gave.append(any(0xD800 <= ord(ch) <= 0xDFFF for ch in r[0]))
        return r

    codecs.register_error("track", track)
    try:
        b.decode(c, "track")
    except UnicodeDecodeError:
        return any(gave)
    return False


def dec_result(b, c, h):
    """The result of `b.decode(c, h)`, as `enc_result` writes it."""
    r = enc_result(lambda: b.decode(c, h))
    return "n surrogate" if r.startswith("e ") and surrogate_then_error(b, c, h) else r


def rbytes(rng):
    kinds = [
        lambda: bytes([rng.randrange(256)]),
        lambda: rng.choice(["é", "€", "\U0001f600", "a"]).encode("utf-8"),
        lambda: rng.choice([b"\xe0\x80", b"\xed\xa0\x80", b"\xf4\x90", b"\xc3", b"\xe2\x82",
                            b"\xf0\x9f\x98", b"\xc0\xaf"]),
        lambda: rng.choice(["a", "€", "\U0001f600"]).encode("utf-16-le"),
        lambda: rng.choice([b"\x00\xd8", b"\x00\xdc", b"\xff\xfe", b"\xfe\xff"]),
        lambda: rng.choice(["a", "\U0001f600"]).encode("utf-32-le"),
        lambda: rng.choice([b"\x00\x00\x11\x00", b"\x00\xd8\x00\x00", b"\xff\xfe\x00\x00",
                            b"\x00\x00\xfe\xff"]),
    ]
    return b"".join(rng.choice(kinds)() for _ in range(rng.randrange(0, 6)))


def needs_handler(s, c):
    """Whether encoding `s` with `c` meets an error, so that the handler runs."""
    try:
        s.encode(c)
        return False
    except UnicodeEncodeError:
        return True


# Byte strings at the boundaries of the decoders: UTF-8's lead and continuation bytes and the
# overlong and surrogate forms, UTF-16's surrogate units, UTF-32's largest code points.
BOUNDARY_BYTES = [
    b"\xf0\x80\x80\x80", b"\xf0\x8f\xbf\xbf", b"\xf0\x90\x80\x80", b"\xf5\x80\x80\x80",
    b"\xe0\xbf\xbf", b"\xe1\x80\xbf", b"\xef\xbf\xbf", b"\xed\x9f\xbf", b"\xed\xa0\x80",
    b"\xed\xbf\xbf", b"\xed\xa0\x80a", b"\xc2\x80", b"\xdf\xbf", b"\xc1\xbf", b"\xf4\x8f\xbf\xbf",
    b"\xf4\x90\x80\x80", b"\x80", b"\xbf", b"\xff\xdb\xff\xdf", b"\xff\xdf", b"\x00\xdc\x00\xd8",
    b"\xff\xff\x10\x00", b"\x00\x00\x11\x00", b"\xff\xd7\x00\x00", b"\x00\xe0\x00\x00",
    b"\xff\xdf\x00\x00", b"\x00\xd8\x00", b"\xf1\xbf\x80\x80", b"\xf3\x80\xbf\x80",
    b"a\x00\x7f", b"\x7f\x00\x00",
]
# Each boundary sequence again with an invalid byte after it, so that valid ones reach CPython's
# loop rather than Lean's validator.
BOUNDARY_BYTES = BOUNDARY_BYTES + [x + b"\x80" for x in BOUNDARY_BYTES]
BOUNDARY_STRS = ["\x7f", "\x80", "\xff", "\u0100", "\u07ff", "\u0800", "\uffff", "\U00010000",
                 "\U0010ffff", "a\u0800b"]


def cases():
    rng = random.Random(20261028)
    out = []
    for x in BOUNDARY_BYTES:
        for c in CODECS:
            for h in ["strict", "replace", "backslashreplace", "surrogatepass",
                      "surrogateescape"]:
                out.append(("decode", c, h, lean_str("".join(chr(v) for v in x)),
                            dec_result(x, c, h)))
    for x in BOUNDARY_STRS:
        for c in CODECS:
            for h in ["strict", "backslashreplace", "namereplace"]:
                out.append(("encode", c, h, lean_str(x),
                            enc_result(lambda: x.encode(c, h),
                                       h == "namereplace" and needs_handler(x, c))))
    for _ in range(600):
        s = "".join(rng.choice(POOL) for _ in range(rng.randrange(0, 6)))
        c, h = rng.choice(CODECS), rng.choice(HANDLERS + ["namereplace"])
        out.append(("encode", c, h, lean_str(s),
                    enc_result(lambda: s.encode(c, h), h == "namereplace" and needs_handler(s, c))))
    for _ in range(1200):
        b = rbytes(rng)
        c, h = rng.choice(CODECS), rng.choice(HANDLERS + ["namereplace"])
        out.append(("decode", c, h, lean_str("".join(chr(x) for x in b)),
                    dec_result(b, c, h)))
    return out


print("""/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-! Generated by `gen_codec_cases.py` from CPython 3.12; do not edit. Each case: `encode` or
`decode`, the codec, the error handler, the input (for `decode`, a string whose code points are
the bytes), and the result, written as the generator says. -/

namespace StrataPython.Dyn.Sem.Library.CodecCases

public section
""")
items = [f"  ({lean_str(k)}, {lean_str(c)}, {lean_str(h)}, {x}, {lean_str(r)})"
         for k, c, h, x, r in cases()]
parts = [items[i:i + 150] for i in range(0, len(items), 150)]
T = "(String × String × String × String × String)"
for k, part in enumerate(parts):
    print(f"def cases{k} : Array {T} := #[")
    print(",\n".join(part))
    print("]\n")
print(f"def cases : Array {T} := " + " ++ ".join(f"cases{k}" for k in range(len(parts))))
print("""
end

end StrataPython.Dyn.Sem.Library.CodecCases""")
