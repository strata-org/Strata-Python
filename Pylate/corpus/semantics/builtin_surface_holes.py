# Three catch-alls that asserted an exception where CPython returns a value.
# Each one deleted the normal completion, which made everything after it
# unreachable, so the obligations downstream discharged for free.
#   properties  - `n.real` is a read with a result, not an AttributeError
#   bytes ops   - bytes concatenates and repeats like str does
#   membership  - bytes admits `in`, and str/bytes probes are typed


def properties(n: int, f: float) -> int:
    # `True.real` is 1, an int, so bool widens rather than staying bool.
    return n.real + n.numerator + n.denominator


def float_properties(f: float) -> float:
    return f.real + f.imag


def range_properties(n: int) -> int:
    r = range(n)
    return r.start + r.stop + r.step


def method_escape(xs: list[int]) -> object:
    # A bound method read as a value: `any`, with a method-escape obligation.
    # Not a TypeError, and not a callable target resolving to nothing.
    return xs.append


def missing_attribute(n: int) -> int:
    # Still an AttributeError, which is the point of keeping the arm.
    return n.nosuch


def bytes_ops(s: str, n: int) -> bytes:
    b = s.encode()
    return b + b + b * n


def bytes_membership(s: str, n: int) -> int:
    # An int probe is a byte, so its range is an obligation, not a fact.
    return 1 if n in s.encode() else 0


def typed_str_probe(s: str, n: int) -> int:
    # `1 in "ab"` is a TypeError: `in` over str is typed, unlike `1 in (1, 2)`.
    return 1 if n in s else 0
