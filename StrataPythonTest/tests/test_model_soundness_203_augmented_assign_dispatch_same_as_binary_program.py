# Augmented assignment dispatch — `x += y` must desugar to `x = x op y` using
# same operator function; separate code path risks incompleteness
"""
Augmented assignment `x += y` desugars to `x = x + y` for immutable types.
The operator dispatch for `+=` must use the SAME tag-matching as `+`.

But there's a subtlety: for mutable types (lists), `+=` calls __iadd__
(in-place add) which is different from __add__. Finding 003/010 covered
this for lists. This finding focuses on IMMUTABLE types where `+=` is
purely `x = x.__add__(y)`:

- `x: int; x += 1` → `x = PAdd(x, 1)` — same dispatch as `+`
- `x: float; x += 0.5` → `x = PAdd(x, 0.5)`
- `x: str; x += "suffix"` → `x = PAdd(x, "suffix")` — string concat

The model must ensure augmented assignment uses the same operator
function as the binary operator, with the result rebound to the variable.

Uses ONLY confirmed-accepted constructs: int, float, str, +=, -=, *=.
"""


def int_augmented_add(x: int, y: int) -> int:
    x += y
    return x


def float_augmented_add(x: float, y: float) -> float:
    x += y
    return x


def str_augmented_add(s: str, suffix: str) -> str:
    s += suffix
    return s


def int_augmented_sub(x: int, y: int) -> int:
    x -= y
    return x


def int_augmented_mul(x: int, y: int) -> int:
    x *= y
    return x


def mixed_augmented(x: int, y: float) -> float:
    """int += float → result is float (type promotion)."""
    # In CPython: x += y raises TypeError because int.__iadd__(float) fails
    # Actually no: int doesn't have __iadd__, so it falls back to __add__
    # int.__add__(float) returns NotImplemented, float.__radd__(int) works
    # Result is float, but x was int... CPython rebinds x to float
    # This is a type-change! x: int becomes x: float
    # Frontend subset says "type stability" — this should be rejected
    result: float = x + y  # use explicit to avoid type instability
    return result


def accumulate_in_loop(xs: list[int]) -> int:
    total: int = 0
    for x in xs:
        total += x
    return total


def build_string(parts: list[str]) -> str:
    result: str = ""
    for p in parts:
        result += p
    return result


def main() -> None:
    assert int_augmented_add(5, 3) == 8
    assert float_augmented_add(1.5, 2.5) == 4.0
    assert str_augmented_add("hello", " world") == "hello world"
    assert int_augmented_sub(10, 3) == 7
    assert int_augmented_mul(4, 5) == 20
    assert mixed_augmented(3, 1.5) == 4.5
    assert accumulate_in_loop([1, 2, 3, 4, 5]) == 15
    assert build_string(["a", "b", "c"]) == "abc"

    print(int_augmented_add(5, 3), str_augmented_add("hi", "!"),
          accumulate_in_loop([1, 2, 3]))


main()
