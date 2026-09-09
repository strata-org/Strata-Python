# Type annotations drive tag assertions — `x: int` must emit `assert
# isfrom_int(x)`; without this, verifier has no type info
"""
Type annotations in the Frontend subset are the SOURCE OF TRUTH for tag
assertions. `x: int` means the verifier should know `isfrom_int(x)` at
that point. The oracle uses annotations to determine the initial tag set
for each variable.

If annotations are ignored or not translated to tag assertions, the
verifier has no type information and can't prove anything.
"""


def typed_arithmetic(x: int, y: int) -> int:
    # Annotations tell verifier: x is from_int, y is from_int
    # Therefore x + y is valid (PAdd on int×int)
    return x + y


def typed_string_ops(s: str, t: str) -> str:
    # Annotations: s is from_str, t is from_str
    # Therefore s + t is valid (string concatenation)
    return s + t


def typed_comparison(x: int, threshold: int) -> bool:
    # Annotations: both from_int
    # Therefore x > threshold is valid (PLt on int×int)
    return x > threshold


def typed_mixed(name: str, age: int, score: float) -> str:
    # Each parameter has a known tag
    # name: from_str, age: from_int, score: from_float
    if age > 18:  # PLt(from_int(18), from_int(age)) — valid
        return name  # from_str — matches return type
    return ""


def local_annotations(n: int) -> int:
    # Local variable annotations also provide tag info
    total: int = 0  # from_int
    i: int = 0      # from_int
    while i < n:
        total = total + i  # PAdd(from_int, from_int) — valid
        i = i + 1
    return total


def main() -> None:
    assert typed_arithmetic(3, 4) == 7
    assert typed_string_ops("hello", " world") == "hello world"
    assert typed_comparison(5, 3) == True
    assert typed_mixed("Alice", 20, 95.0) == "Alice"
    assert local_annotations(5) == 10

    print(typed_arithmetic(3, 4), typed_string_ops("a", "b"))


main()
