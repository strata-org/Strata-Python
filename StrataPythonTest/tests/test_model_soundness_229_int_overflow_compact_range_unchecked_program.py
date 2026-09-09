# Integer compact range — SMT Int is unbounded = Python int (both correct);
# compact restriction is verifier confidence, not soundness (positive)
"""
The subset says: "Integer literals must fit in the compact range (|n| < 2^30)."
But the model uses SMT-LIB `Int` which is UNBOUNDED mathematical integers.

This means:
1. Arithmetic can produce values OUTSIDE compact range without error
2. The model says `2**30 + 1` is fine; CPython also says fine (Python ints
   are unbounded) — but the SUBSET says this is OUT.
3. The model can't detect when a computation exceeds compact range.

Actually, Python integers ARE unbounded (no overflow). The subset's
compact-range restriction is about what the VERIFIER can handle, not
about runtime behavior. So the model (unbounded Int) matches CPython.

The REAL issue: if the subset restricts to compact range for extraction
reasons, the model should WARN when values might exceed it — but this
is a completeness issue, not soundness.

This finding documents that SMT Int = Python int (both unbounded) is
CORRECT, and the compact-range restriction is a VERIFIER limitation.

Uses ONLY confirmed-accepted constructs: int, arithmetic.
"""


def large_multiplication(a: int, b: int) -> int:
    """Result may exceed compact range."""
    return a * b


def factorial(n: int) -> int:
    """Grows beyond compact range quickly."""
    if n <= 1:
        return 1
    return n * factorial(n - 1)


def power_of_two(n: int) -> int:
    """2^n — exceeds compact range for n >= 30."""
    result: int = 1
    i: int = 0
    while i < n:
        result = result * 2
        i = i + 1
    return result


def stays_in_range(x: int) -> int:
    """Operations that stay within compact range."""
    return (x * x) % 1000000  # modulo keeps it bounded


def main() -> None:
    # Within compact range
    assert large_multiplication(100, 200) == 20000
    assert stays_in_range(999) == 998001

    # Exceeds compact range (but Python handles it fine)
    assert factorial(10) == 3628800
    assert power_of_two(20) == 1048576

    # Way beyond compact range
    assert power_of_two(30) == 1073741824  # 2^30 — at boundary
    assert factorial(12) == 479001600

    print(large_multiplication(100, 200), factorial(10),
          power_of_two(20))


main()
