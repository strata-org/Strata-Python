# `len(List_append(xs, v)) == len(xs) + 1` axiom missing — length after append
# unprovable; bounds checks after list building fail
"""
CONS-LIST APPEND LEN AXIOM MISSING — len(append(xs, v)) ≠ len(xs) + 1

CPython: xs = [1, 2]; xs.append(3); len(xs) == 3 (always true)

Model:   List_append is an uninterpreted function (finding 275).
         List_len is an uninterpreted function.
         There is NO AXIOM connecting them:
           List_len(List_append(xs, v)) == List_len(xs) + 1
         Without this axiom, the solver CANNOT prove len grows after append.

         This makes bounds checks after list building UNPROVABLE:
           result = []
           result.append(x)
           result.append(y)
           assert len(result) == 2  # UNPROVABLE without axiom chain

Finding 233 identifies the axiom chain is needed.
This finding provides the MINIMAL program that fails verification
due to the missing axiom, and shows the specific axiom required.
"""


def build_and_check_len() -> bool:
    """Build list, verify length matches number of appends."""
    xs: list[int] = []
    xs.append(10)
    xs.append(20)
    xs.append(30)
    # CPython: len(xs) == 3 (always)
    # Model: len(List_append(List_append(List_append(nil, 10), 20), 30))
    #         = ??? (uninterpreted, no axiom) — UNPROVABLE
    return len(xs) == 3


def safe_access_after_build() -> int:
    """Access element after building — needs len axiom for bounds proof."""
    xs: list[int] = []
    xs.append(42)
    # To prove xs[0] is valid, need: len(xs) >= 1
    # Which requires: len(List_append(nil, 42)) == len(nil) + 1 == 0 + 1 == 1
    # Without axiom: len(xs) is unconstrained — bounds check fails
    return xs[0]


def loop_build_then_access(n: int) -> int:
    """Build in loop, access after — needs inductive len reasoning."""
    xs: list[int] = []
    i: int = 0
    while i < n:
        xs.append(i)
        i += 1
    # After loop: len(xs) == n (needs loop invariant + append axiom)
    if len(xs) > 0:
        return xs[0]
    return -1


def main() -> None:
    # Test 1: length after appends
    assert build_and_check_len()

    # Test 2: access after build
    assert safe_access_after_build() == 42

    # Test 3: loop build
    assert loop_build_then_access(5) == 0
    assert loop_build_then_access(0) == -1

    print("all passed")


main()
