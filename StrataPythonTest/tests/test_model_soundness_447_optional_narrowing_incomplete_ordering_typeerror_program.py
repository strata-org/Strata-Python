# Ordering comparison after narrowing loss — PLt/PGt catch-all returns Hole
# not TypeError; defense-in-depth fails when narrowing is incomplete
"""
OPTIONAL NARROWING INCOMPLETE — ORDERING COMPARISON ON None PRODUCES
HOLE INSTEAD OF TypeError

The subset allows:
  - Optional[int] (= int | None)
  - isinstance narrowing and `is not None` checks
  - Ordering comparisons (<, >, <=, >=) on int

The gap: if narrowing is INCOMPLETE (e.g., narrowing lost at merge point,
or narrowing not applied after function return), a variable annotated
Optional[int] may still hold None when an ordering comparison is attempted.

CPython: `None < 5` → TypeError: '<' not supported between 'NoneType' and 'int'
Model: PLt(from_None(), from_int(5)) → Hole (no case for from_None in PLt)

This is UNSOUND because:
1. The model doesn't report the TypeError (purpose of Frontend is to catch these)
2. The Hole propagates silently, potentially allowing "verified" status
   for a program that crashes at runtime

This differs from finding 204 (operator on None) because here the None
arrives through a LEGITIMATE Optional[int] variable that SHOULD have been
narrowed but wasn't — the narrowing system has a gap, and the operator
dispatch doesn't catch it as a backup.

The combination of:
  - Finding 137 (narrowing lost at merge)
  - Finding 441 (repeated field access narrowing lost)
  - Finding 270 (None + int → Hole not TypeError)
creates a scenario where a well-typed program with proper guards still
has a path where None reaches an operator, and the model doesn't catch it.
"""
from dataclasses import dataclass


@dataclass
class Measurement:
    value: int
    threshold: int


def find_min(xs: list[int]) -> int:
    """Find minimum — returns first element if list has one element."""
    if len(xs) == 0:
        return 0  # sentinel
    result: int = xs[0]
    i: int = 1
    while i < len(xs):
        if xs[i] < result:
            result = xs[i]
        i = i + 1
    return result


def safe_compare(x: int, y: int) -> bool:
    """Simple comparison — both args are int, no issue."""
    return x < y


def process_optional(val: int, flag: bool) -> int:
    """Process a value that may or may not be compared.
    
    The narrowing gap: after the if/else merge, the model may lose
    track of which branch was taken, and a subsequent comparison
    may operate on a value whose tag is uncertain.
    """
    result: int = 0
    if flag:
        result = val * 2
    else:
        result = val + 1
    # At this point, result is definitely int (both branches assign int)
    # But if the model's merge is lossy (finding 255/413), result may be Hole
    if result < 100:  # PLt on Hole → Hole (not TypeError, but wrong)
        return result
    return 100


def compare_after_function_call(items: list[int]) -> bool:
    """Compare return value of function — requires inter-procedural contract.
    
    CPython: find_min returns int, comparison works.
    Model: find_min may return Hole (finding 416 recursive/loop issues),
           then PLt(Hole, from_int(10)) → Hole, not TypeError.
    
    The REAL danger: if find_min could return None (Optional[int]),
    the model wouldn't catch the TypeError.
    """
    m: int = find_min(items)
    # Model may not know m is from_int (no postcondition assumed)
    return m < 10


def threshold_check(m: Measurement) -> bool:
    """Check if measurement exceeds threshold.
    
    Requires: field access returns typed value (finding 335/441).
    If field access returns Hole, comparison produces Hole.
    """
    v: int = m.value
    t: int = m.threshold
    return v > t


def chained_comparison_with_narrowing(x: int, lo: int, hi: int) -> bool:
    """Chained comparison after narrowing.
    
    Even with all-int operands, if the model loses type info at any point
    (e.g., after function call, after field access, after loop), the
    comparison produces Hole instead of the correct bool.
    """
    # This should be: lo < x < hi  (chained comparison)
    # But chained comparisons have their own issues (finding 429)
    # So we use the explicit form:
    return lo < x and x < hi


def main() -> None:
    # All these should work — all operands are int
    assert safe_compare(3, 5) == True
    assert safe_compare(5, 3) == False

    assert process_optional(10, True) == 20
    assert process_optional(10, False) == 11
    assert process_optional(60, True) == 100  # 120 > 100, clamped

    assert compare_after_function_call([5, 3, 8, 1]) == True
    assert compare_after_function_call([15, 20, 30]) == False

    m1: Measurement = Measurement(value=75, threshold=50)
    m2: Measurement = Measurement(value=30, threshold=50)
    assert threshold_check(m1) == True
    assert threshold_check(m2) == False

    assert chained_comparison_with_narrowing(5, 1, 10) == True
    assert chained_comparison_with_narrowing(15, 1, 10) == False

    print("all passed")


main()
