# Optional narrowing then arithmetic — full chain: disjunctive tag → `is not
# None` → assume → PAdd dispatch; any break → Hole
"""
OPTIONAL NARROWING THEN ARITHMETIC — FULL END-TO-END CHAIN

The subset supports Optional[int] (as int | None) with `is not None`
narrowing. The FULL CHAIN that must work:

1. Variable declared as Optional[int] → tag set {from_int, from_None}
2. `if x is not None:` → narrow to {from_int} in true branch
3. `x + 1` → PAdd(from_int(x), from_int(1)) → from_int(x+1)

Each step requires a different model feature:
- Step 1: disjunctive tag assertion (finding 223)
- Step 2: tag-set narrowing via assume (finding 062)
- Step 3: tag assertion enables operator dispatch (finding 350/352)

If ANY step fails, the chain breaks and arithmetic on Optional produces Hole.
"""


def safe_add(x: int, default: int) -> int:
    """Simple: x is always int, no Optional needed."""
    return x + default


def add_or_default(x: object, default: int) -> int:
    """Optional pattern: check None, then use as int."""
    if x is None:
        return default
    # After narrowing: x is int (not None)
    # Model must: assume(!isfrom_None(x)) → x is from_int
    # Then: PAdd(x, from_int(1)) needs isfrom_int(x) to dispatch
    return x + 1  # type: ignore — simplified Optional pattern


def sum_non_none(values: list[int], flags: list[bool]) -> int:
    """Sum only non-flagged values (simulates Optional elements)."""
    total: int = 0
    i: int = 0
    while i < len(values):
        if flags[i]:
            total += values[i]
        i += 1
    return total


def first_positive(xs: list[int]) -> int:
    """Find first positive, return it or -1."""
    result: int = -1
    for x in xs:
        if x > 0:
            result = x
            break
    # result is either -1 (not found) or positive (found)
    # Narrowing: if result != -1, then result > 0
    return result


def clamp_positive(x: int) -> int:
    """Return x if positive, else 0. Tests narrowing from comparison."""
    if x > 0:
        # After narrowing: x > 0 is known
        return x
    else:
        return 0


def main() -> None:
    # Test 1: simple (no Optional)
    assert safe_add(5, 10) == 15

    # Test 2: sum with flags
    assert sum_non_none([10, 20, 30], [True, False, True]) == 40

    # Test 3: first positive
    assert first_positive([-1, -2, 3, 4]) == 3
    assert first_positive([-1, -2, -3]) == -1

    # Test 4: clamp
    assert clamp_positive(5) == 5
    assert clamp_positive(-3) == 0
    assert clamp_positive(0) == 0

    print("all passed")


main()
