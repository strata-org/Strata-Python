# Nested if-else state merge — after branches, variable has value from taken
# branch; solver must handle both cases
"""
After nested if-else branches merge, the verifier must correctly handle
the UNION of possible states. If one branch sets x to a value and the
other doesn't, the merged state must reflect both possibilities.

Uses ONLY confirmed-accepted constructs: if/elif/else, int arithmetic,
comparison, function def.
"""


def abs_value(x: int) -> int:
    if x >= 0:
        result: int = x
    else:
        result = -x
    # At merge: result is defined on both paths
    return result


def classify(x: int) -> int:
    if x > 0:
        category: int = 1
    elif x < 0:
        category = -1
    else:
        category = 0
    # At merge: category is one of {-1, 0, 1}
    return category


def bounded_increment(x: int, limit: int) -> int:
    result: int = x
    if result < limit:
        result = result + 1
    # At merge: result is either x (unchanged) or x+1
    # In both cases: result >= x
    return result


def nested_conditions(a: int, b: int) -> int:
    if a > 0:
        if b > 0:
            return a + b
        else:
            return a - b
    else:
        if b > 0:
            return b - a
        else:
            return -(a + b)


def main() -> None:
    # Abs value: both branches define result
    assert abs_value(5) == 5
    assert abs_value(-3) == 3
    assert abs_value(0) == 0

    # Classify
    assert classify(10) == 1
    assert classify(-5) == -1
    assert classify(0) == 0

    # Bounded increment
    assert bounded_increment(5, 10) == 6
    assert bounded_increment(10, 10) == 10  # at limit, no increment

    # Nested
    assert nested_conditions(3, 4) == 7
    assert nested_conditions(3, -2) == 5
    assert nested_conditions(-3, 4) == 7
    assert nested_conditions(-3, -4) == 7

    print(abs_value(-7), classify(0), bounded_increment(5, 10))


main()
