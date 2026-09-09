# Shift rows distinguish negative counts from oversized left shifts.
"""Shift rows distinguish negative counts from oversized left shifts."""


def observe():
    try:
        1 << -1
    except BaseException as error:
        left_negative = type(error).__name__

    try:
        1 >> -1
    except BaseException as error:
        right_negative = type(error).__name__

    huge = 10**100
    try:
        1 << huge
    except BaseException as error:
        left_huge = type(error).__name__

    right_huge = 1 >> huge
    normal = 3 << True
    return (
        left_negative,
        right_negative,
        left_huge,
        (type(right_huge).__name__, right_huge),
        (type(normal).__name__, normal),
    )


RESULT = observe()
