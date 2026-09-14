def numeric_effects(
    left: int,
    right: int,
    scale: float,
    shift: int,
) -> tuple[float, float, int, bool]:
    quotient = left / right
    mixed = left + scale
    shifted = left << shift
    flags = True & False
    return quotient, mixed, shifted, flags


def divide_or_zero(left: int, right: int) -> float:
    try:
        return left / right
    except ZeroDivisionError as zero:
        return 0.0
