def combine(
    left: int,
    right: int,
    scale: float,
    prefix: str,
    suffix: str,
) -> tuple[int, float, str]:
    whole = left + right
    mixed = whole * scale
    text = prefix + suffix
    return whole, mixed, text
