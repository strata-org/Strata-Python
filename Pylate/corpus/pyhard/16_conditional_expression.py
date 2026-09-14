def choose(flag: bool, number: int, text: str) -> int | str:
    return number if flag else text


def guarded_head(
    use_default: bool,
    values: list[int],
) -> int:
    return 0 if use_default else values[0]
