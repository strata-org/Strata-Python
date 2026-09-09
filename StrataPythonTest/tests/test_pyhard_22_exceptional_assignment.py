def first_or_unbound(values: list[int]) -> int:
    try:
        result = values[0]
    except IndexError as missing:
        pass
    return result


def keep_old_on_failure(values: list[int]) -> int | str:
    result = "old"
    try:
        result = values[0]
    except IndexError as missing:
        pass
    return result


def keep_alias_on_failure(
    original: list[int],
    candidates: list[list[int]],
) -> list[int]:
    result = original
    try:
        result = candidates[0]
    except IndexError as missing:
        pass
    return result
