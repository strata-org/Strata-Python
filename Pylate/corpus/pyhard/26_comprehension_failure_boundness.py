def first(values: list[int]) -> int:
    return values[0]


def collect_or_unbound(groups: list[list[int]]) -> list[int]:
    try:
        result = [first(group) for group in groups]
    except IndexError as missing:
        pass
    return result


def preserve_alias_on_failure(
    groups: list[list[int]],
) -> list[int]:
    old = [0]
    result = old
    try:
        result = [first(group) for group in groups]
    except IndexError as missing:
        pass
    return result
