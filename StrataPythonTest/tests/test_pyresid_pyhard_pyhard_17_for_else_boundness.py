def find_or_default(values: list[int], target: int) -> int:
    for value in values:
        if value == target:
            result = value
            break
    else:
        result = 0 - 1
    return result


def else_only(values: list[int]) -> int:
    for value in values:
        if value:
            break
    else:
        result = 0
    return result
