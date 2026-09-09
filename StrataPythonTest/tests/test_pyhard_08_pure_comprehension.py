def increment(value: int) -> int:
    return value + 1


def collect(values: list[int]) -> list[int]:
    result: list[int] = [
        increment(value)
        for value in values
        if value
    ]
    return result


def collect_unique(values: list[int]) -> set[int]:
    return {
        increment(value)
        for value in values
        if value
    }


def copy_unordered(values: set[int]) -> list[int]:
    return [value for value in values]
