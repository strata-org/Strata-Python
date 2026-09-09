def inspect_containers(
    values: list[int | str],
    lookup: dict[str, set[int]],
    pair: tuple[int, str],
) -> tuple[int | str, set[int], str]:
    first = values[0]
    bucket = lookup["numbers"]
    second = pair[1]
    local: list[int] = [1, 2, 3]
    return first, bucket, second
