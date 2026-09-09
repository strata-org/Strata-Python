def rewrite(
    values: list[int],
    replacements: dict[str, int],
    index: int,
) -> int:
    replacement = replacements["value"]
    values[index] = replacement
    return values[index]


def fixed_tuple_read(pair: tuple[int, str]) -> str:
    return pair[1]
