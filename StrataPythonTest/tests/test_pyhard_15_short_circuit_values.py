def choose_mapping(
    primary: dict[str, int] | None,
    fallback: dict[str, int],
) -> dict[str, int]:
    return primary or fallback


def choose_scalar(primary: int, fallback: str) -> int | str:
    return primary or fallback
