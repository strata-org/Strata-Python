def membership_modes(
    needle: str,
    text: str,
    items: list[str],
    table: dict[str, int],
) -> tuple[bool, bool, bool]:
    as_substring = needle in text
    as_element = needle in items
    as_key = needle in table
    return as_substring, as_element, as_key
