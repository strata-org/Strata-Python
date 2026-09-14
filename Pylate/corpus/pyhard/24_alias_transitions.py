def branch_alias(
    flag: bool,
    left: list[int],
    right: list[int],
) -> list[int]:
    if flag:
        selected = left
    else:
        selected = right
    selected.append(1)
    return selected


def delete_one_name() -> list[int]:
    original = []
    alias = original
    del original
    alias.append(1)
    return alias


def rebind_one_name() -> list[int]:
    original = []
    alias = original
    original = {}
    alias.append(1)
    return alias
