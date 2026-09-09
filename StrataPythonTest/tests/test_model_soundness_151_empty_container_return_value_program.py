# Empty container `[]`/`{}` — needs base-case axioms: `List_len(nil)==0`,
# `!contains(empty, k)`
"""
Returning an empty list `[]` or empty dict `{}` from a function must
produce a valid ListAny/DictStrAny with length 0. If the model doesn't
have a representation for empty containers, or if the empty container
has no postconditions (len == 0, contains nothing), callers can't
reason about the returned value.
"""


def empty_list() -> list[int]:
    return []


def empty_dict() -> dict[str, int]:
    return {}


def build_or_empty(flag: bool) -> list[int]:
    if flag:
        return [1, 2, 3]
    return []


def merge_or_empty(a: dict[str, int], key: str) -> dict[str, int]:
    if key in a:
        return a
    return {}


def main() -> None:
    # Empty list properties
    e: list[int] = empty_list()
    assert len(e) == 0
    assert e == []

    # Empty dict properties
    d: dict[str, int] = empty_dict()
    assert len(d) == 0
    assert "x" not in d

    # Conditional return
    full: list[int] = build_or_empty(True)
    assert len(full) == 3
    empty: list[int] = build_or_empty(False)
    assert len(empty) == 0

    # Append to empty
    result: list[int] = empty_list()
    result = result + [42]
    assert len(result) == 1
    assert result[0] == 42

    print(len(e), len(d), len(result))


main()
