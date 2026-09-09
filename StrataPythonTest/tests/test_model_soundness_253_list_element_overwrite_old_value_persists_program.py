# List element overwrite read-back — `xs[1]=99; xs[1]` needs McCarthy axiom
# `get(set(lst,i,v),i)==v`; without it, read returns unknown
"""
CPython: xs[1] = 99; xs[1] → 99 (overwrite visible)
Model: List_set creates new list, but without McCarthy axiom
       (get(set(lst, i, v), i) == v), the read returns UNKNOWN.

After `xs[1] = 99`, reading `xs[1]` must return 99. This requires
the read-over-write axiom. Without it, the model can't prove that
writing then reading the SAME index returns the written value.

CPython result: xs[1] == 99 (True)
Model result: xs[1] == UNKNOWN (unprovable)
"""


def write_then_read_same() -> int:
    """Write to index, read same index — must get written value."""
    xs: list[int] = [10, 20, 30]
    xs[1] = 99
    return xs[1]  # MUST be 99


def write_preserves_other() -> int:
    """Write to index 1, read index 0 — must get original value."""
    xs: list[int] = [10, 20, 30]
    xs[1] = 99
    return xs[0]  # MUST still be 10


def multiple_writes() -> int:
    """Multiple writes to same index — last write wins."""
    xs: list[int] = [0, 0, 0]
    xs[0] = 1
    xs[0] = 2
    xs[0] = 3
    return xs[0]  # MUST be 3 (last write)


def write_different_indices() -> int:
    """Write to different indices, read all."""
    xs: list[int] = [0, 0, 0]
    xs[0] = 10
    xs[1] = 20
    xs[2] = 30
    return xs[0] + xs[1] + xs[2]  # 60


def write_in_loop() -> list[int]:
    """Write to each index in a loop."""
    xs: list[int] = [0, 0, 0, 0, 0]
    i: int = 0
    while i < 5:
        xs[i] = i * 10
        i = i + 1
    return xs  # [0, 10, 20, 30, 40]


def main() -> None:
    assert write_then_read_same() == 99
    assert write_preserves_other() == 10
    assert multiple_writes() == 3
    assert write_different_indices() == 60
    assert write_in_loop() == [0, 10, 20, 30, 40]

    print(write_then_read_same(), write_preserves_other(),
          write_different_indices())


main()
