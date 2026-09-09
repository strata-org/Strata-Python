# Tuples have no constructor in `Any` datatype — `tuple[T1, T2, ...]` is IN
# but unrepresentable
"""
The Any datatype has no from_Tuple constructor. Tuples are IN the Frontend
subset (tuple[T1, T2, ...] with explicit element types, fixed length),
but there is no way to represent them in the value model. They likely
get encoded as ListAny (losing fixed-length and heterogeneous-type info)
or as Hole.
"""


def swap(a: int, b: int) -> tuple[int, int]:
    return (b, a)


def first_and_len(t: tuple[str, int, bool]) -> tuple[str, int]:
    return (t[0], len(t))


def unpack_pair(p: tuple[int, int]) -> int:
    x: int = p[0]
    y: int = p[1]
    return x + y


def main() -> None:
    # Basic tuple creation and access
    pair: tuple[int, int] = swap(3, 7)
    assert pair[0] == 7
    assert pair[1] == 3

    # Tuple length
    t: tuple[str, int, bool] = ("hello", 42, True)
    assert len(t) == 3
    assert t[0] == "hello"
    assert t[1] == 42

    # Tuple in function return
    result: tuple[str, int] = first_and_len(t)
    assert result[0] == "hello"
    assert result[1] == 3

    # Tuple element access for computation
    s: int = unpack_pair((10, 20))
    assert s == 30

    print(pair, result, s)


main()
