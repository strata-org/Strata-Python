# Negative pair: an unfiltered map preserves source length.
from typing import List


def fetch() -> List[int]:
    return [1, 2, 3]


def main() -> None:
    xs = fetch()
    ys = [value * 2 for value in xs]
    assert len(ys) != len(xs)


main()
