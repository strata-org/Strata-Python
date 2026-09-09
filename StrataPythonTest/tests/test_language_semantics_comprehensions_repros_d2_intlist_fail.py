# Negative pair: an identity comprehension cannot add an element.
from typing import List


def fetch() -> List[int]:
    return [-2, 0, 3]


def main() -> None:
    xs = fetch()
    ys = [x for x in xs]
    assert len(ys) == len(xs) + 1


main()
