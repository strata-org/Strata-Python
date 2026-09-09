# Negative pair: the arithmetic map does not preserve every element.
from typing import List


def fetch() -> List[int]:
    return [-2, 0, 3]


def main() -> None:
    xs = fetch()
    ys = [x * 2 + 1 for x in xs]
    assert ys == xs


main()
