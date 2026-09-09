# Negative pair: a directly returned list also cannot have negative length.
from typing import List


def get_names() -> List[str]:
    return ["alpha", "beta"]


def main() -> None:
    names = get_names()
    assert len(names) < 0


main()
