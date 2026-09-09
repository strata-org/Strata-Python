# Element is a bare NAME (no subscript) -> pure -> closed-form map expected.
from typing import List
def fetch() -> List[int]:
    return [-2, 0, 3]
def main() -> None:
    xs = fetch()
    ys = [x for x in xs]        # identity map, element is pure
    assert len(ys) == len(xs)
main()
