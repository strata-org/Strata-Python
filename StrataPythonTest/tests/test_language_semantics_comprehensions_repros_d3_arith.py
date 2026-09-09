# Pure arithmetic element over a list of ints.
from typing import List
def fetch() -> List[int]:
    return [-2, 0, 3]
def main() -> None:
    xs = fetch()
    ys = [x * 2 + 1 for x in xs]
    assert len(ys) == len(xs)
main()
