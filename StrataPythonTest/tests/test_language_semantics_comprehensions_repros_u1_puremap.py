# U1 puremap
from typing import List

def fetch() -> List[int]:
    return [1, 2, 3]

def main() -> None:
    xs = fetch()
    ys = [x * 2 for x in xs]        # PURE element expr -> should be closed-form
    assert len(ys) == len(xs)

main()
