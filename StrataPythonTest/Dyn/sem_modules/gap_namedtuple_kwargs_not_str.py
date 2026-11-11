# A named tuple's methods called with a keyword that is not a str: CPython raises "keywords must be
# strings", and the call of a built-in with such a keyword stops with a gap.
from typing import NamedTuple


class P(NamedTuple):
    x: int
    y: int = 0


for f in (lambda: P(**{"w": 1, 1: 2}), lambda: P(1, 2, 3, **{1: 2}), lambda: P._make(**{"q": 1, 1: 2}),
          lambda: P(1)._replace(**{1: 2})):
    try:
        print(f())
    except TypeError as e:
        print("TypeError:", e)
