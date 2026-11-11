# NamedTuple twice among the bases.
from typing import NamedTuple
try:
    class P(NamedTuple, NamedTuple):
        x: int
    print("made", P.__bases__, P(1))
except TypeError as e:
    print("TypeError:", e)
