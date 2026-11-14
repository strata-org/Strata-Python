from typing import NamedTuple
class P(NamedTuple):
    x: object
class R:
    def __repr__(self):
        raise KeyError('r')
try:
    repr(P(R()))
except Exception as e:
    print(type(e).__name__, e)
