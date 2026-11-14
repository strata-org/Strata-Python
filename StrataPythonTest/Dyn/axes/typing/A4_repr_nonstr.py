from dataclasses import dataclass
@dataclass
class D:
    a: object
class R:
    def __repr__(self):
        return 5
try:
    repr(D(R()))
except Exception as e:
    print(type(e).__name__, e)
