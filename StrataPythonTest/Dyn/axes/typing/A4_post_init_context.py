from dataclasses import dataclass
@dataclass
class D:
    a: int
    def __post_init__(self):
        try:
            raise KeyError(1)
        except KeyError:
            raise ValueError('pi')
try:
    D(1)
except Exception as e:
    print(type(e).__name__, e, type(e.__context__).__name__)
