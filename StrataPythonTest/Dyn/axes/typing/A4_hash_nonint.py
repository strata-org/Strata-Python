from dataclasses import dataclass
@dataclass(frozen=True)
class D:
    a: object
class H:
    def __hash__(self):
        return 'x'
try:
    hash(D(H()))
except Exception as e:
    print(type(e).__name__, e)
