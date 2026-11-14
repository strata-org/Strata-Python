from dataclasses import dataclass
@dataclass
class D:
    a: int
    @property
    def __post_init__(self):
        print("ev getter")
        return lambda: print("ev called")
print(D(1))
