from dataclasses import dataclass
class B:
    def __post_init__(self):
        print("ev B.pi", self.a)
@dataclass
class D(B):
    a: int
print(D(1))
