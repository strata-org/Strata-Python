from dataclasses import dataclass, field
class S(str):
    def __new__(cls):
        print("ev S.new")
        return super().__new__(cls, "s")
@dataclass
class D:
    a: str = field(default_factory=S)
x = D()
print(type(x.a).__name__, x)
