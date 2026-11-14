from dataclasses import dataclass, field
@dataclass
class D:
    a: dict = field(default_factory={'k': 1}.copy)
    b: str = field(default_factory=''.upper)
x = D()
print(x, x.a is not D().a)
