from dataclasses import dataclass, field
n = [0]
def make():
    n[0] += 1
    if n[0] == 1:
        inner = D()
        print("ev inner", inner)
    return n[0]
@dataclass
class D:
    a: int = field(default_factory=make)
print(D(), n)
