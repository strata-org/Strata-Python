from dataclasses import dataclass
class C:
    def __call__(self, *a):
        print("ev call", len(a))
@dataclass
class D:
    a: int
    __post_init__ = C()
print(D(1))
