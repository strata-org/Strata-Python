from dataclasses import dataclass
class M(type):
    def __getattr__(cls, n):
        print("ev M.getattr", n)
        raise AttributeError(n)
@dataclass
class D(metaclass=M):
    a: int
print(D(1))
