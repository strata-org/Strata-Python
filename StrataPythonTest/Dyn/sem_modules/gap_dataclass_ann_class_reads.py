# A dataclass annotation whose class defines __class__.
from dataclasses import dataclass
class A:
    @property
    def __class__(self):
        print("class read")
        return A
    def __repr__(self):
        return "A()"
@dataclass
class C:
    x: A() = 1
print(C.__doc__)
