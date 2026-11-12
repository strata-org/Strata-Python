# A docstring annotation whose __module__ is not a str.
from dataclasses import dataclass
class A:
    __module__ = None
class B:
    __module__ = 5
@dataclass
class C:
    x: A = 1
print(C.__doc__)
@dataclass
class D:
    x: B = 1
print(D.__doc__)
