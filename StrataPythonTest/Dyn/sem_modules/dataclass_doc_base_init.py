# The docstring takes its annotations from the generated __init__ that it finds.
from dataclasses import dataclass
@dataclass
class A:
    x: int
@dataclass(init=False)
class B(A):
    x: str
print(B.__doc__)
