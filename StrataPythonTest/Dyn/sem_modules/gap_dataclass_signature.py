# The docstring of a class whose MRO defines __signature__.
from dataclasses import dataclass
class B:
    __signature__ = None
@dataclass
class P(B):
    x: int
print(P.__doc__)
