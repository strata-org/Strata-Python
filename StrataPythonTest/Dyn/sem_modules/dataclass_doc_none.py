# The docstring removes every ' -> None'.
from dataclasses import dataclass
@dataclass
class C:
    x: str = " -> None"
print(C.__doc__)
