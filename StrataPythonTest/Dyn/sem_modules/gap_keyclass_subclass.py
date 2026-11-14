# An instance of a plain subclass of a frozen dataclass inherits the generated methods.
from dataclasses import dataclass
@dataclass(frozen=True)
class K:
    a: int
class S(K):
    pass
d = {S(-1): 1, S(-2): 2}
print(len(d))
