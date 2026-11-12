# The generated methods read hash, type, super and NotImplemented as globals of the class's module.
from dataclasses import dataclass
def hash(x):
    print("user hash", x)
    return 42
NotImplemented = "user NI"
@dataclass(frozen=True)
class F:
    a: int
f = F(1)
print(f.__hash__())
print(F.__eq__(f, 3))
type = lambda o: print("user type", o)
try:
    f.a = 2
except AttributeError as e:
    print(e)
