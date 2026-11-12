# The generated __hash__ reads the global hash before the fields.
from dataclasses import dataclass
def myhash(t):
    print("myhash", t)
    return 7
@dataclass(unsafe_hash=True)
class P:
    x: int
    def __getattribute__(self, name):
        global hash
        if name == "x":
            hash = myhash
        return object.__getattribute__(self, name)
print(P.__hash__(P(1)) == (1,).__hash__())
