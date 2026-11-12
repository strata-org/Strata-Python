# The walk over the class's namespace checks its size after its last entry.
from dataclasses import dataclass
class Evil:
    def __set_name__(self, owner, name):
        self.owner = owner
    @property
    def __class__(self):
        self.owner.zzz = 1
        return int
try:
    @dataclass
    class C:
        __doc__ = "d"
        __dataclass_params__ = None
        __slots__ = ()
        x: int = 0
        last = Evil()
    print("no error", C.zzz)
except RuntimeError as e:
    print("RuntimeError", e)
