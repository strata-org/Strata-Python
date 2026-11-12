# The keys of the class namespace change at the same size while the walk over it runs.
from dataclasses import dataclass, field
class Evil:
    def __set_name__(self, owner, name):
        self.owner = owner
    @property
    def __class__(self):
        del self.owner.junk
        self.owner.newf = field()
        return int
try:
    @dataclass
    class C:
        x: int = 0
        junk = 1
        last = Evil()
    print("no error", C.newf is not None)
except TypeError as e:
    print("TypeError", e)
