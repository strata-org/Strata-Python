# A field option that is not a bool.
from dataclasses import dataclass, field
class B:
    def __init__(self, tag, v):
        self.tag = tag
        self.v = v
    def __bool__(self):
        print("bool", self.tag)
        return self.v
@dataclass
class C:
    x: int = field(default=0, init=B("init", True), kw_only=B("kw", False), compare=B("cmp", True))
print("done")
