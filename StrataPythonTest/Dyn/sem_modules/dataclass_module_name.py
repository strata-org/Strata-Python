# The generated methods' __module__ is their module's __name__.
from dataclasses import dataclass
__name__ = "foo"
@dataclass
class C:
    __module__ = "__main__"
    x: int
print(C.__init__.__module__, C.__repr__.__module__, C.__eq__.__module__)
