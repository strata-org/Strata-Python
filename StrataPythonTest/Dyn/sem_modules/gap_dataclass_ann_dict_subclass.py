# A dataclass's __annotations__ that is an instance of a dict subclass: isinstance(ann, dict) passes,
# and dict(ann) could run the subclass's code.
from dataclasses import dataclass
class MyDict(dict):
    pass
@dataclass
class C:
    __annotations__ = MyDict()
    x: int
    y: int = 0
print(C(1), type(C.__annotations__).__name__)
