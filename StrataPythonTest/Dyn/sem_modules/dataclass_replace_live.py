# replace walks the live __dataclass_fields__.
from dataclasses import dataclass, replace
@dataclass
class C:
    x: int
    y: int = 0
    def __getattribute__(self, name):
        if name == "x":
            C.__dataclass_fields__["z"] = C.__dataclass_fields__["y"]
        return object.__getattribute__(self, name)
try:
    print(replace(C(1)))
except RuntimeError as e:
    print("RuntimeError", e)
