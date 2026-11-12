# replace while the keys of __dataclass_fields__ change at the same size.
from dataclasses import dataclass, replace
@dataclass
class C:
    x: int
    y: int = 0
    def __getattribute__(self, name):
        if name == "x":
            fs = C.__dataclass_fields__
            if "z" not in fs:
                fy = fs["y"]
                del fs["x"]
                fs["z"] = fy
        return object.__getattribute__(self, name)
try:
    print(replace(C(1)))
except RuntimeError as e:
    print("RuntimeError", e)
