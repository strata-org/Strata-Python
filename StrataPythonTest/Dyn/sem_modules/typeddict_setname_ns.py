from typing import TypedDict
class M(TypedDict):
    a: int
d = {}
class D:
    def __set_name__(self, owner, name):
        d["__annotations__"] = {"z": int}
d["x"] = D()
N = type(M)("N", (M,), d)
print(N.__required_keys__ == {"a", "z"}, N.__dict__["__annotations__"])
