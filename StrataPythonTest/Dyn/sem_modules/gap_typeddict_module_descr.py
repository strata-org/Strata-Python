from typing import TypedDict
n = 0
mods = ["mod1", "mod2", "mod3"]
class D:
    def __get__(self, obj, owner):
        global n
        n += 1
        print("get module", n)
        return mods[n - 1]
class M(TypedDict):
    __module__ = D()
    a: "X"
    b: "Y"
print(M.__dict__["__annotations__"])
