from typing import TypedDict
class D:
    def __get__(self, obj, owner):
        print("get module")
        return "mod"
class E(TypedDict):
    __module__ = D()
print("E made")
