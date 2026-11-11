from typing import TypedDict
class G:
    def __get__(self, obj, owner):
        print("get", obj, owner.__name__)
        raise AttributeError("no")
class M(TypedDict):
    __total__ = G()
    x: int
print(type(M.__dict__["__total__"]).__name__)
class N(TypedDict):
    x: int
    __total__ = 7
print(N.__total__)
class P(TypedDict):
    __orig_bases__ = 5
    __required_keys__ = 9
    y: int
print(P.__orig_bases__[0] is TypedDict, len(N.__orig_bases__), P.__required_keys__ == {"y"})
import typing
Q = typing._TypedDictMeta("Q", (P,), {"__orig_bases__": 5, "__total__": None, "__module__": 3.5})
print(Q.__orig_bases__, Q.__total__, Q.__module__)
