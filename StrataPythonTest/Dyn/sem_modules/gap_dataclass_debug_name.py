# A field named __debug__.
from dataclasses import dataclass
try:
    @dataclass
    class C:
        x: int
        __annotations__["__debug__"] = int
    print(C(1, 2))
except SyntaxError as e:
    print("SyntaxError", e.msg)
