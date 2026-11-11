from typing import TypedDict
import typing
M = typing._TypedDictMeta
X = M("X", (), {}, total=False)
print(X.__total__, X.__orig_bases__, X.__module__, X.__mro__)
try:
    Y = M("Y", (), {}, False)
    print("Y", Y.__total__)
except TypeError as e:
    print("TypeError:", e)
Z = M.__new__(M, "Z", (), {}, False)
print(Z.__total__, type(Z).__name__)
W = M.__new__(int, "W", (), {})
print(type(W).__name__, W.__module__)
try:
    M("V", (), {}, total=False, other=1)
except TypeError as e:
    print("TypeError:", e)
