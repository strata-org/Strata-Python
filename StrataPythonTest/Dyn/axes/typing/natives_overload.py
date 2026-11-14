from typing import overload
def f(x): return x
g = overload(f)
print(g.__name__, g is f)
@overload
def h(x: int) -> int: ...
try:
    h(1)
except NotImplementedError as e:
    print(type(e).__name__, str(e))
