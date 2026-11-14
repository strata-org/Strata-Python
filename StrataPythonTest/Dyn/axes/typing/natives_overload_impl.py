from typing import overload
@overload
def h(x: int) -> int: ...
try:
    h(1)
except NotImplementedError as e:
    print(type(e).__name__, str(e))
print(overload(h).__name__)
