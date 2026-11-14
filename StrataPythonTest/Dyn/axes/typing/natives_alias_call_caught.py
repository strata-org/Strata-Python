from typing import List, Any
try:
    List[int]([1])
except TypeError as e:
    print(type(e).__name__, e)
try:
    isinstance(1, Any)
except TypeError as e:
    print(type(e).__name__, e)
