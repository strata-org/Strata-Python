from typing import List
try:
    List[int].foo = 1
except TypeError as e:
    print(type(e).__name__, e)
