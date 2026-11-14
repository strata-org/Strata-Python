from typing import List
try:
    print(List[int].append is list.append)
except Exception as e:
    print(type(e).__name__, e)
try:
    print(List[int].__nope__)
except Exception as e:
    print(type(e).__name__, e)
