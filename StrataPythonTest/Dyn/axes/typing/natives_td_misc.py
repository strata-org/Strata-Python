from typing import TypedDict
class TD(TypedDict):
    a: int
print(TD.__name__, TD.__module__, TD(a=1) == {'a': 1}, type(TD).__name__)
try:
    issubclass(dict, TD)
except Exception as e:
    print(type(e).__name__, e)
