from typing import TypedDict
class K(str):
    pass
class TD(TypedDict):
    a: int
x = TD(**{K('a'): 1})
print(type(list(x)[0]).__name__, x)
