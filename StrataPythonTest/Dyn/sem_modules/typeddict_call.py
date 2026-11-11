# Calling a TypedDict class calls dict, the library's.
from typing import TypedDict
class Movie(TypedDict):
    name: str
m = Movie(name="x")
print(m, type(m))
