# A class's __annotations__ is the entry of its own namespace.
from typing import TypedDict
class Movie(TypedDict):
    name: str
print(Movie.__annotations__ is Movie.__dict__["__annotations__"], Movie.__annotations__)
