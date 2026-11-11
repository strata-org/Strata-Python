# TypedDict in class syntax.
from typing import TypedDict, NotRequired, Required, List, Optional
class Movie(TypedDict):
    name: str
    year: NotRequired[int]
class Partial(TypedDict, total=False):
    a: int
    b: Required[str]
class Child(Movie):
    tags: List[str]
    later: "Movie"
print(Movie.__total__, Partial.__total__, type(Movie).__name__, Movie.__module__)
# The key sets' order depends on the hash seed, so the program compares them.
print(Movie.__required_keys__ == {"name"}, Movie.__optional_keys__ == {"year"})
print(Partial.__required_keys__ == {"b"}, Partial.__optional_keys__ == {"a"})
print(Child.__dict__["__annotations__"], Child.__required_keys__ == {"name", "tags", "later"}, Child.__optional_keys__ == {"year"})
print(Movie.__mro__, len(Movie.__orig_bases__), Movie.__orig_bases__[0].__name__, Child.__orig_bases__)
print(type(Movie.__required_keys__).__name__, {Movie.__required_keys__: 1}[Child.__required_keys__ - {"tags", "later"}])
print(Optional[Movie], List[Child])
print(Movie.__required_keys__ | Partial.__required_keys__ == {"name", "b"})
try:
    isinstance({}, Movie)
except TypeError as e:
    print("TypeError:", e)
try:
    class Bad(TypedDict, int):
        pass
except TypeError as e:
    print("TypeError:", e)
try:
    class Bad2(TypedDict):
        x: (int, str)
except TypeError as e:
    print("TypeError:", e)
d = {"__annotations__": {"z": int}}
N = type(Movie)("N", (Movie,), d)
print(N.__module__, "__module__" in d, N.__required_keys__ == {"name", "z"}, Movie.__required_keys__ == {"name"})
