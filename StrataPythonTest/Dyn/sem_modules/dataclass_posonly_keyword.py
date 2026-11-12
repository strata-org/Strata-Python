# dataclass's cls is positional-only: a keyword that names it raises CPython's TypeError, which
# CPython reports before an unexpected keyword, and an unexpected keyword alone raises its own.
from dataclasses import dataclass
class C:
    x: int
for call in [lambda: dataclass(foo=1, cls=C), lambda: dataclass(cls=C), lambda: dataclass(C, foo=1),
             lambda: dataclass(C, cls=C)]:
    try:
        call()
    except TypeError as e:
        print(e)
