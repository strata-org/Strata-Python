from typing import TypedDict
import typing
M = typing._TypedDictMeta
print(M.__dict__["__call__"] is dict, M.__instancecheck__ is M.__subclasscheck__)
print(M.__subclasscheck__.__name__, M.__subclasscheck__.__qualname__, M.__instancecheck__.__qualname__)
print(M.__new__.__name__, M.__new__.__qualname__, type(M.__dict__["__new__"]).__name__)
print(M.__doc__, typing._TypedDict.__doc__)
print(TypedDict.__name__, TypedDict.__qualname__, TypedDict.__module__)
print(TypedDict.__mro_entries__.__name__, TypedDict.__mro_entries__.__qualname__, TypedDict.__mro_entries__.__module__)
print(TypedDict.__mro_entries__((1, 2)))
class A(TypedDict):
    x: int
print(A.__call__ is dict, type(A).__call__ is dict)
try:
    A.__instancecheck__({})
except TypeError as e:
    print("TypeError:", e)
try:
    M.__subclasscheck__(A)
except TypeError as e:
    print("TypeError:", e)
try:
    M.__subclasscheck__(1, 2)
except TypeError as e:
    print("TypeError:", e)
try:
    isinstance(1, (int, A))
    print("ok1")
    isinstance("s", (int, A))
except TypeError as e:
    print("TypeError:", e)
try:
    TypedDict.__mro_entries__()
except TypeError as e:
    print("TypeError:", e)
