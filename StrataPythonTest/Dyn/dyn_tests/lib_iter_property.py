# An __iter__ that is a property giving None: CPython 3.12 says the object is not iterable.
class A:
    __iter__ = property(lambda self: None)


try:
    list(A())
except TypeError as e:
    print(e)
