# Test: a __getattribute__ borrowed from int on a class that inherits object's
class A:
    __getattribute__ = int.__getattribute__
a = A()
try:
    print(a.x)
except TypeError as e:
    print("TE", e)
except AttributeError as e:
    print("AE", e)
