# Test: a __getattribute__ borrowed from type on a plain class
class A:
    __getattribute__ = type.__getattribute__
try:
    print(A().x)
except TypeError as e:
    print("TE", e)
except AttributeError as e:
    print("AE", e)
