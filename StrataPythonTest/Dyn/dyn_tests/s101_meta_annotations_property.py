# Test: a write of a class's __annotations__ through a data descriptor set as the metaclass's __annotations__
class D:
    def __get__(self, o, t):
        return {}
    def __set__(self, o, v):
        print("set")
class M(type):
    pass
M.__annotations__ = D()
class C(metaclass=M):
    pass
C.__annotations__ = {"x": 1}
print("after")
