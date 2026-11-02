# Test: a metaclass's own mro() decides the class's __mro__
class M(type):
    def mro(cls):
        return [cls, object]
class A:
    x = 1
class B(A, metaclass=M):
    pass
print(B.__mro__ == (B, object))
