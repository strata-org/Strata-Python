# Test: a class call whose metaclass defines __getattribute__
class MM(type):
    def __getattribute__(cls, n):
        if n == "__new__":
            print("ga", n)
        return type.__getattribute__(cls, n)
class C(metaclass=MM):
    def __new__(cls):
        return object.__new__(cls)
print("made")
x = C()
print("called")
