# Test: a class's own __new__ called through an instance gets no self, as a static method
class C:
    def __new__(cls):
        return object.__new__(cls)
c = C()
d = c.__new__(C)
print(type(d) is C)
