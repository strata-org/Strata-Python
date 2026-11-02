# Test: a base with its own __new__ and __init_subclass__, and its __new__ called through a subclass instance
class C:
    def __new__(cls):
        return object.__new__(cls)
    def __init_subclass__(cls):
        print("isc", cls.__name__)
class D(C):
    pass
print(type(D().__new__(D)) is D)
