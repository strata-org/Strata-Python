# Class instantiation: boundary case. Custom __new__ returning a different
# type makes the simplified model unsound.
"""Class instantiation: boundary case.
Custom __new__ returning a different type makes the simplified model unsound.
"""

class Singleton:
    _instance = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance  # returns existing object, not fresh!

    def __init__(self):
        self.value = 42

class Weird:
    def __new__(cls):
        # Returns an instance of a DIFFERENT class
        return object.__new__(object)

if __name__ == "__main__":
    a = Singleton()
    b = Singleton()
    print(a is b)        # True -- NOT a fresh object! Model assumes fresh.
    print(type(a))       # <class 'Singleton'>

    w = Weird()
    print(type(w))       # <class 'object'> -- NOT Weird! Model assumes type == Weird.
    print(hasattr(w, 'value'))  # False -- __init__ was skipped (typeobject.c:2474)
