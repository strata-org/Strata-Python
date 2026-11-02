# Test: a metaclass returns 42 without making the class, and a saved method reads __class__
saved = None
class Meta(type):
    def __new__(m, name, bases, ns):
        global saved
        saved = ns["f"]
        return 42
class A(metaclass=Meta):
    def f(self):
        return __class__
print(A)
print(saved(None))
