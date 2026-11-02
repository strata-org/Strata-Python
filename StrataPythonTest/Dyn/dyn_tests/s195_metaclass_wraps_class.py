# Test: a metaclass returns a list that wraps the class whose method reads __class__
class Meta(type):
    def __new__(m, name, bases, ns):
        c = super().__new__(m, name, bases, ns)
        return [c]
class A(metaclass=Meta):
    def f(self):
        return __class__
print(type(A).__name__)
print(A[0].f(None) is A[0])
