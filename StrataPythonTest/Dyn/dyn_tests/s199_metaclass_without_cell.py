# Test: a metaclass sees the namespace of a class whose methods don't read __class__
class Meta(type):
    def __new__(m, name, bases, ns):
        print(len(ns), "f" in ns, "__classcell__" in ns)
        return super().__new__(m, name, bases, ns)
class A(metaclass=Meta):
    def f(self):
        return 1
print(A().f(), type(A) is Meta)
