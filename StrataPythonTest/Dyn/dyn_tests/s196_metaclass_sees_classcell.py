# Test: a metaclass sees __classcell__ in the namespace of a class whose method reads __class__
class Meta(type):
    def __new__(m, name, bases, ns):
        print(len(ns), "__classcell__" in ns)
        return super().__new__(m, name, bases, ns)
class A(metaclass=Meta):
    def f(self):
        return __class__
