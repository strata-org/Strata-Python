# Test: a metaclass deletes __classcell__ before type.__new__
class Meta(type):
    def __new__(m, name, bases, ns):
        del ns["__classcell__"]
        return super().__new__(m, name, bases, ns)
class A(metaclass=Meta):
    def f(self):
        return __class__
print("made")
