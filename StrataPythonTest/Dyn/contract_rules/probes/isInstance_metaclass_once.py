calls = []
class M(type):
    def __instancecheck__(cls, inst):
        calls.append(1)
        return len(calls) == 1
class C(metaclass=M):
    pass
x = 1
# probe: base.Bool = py.isInstance($x, $C) ^err
# python: isinstance(x, C)
# expect: agree
