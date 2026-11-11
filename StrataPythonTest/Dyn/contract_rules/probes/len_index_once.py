calls = []
class I:
    def __index__(self):
        calls.append(1)
        return len(calls) * 10
class A:
    def __len__(self):
        return I()
x = A()
# probe: py.Value = py.len($x) ^err
# python: len(x)
# expect: agree
