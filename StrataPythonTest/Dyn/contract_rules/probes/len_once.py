calls = []
class A:
    def __len__(self):
        calls.append(1)
        return len(calls) * 10
x = A()
# probe: py.Value = py.len($x) ^err
# python: len(x)
# expect: agree
