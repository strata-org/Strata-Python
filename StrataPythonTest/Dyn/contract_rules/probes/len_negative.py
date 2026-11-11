class A:
    def __len__(self):
        return -1
x = A()
# probe: py.Value = py.len($x) ^err
# python: len(x)
# expect: agree
