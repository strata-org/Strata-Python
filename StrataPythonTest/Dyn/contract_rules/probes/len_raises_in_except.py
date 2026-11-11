class A:
    def __len__(self):
        try:
            raise KeyError('k')
        except KeyError:
            raise ValueError('v')
x = A()
# probe: py.Value = py.len($x) ^err
# python: len(x)
# expect: agree
