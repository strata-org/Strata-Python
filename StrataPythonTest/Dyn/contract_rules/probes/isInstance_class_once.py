calls = []
class A:
    @property
    def __class__(self):
        calls.append(1)
        return int if len(calls) == 1 else str
a = A()
I = int
# probe: base.Bool = py.isInstance($a, $I) ^err
# python: isinstance(a, I)
# expect: agree
