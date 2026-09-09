# iter() called once; custom iterator with state
class OneShotRange:
    def __init__(self, n): self.n = n; self.called = 0
    def __iter__(self):
        self.called += 1
        return iter(range(self.n))
r = OneShotRange(3)
result = [x for x in r]
assert r.called == 1 and result == [0, 1, 2]
print("OK: for loop — iter() called exactly once")
