# NAIVE MODEL WOULD GET WRONG: calls iter() each iteration
class CountedIter:
    def __init__(self): self.iter_calls = 0; self.items = [1,2,3]; self.idx = 0
    def __iter__(self): self.iter_calls += 1; return self
    def __next__(self):
        if self.idx >= len(self.items): raise StopIteration
        v = self.items[self.idx]; self.idx += 1; return v
ci = CountedIter()
for _ in ci: pass
# Naive (iter at each step): iter_calls > 1. CPython: exactly 1
assert ci.iter_calls == 1
print("BOUNDARY: naive model might call iter() per iteration; CPython calls it once")
