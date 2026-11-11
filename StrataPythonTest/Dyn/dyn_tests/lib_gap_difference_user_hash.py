# The difference of a large set and a small dict whose key has a user __hash__: CPython hashes the
# key again; the model stops with a gap before its walk of the dict.
class H:
    def __init__(self, n): self.n = n
    def __hash__(self): print("hash", self.n); return self.n
    def __eq__(self, o): return isinstance(o, H) and self.n == o.n
print(len(set(range(100)).difference({H(1): 0})))
