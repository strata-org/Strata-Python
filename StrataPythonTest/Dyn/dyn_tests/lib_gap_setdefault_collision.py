# dict.setdefault with a key whose hash collides with a stored, unequal key: the model runs the
# stored key's __eq__ once, as CPython does, then stops with a gap at the false comparison.
class K:
    def __init__(self, n): self.n = n
    def __hash__(self): return 1
    def __eq__(self, o):
        print("eq", self.n, o.n); return self.n == o.n
d = {K(1): "a"}
print(d.setdefault(K(2), "b"))
