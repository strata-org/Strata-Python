# Test: a dict resized during its own repr, after a deletion, stops with a gap
class K:
    def __repr__(self):
        del d['a']
        for i in range(4):
            d[i] = i
        return "K"
d = {'a': 1, 'b': K()}
print(d)
