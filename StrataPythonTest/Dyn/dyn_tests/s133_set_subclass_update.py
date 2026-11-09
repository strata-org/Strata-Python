# Test: {*S(...)} for a subclass of set merges its members without its __iter__ (stops with a gap until set() exists)
class S(set):
    def __iter__(self):
        return iter([9])
s = {*S([1])}
print(len(s), 1 in s)
