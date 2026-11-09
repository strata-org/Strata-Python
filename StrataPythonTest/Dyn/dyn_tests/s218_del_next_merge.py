# Test: a dict display merging a mapping whose keys iterator's class loses __next__
class KI:
    def __iter__(self): return self
    def __next__(self):
        del KI.__next__
        return "a"
class M:
    def keys(self): return KI()
    def __getitem__(self, k): return 1
try:
    d = {**M()}
except TypeError as e:
    msg = e.args[0]
