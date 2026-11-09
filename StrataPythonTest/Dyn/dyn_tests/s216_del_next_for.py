# Test: a for loop over an iterator whose class loses __next__ while it is in use
class It:
    def __iter__(self): return self
    def __next__(self):
        del It.__next__
        return 1
try:
    for x in It():
        pass
except TypeError as e:
    msg = e.args[0]
