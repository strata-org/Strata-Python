# Test: a list display unpacking an iterator whose class loses __next__ while it is in use
class It:
    def __iter__(self): return self
    def __next__(self):
        del It.__next__
        return 1
try:
    a = [*It()]
except TypeError as e:
    caught = "TypeError: " + e.args[0]
