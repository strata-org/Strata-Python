# Test: f(*x) with a length hint beyond the model's bound stops with a gap, where CPython may raise MemoryError
class It:
    def __init__(self):
        self.i = 0
    def __iter__(self):
        return self
    def __next__(self):
        self.i += 1
        if self.i > 2:
            raise StopIteration
        return self.i
    def __length_hint__(self):
        return 2**62
def f(*a):
    return len(a)
try:
    print(f(*It()))
except MemoryError:
    print("MemoryError")
