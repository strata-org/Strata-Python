# Test: a __length_hint__ that returns a str's hash, whose number depends on the hash seed
class L:
    def __iter__(self):
        return iter([1, 2])
    def __length_hint__(self):
        return "a".__hash__()
try:
    x = [*L()]
    print(x[0])
except (TypeError, ValueError, OverflowError) as e:
    print(type(e).__name__)
