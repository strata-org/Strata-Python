# Test: a __hash__ that returns a str's hash, whose number depends on the hash seed
class K:
    def __hash__(self):
        return "a".__hash__()
try:
    s = {K()}
    print("ok")
except TypeError as e:
    print("TypeError", e)
