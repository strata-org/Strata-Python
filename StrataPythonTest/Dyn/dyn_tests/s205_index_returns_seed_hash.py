# Test: an __index__ that returns a str's hash, whose number depends on the hash seed
class I:
    def __index__(self):
        return "a".__hash__()
try:
    x = [1, 2, 3][I()]
    print("ok")
except IndexError:
    print("IndexError")
