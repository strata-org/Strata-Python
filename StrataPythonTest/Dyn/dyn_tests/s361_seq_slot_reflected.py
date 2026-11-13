# A built-in sequence's own + and * against a user object: CPython tries the sequence's slot after
# the number protocol, so the user object's reflected dunder runs first.
class X(Exception):
    def __radd__(self, o):
        return "X.radd"
    def __rmul__(self, o):
        return "X.rmul"
print([1] + X(), (1,) + X(), "a" + X(), b"a" + X())
print([1] * X(), "a" * X())
x = [1]
x += X()
print(x)
