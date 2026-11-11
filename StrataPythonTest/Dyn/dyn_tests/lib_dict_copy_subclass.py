# d.copy() of a dict subclass that overrides __iter__ follows dict_merge: it looks keys up once,
# and an error of that lookup propagates.
class D(dict):
    def __iter__(self):
        return iter(["a"])

    @property
    def keys(self):
        print("keys looked up")
        return lambda: ["a"]


c = D(a=0).copy()
print(type(c).__name__, c)


class E(dict):
    def __iter__(self):
        return iter([("x", 1)])

    def __getattribute__(self, n):
        if n == "keys":
            return object.__getattribute__(self, "nokeys")
        return object.__getattribute__(self, n)


try:
    print(E(a=0).copy())
except AttributeError as e:
    print("AttributeError", e)
print(D(b=1, a=2).copy(), D().copy())
