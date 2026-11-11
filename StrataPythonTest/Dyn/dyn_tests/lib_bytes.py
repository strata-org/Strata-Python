# bytes as a constructor: sizes, iterables of ints, encodings, __bytes__ and the errors.
class B:
    def __bytes__(self):
        return b"from bytes"


class Idx:
    def __index__(self):
        return 3


class BadIdx:
    def __index__(self):
        raise TypeError("no")

    def __iter__(self):
        return iter([65])


class Down:
    def __init__(self, n):
        self.n = n

    def __iter__(self):
        return self

    def __next__(self):
        if self.n == 0:
            raise StopIteration
        self.n -= 1
        return self.n + 64


class Bs(bytes):
    pass


def errors(f, *args, **kwargs):
    try:
        f(*args, **kwargs)
    except (TypeError, ValueError, OverflowError) as e:
        print(type(e).__name__, e.args[0])


print(bytes(), bytes(3), bytes([65, 66]), bytes((67,)), bytes(range(68, 70)), bytes(Idx()))
print(bytes(B()), bytes("é", "utf-8"), bytes("ab", encoding="ascii"), bytes(b"xy"), bytes(Down(3)))
print(bytes(BadIdx()), bytes(Bs(b"q")), type(Bs(b"q")).__name__, Bs([70]))
errors(bytes, -1)
errors(bytes, "a")
errors(bytes, 1.5)
errors(bytes, [256])
errors(bytes, [-1])
errors(bytes, ["a"])
errors(bytes, 1, "ascii")
errors(bytes, "a", errors="strict")
errors(bytes, encoding="ascii")
errors(bytes, errors="strict")
errors(bytes, "a", 1)
errors(bytes, 1, 2, 3, 4)
errors(bytes, 2 ** 70)
