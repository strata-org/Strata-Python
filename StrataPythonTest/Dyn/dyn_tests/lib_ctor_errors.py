# The errors of int(), float(), str(), bytes() and set.__new__ as CPython 3.12 gives them: a str
# or bytes subclass named by its own __repr__, the limits of a message, a NUL in a codec name,
# and the keywords that set.__new__ accepts.
class S(str):
    def __repr__(self):
        print("S.__repr__")
        return "SSS"


class B(bytes):
    def __repr__(self):
        print("B.__repr__")
        return "BBB"


class R(str):
    def __repr__(self):
        raise KeyError("repr")


def show(f):
    try:
        print(repr(f()))
    except Exception as e:
        print(type(e).__name__, e)


show(lambda: int(S("abc")))
show(lambda: int(S("xyz"), 16))
show(lambda: float(S("abc")))
show(lambda: float(B(b"xyz")))
show(lambda: int(B(b"xyz")))
show(lambda: int(R("abc")))
show(lambda: int(S("12")) + float(S("1.5")))
try:
    int(b"x" * 201)
except ValueError as e:
    print(len(str(e)), str(e)[-6:])
try:
    int(b"1" * 4301 + b"\x00")
except ValueError as e:
    print(str(e)[:30])
try:
    int(b"1" * 4301 + b"x")
except ValueError as e:
    print(str(e)[:30])
try:
    int(b"1" * 4301 + b"\x00\xff")
except ValueError as e:
    print(str(e)[:30])
show(lambda: str("a", "utf\x008"))
show(lambda: str(5, "utf-8", "x\x00"))
show(lambda: bytes(5, "utf\x008"))
show(lambda: bytes("a", errors="x\x00"))
show(lambda: set.__new__(set, x=1))
show(lambda: set(x=1))
