# int, float, bool and str as constructors, and their subclasses.
class I(int):
    pass


class F(float):
    pass


class S(str):
    pass


class HasInt:
    def __int__(self):
        return 42


class HasIndex:
    def __index__(self):
        return 7


class HasFloat:
    def __float__(self):
        return 2.5


class BadInt:
    def __int__(self):
        return "x"


class BadFloat:
    def __float__(self):
        return 1


class Text:
    def __str__(self):
        return "text"


def errors(f, *args, **kwargs):
    try:
        f(*args, **kwargs)
    except (TypeError, ValueError, OverflowError) as e:
        print(type(e).__name__, e.args[0])


print(int(), int(7), int(-2.9), int(True), int("  -42 "), int("ff", 16), int("0x1f", 0), int("1_000"))
print(int(b"12"), int(b"z", 36), int(HasInt()), int(HasIndex()), int("١٢"), int(" 7\t"))
print(int(7, base=10) if False else int("10", base=2))
errors(int, "x")
errors(int, "12", 1)
errors(int, "12", 37)
errors(int, 1, 2)
errors(int, 1.5, 2)
errors(int, [])
errors(int, BadInt())
errors(int, 1e308 * 10)
errors(int, 1, 2, 3)
errors(int, base=2)
errors(int, x=1)
errors(int, b"x")
print(float(), float(3), float("1.5"), float(" -2.5e3 "), float("inf"), float("-nan") != 0, float(True))
print(float(HasFloat()), float(HasIndex()), float(b"1.25"), float("1_0.5"), float("١.٥"))
errors(float, "x")
errors(float, [])
errors(float, BadFloat())
errors(float, 1, 2)
errors(float, x=1)
errors(float, 10 ** 400)
print(bool(), bool(0), bool(3), bool(""), bool([1]), bool(Text()))
errors(bool, 1, 2)
errors(bool, x=1)
print(str(), str(5), str(1.5), str(Text()), str(b"ab", "ascii"), str(b"\xc3\xa9", encoding="utf-8"), str(None))
errors(str, 1, "utf-8")
errors(str, "a", "utf-8")
errors(str, b"a", 1)
errors(str, 1, 2, 3, 4)
print(I(5) + 1, type(I(5)).__name__, I("12"), I(), F(1.5) * 2, type(F("2")).__name__, S("ab").upper() if False else S(5) == "5")
print(type(S(5)).__name__, isinstance(I(3), int), I(3) == 3, hash(I(5)), abs(I(-3)), divmod(I(7), 2))
print(I(5).__int__(), type(I(5).__int__()).__name__, F(1.5).__float__(), type(F(1.5).__float__()).__name__)
