# The str methods that convert their arguments and run no other user code: results, argument
# errors in CPython's order, a str subclass as self and as an argument, and __index__.
class S(str):
    pass


class I:
    def __index__(self):
        print("index")
        return 2


def show(f, *args, **kwargs):
    try:
        print(repr(f(*args, **kwargs)))
    except (TypeError, ValueError, OverflowError) as e:
        print(type(e).__name__, e.args[0])


s = "Hello World\tab"
for name in ["upper", "lower", "casefold", "swapcase", "capitalize", "title", "isalpha",
             "isdecimal", "isdigit", "isnumeric", "isalnum", "isspace", "isupper", "islower",
             "istitle", "isidentifier", "isprintable", "isascii"]:
    print(name, repr(getattr(s, name)()), repr(getattr("ΑΣ", name)()), repr(getattr("", name)()))
show(s.find, "o")
show(s.find, "o", 5)
show(s.find, "o", I(), None)
show(s.rfind, "o", -100, 100)
show(s.index, "z")
show(s.rindex, "z")
show(s.count, "l")
show(s.count, "")
show(s.find, 1)
show(s.find, "a", "x")
show(s.find, 1, "x")
show(s.startswith, "He")
show(s.startswith, ("x", "He", 1))
show(s.startswith, ("x", 1))
show(s.endswith, "ab", 0, I())
show(s.startswith, 1)
show(s.endswith, ["a"])
show(s.replace, "l", "L")
show(s.replace, "l", "L", 1)
show(s.replace, "", "-", I())
show(s.replace, 1, "a")
show(s.replace, "a", 1)
show(s.replace, "a", "b", "x")
show(s.replace, "a", "b", 2 ** 70)
show(s.split)
show(s.split, "o")
show(s.split, None, 1)
show(s.split, maxsplit=1, sep="l")
show(s.rsplit, "o", 1)
show(s.rsplit, None, 1)
show(s.split, 1)
show(s.split, "")
show(s.split, "a", 1.5)
show(s.split, "a", 2 ** 70)
show("a\nb\r\nc".splitlines)
show("a\nb\r\nc".splitlines, True)
show("a\nb".splitlines, keepends=1.5)
show(s.partition, "o")
show(s.rpartition, "o")
show(s.partition, "z")
show(s.partition, 1)
show(s.partition, "")
show("  ab  ".strip)
show("xxabyy".strip, "xy")
show("  ab  ".lstrip, None)
show("  ab  ".rstrip)
show(s.strip, 1)
show(s.lstrip, 1)
show(s.rstrip, 1)
show(s.removeprefix, "Hel")
show(s.removesuffix, "ab")
show(s.removeprefix, 1)
show(s.removesuffix, 1)
show("ab".ljust, 5)
show("ab".rjust, 5, "*")
show("ab".center, 7, S("-"))
show("ab".center, I())
show("ab".ljust, "x")
show("ab".ljust, 3, "xy")
show("ab".ljust, 3, 1)
show("ab".ljust, 2 ** 70)
show("-42".zfill, 6)
show("ab".zfill, "x")
show("a\tbc\td".expandtabs)
show("a\tbc\td".expandtabs, 4)
show("a\tb".expandtabs, tabsize=I())
show("a\tb".expandtabs, "x")
show("a\tb".expandtabs, 2 ** 40)
t = S("Hello")
print(type(t.upper()).__name__, t.upper(), t.find("l"), t.split("l"), type(t.strip()).__name__)
print(str.upper("ab"), str.count("aaa", "a"))
show(str.upper, 1)
print("ß".upper(), "ŉ".upper(), "İ".lower(), "ﬁ".title())
show("ab".removeprefix, None)
show("ab".replace, None, "a")
show("ab".replace, "a", None)
show("ab".encode, None)
show("ab".find, None)
