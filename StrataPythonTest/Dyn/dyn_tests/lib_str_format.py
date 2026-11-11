# str.format and str.format_map: numbering, names, accessors, conversions, nested specs, the
# order of the lookups and calls, and the errors.
class P:
    def __init__(self, v):
        self.v = v

    def __format__(self, spec):
        print("format", self.v, repr(spec))
        return f"<{self.v}:{spec}>"

    def __repr__(self):
        return f"P({self.v})"

    def __getitem__(self, k):
        print("getitem", repr(k))
        return P(k)


class M:
    def __getitem__(self, k):
        print("map", repr(k))
        return len(k)


def show(f, *args, **kwargs):
    try:
        print(repr(f(*args, **kwargs)))
    except (ValueError, IndexError, KeyError, AttributeError, TypeError) as e:
        print(type(e).__name__, e.args[0])


print("{} and {}".format(1, "a"), "{1}{0}{1}".format("x", "y"), "{a}-{b}".format(a=1, b=2))
print("{{}} {0!r} {0!s} {0!a}".format("é"), "{0:>5}|{1:.2f}|{2:x}".format("ab", 3.14159, 255))
print("{0.v} {0[3]} {0[k]}".format(P(7)))
print("{:{}}".format(P(1), "w"), "{0:{1}{2}}".format(3.5, ">", 8))
print("{p} {p!r:>8}".format(p=P(2)))
print("a{x}b{y}".format_map(M()))
print("{0[0]} {0[1][1]}".format([1, "ab"]), "{d[k]}".format(d={"k": "v"}))
show("{} {1}".format, 1, 2)
show("{1} {}".format, 1, 2)
show("{5}".format, 1)
show("{x}".format, y=1)
show("{0.nope}".format, 1)
show("{0!z}".format, 1)
show("{".format)
show("}".format)
show("{0:{1:{2}}}".format, 1, 2, 3)
show("{0}".format_map, {})
show("{x}".format_map, {})
show("{0[}".format, [1])
show("{0.}".format, 1)
show("{:d}".format, "x")
show(str.format, 1)
print(str.format("{}-{}", 1, 2), "{}".format(P(3)))
