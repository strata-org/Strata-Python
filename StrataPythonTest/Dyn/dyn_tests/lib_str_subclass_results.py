# Where CPython 3.12 gives a str subclass instance back itself: split and rsplit by a separator
# that is longer or stored wider, partition without a match, and format and format_map when the
# template is the only write, or the last field is.
class S(str):
    def __str__(self):
        return "STR"


class F:
    def __format__(self, spec):
        return S("q" + spec)


x = S("ab")
for r in [x.split("abc")[0], x.rsplit("abc", 1)[0], x.split("\u20ac")[0], x.split("c")[0],
          x.split("\xe9")[0], x.partition("c")[0], x.partition("c")[2], x.rpartition("c")[2],
          x.rpartition("c")[0], x.partition("a")[2], x.format(), S("a{{b").format(),
          x.format_map({}), S("").format()]:
    print(type(r).__name__, r)
for t, a in [("{}", (F(),)), ("{:x}", (F(),)), ("a{}", (F(),)), ("{}{}", ("", F())),
             ("{}{}", (F(), "")), ("{!s}", (x,))]:
    r = t.format(*a)
    print(t, type(r).__name__, r)
