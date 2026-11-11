# partition and rpartition put the separator argument itself in the result when it matches, an
# instance of a str subclass too, as CPython 3.12 does.
class S(str):
    pass


s = S("b")
r = "ab".partition(s)
print(type(r[1]).__name__, r[1] is s, r)
r = "ab".rpartition(s)
print(type(r[1]).__name__, r[1] is s, r)
r = "ac".partition(s)
print(type(r[1]).__name__, r)
