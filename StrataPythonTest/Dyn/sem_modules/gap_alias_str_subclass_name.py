# __getattribute__ of a GenericAlias or a UnionType called with a name that is an instance of a str
# subclass: CPython's type lookup hashes it with its own __hash__, so it stops with a gap.
class S(str):
    pass
GA = type(list[int])
print(GA.__getattribute__(list[int], S("__origin__")))
print(GA.__getattribute__(list[int], S("append")))
