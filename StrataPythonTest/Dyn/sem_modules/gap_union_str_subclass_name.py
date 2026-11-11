# __getattribute__ of a UnionType called with a name that is an instance of a str subclass stops
# with a gap, as a GenericAlias's does.
class S(str):
    pass
U = type(int | str)
print(U.__getattribute__(int | str, S("__args__")))
