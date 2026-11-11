# An attribute name that is an instance of a str subclass stops with a gap.
class S(str):
    pass


print("before")
getattr(1, S("real"))
