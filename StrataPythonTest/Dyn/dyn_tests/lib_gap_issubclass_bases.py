# issubclass of an object that is no class but has __bases__ stops with a gap.
def f():
    pass


f.__bases__ = (int,)
print("before")
issubclass(f, int)
