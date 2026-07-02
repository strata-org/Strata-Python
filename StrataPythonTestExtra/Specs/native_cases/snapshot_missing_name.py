# @snapshot requires a name= keyword argument; omitting it is a hard error.
@snapshot(lambda x: x)
def f(x: int) -> int:
    ...
