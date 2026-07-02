# @ghost requires a name= keyword argument; omitting it is a hard error.
@ghost(type=int)
def f(x: int) -> int:
    ...
