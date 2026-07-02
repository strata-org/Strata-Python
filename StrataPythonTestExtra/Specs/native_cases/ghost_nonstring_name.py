# @ghost name= must be a string literal; a non-string is a hard error.
@ghost(name=123)
def f(x: int) -> int:
    ...
