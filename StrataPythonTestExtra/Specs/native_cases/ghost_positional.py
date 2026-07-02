# @ghost takes no positional arguments; a positional is a hard error.
@ghost("g")
def f(x: int) -> int:
    ...
