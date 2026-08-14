# OLD takes no keyword arguments; passing one must be a hard error.
@admit(lambda x, result: OLD(x, extra="y") >= x)
def f(x: int) -> int:
    ...
