# A bare `OLD` (not applied to an expression) must be a hard error.
@admit(lambda x, result: OLD >= x)
def f(x: int) -> int:
    ...
