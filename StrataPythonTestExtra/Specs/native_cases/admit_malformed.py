# Malformed @admit: the argument is not a lambda. Must be a hard error.
@admit(42)
def f(x: int) -> int:
    ...
