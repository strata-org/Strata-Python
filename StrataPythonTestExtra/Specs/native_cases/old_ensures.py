# OLD(expr) in @ensures is a valid two-state pre-state reference.
@ensures(lambda x, result: OLD(x) >= x)
def f(x: int) -> int:
    ...
