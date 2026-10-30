# Two `finally` bodies in one function that both `return`: both `fin` blocks end in `ret`.
def f(c, a, b):
    if c:
        try:
            a()
        finally:
            return 1
    try:
        b()
    finally:
        return 2
