# with + return: `__exit__` must run before the function returns.
def acquire():
    return 1

def f(x):
    with acquire() as r:
        return r
