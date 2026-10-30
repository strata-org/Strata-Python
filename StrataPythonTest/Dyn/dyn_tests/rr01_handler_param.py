# A local assigned around two raising calls and read in `except`: the handler's block takes its
# content as a new parameter.
def f(a, b):
    x = 0
    try:
        x = g(a)
        x = g(b)
    except ValueError:
        return x
    return x
