# CPython 3.12 with -S, with 100 frames below this module, runs this operation at depth 859 and
# raises RecursionError at depth 860; the model must stop with a gap at depth 860.
def op():
    import typing
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(860)
    print('ok')
except RecursionError:
    print('RecursionError')
