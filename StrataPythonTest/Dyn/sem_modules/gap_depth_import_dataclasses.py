# CPython 3.12 with -S, with 100 frames below this module, runs this operation at depth 853 and
# raises RecursionError at depth 854; the model must stop with a gap at depth 854.
def op():
    import dataclasses
def f(k):
    if k == 0:
        return op()
    return f(k - 1)
try:
    f(854)
    print('ok')
except RecursionError:
    print('RecursionError')
