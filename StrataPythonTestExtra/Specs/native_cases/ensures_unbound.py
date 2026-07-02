# @ensures lambda binder `q` is neither a parameter nor `result`: recognized
# as a postcondition, but warned as unbound at the use site.
@ensures(lambda q: q >= 0)
def f(x: int) -> int:
    ...
