# @admit lambda binder `q` is neither a parameter nor `result`: recognized
# as an admitted postcondition, but warned as unbound at the use site.
@admit(lambda q: q >= 0)
def f(x: int) -> int:
    ...
