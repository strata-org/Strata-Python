# An @ensures that PySpec can't translate is recorded as dropped.
@ensures(lambda result: result.bit_length() > 0)
def f() -> int:
    ...
