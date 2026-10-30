# A ghost whose initializer its declared type doesn't accept rejects the model.
ghost(name="g", type=int, init=1.5)

@admit(lambda result: result == g)
def f() -> int:
    ...
