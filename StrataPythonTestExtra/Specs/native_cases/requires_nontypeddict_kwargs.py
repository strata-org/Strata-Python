# Non-TypedDict **kwargs are dropped from the model, so contracts that
# reference them must fail loudly at lowering.
@requires(lambda kw: kw['a'] >= 0)
def h(**kw: int) -> int:
    ...
