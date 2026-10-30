# A ghost without init= or type= still has the invariant that it is defined.
ghost(name="limit")


@requires(lambda x: x <= limit)
def f(x: int) -> None:
    ...
