# All native method decorators together on one function: each populates its own
# field with no cross-wiring.
@requires(lambda x: x >= 0)
@ensures(lambda result: result >= 0)
@modifies(lambda x: x)
@snapshot(lambda x: x, name="v0")
@ghost(name="g")
def f(x: int) -> int:
    ...
