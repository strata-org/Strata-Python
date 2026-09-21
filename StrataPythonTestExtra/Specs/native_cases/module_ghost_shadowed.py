# The parameter shadows the module ghost: `counter` here is the int parameter.
ghost(name="counter", type=int, init=0)


@requires(lambda counter: counter >= 0)
def takes_counter(counter: int) -> int:
    ...
