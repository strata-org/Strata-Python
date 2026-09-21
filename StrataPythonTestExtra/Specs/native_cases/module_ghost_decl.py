# `counter` has an explicit initializer; `flag` is left nondeterministic.
ghost(name="counter", type=int, init=0)
ghost(name="flag", type=bool)


@admit(lambda result: result >= counter)
def read_counter() -> int:
    ...
