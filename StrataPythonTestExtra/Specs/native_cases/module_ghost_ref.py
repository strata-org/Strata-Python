# A contract may reference a module ghost with its declared type in scope.
ghost(name="counter", type=int, init=0)


@admit(lambda result: result >= counter)
def read_counter() -> int:
    ...
