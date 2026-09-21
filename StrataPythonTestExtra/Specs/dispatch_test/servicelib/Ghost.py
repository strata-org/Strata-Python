# Module-scope spec-only state referenced by contracts below.
ghost(name="floor", type=int, init=0)


@admit(lambda result: result >= floor)
def bounded_value() -> int:
    ...


@admit(lambda result: result == floor)
def floor_value() -> int:
    ...
