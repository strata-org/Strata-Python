# INVALID: OLD over `c` without @modifies must be rejected at translation.
ghost(name="c", type=int, init=0)


@admit(lambda result: c == OLD(c) + 1)
def bump() -> None:
    ...
