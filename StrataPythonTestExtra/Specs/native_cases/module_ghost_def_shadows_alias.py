# A def rebinding a type alias invalidates it for later ghost types.
MyInt = int


def MyInt() -> int:
    ...


ghost(name="g", type=MyInt, init=0)
