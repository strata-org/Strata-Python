# Implicit `return None` — `-> None` functions falling off end must produce
# `from_None()`; if missing, return is Hole
"""
A function annotated `-> None` that reaches the end of its body without
an explicit `return` implicitly returns None. The model must produce
`from_None()` as the return value. If it produces Hole or doesn't
return anything, callers that check the return value get garbage.
"""


def greet(name: str) -> None:
    print("Hello, " + name)
    # No explicit return — implicitly returns None


def modify_and_return_nothing(lst: list[int]) -> None:
    lst = lst + [99]  # local modification (value semantics)
    # Falls off end — returns None


def conditional_return(x: int) -> None:
    if x > 0:
        return  # explicit return None
    # else: falls off end — also returns None


def void_chain() -> None:
    """Multiple void functions called in sequence."""
    greet("Alice")
    greet("Bob")
    # Falls off end


def check_return_is_none() -> bool:
    """The return value of a -> None function IS None."""
    result = greet("test")  # type: ignore
    return result is None


def main() -> None:
    # Void functions work
    greet("World")
    modify_and_return_nothing([1, 2])
    conditional_return(5)
    conditional_return(-1)
    void_chain()

    # Return value is None
    assert check_return_is_none() == True

    # Explicit None return
    r = conditional_return(5)  # type: ignore
    assert r is None

    print("done")


main()
