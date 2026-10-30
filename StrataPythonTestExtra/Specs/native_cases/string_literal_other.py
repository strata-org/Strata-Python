# A comparison with a string literal outside the known patterns is dropped.
def f(x: str) -> None:
    assert x > "a", "x must sort after a"
