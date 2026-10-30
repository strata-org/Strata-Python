# Without "from re import compile", compile is the builtin, which needs more arguments.
def f(s: str) -> None:
    assert compile("a").search(s) is not None
