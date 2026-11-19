# An @admit_raise whose call PySpec reads as its builtin's meaning, but that passes a keyword
# argument, means something else in CPython: it is left out with a warning.
@admit_raise(lambda exc, s: len(s, x=1) >= 1)
def f(s: str) -> None:
    ...
