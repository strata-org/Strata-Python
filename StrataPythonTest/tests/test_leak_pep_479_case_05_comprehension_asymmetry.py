"""Case 5 (PEP 479): A genexp boundary changes a body StopIteration."""


def exception_name(thunk):
    try:
        thunk()
    except BaseException as error:
        return type(error).__name__
    return "no exception"


def bad_iterable():
    raise StopIteration("while evaluating the outermost iterable")


RESULT = {
    "listcomp": exception_name(
        lambda: [next(iter([])) for _ in range(3)]
    ),
    "genexp": exception_name(
        lambda: list(next(iter([])) for _ in range(3))
    ),
    "setcomp": exception_name(
        lambda: {next(iter([])) for _ in range(3)}
    ),
    "dictcomp": exception_name(
        lambda: {index: next(iter([])) for index in range(3)}
    ),
    "genexp_outermost_iterable": exception_name(
        lambda: (item for item in bad_iterable())
    ),
}


if __name__ == "__main__":
    print(repr(RESULT))
