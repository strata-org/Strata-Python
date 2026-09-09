"""Unsupported exact builtin pairs exhaust the protocol with TypeError."""


def observe():
    try:
        1 < "1"
    except BaseException as error:
        ordering = type(error).__name__

    try:
        1 & 1.0
    except BaseException as error:
        bitwise = type(error).__name__

    try:
        1 << 1.0
    except BaseException as error:
        shift = type(error).__name__

    return ordering, bitwise, shift, type(1 < 1.0).__name__


RESULT = observe()
