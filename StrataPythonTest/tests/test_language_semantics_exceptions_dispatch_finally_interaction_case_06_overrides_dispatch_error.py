# An abrupt finally completion replaces the pending dispatch exception.
"""An abrupt finally completion replaces the pending dispatch exception."""


def return_override():
    try:
        object().missing
    finally:
        return "replacement"


def raise_override():
    try:
        object().missing
    finally:
        raise TypeError("cleanup failed")


try:
    raise_override()
except TypeError as error:
    replacement = (
        type(error).__name__,
        type(error.__context__).__name__,
    )
else:
    replacement = ("not raised", None)

RESULT = (return_override(), replacement)
