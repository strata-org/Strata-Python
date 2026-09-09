# A live missing-member table cell is a catchable Python exception.
"""A live missing-member table cell is a catchable Python exception."""


class B:
    pass


try:
    B().only_a()
except AttributeError as error:
    RESULT = (type(error).__name__, "only_a" in str(error))
else:
    RESULT = ("not raised", False)
