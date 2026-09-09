# An exception from a selected candidate stops binary fallback.
"""An exception from a selected candidate stops binary fallback."""


EVENTS = []


class Left:
    def __add__(self, other):
        EVENTS.append("left-add")
        raise KeyError("forward failed")


class Right:
    def __radd__(self, other):
        EVENTS.append("right-radd")
        return 41


try:
    Left() + Right()
except Exception as error:
    RESULT = (type(error).__name__, EVENTS)
else:
    RESULT = ("not raised", EVENTS)
