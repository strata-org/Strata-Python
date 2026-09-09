"""Exhausting all NotImplemented candidates produces TypeError."""


EVENTS = []


class Left:
    def __add__(self, other):
        EVENTS.append("left-add")
        return NotImplemented


class Right:
    def __radd__(self, other):
        EVENTS.append("right-radd")
        return NotImplemented


try:
    Left() + Right()
except Exception as error:
    RESULT = (type(error).__name__, EVENTS)
else:
    RESULT = ("not raised", EVENTS)
