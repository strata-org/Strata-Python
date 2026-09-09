"""A strict right subclass's reflected override runs before the left method."""


EVENTS = []


class Number:
    def __add__(self, other):
        EVENTS.append("base-add")
        return 50

    def __radd__(self, other):
        EVENTS.append("base-radd")
        return 51


class SubNumber(Number):
    def __radd__(self, other):
        EVENTS.append("sub-radd")
        return 99


RESULT = (Number() + SubNumber(), EVENTS)
