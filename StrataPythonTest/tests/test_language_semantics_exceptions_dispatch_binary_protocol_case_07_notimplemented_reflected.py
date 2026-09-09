# NotImplemented advances from the forward to the reflected candidate.
"""NotImplemented advances from the forward to the reflected candidate."""


EVENTS = []


class Left:
    def __add__(self, other):
        EVENTS.append("left-add")
        return NotImplemented


class Right:
    def __radd__(self, other):
        EVENTS.append("right-radd")
        return 41


RESULT = (Left() + Right(), EVENTS)
