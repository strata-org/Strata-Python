"""Membership prefers __contains__; iteration prefers __iter__."""


EVENTS = []


class Protocols:
    def __contains__(self, value):
        EVENTS.append("contains")
        return value == 2

    def __iter__(self):
        EVENTS.append("iter")
        return iter([1, 2])

    def __getitem__(self, index):
        EVENTS.append(("getitem", index))
        return [1, 2][index]


value = Protocols()
membership = 2 in value
iteration = list(value)

RESULT = (membership, iteration, EVENTS)
