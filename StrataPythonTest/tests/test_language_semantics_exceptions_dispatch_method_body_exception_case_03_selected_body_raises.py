# Failure after successful lookup is not an AttributeError table cell.
"""Failure after successful lookup is not an AttributeError table cell."""


EVENTS = []


class A:
    def work(self):
        EVENTS.append("body")
        raise ValueError("selected body failed")


try:
    A().work()
except Exception as error:
    RESULT = (type(error).__name__, EVENTS)
else:
    RESULT = ("not raised", EVENTS)
