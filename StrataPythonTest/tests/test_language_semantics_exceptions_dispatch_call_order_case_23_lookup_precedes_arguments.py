# Method lookup completes before call arguments are evaluated.
"""Method lookup completes before call arguments are evaluated."""


EVENTS = []


class CallableSource:
    @property
    def operation(self):
        EVENTS.append("lookup")

        def selected(value):
            EVENTS.append(("body", value))
            return value

        return selected


def argument():
    EVENTS.append("argument")
    return 7


RESULT = (CallableSource().operation(argument()), EVENTS)
