"""A dispatch exception enters handlers and skips the try-else suite."""


EVENTS = []


class Good:
    def work(self):
        EVENTS.append("body")


class Missing:
    pass


def run(value):
    try:
        value.work()
    except AttributeError:
        EVENTS.append("handler")
    else:
        EVENTS.append("else")


run(Good())
run(Missing())
RESULT = EVENTS
