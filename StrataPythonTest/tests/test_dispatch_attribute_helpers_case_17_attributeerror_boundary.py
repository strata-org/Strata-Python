"""getattr defaults and hasattr suppress only AttributeError."""


EVENTS = []


class Source:
    @property
    def absent(self):
        EVENTS.append("absent-getter")
        raise AttributeError("computed absence")

    @property
    def broken(self):
        EVENTS.append("broken-getter")
        raise RuntimeError("not absence")


def make_default():
    EVENTS.append("default")
    return "fallback"


source = Source()
fallback = getattr(source, "absent", make_default())
present = hasattr(source, "absent")

try:
    getattr(source, "broken", "unused")
except RuntimeError:
    propagated = "RuntimeError"
else:
    propagated = "suppressed"

RESULT = (fallback, present, propagated, EVENTS)
