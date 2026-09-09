# dict.get treats absence as a result and never calls __missing__.
"""dict.get treats absence as a result and never calls __missing__."""


EVENTS = []


class DefaultingDict(dict):
    def __missing__(self, key):
        EVENTS.append(("missing", key))
        return 17


values = DefaultingDict()
subscription = values["x"]
get_result = values.get("y", 23)

RESULT = (subscription, get_result, EVENTS)
