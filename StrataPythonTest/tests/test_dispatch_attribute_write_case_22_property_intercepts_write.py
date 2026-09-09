"""A property without a setter intercepts writes and raises."""


class Record:
    @property
    def value(self):
        return "managed"

    def method(self):
        return "method"


record = Record()
record.__dict__["value"] = "hidden-instance-value"

try:
    record.value = "new"
except AttributeError:
    property_write = "AttributeError"
else:
    property_write = "stored"

record.method = "shadow"

RESULT = (
    property_write,
    record.value,
    record.__dict__["value"],
    record.method,
)
