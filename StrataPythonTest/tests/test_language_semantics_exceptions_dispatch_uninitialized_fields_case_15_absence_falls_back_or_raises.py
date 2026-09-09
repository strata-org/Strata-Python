# An annotation does not initialize a field; deletion restores fallback.
"""An annotation does not initialize a field; deletion restores fallback."""


class Record:
    declared_only: str
    value = "class-fallback"


record = Record()
record.value = "instance"
before_delete = record.value
del record.value
after_delete = record.value

try:
    record.declared_only
except AttributeError:
    missing = "AttributeError"
else:
    missing = "present"

RESULT = (before_delete, after_delete, missing)
