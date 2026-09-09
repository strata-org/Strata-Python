# A data-descriptor property wins over a same-named instance field.
"""A data-descriptor property wins over a same-named instance field."""


class Record:
    def __init__(self):
        self.__dict__["value"] = "instance"

    @property
    def value(self):
        return "property"


record = Record()
RESULT = (record.value, record.__dict__["value"])
