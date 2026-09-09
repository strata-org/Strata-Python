# Sequence indexing normalizes negatives and preserves boundary errors.
"""Sequence indexing normalizes negatives and preserves boundary errors."""


class Index:
    def __init__(self, value):
        self.value = value

    def __index__(self):
        return self.value


values = [10, 20, 30]
negative = values[Index(-1)]

try:
    values[Index(8)]
except IndexError:
    out_of_range = "IndexError"
else:
    out_of_range = "not raised"

try:
    values[::0]
except ValueError:
    zero_step = "ValueError"
else:
    zero_step = "not raised"

RESULT = (negative, out_of_range, zero_step)
