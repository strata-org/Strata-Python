# Nested functions, a class and imports together.
import os.path
from collections import Counter as C


def make(prefix):
    import json
    count = 0

    class Box:
        label = prefix

        def show(self):
            nonlocal count
            count += 1
            return json.dumps([prefix, count, label])

    def total():
        return lambda: count
    return Box, total
