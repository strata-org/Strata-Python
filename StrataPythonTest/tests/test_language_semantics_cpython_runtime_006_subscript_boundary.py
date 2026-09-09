# Subscript: boundary case. User-defined __getitem__ with side effects cannot
# be modeled as a pure read.
"""Subscript: boundary case.
User-defined __getitem__ with side effects cannot be modeled as a pure read.
"""

class LoggingDict:
    def __init__(self):
        self._data = {}
        self.access_count = 0

    def __getitem__(self, key: str):
        self.access_count += 1  # side effect!
        return self._data.get(key, "default")

    def __setitem__(self, key: str, value):
        self._data[key] = value

if __name__ == "__main__":
    d = LoggingDict()
    d["x"] = 42
    print(d["x"])            # 42
    print(d["missing"])      # default
    print(d.access_count)    # 2 -- side effect from __getitem__
    # A simplified model treating [] as pure map read would miss access_count mutation
