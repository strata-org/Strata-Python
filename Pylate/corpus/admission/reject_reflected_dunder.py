class Vec2:
    def __radd__(self, other):
        return self

    def __iadd__(self, other):
        return self
