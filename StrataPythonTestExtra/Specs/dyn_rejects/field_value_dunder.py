# Class creation gives __slots__ a meaning, so a field of that name has no value.
class C:
    __slots__: int = 0
