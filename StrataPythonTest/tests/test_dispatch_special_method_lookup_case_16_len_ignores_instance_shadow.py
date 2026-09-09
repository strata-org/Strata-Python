"""Implicit len lookup ignores an instance field named __len__."""


class Sized:
    def __len__(self):
        return 3


value = Sized()
value.__len__ = lambda: 99

RESULT = (value.__len__(), len(value))
