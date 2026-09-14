"""An IndexError subclass from __getitem__ is end-of-sequence, not an error.

CPython catches subclasses in both places that use the legacy sequence protocol:
iterating `Seq()` yields [0, 1] and stops, and `9 in Seq()` is False rather than
propagating. The iteration transfer followed the exception MRO; the membership
transfer matched the class name exactly, so a subclass ended a for loop but
escaped an `in` test -- the same signal with two verdicts.
"""


class PastEnd(IndexError):
    pass


class Seq:
    def __getitem__(self, index: int) -> int:
        if index < 2:
            return index
        raise PastEnd("past end")


def membership_subclass_is_not_found(s: Seq) -> int:
    return 1 if 9 in s else 0


def iteration_subclass_is_exhaustion(s: Seq) -> int:
    total = 0
    for value in s:
        total = total + value
    return total
