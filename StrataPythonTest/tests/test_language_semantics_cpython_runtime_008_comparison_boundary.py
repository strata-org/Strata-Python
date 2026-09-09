# Comparison: boundary case. Custom __eq__ with side effects makes comparison
# non-pure. The simplified model would miss the mutation.
"""Comparison: boundary case.
Custom __eq__ with side effects makes comparison non-pure.
The simplified model would miss the mutation.
"""

class Tracker:
    eq_calls = 0

    def __init__(self, val: int):
        self.val = val

    def __eq__(self, other) -> bool:
        Tracker.eq_calls += 1  # side effect!
        if isinstance(other, Tracker):
            return self.val == other.val
        return NotImplemented

if __name__ == "__main__":
    a = Tracker(1)
    b = Tracker(1)
    print(a == b)            # True
    print(Tracker.eq_calls)  # 1 -- side effect from __eq__
    print(a == b)            # True
    print(Tracker.eq_calls)  # 2 -- model treating == as pure would miss this
