# Truth testing: boundary case. Custom __bool__ with side effects makes truth
# testing non-pure.
"""Truth testing: boundary case.
Custom __bool__ with side effects makes truth testing non-pure.
"""

class WeirdBool:
    def __init__(self):
        self.call_count = 0
        self._value = True

    def __bool__(self) -> bool:
        self.call_count += 1  # side effect!
        self._value = not self._value  # alternates!
        return self._value

if __name__ == "__main__":
    w = WeirdBool()
    print(bool(w))  # False (first call: flips True->False)
    print(bool(w))  # True  (second call: flips False->True)
    print(w.call_count)  # 2
    # A simplified model treating bool(w) as a pure predicate would be wrong
    # -- it would predict the same result both times
