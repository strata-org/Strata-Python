# Field write then method call — method must receive post-write ClassInstance;
# stale self gives wrong field values
"""
FIELD WRITE THEN METHOD CALL — METHOD RECEIVES STALE SELF

CPython: obj.x = 10; result = obj.compute()
         compute() sees self.x == 10 (the updated value)

Model:   obj.x = 10 translates to:
           obj = from_ClassInstance("C", DictStrAny_set(attrs, "x", 10))
         obj.compute() translates to:
           C_compute(obj)
         IF the translator correctly rebinds obj before the method call,
         compute() receives the updated ClassInstance. CORRECT.

         BUT: if the translator doesn't rebind (finding 191), or if
         the method call uses a STALE copy of obj from before the write,
         compute() sees the OLD value of x.

This tests the INTERACTION between field write (finding 191) and
subsequent method call (finding 234) in sequence. The method must
receive the POST-WRITE version of the object.
"""
from dataclasses import dataclass


@dataclass
class Accumulator:
    total: int
    count: int

    def average(self: "Accumulator") -> int:
        if self.count == 0:
            return 0
        return self.total // self.count

    def add(self: "Accumulator", value: int) -> "Accumulator":
        return Accumulator(self.total + value, self.count + 1)


class Counter:
    def __init__(self: "Counter", value: int) -> None:
        self.value: int = value

    def get(self: "Counter") -> int:
        return self.value

    def is_positive(self: "Counter") -> bool:
        return self.value > 0


def write_then_read_method(initial: int, new_val: int) -> int:
    """Write field, then call method that reads it."""
    c: Counter = Counter(initial)
    # Write: c.value = new_val
    c = Counter(new_val)  # In subset, must reconstruct (finding 191)
    # Method call: must see new_val, not initial
    return c.get()


def write_then_conditional_method(val: int) -> bool:
    """Write field, then method uses it in condition."""
    c: Counter = Counter(val)
    c = Counter(val * 2)  # double the value
    return c.is_positive()


def sequential_modifications() -> int:
    """Multiple writes then method call."""
    acc: Accumulator = Accumulator(0, 0)
    acc = acc.add(10)
    acc = acc.add(20)
    acc = acc.add(30)
    # acc should now have total=60, count=3
    # average() must see the FINAL state
    return acc.average()


def main() -> None:
    # Test 1: write then method sees new value
    result: int = write_then_read_method(5, 42)
    # CPython: 42 (method sees updated value)
    # Model (if stale): 5 (method sees original value)
    assert result == 42

    # Test 2: write then conditional method
    assert write_then_conditional_method(3)   # 3*2=6 > 0
    assert not write_then_conditional_method(-1)  # -1*2=-2 not > 0

    # Test 3: sequential modifications
    avg: int = sequential_modifications()
    # CPython: 60 // 3 = 20
    # Model (if stale): 0 // 0 or wrong values
    assert avg == 20

    print("all passed")


main()
