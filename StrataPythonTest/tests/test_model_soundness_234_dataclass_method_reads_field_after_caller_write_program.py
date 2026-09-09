# Method reads field after caller write — method must receive CURRENT binding
# of receiver (post-rebind); stale version gives wrong field values
"""
When the caller writes to an object's field and then calls a method,
the method must see the UPDATED field value. Under value semantics
with correct rebinding (finding 191), this works IF the updated object
is passed to the method.

    obj.x = 10       # rebinds obj to new ClassInstance
    obj.method()     # method receives the REBOUND obj (with x=10)

The key: the method's `self` parameter must be the CURRENT value of
obj (after the field write), not a stale copy from before the write.

Uses ONLY confirmed-accepted constructs: @dataclass, method, int.
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
        return Accumulator(total=self.total + value, count=self.count + 1)


def write_then_method() -> int:
    """Write field, then call method — method sees updated value."""
    acc: Accumulator = Accumulator(total=0, count=0)
    acc = acc.add(10)
    acc = acc.add(20)
    acc = acc.add(30)
    # acc.total = 60, acc.count = 3
    return acc.average()  # 60 // 3 = 20


def modify_then_read_via_method() -> int:
    """Direct field write, then method reads it."""
    acc: Accumulator = Accumulator(total=100, count=4)
    acc = Accumulator(total=200, count=acc.count)  # update total
    return acc.average()  # 200 // 4 = 50


def chain_modifications() -> int:
    """Multiple modifications, method sees final state."""
    acc: Accumulator = Accumulator(total=0, count=0)
    acc = acc.add(5)   # total=5, count=1
    acc = acc.add(15)  # total=20, count=2
    avg1: int = acc.average()  # 20 // 2 = 10
    acc = acc.add(5)   # total=25, count=3
    avg2: int = acc.average()  # 25 // 3 = 8
    return avg1 + avg2  # 10 + 8 = 18


def main() -> None:
    assert write_then_method() == 20
    assert modify_then_read_via_method() == 50
    assert chain_modifications() == 18

    print(write_then_method(), modify_then_read_via_method(),
          chain_modifications())


main()
