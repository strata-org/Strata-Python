# `self.field += value` — augmented assignment on object fields requires
# rebinding self AND propagating to caller; value semantics loses both
"""
Augmented assignment on object fields (`self.x += 1`) desugars to
`self.x = self.x + 1` in CPython. But in the value-semantics model,
`self` is a from_ClassInstance value. Reading `self.x` extracts from
the DictStrAny, and writing `self.x = ...` must produce a NEW
ClassInstance with updated attrs. If the translator doesn't rebind
`self` to the new instance, subsequent reads of `self.x` see the old
value. Furthermore, the CALLER's reference to the object is never
updated (value semantics), so mutations through methods are invisible.
"""
from dataclasses import dataclass


@dataclass
class Accumulator:
    total: int
    count: int

    def add(self: "Accumulator", value: int) -> None:
        self.total += value  # self.total = self.total + value
        self.count += 1      # self.count = self.count + 1

    def average(self: "Accumulator") -> int:
        if self.count == 0:
            return 0
        return self.total // self.count


def accumulate_values(acc: Accumulator, values: list[int]) -> None:
    for v in values:
        acc.add(v)


def main() -> None:
    acc: Accumulator = Accumulator(total=0, count=0)

    # Method mutates fields via augmented assignment
    acc.add(10)
    acc.add(20)
    acc.add(30)

    # CPython: acc.total = 60, acc.count = 3
    assert acc.total == 60
    assert acc.count == 3
    assert acc.average() == 20

    # Mutation through function call
    acc2: Accumulator = Accumulator(total=0, count=0)
    accumulate_values(acc2, [5, 15, 25])

    # CPython: acc2.total = 45, acc2.count = 3
    # Model: acc2 unchanged (value passed to function, mutations invisible)
    assert acc2.total == 45
    assert acc2.count == 3
    assert acc2.average() == 15

    print(acc.total, acc.count, acc2.total, acc2.count)


main()
