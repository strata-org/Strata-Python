# Attribute write: supported case. Known class, declared field, no
# descriptors.
"""Attribute write: supported case.
Known class, declared field, no descriptors.
"""

class Counter:
    __slots__ = ('value',)

    def __init__(self, value: int = 0) -> None:
        self.value = value

    def increment(self) -> None:
        self.value += 1

if __name__ == "__main__":
    c = Counter(10)
    c.value = 20
    print(c.value)  # 20
    c.increment()
    print(c.value)  # 21
