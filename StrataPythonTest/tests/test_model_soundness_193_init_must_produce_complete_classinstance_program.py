# `__init__` must produce complete ClassInstance — all declared fields must be
# assigned on all paths; needs definite-assignment check
"""
`__init__` must produce a COMPLETE ClassInstance with ALL declared fields.
If __init__ has conditional paths where some fields are not assigned,
the resulting ClassInstance has missing keys in its attrs dict.

Reading a missing field returns Hole (finding 081). The model must
either:
1. Verify that __init__ assigns ALL fields on ALL paths
2. Or emit postconditions that all declared fields are present

For @dataclass, this is automatic (all fields are constructor params).
For regular classes with __init__, the translator must verify completeness.

Uses ONLY confirmed-accepted constructs: class, __init__, int, str.
"""
from dataclasses import dataclass


@dataclass
class Complete:
    """@dataclass guarantees all fields are set."""
    x: int
    y: int
    z: int


class ManualInit:
    """Manual __init__ — must set all fields."""
    name: str
    value: int
    active: bool

    def __init__(self: "ManualInit", name: str, value: int) -> None:
        self.name = name
        self.value = value
        self.active = True  # always set

    def get_name(self: "ManualInit") -> str:
        return self.name

    def get_value(self: "ManualInit") -> int:
        return self.value

    def is_active(self: "ManualInit") -> bool:
        return self.active


class ConditionalInit:
    """Fields conditionally set — problematic."""
    base: int
    bonus: int

    def __init__(self: "ConditionalInit", base: int, has_bonus: bool) -> None:
        self.base = base
        if has_bonus:
            self.bonus = 50
        else:
            self.bonus = 0  # MUST set on all paths!

    def total(self: "ConditionalInit") -> int:
        return self.base + self.bonus


def dataclass_always_complete() -> int:
    c: Complete = Complete(x=1, y=2, z=3)
    return c.x + c.y + c.z  # 6


def manual_init_complete() -> str:
    m: ManualInit = ManualInit(name="test", value=42)
    return m.get_name()


def conditional_init_both_paths() -> int:
    c1: ConditionalInit = ConditionalInit(base=100, has_bonus=True)
    c2: ConditionalInit = ConditionalInit(base=100, has_bonus=False)
    return c1.total() + c2.total()  # 150 + 100 = 250


def main() -> None:
    assert dataclass_always_complete() == 6
    assert manual_init_complete() == "test"
    assert conditional_init_both_paths() == 250

    m: ManualInit = ManualInit(name="hello", value=99)
    assert m.is_active() == True
    assert m.get_value() == 99

    print(dataclass_always_complete(), manual_init_complete(),
          conditional_init_both_paths())


main()
