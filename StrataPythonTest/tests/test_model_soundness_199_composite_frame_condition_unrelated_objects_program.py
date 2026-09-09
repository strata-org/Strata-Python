# Composite frame conditions — after method on object A, unrelated objects B,C
# must be provably unchanged; value semantics gives this free
"""
Frame conditions: after a method call on object A, all UNRELATED objects
must retain their field values. Under Composite/heap semantics, this
requires explicit frame conditions (what DIDN'T change).

Finding 106 identified this. This finding provides a systematic test:
after calling a method on one object, verify that N other objects are
all unchanged. The solver must be able to prove this.

Under value semantics (ClassInstance), frame conditions are FREE —
objects are independent values. Under Composite, the solver needs
explicit `ensures old(b.field) == b.field` for every unrelated object.

Uses ONLY confirmed-accepted constructs: @dataclass, method, int, list.
"""
from dataclasses import dataclass


@dataclass
class Sensor:
    id: int
    reading: int

    def update(self: "Sensor", new_reading: int) -> "Sensor":
        return Sensor(id=self.id, reading=new_reading)


def one_update_others_preserved() -> bool:
    """Update one sensor, verify all others unchanged."""
    s1: Sensor = Sensor(id=1, reading=10)
    s2: Sensor = Sensor(id=2, reading=20)
    s3: Sensor = Sensor(id=3, reading=30)

    # Update only s2
    s2 = s2.update(99)

    # s1 and s3 must be provably unchanged
    return (s1.reading == 10 and s2.reading == 99 and s3.reading == 30
            and s1.id == 1 and s3.id == 3)


def update_in_loop_preserves_others() -> int:
    """Update sensors in sequence — each preserves the others."""
    sensors: list[Sensor] = [
        Sensor(id=0, reading=0),
        Sensor(id=1, reading=0),
        Sensor(id=2, reading=0),
    ]

    # Update each sensor independently
    sensors[0] = sensors[0].update(100)
    sensors[1] = sensors[1].update(200)
    sensors[2] = sensors[2].update(300)

    # Each has its own value
    return sensors[0].reading + sensors[1].reading + sensors[2].reading  # 600


def function_call_preserves_unrelated() -> int:
    """Calling a function that modifies one object preserves others."""
    a: Sensor = Sensor(id=1, reading=50)
    b: Sensor = Sensor(id=2, reading=75)

    def double_reading(s: Sensor) -> Sensor:
        return s.update(s.reading * 2)

    a = double_reading(a)
    # b must be unchanged
    return a.reading + b.reading  # 100 + 75 = 175


def main() -> None:
    assert one_update_others_preserved() == True
    assert update_in_loop_preserves_others() == 600
    assert function_call_preserves_unrelated() == 175

    print(one_update_others_preserved(),
          update_in_loop_preserves_others(),
          function_call_preserves_unrelated())


main()
