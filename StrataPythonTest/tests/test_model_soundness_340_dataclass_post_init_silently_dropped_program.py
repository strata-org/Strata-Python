# @dataclass `__post_init__` silently dropped — validation/derived-field
# computation never runs; invalid objects accepted, exceptions missed
"""
DATACLASS __post_init__ SILENTLY DROPPED

CPython: @dataclass classes can define __post_init__ which runs after
         the generated __init__. It can validate fields, compute derived
         fields, or raise exceptions.

Model:   The translator generates a constructor that sets fields from args.
         If __post_init__ is defined, it is NEVER CALLED — the method exists
         in the class but the generated __init__ translation doesn't invoke it.

This is a soundness issue because __post_init__ can:
1. Raise exceptions (validation) — model misses the error path
2. Modify fields — model has stale initial values
3. Compute derived fields — model has uninitialized/wrong values
"""
from dataclasses import dataclass


@dataclass
class Temperature:
    celsius: float

    def __post_init__(self: "Temperature") -> None:
        # Validation: reject absolute zero violations
        if self.celsius < -273.15:
            raise ValueError("below absolute zero")


@dataclass
class Segment:
    start: int
    end: int

    def __post_init__(self: "Segment") -> None:
        # Validation: ensure start <= end
        if self.start > self.end:
            raise ValueError("start must be <= end")

    def length(self: "Segment") -> int:
        return self.end - self.start


@dataclass
class NormalizedName:
    raw: str
    normalized: str = ""  # computed in __post_init__

    def __post_init__(self: "NormalizedName") -> None:
        # Derived field: computed from another field
        self.normalized = self.raw.strip().lower()


def create_valid_temp() -> Temperature:
    t: Temperature = Temperature(100.0)
    # CPython: __post_init__ runs, celsius=100.0 passes validation
    # Model: constructor sets celsius=100.0, no validation runs
    return t


def create_invalid_temp() -> Temperature:
    # CPython: __post_init__ raises ValueError("below absolute zero")
    # Model: constructor succeeds, returns Temperature(celsius=-500.0)
    #        The error is MISSED — unsound
    t: Temperature = Temperature(-500.0)
    return t


def create_valid_segment() -> Segment:
    s: Segment = Segment(1, 10)
    return s


def create_invalid_segment() -> Segment:
    # CPython: raises ValueError("start must be <= end")
    # Model: succeeds, returns Segment(start=10, end=1)
    s: Segment = Segment(10, 1)
    return s


def main() -> None:
    # Test 1: valid construction works
    t: Temperature = create_valid_temp()
    assert t.celsius == 100.0

    # Test 2: invalid construction should raise
    raised: bool = False
    try:
        bad_t: Temperature = create_invalid_temp()
    except ValueError:
        raised = True
    # CPython: raised == True
    # Model: raised == False (exception never produced)
    assert raised

    # Test 3: segment validation
    s: Segment = create_valid_segment()
    assert s.length() == 9

    # Test 4: invalid segment should raise
    raised2: bool = False
    try:
        bad_s: Segment = create_invalid_segment()
    except ValueError:
        raised2 = True
    assert raised2

    print("all passed")


main()
