# Enum equality narrowing (`j.status == Status.ACTIVE`) invalidated by method
# call that changes the enum field.
"""
a13_enum_narrowing.py — Enum value used after status mutation.

After checking j.status == Status.ACTIVE, a method changes the status.
Code in the narrowed branch uses .value expecting "active" but gets "inactive".
Subtracting 1 from a str → TypeError.

mypy --strict: Success (0 errors)
Runtime: TypeError — unsupported operand type(s) for -: 'str' and 'int'
"""
from enum import Enum

class Status(Enum):
    ACTIVE = "active"
    INACTIVE = "inactive"

class Job:
    def __init__(self) -> None:
        self.status: Status = Status.ACTIVE

    def deactivate(self) -> None:
        self.status = Status.INACTIVE

def process(j: Job) -> object:
    if j.status == Status.ACTIVE:
        j.deactivate()  # changes status to INACTIVE
        # mypy still thinks j.status is ACTIVE in this branch
        # j.status.value is "inactive" (str), not "active"
        return j.status.value - 1  # mypy: str - int → TypeError
    return 0

def main() -> None:
    process(Job())

if __name__ == "__main__":
    main()
