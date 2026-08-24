import sys


def helper() -> int:
    return 7


def declare_import():
    global sys


def call_helper() -> int:
    global helper
    return helper()


assert call_helper() == 7, "read-only global declaration preserves function calls"
