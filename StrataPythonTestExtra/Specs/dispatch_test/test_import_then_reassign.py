from servicelib import connect

connect: int = 42


def use_int() -> bool:
    x = connect + 1
    return x > 0
