import servicelib


def factory():
    sl = servicelib
    return sl.connect("storage")


def user_fn(sl: int):
    return sl.connect("storage")
