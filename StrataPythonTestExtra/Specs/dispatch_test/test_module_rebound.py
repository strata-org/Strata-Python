import servicelib

servicelib: int = 42


def use_it():
    return servicelib.connect("storage")
