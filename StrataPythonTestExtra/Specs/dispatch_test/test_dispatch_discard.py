import servicelib


def connect_discard() -> bool:
    servicelib.connect("storage")
    return True
