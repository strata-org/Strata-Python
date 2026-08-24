state: int = 0


def mark():
    global state
    state = 1
    return 1


def read(value=mark()):
    return value
