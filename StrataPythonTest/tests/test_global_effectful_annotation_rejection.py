state: int = 0


def mark():
    global state
    state = 1
    return int


value: mark() = 0
