captured = 1


def read(value=captured):
    return value


captured = 2
assert read() == 1
