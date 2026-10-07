# A module global mutated after the `def` is read by the function at call time.
counter = 0


def read():
    return counter


counter = 5
print(read())
