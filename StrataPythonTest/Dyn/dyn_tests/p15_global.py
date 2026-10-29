# `global x` writes the module's `x`; the module and other functions read it back.
def set_x():
    global x
    x = 1


def get_x():
    return x


set_x()
print(x)
