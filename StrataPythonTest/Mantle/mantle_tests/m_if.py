# `if`/`elif`/`else`, and an `if` whose branches all return.
def classify(x):
    if x < 0:
        r = "neg"
    elif x == 0:
        r = "zero"
    else:
        r = "pos"
    return r

def sign(x):
    if x < 0:
        return -1
    else:
        return 1
