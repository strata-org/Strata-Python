def parse(flag):
    try:
        if flag:
            raise KeyError("bad")
        x = 1
    except ValueError:
        x = 2
    finally:
        y = x
    return y


def scan(xs):
    total = 0
    for v in xs:
        try:
            if v > 10:
                break
            total = total + v
        finally:
            total = total + 1
    return total


def risky(b):
    if b:
        z = 10
    return z + 1


a = parse(0)
b = scan([1, 2, 30])
c = risky(1)
