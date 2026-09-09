def pick(k):
    try:
        if k:
            raise KeyError("missing")
        v = 1
    except KeyError as e:
        print(e)
        v = 0
    z = e
    return v


def with_finally(k):
    try:
        if k:
            raise ValueError("bad")
        v = 1
    except ValueError as e:
        return 0
    finally:
        leak = e
    return v


a = pick(1)
b = with_finally(0)
