# return through a finally or a with: the value is computed first, in the try or with body, and
# then the finally body or __exit__ runs.  A returned closure sees what the finally body assigns.
log = []

def note(x):
    log.append(x)
    return x

def deletes():
    x = "try"
    try:
        return x
    finally:
        del x  # no UnboundLocalError: the function returns "try"

def closure():
    x = "try"
    try:
        return lambda: x
    finally:
        x = "finally"  # the returned function reads x's cell: it returns "finally"

class Box:
    def __init__(self, value, suppress):
        self.value = value
        self.suppress = suppress
    def __enter__(self):
        return self
    def __exit__(self, t, v, tb):
        note(v)
        self.value = "exit"
        return self.suppress

def in_with():
    with Box("body", False) as b:
        return note(b.value)  # "body": read before __exit__ changes it

def value_raises():
    with Box("body", True) as b:
        return b.missing  # AttributeError inside the with: __exit__ gets it and suppresses it
    return "after"  # so the function returns here
