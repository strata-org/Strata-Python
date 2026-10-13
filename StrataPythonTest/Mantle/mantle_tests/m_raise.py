# raise and raise … from …
class Oops(Exception):
    pass

def instance(msg):
    raise ValueError(msg)

def cls():
    raise Oops

def cause(e):
    raise Oops from e

def no_cause():
    raise Oops("quiet") from None

def in_loop(xs):
    for x in xs:
        if x:
            raise KeyError(x)
    return 0

def both(x):
    if x:
        raise KeyError
    else:
        raise ValueError
    return 1

def reraise():
    raise

def gen(e):
    raise e from (yield)
