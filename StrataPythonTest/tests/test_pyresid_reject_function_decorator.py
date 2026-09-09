def cached(fn):
    return fn


@cached
def compute(x):
    return x
