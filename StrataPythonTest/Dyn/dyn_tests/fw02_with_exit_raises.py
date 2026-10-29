# with: an exception that __exit__ raises replaces however the body ended, and __exit__ is not
# called again for it.
log = []

def note(x):
    log.append(x)
    return x

class Failing:
    def __enter__(self):
        return self
    def __exit__(self, t, v, tb):
        note(v)  # one call per with, also when it raises
        raise ValueError("exit")

def on_raise():
    with Failing():
        raise KeyError("body")  # replaced by __exit__'s ValueError, whose __context__ it is

def on_normal():
    with Failing():
        note("body")  # __exit__'s ValueError has no __context__

def on_return():
    try:
        with Failing():
            return "body"  # dropped: __exit__'s ValueError reaches the except clause below
    except ValueError as e:
        return e

def in_handler():
    try:
        raise KeyError("handled")
    except KeyError:
        with Failing():
            note("body")  # __exit__'s ValueError has the KeyError being handled as its __context__
