# with: __exit__'s result is tested for truth only when the body raised; on every other way
# out of the body it is ignored.
log = []

def note(x):
    log.append(x)
    return x

class Flag:
    # A result whose truth test shows in the log, and raises for value None.
    def __init__(self, value):
        self.value = value
    def __bool__(self):
        note("bool")
        if self.value is None:
            raise ValueError("bool")
        return self.value

class Ctx:
    def __init__(self, result):
        self.result = result
    def __enter__(self):
        return self
    def __exit__(self, t, v, tb):
        note("exit")
        return self.result

def raises(result):
    with Ctx(result):
        # Suppressed if bool(result) is true, e.g. for 1 or [0].  If bool(result) raises, its
        # exception propagates, with this KeyError as its __context__.
        raise KeyError("body")
    return "after"  # reached only when suppressed

def falls_off(result):
    with Ctx(result):
        note("body")
    return "after"  # bool(result) is never computed: Flag(None) does not raise

def returns(result):
    with Ctx(result):
        return "body"  # a true result does not cancel the return
    return "after"
