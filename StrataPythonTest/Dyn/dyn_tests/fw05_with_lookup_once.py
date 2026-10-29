# with: __enter__ and __exit__ are both looked up on the manager's type before __enter__ is
# called, and the __exit__ found then is the one that runs.
log = []

def note(x):
    log.append(x)
    return x

class Ctx:
    def __enter__(self):
        note("enter")
        return "value"
    def __exit__(self, t, v, tb):
        note("exit")
        return False

def other_exit(self, t, v, tb):
    note("other exit")
    return False

def replaced_in_body():
    class Local(Ctx):
        pass
    with Local():
        Local.__exit__ = other_exit  # too late for this with: its __exit__ was found already
    with Local():
        note("body")  # this with finds other_exit

def rebound_manager():
    m = Ctx()
    with m as m:  # rebinding m does not change whose __exit__ runs
        note(m)
    return m

class NoExit:
    def __enter__(self):
        note("enter")  # never called
        return self

def missing_exit():
    # TypeError: 'NoExit' object does not support the context manager protocol (missed
    # __exit__ method), raised before __enter__ is called.
    with NoExit():
        note("body")
