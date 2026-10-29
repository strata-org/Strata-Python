# with and for loops: an exception the with suppresses ends only the with, even a
# StopIteration, and a loop's own end is never confused with an exception in a with body.
log = []

def note(x):
    log.append(x)
    return x

class Suppress:
    def __enter__(self):
        return self
    def __exit__(self, t, v, tb):
        note(v)
        return True

def with_in_loop(xs):
    it = iter(xs)
    for x in it:
        with Suppress():
            note(next(it))  # once it runs out, next(it)'s StopIteration is suppressed ...
        note(x)  # ... so this runs in the same iteration ...
    else:
        note("else")  # ... and the loop ends by running out, which runs the else
    return x

def loop_in_with(xs):
    with Suppress():
        for x in xs:
            raise StopIteration(x)  # leaves the loop for the with, not for the else
        else:
            note("else")  # skipped
        note("after loop")  # skipped
    return "after"
