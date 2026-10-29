# finally + return from inside a loop.
def cleanup():
    pass

def f(xs):
    try:
        for x in xs:
            return x
    finally:
        cleanup()
