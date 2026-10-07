# finally + continue: `cleanup()` must run before the next iteration.
def cleanup():
    pass

def f(xs):
    for x in xs:
        try:
            continue
        finally:
            cleanup()
    return 0
