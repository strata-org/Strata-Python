# finally + break: `cleanup()` must run before leaving the loop.
def cleanup():
    pass

def f(xs):
    for x in xs:
        try:
            break
        finally:
            cleanup()
    return 0
