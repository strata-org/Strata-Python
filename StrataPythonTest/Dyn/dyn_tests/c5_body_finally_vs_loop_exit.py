# A try/finally in the loop body, competing with the loop's own exit edge.
def cleanup():
    pass

def note():
    pass

def f(xs):
    for x in xs:
        try:
            cleanup()
        finally:
            note()
    return 0
