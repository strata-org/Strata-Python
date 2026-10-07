# finally + return: Python runs `cleanup()` before returning 1.
def cleanup():
    pass

def f(x):
    try:
        return 1
    finally:
        cleanup()
