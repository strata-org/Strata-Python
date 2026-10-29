# `break` outside a loop, here inside a try/finally: CPython's compiler rejects it.
def f():
    try:
        break
    finally:
        pass
