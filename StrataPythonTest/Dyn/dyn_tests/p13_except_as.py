# `except E as e` binds `e`, which is unbound after the handler.
def f():
    try:
        g()
    except ValueError as e:
        print(e)
    return e


try:
    pass
except Exception as err:
    pass
