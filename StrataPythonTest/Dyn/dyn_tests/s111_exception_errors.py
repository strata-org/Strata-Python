# Test: the TypeErrors and RuntimeError of raise, except and with
class E(Exception):
    pass
class NotExc:
    pass
class OnlyEnter:
    def __enter__(self):
        return 1
def t1():
    raise 1
def t2():
    class B(Exception):
        def __new__(cls):
            return 5
    raise B
def t4():
    try:
        raise E
    except (ValueError, 1):
        pass
def t5():
    raise
def t6():
    with NotExc():
        pass
def t7():
    with OnlyEnter():
        pass
def run(t):
    try:
        t()
    except Exception as e:
        print(t.__name__, type(e).__name__, e.args[0])
run(t1)
run(t2)
run(t4)
run(t5)
run(t6)
run(t7)
