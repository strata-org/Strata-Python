# Test: try, except, finally, a bare raise, and the __context__ chain with its cycle cut
try:
    1 // 0
except ZeroDivisionError as e:
    print("caught", e.args[0])
try:
    {}[1]
except (ValueError, KeyError):
    print("tuple")
try:
    try:
        1 // 0
    except ZeroDivisionError:
        {}["k"]
except KeyError as e:
    print(type(e.__context__) is ZeroDivisionError, e.__cause__ is None, e.__suppress_context__)
try:
    try:
        1 // 0
    finally:
        print("finally")
except ZeroDivisionError:
    print("after finally")
try:
    raise
except RuntimeError as e:
    print(e.args[0])
def f():
    try:
        1 // 0
    except ZeroDivisionError:
        raise
try:
    f()
except ZeroDivisionError as e:
    print("reraised", e.__context__)
try:
    try:
        raise ValueError("a")
    except ValueError as a:
        try:
            raise KeyError("b")
        except KeyError as b:
            bb = b
            raise a
except ValueError as x:
    print(x.__context__ is bb, bb.__context__ is None)
