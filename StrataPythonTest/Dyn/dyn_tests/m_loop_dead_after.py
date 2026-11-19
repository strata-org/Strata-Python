# The code after a loop is not lowered when no `break` leaves the loop and its `else` clause
# returns.
def f(xs):
    for x in xs:
        pass
    else:
        return 1
    return 1j

def g(c):
    while c:
        pass
    else:
        return 1
    return 2
