# @ensures and @admit on one function populate their own stores with no
# cross-wiring: the verified and the admitted postcondition stay distinct.
@ensures(lambda result: result >= 0)
@admit(lambda result: result <= 100)
def f(x: int) -> int:
    ...
