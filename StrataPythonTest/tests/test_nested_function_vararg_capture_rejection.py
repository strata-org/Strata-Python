# A nested function that declares *args AND reads an enclosing binding is
# rejected up-front: the lifted procedure's declared inputs include the vararg
# slot, but call sites emit no positional value for it, so appending the capture
# arguments would misalign the call (previously an internal arity error).
def outer(a: int) -> int:
    bonus: int = 10
    def inner(*args: int) -> int:
        return bonus
    return inner(1)


outer(0)
