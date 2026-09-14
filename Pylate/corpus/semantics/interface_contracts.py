# Interface annotations are assume-guarantee: asserted at the call, assumed in
# the body. The slice of the argument that satisfies the annotation continues
# into the body; the slice that does not aborts.
#   satisfied          - discharged statically, no obligation
#   partial_violation  - the good slice continues, the bad slice aborts
#   definite_violation - everything aborts, and an extra obligation says so,
#                        because a body analysed against bottom returns bottom
#                        and would leave the rest of the caller vacuously fine
#
# The abort is our semantics, not CPython's. CPython accepts the ill-typed
# argument and only raises later, if the body uses it in a way that raises. So
# the abort is uncatchable and is never modelled as a TypeError edge under any
# policy preset -- an edge would put an exception in `may_raise` that no
# execution produces, and a handler would appear to recover from it.
class Box:
    def foo(self, y: int) -> int:
        return y + 1


def definite_violation(b: Box) -> int:
    return b.foo(None)


def partial_violation(n: int, b: Box) -> int:
    y = 5 if n == 0 else None
    return b.foo(y)


def satisfied(n: int, b: Box) -> int:
    return b.foo(n)


def handler_cannot_catch_it(b: Box) -> int:
    # `except TypeError` catches nothing here, so it must not suppress the
    # abort. A modelled edge would have been caught and the return silently
    # rerouted to 0.
    try:
        return b.foo(None)
    except TypeError:
        return 0
