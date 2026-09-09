# Witness: raise in a function, caught by an enclosing except.
# CPython: caught == 1 (raise propagates out of parse() to the handler).
# Strata:  `raise` is lowered to a Hole (no propagation); the handler is
#          unreachable, caught stays 0 -> unsound (laurel 14, 274, 385).
def parse(s: str) -> int:
    if s == "":
        raise ValueError("empty")
    return 1

caught: int = 0
try:
    parse("")
except ValueError:
    caught = 1

assert caught == 1
