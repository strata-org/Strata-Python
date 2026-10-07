# `match` is rejected, but its captures still bind.
def f(cmd):
    match cmd:
        case [x, *rest]:
            return x, rest
        case {"k": v, **others}:
            return v, others
        case Point(x=px) as whole:
            return px, whole
        case _:
            return None
